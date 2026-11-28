import Lean

/-!
Saturation engine, compiled natively (`precompileModules`); imports only Lean.
The rules, lemmas and `linarith` come from `SystemE.Meta.Tactics.Saturate`.

Facts are literals from the context. Each rule `∀ objs, P₁ ∧ … → Q₁ ∧ …`
gives clauses: a forward one per conclusion, and contrapositives
(other premises, `¬Qⱼ` ⊢ `¬Pₖ`). Diagrammatic clauses fire forward until
nothing new follows; any clause may be used backward on a goal literal, with
metric literals proved by `linarith only` over the metric facts.
-/

open Lean Elab Tactic Meta

register_option systemE.saturate : Bool := {
  defValue := true
  descr := "Try saturation (kernel-checked) before the SMT solvers."
}

register_option systemE.saturateBudget : Nat := {
  defValue := 20000
  descr := "Heartbeats (in thousands) one saturation attempt may spend before giving up."
}

register_option systemE.stats : Bool := {
  defValue := false
  descr := "Log whether each step was closed by saturation or sent to the solvers."
}

register_option systemE.smt : Bool := {
  defValue := true
  descr := "Fall back to the SMT solvers when saturation fails."
}

namespace SystemE.Saturate

/-- Head relation of a literal, with its polarity. -/
def head (e : Expr) : Option (Name × Bool) :=
  if e.ne?.isSome then some (``Eq, false) else
  match e.not? with
  | some p => p.getAppFn.constName?.map (·, false)
  | none => e.getAppFn.constName?.map (·, true)

structure Fact where
  type : Expr
  proof : Expr
deriving Inhabited

/-- Facts whose head can match `e`'s. -/
def candidates (facts : Array Fact) (e : Expr) : Array Fact :=
  match head e with
  | some h => facts.filter fun f => head f.type == some h
  | none => facts

/-- What the engine needs from System E: lemma names and a `linarith` call. -/
structure Config where
  /-- Lemmas used like System E's inference axioms. -/
  lemmas : Array Name := #[]
  /-- Multi-step lemmas, used only backward, without contrapositives. -/
  backwardLemmas : Array Name := #[]
  /-- Lemmas with one metric premise, applied forward when `linarith` proves it. -/
  guardedLemmas : Array Name := #[]
  /-- Sorts of the objects rules are instantiated with. -/
  objectSorts : Array Name := #[`Point, `Line, `Circle]
  /-- Prove the goal from the given proofs by `linarith only`. -/
  linarith : List Expr → Expr → MetaM (Option Expr) := fun _ _ => pure none
deriving Inhabited

initialize configRef : IO.Ref Config ← IO.mkRef {}

/-- Per clause: time (ns) and facts produced; filled when `systemE.stats` is on. -/
initialize profRef : IO.Ref (Std.HashMap String (Nat × Nat)) ← IO.mkRef {}

/-- Depth of backward chaining. -/
def maxDepth : Nat := 3

def maxRounds : Nat := 10
def maxFacts : Nat := 2000

/-- Split `h : e` into its conjuncts; `¬ a = b` is also stored as `a ≠ b`. -/
partial def project (e h : Expr) : MetaM (Array Fact) := do
  match (← whnfR e).and? with
  | some (p, q) =>
    return (← project p (mkApp3 (mkConst ``And.left) p q h)) ++
           (← project q (mkApp3 (mkConst ``And.right) p q h))
  | none =>
    if let some p := e.not? then
      if let some (t, x, y) := p.eq? then
        let u ← getLevel t
        return #[⟨mkApp3 (mkConst ``Ne [u]) t x y, h⟩]
    return #[⟨e, h⟩]

partial def literals (e : Expr) : MetaM (List Expr) := do
  let e ← instantiateMVars e
  match (← whnfR e).and? with
  | some (p, q) => return (← literals p) ++ (← literals q)
  | none => return [e.consumeMData]

/-- Facts indexed by statement and by head. -/
structure Store where
  facts : Array Fact
  map : Std.HashMap Expr Expr
  byHead : Std.HashMap (Option (Name × Bool)) (Array Fact)

def Store.of (facts : Array Fact) : Store :=
  facts.foldl (fun s f => { s with
    map := if s.map.contains f.type then s.map else s.map.insert f.type f.proof
    byHead := s.byHead.alter (head f.type) fun a => some ((a.getD #[]).push f) })
    ⟨facts, {}, {}⟩

/-- A fact stating `e`, compared structurally (facts are normalized by `project`). -/
def find (facts : Array Fact) (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  return (facts.find? (·.type == e)).map (·.proof)

/-- A fact stating `e` up to reducible unfolding; for goal literals as written. -/
def findDefEq (facts : Array Fact) (e : Expr) : MetaM (Option Expr) := do
  if let some p ← find facts e then return p
  for f in candidates facts e do
    if ← withReducible (isDefEq e f.type) then return some f.proof
  return none

/-- `¬(p ∧ q)` (up to reducible unfolding, as `¬x.outsideCircle α`) as `(p, q)`. -/
def notAnd? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some x := e.not? | return none
  return (← whnfR x).and?

/-- Prove a conjunction, each literal by `leaf`. -/
partial def prove (leaf : Expr → MetaM (Option Expr)) (e : Expr)
    (quick : Expr → MetaM (Option Expr) := fun _ => pure none) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  -- `¬(p ∧ q)` from `¬p` or `¬q`, a known fact first
  if let some (p, q) ← notAnd? e then
    let pq := mkApp2 (mkConst ``And) p q
    let sides := [(p, mkApp2 (mkConst ``And.left) p q), (q, mkApp2 (mkConst ``And.right) p q)]
    for look in [quick, leaf] do
      for (r, pr) in sides do
        if let some hr ← prove look (mkNot r) then
          return some (← withLocalDeclD `h pq fun h => mkLambdaFVars #[h] (mkApp hr (mkApp pr h)))
    return none
  -- `¬¬p` from `p`
  if let some x := e.not? then
    if let some p := x.not? then
      let some hp ← prove leaf p quick | return none
      return some (← withLocalDeclD `h x fun h => mkLambdaFVars #[h] (mkApp h hp))
  match (← whnfR e).and? with
  | some (p, q) =>
    let some hp ← prove leaf p quick | return none
    let some hq ← prove leaf q quick | return none
    return mkApp4 (mkConst ``And.intro) p q hp hq
  | none =>
    -- a disjunction by either side
    match (← whnfR e).app2? ``Or with
    | some (p, q) =>
      if let some hp ← prove leaf p quick then return mkApp3 (mkConst ``Or.inl) p q hp
      if let some hq ← prove leaf q quick then return mkApp3 (mkConst ``Or.inr) p q hq
      return none
    | none => leaf e

def isArith (e : Expr) : MetaM Bool := do
  match e.getAppFnArgs with
  | (``Eq, #[t, _, _]) | (``LT.lt, #[t, _, _, _]) | (``LE.le, #[t, _, _, _])
  | (``GT.gt, #[t, _, _, _]) | (``GE.ge, #[t, _, _, _]) =>
    return (← instantiateMVars t).isConstOf `Real
  | _ => return false

/-- `x ≠ y` over the reals. -/
def isRealNe (e : Expr) : MetaM Bool := do
  match e.ne? with
  | some (t, _, _) => return (← instantiateMVars t).isConstOf `Real
  | none => return false

/-- A fact `linarith` can use: a comparison, its negation, or `≠` (by cases). -/
def isMetricFact (e : Expr) : MetaM Bool := do
  if ← isArith e then return true
  if ← isRealNe e then return true
  match e.not? with
  | some p => isArith p
  | none => return false

/-- Segments `|(x─y)|` occurring in `e`, as endpoint pairs. -/
partial def segments (e : Expr) (acc : Array (Expr × Expr) := #[]) : Array (Expr × Expr) :=
  if e.isAppOfArity `Segment.length 1 then
    match e.appArg!.getAppFnArgs with
    | (`Segment.endpoints, #[x, y]) => acc.push (x, y)
    | _ => acc
  else match e with
    | .app f a => segments a (segments f acc)
    | _ => acc

/-- Angles `∠ x:y:z` occurring in `e`. -/
partial def angles (e : Expr) (acc : Array (Expr × Expr × Expr) := #[]) :
    Array (Expr × Expr × Expr) :=
  if e.isAppOfArity `Angle.degree 1 then
    match e.appArg!.getAppFnArgs with
    | (`Angle.ofPoints, #[x, y, z]) => acc.push (x, y, z)
    | _ => acc
  else match e with
    | .app f a => angles a (angles f acc)
    | _ => acc

/-- Triangles `△ x:y:z` whose areas occur in `e`. -/
partial def triangles (e : Expr) (acc : Array (Expr × Expr × Expr) := #[]) :
    Array (Expr × Expr × Expr) :=
  if e.isAppOfArity `Triangle.area 1 then
    match e.appArg!.getAppFnArgs with
    | (`Triangle.ofPoints, #[x, y, z]) => acc.push (x, y, z)
    | _ => acc
  else match e with
    | .app f a => triangles a (triangles f acc)
    | _ => acc

/-- Space's measures (Book 11): head and arity. -/
def spaceHeads : Array (Name × Nat) :=
  #[(`Space.dist, 2), (`Space.angle, 3), (`Space.area, 3), (`Space.volume, 4)]

def isSpaceAtom (e : Expr) : Bool := spaceHeads.any fun (n, k) => e.isAppOfArity n k

/-- Space measures occurring in `e`. -/
partial def spaceTerms (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if isSpaceAtom e then (if acc.contains e then acc else acc.push e)
  else match e with
    | .app f a => spaceTerms a (spaceTerms f acc)
    | _ => acc

/-- The generators of a space measure's symmetries: lemma and permutation. -/
def spaceGens : Name → Array (Name × Array Nat)
  | `Space.dist => #[(`Space.dist_symm, #[1, 0])]
  | `Space.area => #[(`Space.area_symm_1, #[1, 2, 0]), (`Space.area_symm_2, #[0, 2, 1])]
  | `Space.volume => #[(`Space.volume_symm_1, #[1, 0, 2, 3]),
      (`Space.volume_symm_2, #[0, 2, 1, 3]), (`Space.volume_symm_3, #[0, 1, 3, 2])]
  | _ => #[]

/-- `s = t` for space measures `t` a permutation of `s`, by the generators. -/
def spacePerm (s t : Expr) : MetaM (Option Expr) := do
  let some n := s.getAppFn.constName? | return none
  let gens := spaceGens n
  let mut queue := #[(s.getAppArgs, ← mkEqRefl s)]
  let mut i := 0
  for _ in [0:24] do
    if i ≥ queue.size then break
    let (xs, p) := queue[i]!
    i := i + 1
    if xs == t.getAppArgs then return some p
    for (lem, perm) in gens do
      let ys := perm.map (xs[·]!)
      unless queue.any (·.1 == ys) do
        queue := queue.push (ys, ← mkEqTrans p (mkAppN (mkConst lem) xs))
  return none

def areaOf (t : Expr × Expr × Expr) : Expr :=
  mkApp (mkConst `Triangle.area) (mkApp3 (mkConst `Triangle.ofPoints) t.1 t.2.1 t.2.2)

/-- `area △s = area △t` for a permutation `t` of `s`, by rotations and swaps. -/
def areaPerm (s t : Expr × Expr × Expr) : MetaM (Option Expr) := do
  let mut queue := #[(s, ← mkEqRefl (areaOf s))]
  let mut i := 0
  for _ in [0:6] do
    if i ≥ queue.size then break
    let ((a, b, c), p) := queue[i]!
    i := i + 1
    if (a, b, c) == t then return some p
    for (h, q) in [(mkApp3 (mkConst `area_symm_1) a b c, (c, a, b)),
                   (mkApp3 (mkConst `area_symm_2) a b c, (a, c, b))] do
      unless queue.any (·.1 == q) do queue := queue.push (q, ← mkEqTrans p h)
  return none

/-- Unordered key of a segment. -/
def segKey (p : Expr × Expr) : Expr × Expr :=
  if Expr.lt p.2 p.1 then (p.2, p.1) else p

/-- Metric atoms of `e` (segments, angles, triangle areas), each keyed up to
the symmetries of its points. -/
partial def atoms (e : Expr) (acc : Array (Array Expr) := #[]) : Array (Array Expr) :=
  let sort := fun (xs : Array Expr) => xs.qsort Expr.lt
  if isSpaceAtom e then
    let xs := e.getAppArgs
    if e.isAppOfArity `Space.angle 3 then acc.push (#[e.getAppFn, xs[1]!] ++ sort #[xs[0]!, xs[2]!])
    else acc.push (#[e.getAppFn] ++ sort xs)
  else if e.isAppOfArity `Segment.length 1 then
    acc.push (sort e.appArg!.getAppArgs)
  else if e.isAppOfArity `Angle.degree 1 then
    match e.appArg!.getAppArgs with
    | #[x, y, z] => acc.push (#[y] ++ sort #[x, z])
    | _ => acc
  else if e.isAppOfArity `Triangle.area 1 then
    acc.push (#[mkConst `Triangle.area] ++ sort e.appArg!.getAppArgs)
  else match e with
    | .app f a => atoms a (atoms f acc)
    | _ => acc

/-- Metric atom subterms of `e` (segment lengths, angles, triangle areas). -/
partial def atomTerms (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity `Segment.length 1 || e.isAppOfArity `Angle.degree 1 ||
     e.isAppOfArity `Triangle.area 1 || isSpaceAtom e then acc.push e
  else match e with
    | .app f a => atomTerms a (atomTerms f acc)
    | _ => acc

/-- An atom and its forms under the symmetries of its points. -/
def variants (a : Expr) : Array Expr :=
  if isSpaceAtom a then
    let f := a.getAppFn
    let xs := a.getAppArgs
    if a.isAppOfArity `Space.angle 3 then #[a, mkApp3 f xs[2]! xs[1]! xs[0]!]
    else Id.run do
      -- all permutations reachable by the generators
      let gens := (spaceGens f.constName!).map (·.2)
      let mut out := #[xs]
      let mut i := 0
      while i < out.size do
        for g in gens do
          let ys := g.map (out[i]![·]!)
          unless out.contains ys do out := out.push ys
        i := i + 1
      return out.map (mkAppN f)
  else
  let f := a.appFn!
  let inner := a.appArg!
  let g := inner.getAppFn
  match inner.getAppArgs with
  | #[x, y] => #[a, mkApp f (mkApp2 g y x)]
  | #[x, y, z] =>
    if a.isAppOfArity `Angle.degree 1 then #[a, mkApp f (mkApp3 g z y x)]
    else #[mkApp3 g x y z, mkApp3 g x z y, mkApp3 g y x z,
           mkApp3 g y z x, mkApp3 g z x y, mkApp3 g z y x].map (mkApp f)
  | _ => #[a]

/-- Metric facts with their atoms. -/
def metricPool (facts : Array Fact) : MetaM (Array (Fact × Array (Array Expr))) :=
  facts.filterMapM fun f => do
    return if ← isMetricFact f.type then some (f, atoms f.type) else none

/-- Layers of facts tried by `arith`, and the most facts sent to `linarith`. -/
def maxLayers : Nat := 4
def maxHyps : Nat := 120

/-! A linear arithmetic oracle: does a Farkas certificate exist, and which
facts does it use? `linarith` is then run on those only. -/

/-- A linear form: a constant and coefficients by atom. -/
structure Lin where
  c : Rat := 0
  xs : Std.HashMap Nat Rat := {}
deriving Inhabited

def Lin.add (a b : Lin) : Lin :=
  ⟨a.c + b.c, b.xs.fold (fun m k v =>
    let w := m.getD k 0 + v
    if w == 0 then m.erase k else m.insert k w) a.xs⟩

def Lin.scale (r : Rat) (a : Lin) : Lin :=
  if r == 0 then {} else ⟨r * a.c, a.xs.fold (fun m k v => m.insert k (r * v)) {}⟩

abbrev AtomM := StateM (Std.HashMap Expr Nat)

def Lin.atom (e : Expr) : AtomM Lin := do
  let m ← get
  let i ← match m[e]? with
    | some i => pure i
    | none => do set (m.insert e m.size); pure m.size
  return ⟨0, ({} : Std.HashMap Nat Rat).insert i 1⟩

/-- `e` as a linear form; other terms are atoms. -/
partial def linOf (e : Expr) : AtomM Lin := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return (← linOf a).add (← linOf b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return (← linOf a).add ((← linOf b).scale (-1))
  | (``Neg.neg, #[_, _, a]) => return (← linOf a).scale (-1)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    let s ← get
    let la ← linOf a
    let lb ← linOf b
    if la.xs.isEmpty then return lb.scale la.c
    if lb.xs.isEmpty then return la.scale lb.c
    set s
    Lin.atom e
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
    let s ← get
    let lb ← linOf b
    if lb.xs.isEmpty && lb.c != 0 then return (← linOf a).scale lb.c⁻¹
    set s
    Lin.atom e
  | (``OfNat.ofNat, #[_, n, _]) =>
    match n.rawNatLit? with
    | some k => return ⟨k, {}⟩
    | none => Lin.atom e
  | _ => Lin.atom e

/-- A real comparison as `p R 0`, `R` 0 for `=`, 1 for `≤`, 2 for `<`. -/
def relOf (e : Expr) : AtomM (Option (Lin × Nat)) := do
  let real := fun (t : Expr) => t.consumeMData.isConstOf `Real
  let d := fun (a b : Expr) => do return (← linOf a).add ((← linOf b).scale (-1))
  match e.consumeMData.getAppFnArgs with
  | (``Eq, #[t, a, b]) => if real t then return some (← d a b, 0) else return none
  | (``LE.le, #[t, _, a, b]) => if real t then return some (← d a b, 1) else return none
  | (``LT.lt, #[t, _, a, b]) => if real t then return some (← d a b, 2) else return none
  | (``GE.ge, #[t, _, a, b]) => if real t then return some (← d b a, 1) else return none
  | (``GT.gt, #[t, _, a, b]) => if real t then return some (← d b a, 2) else return none
  | (``Not, #[p]) =>
    match p.consumeMData.getAppFnArgs with
    | (``LT.lt, #[t, _, a, b]) => if real t then return some (← d b a, 1) else return none
    | (``LE.le, #[t, _, a, b]) => if real t then return some (← d b a, 2) else return none
    | (``GT.gt, #[t, _, a, b]) => if real t then return some (← d a b, 1) else return none
    | (``GE.ge, #[t, _, a, b]) => if real t then return some (← d a b, 2) else return none
    | _ => return none
  | _ => return none

/-- A Farkas certificate for the rows `p R 0`: multipliers (nonnegative unless
`R` is `=`) cancelling every atom, with a constant `C ≥ 0` and `C + Σ strict > 0`.
Its rows, if one exists. Phase-1 simplex over `Rat`, Bland's rule. -/
def farkas (rows : Array (Lin × Nat)) (atoms : Nat) : Option (Array Nat) := Id.run do
  -- columns: a multiplier per row (two for `=`), then the slacks of C and C + S
  let mut cols : Array (Nat × Rat) := #[]
  for i in [0:rows.size] do
    cols := cols.push (i, 1)
    if rows[i]!.2 == 0 then cols := cols.push (i, -1)
  let n := cols.size + 2
  let m := atoms + 2
  -- tableau rows: atoms, C - s1 = 0, C + S - s2 = 1; then artificials
  let mut t : Array (Array Rat) := Array.replicate m (Array.replicate (n + m + 1) 0)
  for j in [0:cols.size] do
    let (i, sg) := cols[j]!
    let (p, r) := rows[i]!
    for (k, v) in p.xs.toList do
      t := t.modify k (·.set! j (sg * v))
    t := t.modify atoms (·.set! j (sg * p.c))
    t := t.modify (atoms + 1) (·.set! j (sg * p.c + (if r == 2 then 1 else 0)))
  t := t.modify atoms (·.set! cols.size (-1))
  t := t.modify (atoms + 1) (·.set! (cols.size + 1) (-1))
  t := t.modify (atoms + 1) (·.set! (n + m) 1)
  for r in [0:m] do t := t.modify r (·.set! (n + r) 1)
  let mut basis : Array Nat := (List.range m).toArray.map (n + ·)
  -- objective: minimize the sum of the artificials; reduced costs
  let mut obj : Array Rat := Array.replicate (n + m + 1) 0
  for r in [0:m] do
    for j in [0:n] do obj := obj.set! j (obj[j]! - t[r]![j]!)
    obj := obj.set! (n + m) (obj[n + m]! - t[r]![n + m]!)
  for _ in [0:500] do
    -- entering: the first column with a negative reduced cost
    let some pc := (List.range n).find? (obj[·]!.blt 0) | break
    -- leaving: least ratio, ties by least basic variable
    let mut leave : Option Nat := none
    for r in [0:m] do
      let a := t[r]![pc]!
      unless (0 : Rat).blt a do continue
      match leave with
      | none => leave := some r
      | some q =>
        let x := t[r]![n + m]! / a
        let y := t[q]![n + m]! / t[q]![pc]!
        if x.blt y || (x == y && basis[r]! < basis[q]!) then leave := some r
    let some pr := leave | return none
    let piv := t[pr]![pc]!
    let prow := t[pr]!.map (· / piv)
    let nz := (List.range (n + m + 1)).filter (prow[·]! != 0)
    t := t.set! pr prow
    for r in [0:m] do
      if r == pr then continue
      let f := t[r]![pc]!
      if f == 0 then continue
      t := t.modify r fun row => nz.foldl (fun row j => row.set! j (row[j]! - f * prow[j]!)) row
    let f := obj[pc]!
    obj := nz.foldl (fun o j => o.set! j (o[j]! - f * prow[j]!)) obj
    basis := basis.set! pr pc
  if obj[n + m]! != 0 then return none
  -- rows whose multiplier is positive
  let mut used : Array Nat := #[]
  for r in [0:m] do
    let b := basis[r]!
    if b < cols.size && t[r]![n + m]! != 0 && !used.contains cols[b]!.1 then
      used := used.push cols[b]!.1
  return some used

/-- The facts a certificate for `e` uses (indices into `hyps`), `some none` if
there is none, `none` if `e` is not a comparison. -/
def oracle (hyps : Array Expr) (e : Expr) : Option (Option (Array Nat)) := Id.run do
  let (res, st) := (do
    let rs ← hyps.mapM relOf
    let g : Option (Option (Lin × Nat)) ←
      if e.isConstOf ``False then pure (some none) else pure ((← relOf e).map some)
    return (rs, g) : AtomM _).run {}
  let (rs, g) := res
  let some g := g | return none
  let mut idx : Array Nat := #[]
  let mut rows : Array (Lin × Nat) := #[]
  for i in [0:rs.size] do
    if let some row := rs[i]! then
      idx := idx.push i
      rows := rows.push row
  -- the negated goal: `p ≤ 0` to `-p < 0`, `p < 0` to `-p ≤ 0`, `p = 0` to either
  let negs : List (Option (Lin × Nat)) := match g with
    | none => [none]
    | some (p, 1) => [some (p.scale (-1), 2)]
    | some (p, 2) => [some (p.scale (-1), 1)]
    | some (p, _) => [some (p.scale (-1), 2), some (p, 2)]
  let mut used : Array Nat := #[]
  for ng in negs do
    let rows' := match ng with | some r => rows.push r | none => rows
    let some u := farkas rows' st.size | return some none
    for k in u do
      if k < idx.size && !used.contains idx[k]! then used := used.push idx[k]!
  return some (some used)

/-- Goals and hypothesis sets (hashed) `arithWith` failed on in this step. -/
initialize arithFails : IO.Ref (Std.HashSet (Expr × UInt64 × Bool)) ← IO.mkRef {}

/-- Products `u * v` of non-constant terms occurring in `e`. -/
partial def products (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    let acc := products b (products a acc)
    if a.isAppOf ``OfNat.ofNat || b.isAppOf ``OfNat.ofNat || acc.contains e then acc else acc.push e
  | _ => match e with
    | .app f a => products a (products f acc)
    | _ => acc

def isAtomTerm (e : Expr) : Bool :=
  e.isAppOfArity `Segment.length 1 || e.isAppOfArity `Angle.degree 1 ||
    e.isAppOfArity `Triangle.area 1 || isSpaceAtom e

/-- The least term equal to `u` along `edges`, and a proof of `u = it`. -/
def representative (edges : Std.HashMap Expr (Array (Expr × Expr))) (u : Expr) :
    MetaM (Expr × Expr) := do
  let mut queue := #[(u, ← mkEqRefl u)]
  let mut best := (u, ← mkEqRefl u)
  let mut i := 0
  while i < queue.size do
    let (x, px) := queue[i]!
    i := i + 1
    if Expr.lt x best.1 then best := (x, px)
    for (y, h) in edges.getD x #[] do
      unless queue.any (·.1 == y) do queue := queue.push (y, ← mkEqTrans px h)
  return best

/-- For each product, `u * v = u' * v'` with each factor replaced by its class
representative under the atom equalities `ts`, the factors in a fixed order. -/
def productEqs (ts : Array (Expr × Expr)) (prods : Array Expr) : MetaM (Array Expr) := do
  let mut edges : Std.HashMap Expr (Array (Expr × Expr)) := {}
  for (t, p) in ts do
    if let some (_, x, y) := t.eq? then
      if isAtomTerm x && isAtomTerm y && x != y then
        let q ← mkEqSymm p
        edges := edges.alter x (fun a => some ((a.getD #[]).push (y, p)))
        edges := edges.alter y (fun a => some ((a.getD #[]).push (x, q)))
  let mut out := #[]
  for m in prods do
    let some (u, v) := (match m.getAppFnArgs with
      | (``HMul.hMul, #[_, _, _, _, a, b]) => some (a, b) | _ => none) | continue
    let (u', pu) ← representative edges u
    let (v', pv) ← representative edges v
    let f := m.appFn!.appFn!
    let mut p ← mkCongr (← mkCongrArg f pu) pv
    let mut r := mkApp2 f u' v'
    if Expr.lt v' u' then
      r := mkApp2 f v' u'
      -- stated with the product as written, not `mul_comm`'s instances
      let c ← mkExpectedTypeHint (← mkAppM `mul_comm #[u', v']) (← mkEq (mkApp2 f u' v') r)
      p ← mkEqTrans p c
    unless r == m do out := out.push p
  return out

/-- `¬between b a b'` from the facts: stated, `b = b'`, or `b`, `b'` in order from `a`. -/
def notBetween (look : Expr → MetaM (Option Expr)) (b a b' : Expr) : MetaM (Option Expr) := do
  if b == b' then return some (mkApp2 (mkConst `not_between_self) a b)
  if let some p ← look (mkNot (mkApp3 (mkConst `between) b a b')) then return some p
  if let some p ← look (mkApp3 (mkConst `between) a b b') then
    return some (mkApp4 (mkConst `not_between_of_between_1) a b b' p)
  if let some p ← look (mkApp3 (mkConst `between) a b' b) then
    return some (mkApp4 (mkConst `not_between_of_between_2) a b b' p)
  return none

/-- Right-nested `And.intro` of the proofs. -/
def mkAnds : List Expr → MetaM Expr
  | [] => return mkConst ``True.intro
  | [p] => return p
  | p :: ps => do mkAppM ``And.intro #[p, ← mkAnds ps]

/-- `∠ x:y:z = ∠ x':y:z'` when `x'`, `z'` are on the rays `yx`, `yz` (`equal_angles`),
for the angles at a common vertex; the premises are looked up among the facts. -/
def angleEqs (angs : Array (Expr × Expr × Expr)) (lines : Array Expr)
    (look : Expr → MetaM (Option Expr)) : MetaM (Array Expr) := do
  let on := fun (p l : Expr) => look (mkApp2 (mkConst `Point.onLine) p l)
  let through := fun (y x x' : Expr) => do
    for l in lines do
      let some p1 ← on y l | continue
      let some p2 ← on x l | continue
      let some p3 ← on x' l | continue
      return some (l, p1, p2, p3)
    return none
  let ne := fun (x y : Expr) => do look (← mkAppM ``Ne #[x, y])
  let mut out := #[]
  for i in [0:angs.size] do
    for j in [i+1:angs.size] do
      let (x, y, z) := angs[i]!
      let (x', y', z') := angs[j]!
      if y != y' || (x == z' && z == x') then continue
      for (u, w, rev) in [(x', z', false), (z', x', true)] do
        if x == u && z == w then continue
        let some (l, hyl, hxl, hul) ← through y x u | continue
        let some (m, hym, hzm, hwm) ← through y z w | continue
        if l == m then continue
        let some n1 ← ne x y | continue
        let some n2 ← ne u y | continue
        let some n3 ← ne z y | continue
        let some n4 ← ne w y | continue
        let some b1 ← notBetween look x y u | continue
        let some b2 ← notBetween look z y w | continue
        let h ← mkAnds [hyl, hxl, hul, hym, hzm, hwm, n1, n2, n3, n4, b1, b2]
        let p := mkApp (mkAppN (mkConst `equal_angles) #[y, x, u, z, w, l, m]) h
        out := out.push p
        if rev then
          -- `∠ z':y:x' = ∠ x':y:z'`
          let some s1 ← ne x' y | continue
          let some s2 ← ne y z' | continue
          out := out.push (mkApp4 (mkConst `angle_symm) z' y x'
            (mkApp4 (mkConst ``And.intro) (← mkAppM ``Ne #[z', y]) (← mkAppM ``Ne #[y, x'])
              (← mkAppM ``Ne.symm #[s2]) (← mkAppM ``Ne.symm #[s1])))
        break
  return out

/-- `linarith only` over `hyps`, plus the symmetries of the segments and angles. -/
def arithWith (hyps : Array Fact) (ne : Expr → MetaM (Option Expr)) (e : Expr)
    (split := true) (lines : Array Expr := #[]) : MetaM (Option Expr) := do
  let neqs ← hyps.filterM (isRealNe ·.type)
  let hyps ← hyps.filterM (fun f => return !(← isRealNe f.type))
  let mut segs := segments e
  for f in hyps do segs := segments f.type segs
  let mut proofs := hyps.map (·.proof)
  let mut done : Array (Expr × Expr) := #[]
  -- nonnegativity of the goal's segments and angles
  for (x, y) in segments e do
    proofs := proofs.push (mkApp (mkConst `segment_gte_zero) (mkApp2 (mkConst `Segment.endpoints) x y))
  for (x, y, z) in angles e do
    let r := mkApp (mkConst `angle_range) (mkApp3 (mkConst `Angle.ofPoints) x y z)
    proofs := proofs.push (← mkAppM ``And.left #[r])
  for (x, y) in segs do
    if segs.contains (y, x) && x != y && !done.contains (segKey (x, y)) then
      done := done.push (segKey (x, y))
      proofs := proofs.push (mkApp2 (mkConst `segment_symmetric) x y)
  let mut angs := angles e
  for f in hyps do angs := angles f.type angs
  let mut doneA : Array (Expr × Expr × Expr) := #[]
  for (x, y, z) in angs do
    if angs.contains (z, y, x) && x != z && !doneA.contains (z, y, x) then
      doneA := doneA.push (x, y, z)
      let t1 ← mkAppM ``Ne #[x, y]
      let t2 ← mkAppM ``Ne #[y, z]
      let some h1 ← ne t1 | continue
      let some h2 ← ne t2 | continue
      proofs := proofs.push
        (mkApp4 (mkConst `angle_symm) x y z (mkApp4 (mkConst ``And.intro) t1 t2 h1 h2))
  -- angles at one vertex with their sides on the same rays
  for p in ← angleEqs angs lines ne do proofs := proofs.push p
  -- each triangle's area equals that of its first occurrence in another order
  let mut tris := triangles e
  for f in hyps do tris := triangles f.type tris
  let mut refs : Array (Expr × Expr × Expr) := #[]
  let mut doneT : Array (Expr × Expr × Expr) := #[]
  for t in tris do
    if doneT.contains t then continue
    doneT := doneT.push t
    let key := fun (u : Expr × Expr × Expr) => #[u.1, u.2.1, u.2.2].qsort Expr.lt
    match refs.find? (key · == key t) with
    | some r => if let some p ← areaPerm r t then proofs := proofs.push p
    | none => refs := refs.push t
  -- space measures: nonnegativity of the goal's, symmetries among all
  for t in spaceTerms e do
    if t.isAppOfArity `Space.dist 2 then
      proofs := proofs.push (mkAppN (mkConst `Space.dist_nonneg) t.getAppArgs)
    if t.isAppOfArity `Space.volume 4 then
      proofs := proofs.push (mkAppN (mkConst `Space.volume_nonneg) t.getAppArgs)
  let sps := hyps.foldl (fun acc f => spaceTerms f.type acc) (spaceTerms e)
  let mut refsS : Array Expr := #[]
  for t in sps do
    let key := fun (u : Expr) => (atoms u)[0]!
    match refsS.find? (key · == key t) with
    | none => refsS := refsS.push t
    | some r =>
      if t.isAppOfArity `Space.angle 3 then
        let xs := r.getAppArgs
        let some h1 ← ne (← mkAppM ``Ne #[xs[0]!, xs[1]!]) | continue
        let some h2 ← ne (← mkAppM ``Ne #[xs[2]!, xs[1]!]) | continue
        proofs := proofs.push (mkApp4 (mkConst `Space.angle_symm) xs[0]! xs[1]! xs[2]!
          (← mkAppM ``And.intro #[h1, h2]))
      else if let some p ← spacePerm r t then proofs := proofs.push p
  let lin0 := (← configRef.get).linarith
  let mut types := hyps.map (·.type)
  for p in proofs.extract hyps.size proofs.size do types := types.push (← inferType p)
  -- products of equal factors, in either order, are one term
  let prods := hyps.foldl (fun acc f => products f.type acc) (products e)
  unless prods.isEmpty do
    for p in ← productEqs (types.zip proofs) prods do
      proofs := proofs.push p
      types := types.push (← inferType p)
  -- `linarith` on the facts of the oracle's certificate, or not at all
  let lin := fun (ps : List Expr) (ts : Array Expr) => do
    match oracle ts e with
    | none => lin0 ps e
    | some none => return none
    | some (some used) =>
      let ps' := used.toList.map (ps[·]!)
      if let some p ← lin0 ps' e then return some p
      lin0 ps e
  -- failed already
  let key := (e, hash (hyps.map (·.type)), split)
  if (← arithFails.get).contains key then return none
  if let some p ← lin proofs.toList types then return some p
  unless split do
    arithFails.modify (·.insert key)
    return none
  -- by cases on `x ≠ y` about the goal's quantities: `x < y` or `x > y`
  let ks := atoms e
  let neqs := neqs.filter fun n => ks.isEmpty || (atoms n.type).any ks.contains
  for n in neqs.extract 0 2 do
    let some (_, x, y) := n.type.ne? | continue
    let branch := fun (t : Expr) => withLocalDeclD `h t fun h => do
      (← lin (h :: proofs.toList) (#[t] ++ types)).mapM (mkLambdaFVars #[h])
    let some p1 ← branch (← mkAppM ``LT.lt #[x, y]) | continue
    let some p2 ← branch (← mkAppM ``GT.gt #[x, y]) | continue
    return some (← mkAppM ``Or.elim #[← mkAppM `lt_or_gt_of_ne #[n.proof], p1, p2])
  arithFails.modify (·.insert key)
  return none

/-- An atom with a repeated point, like `∠aba`. -/
def degenerate (k : Array Expr) : Bool :=
  (k.filter (!·.isConst)).toList.eraseDups.length < (k.filter (!·.isConst)).size

/-- Union-find root. -/
partial def root (uf : Std.HashMap (Array Expr) (Array Expr)) (k : Array Expr) : Array Expr :=
  match uf[k]? with
  | some k' => root uf k'
  | none => k

/-- Prove a metric literal by `linarith only`, over the metric facts connected
to it by shared atoms, plus `ab = ba` and `∠abc = ∠cba` where both orders occur. -/
def arith (pool : Array (Fact × Array (Array Expr))) (ne : Expr → MetaM (Option Expr))
    (e : Expr) (seeds := atoms e) (lines : Array Expr := #[]) : MetaM (Option Expr) := do
  -- of the equalities between atoms, keep a spanning forest, and one of
  -- each symmetric pair `∠abc = ∠cba`
  let mut uf : Std.HashMap (Array Expr) (Array Expr) := {}
  let mut symm : Std.HashSet (Array Expr) := {}
  let mut forest := #[]
  for (f, ks) in pool do
    -- facts about degenerate atoms (`∠aba`, `|aa|`) unless the goal has one
    if ks.any degenerate && !(seeds.any degenerate) then continue
    if let some (_, x, y) := f.type.eq? then
      if atomTerms x == #[x] && atomTerms y == #[y] && ks.size == 2 then
        if ks[0]! == ks[1]! then
          if symm.contains ks[0]! then continue
          symm := symm.insert ks[0]!
        else
          let rx := root uf ks[0]!
          let ry := root uf ks[1]!
          if rx == ry then continue
          uf := uf.insert rx ry
    forest := forest.push (f, ks)
  if seeds.isEmpty then return ← arithWith (forest.map (·.1)) ne e (lines := lines)
  -- facts in layers by distance from the goal's atoms; try the nearest first
  let mut pool := forest
  let mut keys : Std.HashSet (Array Expr) := seeds.foldl (·.insert ·) {}
  -- angles at one vertex are connected (their sides may lie on the same rays)
  let vertex := fun (k : Array Expr) => if k.size == 3 && !k[0]!.isConst then some k[0]! else none
  let mut verts : Std.HashSet Expr := seeds.foldl (fun s k => (vertex k).elim s s.insert) {}
  let mut hyps := #[]
  for _ in [0:maxLayers] do
    let mut layer := #[]
    let mut rest := #[]
    for (f, ks) in pool do
      if ks.any (fun k => keys.contains k || (vertex k).any verts.contains) then
        layer := layer.push (f, ks)
      else rest := rest.push (f, ks)
    if layer.isEmpty then break
    pool := rest
    -- over the cap: the first facts of the layer (context facts come first)
    let full := hyps.size + layer.size > maxHyps
    layer := layer.extract 0 (maxHyps - hyps.size)
    hyps := hyps ++ layer.map (·.1)
    keys := layer.foldl (fun s (_, ks) => ks.foldl (·.insert ·) s) keys
    verts := layer.foldl (fun s (_, ks) => ks.foldl (fun s k => (vertex k).elim s s.insert) s) verts
    -- every atom of the goal must occur in some fact
    let seen := hyps.foldl (fun s f => (atoms f.type).foldl (·.insert ·) s) ({} : Std.HashSet (Array Expr))
    unless (atoms e).all seen.contains do continue
    if let some p ← arithWith hyps ne e (split := false) (lines := lines) then return some p
    if full then break
  -- case splits only over all the facts
  let neq ← hyps.anyM (isRealNe ·.type)
  if neq && (atoms e).all (hyps.foldl (fun s f => (atoms f.type).foldl (·.insert ·) s)
      ({} : Std.HashSet (Array Expr))).contains then
    return ← arithWith hyps ne e (lines := lines)
  -- a goal about products may need no facts, or facts sharing none of its atoms
  if !(products e).isEmpty then return ← arithWith hyps ne e (split := false) (lines := lines)
  return none

/-- Ground objects (points, lines, circles) of the context, by sort. -/
abbrev Objects := Array (Name × Array Expr)

def objectsOf (objs : Objects) (ty : Expr) : Array Expr :=
  match ty.constName? with
  | some n => (objs.find? (·.1 == n)).map (·.2) |>.getD #[]
  | none => #[]

/-- Split telescope arguments into objects and premise literals. -/
def premises (args : Array Expr) (skipArith : Bool) : MetaM (List Expr × List Expr) := do
  let mut lits := []
  let mut vars := []
  for a in args do
    let t ← inferType a
    if ← isProp t then
      for l in ← literals t do
        unless skipArith && (← isArith l) do lits := lits ++ [l]
    else vars := vars ++ [a]
  return (lits, vars)

/-- Instantiate the rule's arguments, proving premises by `leaf`. -/
def apply (c : Expr) (args : Array Expr) (leaf : Expr → MetaM (Option Expr)) :
    MetaM (Option Expr) := do
  let mut vals := #[]
  for a in args do
    let t ← inferType a
    if ← isProp t then
      let some h ← prove leaf t | return none
      vals := vals.push h
    else vals := vals.push (← instantiateMVars a)
  return some (← instantiateMVars (mkAppN c vals))

/-- Negation of a literal, without double negation; `¬ a = b` is `a ≠ b`. -/
def negLit (e : Expr) : MetaM Expr := do
  if let some p := e.not? then return p
  if let some (_, x, y) := e.ne? then return ← mkEq x y
  if let some (_, x, y) := e.eq? then return ← mkAppM ``Ne #[x, y]
  return mkNot e

/-- `False` from `h : e` and `hn : negLit e`. -/
def contra (e h hn : Expr) : Expr :=
  if e.not?.isSome || e.ne?.isSome then mkApp h hn else mkApp hn h

/-- A rule's telescope: premise and conclusion literals over fresh metavariables. -/
structure Inst where
  c : Expr
  args : Array Expr
  prem : Array Expr
  concl : Array Expr
  conclExpr : Expr

def inst (rule : Name) : MetaM Inst := do
  let c := mkConst rule
  let (args, _, concl) ← forallMetaTelescope (← inferType c)
  let (lits, _) ← premises args false
  return ⟨c, args, lits.toArray, (← literals concl).toArray, concl⟩

/-- One rule in one direction: `drop = none` gives conclusion literal `concl`
from the premises; `drop = some k` gives the negation of premise `k` from the
other premises and the negation of conclusion literal `concl`. -/
structure Clause where
  rule : Name
  drop : Option Nat
  concl : Nat
  head : Option (Name × Bool)
  forward : Bool
  /-- Heads of the literals the clause needs. -/
  needs : Array (Option (Name × Bool)) := #[]
  /-- Needed literals and result over pattern variables: `#i` is the rule's
  `i`-th object. -/
  needT : Array Expr := #[]
  resT : Expr := default
  /-- Sorts of the rule's objects. -/
  sorts : Array Expr := #[]
  arith : Array Bool := #[]
deriving Inhabited

/-- Some object is bound by no needed literal. -/
def Clause.free (cl : Clause) : Bool :=
  (List.range cl.sorts.size).any fun k => !cl.needT.any (·.hasLooseBVar k)

/-- Literals a clause needs, and the literal it gives. -/
def Clause.shape (cl : Clause) (i : Inst) : MetaM (List Expr × Expr) := do
  let q := i.concl[cl.concl]!
  match cl.drop with
  | none => return (i.prem.toList, q)
  | some k => return ((i.prem.eraseIdx! k).toList ++ [← negLit q], ← negLit i.prem[k]!)

/-- Proof of the clause's result, its needed literals proved by `leaf`. -/
def Clause.proof (cl : Clause) (i : Inst) (leaf : Expr → MetaM (Option Expr)) :
    MetaM (Option Expr) := do
  let projQ := fun (pf : Expr) => do
    let fs ← project (← instantiateMVars i.conclExpr) pf
    return fs[cl.concl]!.proof
  match cl.drop with
  | none =>
    let some pf ← apply i.c i.args leaf | return none
    return some (← instantiateMVars (← projQ pf))
  | some k =>
    let pk ← instantiateMVars i.prem[k]!
    let q ← instantiateMVars i.concl[cl.concl]!
    let some hn ← leaf (← negLit q) | return none
    withLocalDeclD `h pk fun h => do
      let leaf' := fun l => do
        if (← instantiateMVars l) == pk then return some h
        leaf l
      let some pf ← apply i.c i.args leaf' | return none
      let lam ← mkLambdaFVars #[h] (contra q (← projQ pf) hn)
      if pk.not?.isSome || pk.ne?.isSome then
        return some (← instantiateMVars
          (mkApp2 (mkConst ``Classical.byContradiction) (← negLit pk) lam))
      return some (← instantiateMVars lam)

/-- Not a literal: disjunction, existential, quantified statement. -/
def compound (e : Expr) : Bool :=
  e.isAppOf ``Or || e.isAppOf ``Exists || e.isAppOf ``Iff || e.isForall

def isObject (e : Expr) : MetaM Bool := do
  let t ← instantiateMVars (← inferType e)
  let some n := t.constName? | return false
  return (← configRef.get).objectSorts.contains n

/-- Clauses needing more literals are used only backward. -/
def maxForwardNeeds : Nat := 6

/-- Clauses needing more literals, up to this, are used forward uncontraposed. -/
def maxForwardNeedsMain : Nat := 10

/-- `e` with the objects `objs` (metavariables) replaced by pattern variables. -/
def template (objs : Array Expr) (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  let t := e.replace fun x => match x with
    | .mvar m => (objs.findIdx? (·.mvarId! == m)).map mkBVar
    | _ => none
  return if t.hasMVar then none else some t

/-- A clause of rule `n` with its templates; `none` if some object occurs in
neither the needed literals nor the result. -/
def mkClause (n : Name) (i : Inst) (objs : Array Expr) (drop : Option Nat) (j : Nat)
    (back : Bool) : MetaM (Option Clause) := do
  let (need, res) ← (⟨n, drop, j, none, false, #[], #[], default, #[], #[]⟩ : Clause).shape i
  let some resT ← template objs res | return none
  let mut needT := #[]
  for l in need do
    let some t ← template objs l | return none
    needT := needT.push t
  let inNeed := fun (k : Nat) => needT.any (·.hasLooseBVar k)
  unless (List.range objs.size).all fun k => inNeed k || resT.hasLooseBVar k do return none
  let arith ← need.toArray.mapM isArith
  -- forward: metric-free; a contrapositive must bind every object
  -- big configurations are matched only against a goal
  let fwd := !back && !arith.any id && !needT.isEmpty &&
    (needT.size ≤ maxForwardNeeds || (drop.isNone && needT.size ≤ maxForwardNeedsMain)) &&
    (drop.isNone || (List.range objs.size).all inNeed)
  let sorts ← objs.mapM inferType
  return some ⟨n, drop, j, head res, fwd, needT.map head, needT, resT, sorts, arith⟩

/-- The clauses of a rule. -/
def clausesOf (n : Name) : MetaM (Array Clause) := withNewMCtxDepth do
  let i ← inst n
  if i.prem.any compound then return #[]
  let objs ← i.args.filterM isObject
  let cfg ← configRef.get
  let back := cfg.backwardLemmas.contains n || cfg.guardedLemmas.contains n
  let mut out := #[]
  for j in [0:i.concl.size] do
    let q := i.concl[j]!
    if compound q then continue
    if let some cl ← mkClause n i objs none j back then out := out.push cl
    if back || (← isArith q) then continue
    for k in [0:i.prem.size] do
      if ← isArith i.prem[k]! then continue
      if let some cl ← mkClause n i objs (some k) j back then out := out.push cl
  return out

/-- Rules: System E's inference axioms and the lemmas above. -/
def ruleNames : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless ci matches .axiomInfo _ do continue
    let some m := env.getModuleIdxFor? n | continue
    if (`SystemE.Theory.Inferences).isPrefixOf env.header.moduleNames[m.toNat]! then
      out := out.push n
  out := out.qsort (·.toString < ·.toString)
  let cfg ← configRef.get
  return out ++ (cfg.lemmas ++ cfg.backwardLemmas ++ cfg.guardedLemmas).filter env.contains

initialize clauseCache : IO.Ref (Array Clause) ← IO.mkRef #[]

def clauses : MetaM (Array Clause) := do
  let c ← clauseCache.get
  unless c.isEmpty do return c
  let mut out := #[]
  for n in ← ruleNames do out := out ++ (← clausesOf n)
  clauseCache.set out
  return out

initialize backwardCache : IO.Ref (Std.HashMap (Option (Name × Bool)) (Array Clause)) ←
  IO.mkRef {}

/-- Clauses by result head, for backward search: lemmas first, clauses
needing metric literals last. -/
def backwardClauses : MetaM (Std.HashMap (Option (Name × Bool)) (Array Clause)) := do
  let c ← backwardCache.get
  unless c.isEmpty do return c
  let cls ← clauses
  let cfg ← configRef.get
  let isLemma := fun (cl : Clause) =>
    cfg.lemmas.contains cl.rule || cfg.backwardLemmas.contains cl.rule ||
      cfg.guardedLemmas.contains cl.rule
  -- stated direction before contrapositives, then fewest needed literals
  let sort := fun (a : Array Clause) => a.qsort fun x y =>
    let kx := (if x.drop.isSome then 100 else 0) + x.needT.size
    let ky := (if y.drop.isSome then 100 else 0) + y.needT.size
    kx < ky
  let ordered := cls.filter isLemma ++ sort (cls.filter fun cl => !isLemma cl && !cl.arith.any id) ++
    sort (cls.filter fun cl => !isLemma cl && cl.arith.any id)
  let out := ordered.foldl (fun m cl => m.alter cl.head fun a => some ((a.getD #[]).push cl)) {}
  backwardCache.set out
  return out

/-- The atom of a literal. -/
def atomOf (e : Expr) : Expr := (e.not?).getD e

/-- Facts, each with the round it was added in: by head, by head and an object
argument (position and value), and by statement. -/
structure Index where
  byHead : Std.HashMap (Option (Name × Bool)) (Array (Fact × Nat)) := {}
  byArg : Std.HashMap (Option (Name × Bool) × Nat × Expr) (Array (Fact × Nat)) := {}
  exact : Std.HashMap Expr (Array (Fact × Nat)) := {}
deriving Inhabited

def Index.contains (idx : Index) (h : Option (Name × Bool)) : Bool := idx.byHead.contains h

def Index.insert (idx : Index) (f : Fact) (r : Nat) : Index := Id.run do
  let h := head f.type
  let push := fun (a : Option (Array (Fact × Nat))) => some ((a.getD #[]).push (f, r))
  let mut idx := { idx with byHead := idx.byHead.alter h push, exact := idx.exact.alter f.type push }
  let args := (atomOf f.type).getAppArgs
  for i in [0:args.size] do
    if args[i]!.isFVar then idx := { idx with byArg := idx.byArg.alter (h, i, args[i]!) push }
  return idx

def Index.of (facts : Array Fact) (r : Nat := 0) : Index :=
  facts.foldl (·.insert · r) {}

/-- Pattern-variable bindings. -/
abbrev Subst := Std.HashMap Nat Expr

/-- Match template `p` against ground `t`. -/
partial def pmatch (p t : Expr) (σ : Subst) : Option Subst :=
  match p, t with
  | _, .mdata _ t => pmatch p t σ
  | .bvar i, _ => match σ[i]? with
    | some v => if v == t then some σ else none
    | none => some (σ.insert i t)
  | .app f a, .app g b => (pmatch f g σ).bind (pmatch a b ·)
  | .mdata _ p, _ => pmatch p t σ
  | _, _ => if p == t then some σ else none

/-- Template `t` with its pattern variables replaced by `σ`. -/
def fill (t : Expr) (σ : Subst) : Expr :=
  t.replace fun x => match x with
    | .bvar i => σ[i]?
    | _ => none

/-- Pattern variables of `t` not bound by `σ`. -/
def unbound (t : Expr) (σ : Subst) (n : Nat) : Nat :=
  (List.range n).foldl (fun c k => if t.hasLooseBVar k && !σ.contains k then c + 1 else c) 0

/-- The clause's proof for the bindings `σ` (all objects bound), needed
literals proved by `leaf`. -/
def Clause.build (cl : Clause) (σ : Subst) (leaf : Expr → MetaM (Option Expr)) :
    MetaM (Option Expr) := do
  let s ← saveState
  try
    let i ← inst cl.rule
    let objs ← i.args.filterM isObject
    for k in [0:objs.size] do
      let some v := σ[k]? | return none
      objs[k]!.mvarId!.assign v
    let r ← cl.proof i leaf
    return r.filter (!·.hasExprMVar)
  finally
    s.restore

/-- Facts that may match template `t` under `σ`: by statement if it is ground,
else the fewest of those sharing a bound object argument. -/
def Index.cands (idx : Index) (t : Expr) (σ : Subst) : Array (Fact × Nat) := Id.run do
  let h := head t
  let g := fill t σ
  if !g.hasLooseBVars then return idx.exact.getD g #[]
  -- the smallest bucket of a bound object argument
  let mut best := idx.byHead.getD h #[]
  let args := (atomOf g).getAppArgs
  for i in [0:args.size] do
    if args[i]!.isFVar then
      let c := idx.byArg.getD (h, i, args[i]!) #[]
      if c.size < best.size then best := c
  return best

/-- Bind the templates (with positions) to facts allowed by `ok` (position,
round), the one with the fewest candidate facts first (or `first`), then the
remaining objects to context objects; run `k` on each full binding. -/
partial def matchAll (idx : Index) (objs : Objects) (sorts : Array Expr)
    (ok : Nat → Nat → Bool) (k : Subst → MetaM Unit) (lits : List (Nat × Expr))
    (σ : Subst) (first : Option Nat := none) : MetaM Unit := do
  match lits with
  | l0 :: _ =>
    -- the literal with the fewest candidate facts (or `first`)
    let (best, cs) := match first.bind fun p => lits.find? (·.1 == p) with
      | some l => (l, idx.cands l.2 σ)
      | none => lits.foldl (fun ((b, bc) : (Nat × Expr) × Array (Fact × Nat)) (l : Nat × Expr) =>
          if bc.isEmpty then (b, bc) else
          let c := idx.cands l.2 σ
          if c.size < bc.size then (l, c) else (b, bc)) (l0, idx.cands l0.2 σ)
    let rest := lits.filter (·.1 != best.1)
    for (f, r) in cs do
      if ok best.1 r then
        if let some σ' := pmatch best.2 f.type σ then matchAll idx objs sorts ok k rest σ'
  | [] =>
    match (List.range sorts.size).find? (!σ.contains ·) with
    | some v =>
      for o in objectsOf objs sorts[v]! do
        matchAll idx objs sorts ok k [] (σ.insert v o)
    | none => k σ

/-- Results of a forward clause in `round`: from round 1 on, each match uses a
fact from the previous round (semi-naive). -/
def fire (map : Std.HashMap Expr Expr) (idx : Index) (objs : Objects) (round : Nat)
    (fresh : Std.HashSet (Option (Name × Bool))) (cl : Clause)
    (keep : Expr → Bool := fun _ => true) (σ0 : Subst := {})
    (seen : Option (IO.Ref (Std.HashSet Expr)) := none) : MetaM (Array Fact) := do
  let out ← IO.mkRef (#[] : Array Fact)
  let k := fun (σ : Subst) => do
    Core.checkSystem "saturate"
    let res := fill cl.resT σ
    -- skip `x = x`
    if let some (_, x, y) := res.eq? then if x == y then return
    unless keep res do return
    -- known, or built already
    if map.contains res then return
    if let some r := seen then
      if (← r.get).contains res then return
      r.modify (·.insert res)
    if let some pf ← cl.build σ (fun l => return map[l]?) then
      out.modify (·.push ⟨res, pf⟩)
  let lits := (List.range cl.needT.size).zip cl.needT.toList
  if round == 0 then
    matchAll idx objs cl.sorts (fun _ _ => true) k lits σ0
  else
    for p in [0:cl.needT.size] do
      unless fresh.contains cl.needs[p]! do continue
      -- facts from the previous round carry stamp `round`
      let ok := fun (j r : Nat) =>
        if j < p then decide (r < round) else if j == p then r == round else true
      matchAll idx objs cl.sorts ok k lits {} (some p)
  let mut res := #[]
  for f in ← out.get do
    res := res ++ (← project f.type f.proof)
  return res

structure Ctx where
  facts : Array Fact
  store : Store
  objs : Objects
  /-- Per literal: its proof, or the depth at which it failed. -/
  memo : IO.Ref (Std.HashMap Expr (Option Expr × Nat))
  calls : IO.Ref Nat
  ariths : IO.Ref Nat
  /-- `neByMetric` calls. -/
  substs : IO.Ref Nat
  /-- Refutations: per top-level literal, and the literals tried. -/
  refutes : IO.Ref Nat
  refuted : IO.Ref (Std.HashSet Expr)
  /-- Per expanded atom, the metric facts derived from it on demand. -/
  expanded : IO.Ref (Std.HashMap (Array Expr) (Array Fact))
  idx : Index
  /-- The context's metric facts with their atoms, and all those atoms. -/
  pool : Array (Fact × Array (Array Expr))
  known : Std.HashSet (Array Expr)
  /-- Depth of the current top-level call (iterative deepening). -/
  top : IO.Ref Nat

def Ctx.new (facts : Array Fact) (objs : Objects) : MetaM Ctx := do
  let pool ← metricPool facts
  return ⟨facts, Store.of facts, objs, ← IO.mkRef {}, ← IO.mkRef 0, ← IO.mkRef 0,
    ← IO.mkRef 0, ← IO.mkRef 0, ← IO.mkRef {}, ← IO.mkRef {},
    Index.of facts,
    pool, pool.foldl (fun s (_, ks) => ks.foldl (·.insert ·) s) {}, ← IO.mkRef maxDepth⟩

/-- Metric forward clauses. -/
def metricClauses : MetaM (Array Clause) := do
  -- any size: results are kept only for the atoms being expanded
  let cfg ← configRef.get
  let back := cfg.backwardLemmas ++ cfg.guardedLemmas
  (← clauses).filterM fun cl => do
    return !back.contains cl.rule && cl.drop.isNone && !cl.needT.isEmpty &&
      !cl.arith.any id && (← isArith cl.resT)

/-- Metric facts derived from the atoms `todo`: fire the metric clauses whose
results mention one (cached per atom). -/
def expandMetric (ctx : Ctx) (todo : Array Expr) : MetaM (Array Fact) := do
  let idx := ctx.idx
  let done ← ctx.expanded.get
  let new := todo.filter fun a => !done.contains (atoms a)[0]!
  -- facts of earlier expansions, each once
  let mut seen : Std.HashSet Expr := {}
  let mut out := #[]
  for a in todo do
    for f in done.getD (atoms a)[0]! #[] do
      unless seen.contains f.type do
        seen := seen.insert f.type
        out := out.push f
  if new.isEmpty then return out
  let keys := new.map fun a => (atoms a)[0]!
  let keep := fun (r : Expr) => (atoms r).any keys.contains
  let targets := new.foldl (fun acc a => acc ++ variants a) #[]
  let mut fresh := #[]
  let built ← IO.mkRef seen
  for cl in ← metricClauses do
    unless cl.needs.all idx.contains do continue
    -- bind a result atom of the clause to a target first
    for t in atomTerms cl.resT do
      for a in targets do
        let some σ0 := pmatch t a {} | continue
        let fs ← fire ctx.store.map idx ctx.objs 0 {} cl keep σ0 (some built)
        for f in fs do
          unless ctx.store.map.contains f.type || seen.contains f.type do
            seen := seen.insert f.type
            fresh := fresh.push f
  ctx.expanded.modify fun s => keys.foldl (·.insert · fresh) s
  return out ++ fresh

/-- The metric facts for `e`: the context's, and those derived from the atoms
of `e` (`level` 0) and then from the atoms of those (`level` 1). -/
def metricFor (ctx : Ctx) (ts : Array Expr) (level : Nat) :
    MetaM (Array (Fact × Array (Array Expr))) := do
  let mut fs ← expandMetric ctx ts
  if level > 0 then
    let more ← expandMetric ctx (fs.foldl (fun acc f => acc ++ atomTerms f.type) #[])
    let known := fs.foldl (fun s f => s.insert f.type) ({} : Std.HashSet Expr)
    fs := fs ++ more.filter (!known.contains ·.type)
  return ctx.pool ++ fs.map fun f => (f, atoms f.type)

/-- Recursive calls and `linarith` calls one attempt may make. -/
def maxCalls : Nat := 800
def maxAriths : Nat := 60

/-- A fact stating `l`, or `b ≠ a` for `l = (a ≠ b)`. -/
def Ctx.fact? (ctx : Ctx) (cache : Array Fact) (l : Expr) : MetaM (Option Expr) := do
  if let some p := ctx.store.map[l]? then return some p
  if let some p ← find cache l then return some p
  if let some (t, x, y) := l.ne? then
    if let some p := ctx.store.map[mkApp3 l.getAppFn t y x]? then
      return some (← mkAppM ``Ne.symm #[p])
  return none

/-- A fact `l`, or `b ≠ a` for `l = (a ≠ b)`; side conditions of angle symmetry. -/
def Ctx.lines (ctx : Ctx) : Array Expr := objectsOf ctx.objs (mkConst `Line)

def Ctx.neFact (ctx : Ctx) (l : Expr) : MetaM (Option Expr) := do
  if let some p := ctx.store.map[l]? then return some p
  if let some (t, x, y) := l.ne? then
    if let some p := ctx.store.map[mkApp3 l.getAppFn t y x]? then
      return some (← mkAppM ``Ne.symm #[p])
  return none

/-- Most atoms `neByMetric` substitutes in, and most calls per literal. -/
def maxSubst : Nat := 30
def maxSubsts : Nat := 20

/-- `x ≠ y` for points: assuming `x = y`, each atom mentioning `y` equals the
one with `x` in its place, and `linarith` finds a contradiction. -/
def neByMetric (ctx : Ctx) (x y : Expr) : MetaM (Option Expr) := do
  let mut ts : Array Expr := #[]
  for (f, _) in ctx.pool do
    for a in atomTerms f.type do
      if a.containsFVar y.fvarId! && !ts.contains a && ts.size < maxSubst then ts := ts.push a
  if ts.isEmpty then return none
  ctx.substs.modify (· + 1)
  if (← ctx.substs.get) > maxSubsts then return none
  let pool ← metricFor ctx (ts ++ ts.map (·.replaceFVar y x)) 0
  let point := mkConst `Point
  withLocalDeclD `h (← mkEq x y) fun h => do
    let mut eqs : Array Fact := #[]
    for a in ts do
      let b := a.replaceFVar y x
      let ty ← mkEq b a
      let pf ← mkAppM ``congrArg #[.lam `z point (a.abstract #[y]) .default, h]
      eqs := eqs.push ⟨ty, ← mkExpectedTypeHint pf ty⟩
    for (u, v, hh) in [(x, y, h), (y, x, ← mkEqSymm h)] do
      let z := mkApp2 (mkConst `zero_segment_onlyif) u v
      eqs := eqs.push ⟨← inferType (mkApp z hh), mkApp z hh⟩
    let seeds := eqs.foldl (fun acc f => acc ++ atoms f.type) #[]
    let some p ← arith (eqs.map (fun f => (f, atoms f.type)) ++ pool) ctx.neFact (lines := ctx.lines)
      (mkConst ``False) seeds | return none
    return some (← mkLambdaFVars #[h] p)

/-- Close the facts under the forward clauses. If `closed`, `facts0` is already
closed: only consequences of `extra` are derived (and of `objs`' new objects if
`newObjs`). The metric pass, if `metric`, adds metric facts about known atoms. -/
def saturate (objs : Objects) (facts0 : Array Fact) (goal : Expr) (extra : Array Fact := #[])
    (conflict := false) (closed := !extra.isEmpty) (metric := extra.isEmpty)
    (newObjs := false) : MetaM (Array Fact) := do
  let prof := systemE.stats.get (← getOptions)
  let mut facts := facts0
  let mut idx := Index.of facts
  let mut map : Std.HashMap Expr Expr :=
    facts.foldl (fun m f => if m.contains f.type then m else m.insert f.type f.proof) {}
  let start := if closed then 1 else 0
  let mut fresh : Std.HashSet (Option (Name × Bool)) := idx.byHead.keys.foldl (·.insert ·) {}
  if closed then
    fresh := {}
    for f in extra do
      unless map.contains f.type do
        -- with `conflict`, stop at a fact whose negation is known
        if conflict && map.contains (← negLit f.type) then return facts.push f
        map := map.insert f.type f.proof
        facts := facts.push f
        idx := idx.insert f 1
        fresh := fresh.insert (head f.type)
  let mut cls := #[]
  for cl in (← clauses).filter fun cl => cl.forward && !cl.needs.isEmpty do
    unless ← isArith cl.resT do cls := cls.push cl
  for round in [start:maxRounds + start] do
    let mut added := false
    let mut new := #[]
    for cl in cls do
      Core.checkSystem "saturate"
      -- clauses with objects bound by no fact: also on new objects
      let all := newObjs && round == start && closed && cl.free
      unless cl.needs.all idx.contains && (all || cl.needs.any fresh.contains) do continue
      let t0 ← IO.monoNanosNow
      let fs ← fire map idx objs (if all then 0 else round) fresh cl
      if prof then
        let dt := (← IO.monoNanosNow) - t0
        profRef.modify fun m => m.alter s!"{cl.rule} {cl.drop}" fun v =>
          some ((v.getD (0, 0)).1 + dt, (v.getD (0, 0)).2 + fs.size)
      for f in fs do
        unless map.contains f.type do
          if conflict && map.contains (← negLit f.type) then return facts ++ new.push f
          map := map.insert f.type f.proof
          new := new.push f
          added := true
    fresh := new.foldl (fun s f => s.insert (head f.type)) {}
    for f in new do
      facts := facts.push f
      idx := idx.insert f (round + 1)
    if !added || facts.size > maxFacts then break
  unless metric do return facts
  -- metric clauses: one pass, keeping results about atoms mostly mentioned
  let known : Std.HashSet (Array Expr) :=
    facts.foldl (fun s f => (atoms f.type).foldl (·.insert ·) s) ((atoms goal).foldl (·.insert ·) {})
  -- for a goal without quantities (`False`), at most one new one: a part of a
  -- known whole, a positive angle
  let free := if goal.isConstOf ``False then 1 else 0
  let keep := fun (e : Expr) => ((atoms e).filter (!known.contains ·)).size ≤ free
  -- big clauses (angle sums) only for `False`; otherwise derived on demand
  for cl in ← metricClauses do
    unless cl.needs.all idx.contains && (free > 0 || cl.forward) do continue
    for f in ← fire map idx objs 0 {} cl keep do
      unless map.contains f.type do
        map := map.insert f.type f.proof
        facts := facts.push f
  return facts

/-- Conclusions of the guarded lemmas: diagram premises matched against the
facts (one of them in `fresh`, if given), the metric premise proved by `linarith`. -/
def guarded (ctx : Ctx) (fresh : Option (Std.HashSet Expr) := none) : MetaM (Array Fact) := do
  let g := (← configRef.get).guardedLemmas
  let out ← IO.mkRef (#[] : Array Fact)
  -- classes of atoms equal by the facts: an equality premise must link two
  let mut uf : Std.HashMap (Array Expr) (Array Expr) := {}
  for (f, ks) in ctx.pool do
    if let some (_, x, y) := f.type.eq? then
      if atomTerms x == #[x] && atomTerms y == #[y] && ks.size == 2 then
        let rx := root uf ks[0]!
        let ry := root uf ks[1]!
        if rx != ry then uf := uf.insert rx ry
  let linked := fun (l : Expr) => match l.eq? with
    | some (_, x, y) =>
      if atomTerms x == #[x] && atomTerms y == #[y] then
        root uf (atoms x)[0]! == root uf (atoms y)[0]!
      else true
    | none => true
  for cl in ← clauses do
    unless g.contains cl.rule && cl.drop.isNone do continue
    let lits := ((List.range cl.needT.size).zip cl.needT.toList).filter (!cl.arith[·.1]!)
    unless lits.all (ctx.idx.contains <| head ·.2) do continue
    matchAll ctx.idx ctx.objs cl.sorts (fun _ _ => true) (fun σ => do
      if let some fr := fresh then
        unless lits.any (fr.contains <| fill ·.2 σ) do return
      let res := fill cl.resT σ
      -- skip known results and degenerate ones like `between a x x`
      let args := res.getAppArgs
      if ctx.store.map.contains res || args.size != (args.toList.eraseDups).length then return
      let leaf := fun l => do
        if let some p := ctx.store.map[l]? then return some p
        unless (← isArith l) && (atoms l).all ctx.known.contains && linked l do return none
        arith ctx.pool ctx.neFact l (lines := ctx.lines)
      if let some pf ← cl.build σ leaf then out.modify (·.push ⟨res, pf⟩)) lits {}
  out.get

/-- Most refutations per top-level literal. -/
def maxRefutes : Nat := 4

/-- Prove `e` by contradiction: assume its negation, saturate from it (with the
guarded lemmas), and look for a fact whose negation is also a fact. -/
def refute (ctx : Ctx) (e : Expr) : MetaM (Option Expr) := do
  let p ← negLit e
  withLocalDeclD `h p fun h => do
    let false := mkConst ``False
    let mut facts ← saturate ctx.objs ctx.facts false (← project p h) true
    let mut fresh := facts.extract ctx.facts.size facts.size
    let g ← guarded (← Ctx.new facts ctx.objs) (some (fresh.foldl (·.insert ·.type) {}))
    unless g.isEmpty do
      facts ← saturate ctx.objs facts false (← g.flatMapM fun f => project f.type f.proof) true
      fresh := facts.extract ctx.facts.size facts.size
    let map : Std.HashMap Expr Expr :=
      facts.foldl (fun m f => if m.contains f.type then m else m.insert f.type f.proof) {}
    for f in fresh do
      if let some q := map[← negLit f.type]? then
        let lam ← mkLambdaFVars #[h] (contra f.type f.proof q)
        if e.not?.isSome then return some lam
        return some (mkApp2 (mkConst ``Classical.byContradiction) e lam)
    return none

/-- Literals worth refuting: diagrammatic, not (in)equalities. -/
def refutable (e : Expr) : MetaM Bool := do
  match head e with
  | some (n, _) => return n != ``Eq && n != ``False && !(← isArith e)
  | none => return false

/-- `refute`, once per literal and at most `maxRefutes` times per top-level literal. -/
def tryRefute (ctx : Ctx) (e : Expr) : MetaM (Option Expr) := do
  unless (← refutable e) && (← ctx.refutes.get) < maxRefutes && !(← ctx.refuted.get).contains e do
    return none
  ctx.refutes.modify (· + 1)
  ctx.refuted.modify (·.insert e)
  let t0 ← IO.monoNanosNow
  let r ← refute ctx e
  if systemE.stats.get (← getOptions) then
    let dt := (← IO.monoNanosNow) - t0
    profRef.modify fun m => m.alter s!"refute {r.isSome}" fun v =>
      let (a, b) := v.getD (0, 0)
      some (a + dt, b + 1)
  return r

/-- `¬x.onLine L` by refutation, where the incidence is unknown and the point
or the line occurs in a same-side or incidence literal `l`. -/
def settle (ctx : Ctx) (l : Expr) : MetaM (Array Fact) := do
  let some (n, _) := head l | return #[]
  unless n == `Point.sameSide || n == `Point.onLine do return #[]
  let mut pts := #[]
  let mut lines := #[]
  for x in (collectFVars {} l).fvarIds do
    let t ← instantiateMVars (← inferType (.fvar x))
    if t.isConstOf `Point then pts := pts.push (Expr.fvar x)
    if t.isConstOf `Line then lines := lines.push (Expr.fvar x)
  let mut out := #[]
  let allPts := objectsOf ctx.objs (mkConst `Point)
  let allLines := objectsOf ctx.objs (mkConst `Line)
  for L in allLines do
    for x in allPts do
      unless pts.contains x || lines.contains L do continue
      let on := mkApp2 (mkConst `Point.onLine) x L
      if ctx.store.map.contains on || ctx.store.map.contains (mkNot on) then continue
      if let some p ← refute ctx (mkNot on) then out := out.push ⟨mkNot on, p⟩
  return out

/-- `L ≠ M` for lines: a point of one line refuted on the other. -/
def lineNe (ctx : Ctx) (e : Expr) : MetaM (Option Expr) := do
  let some (t, l, m) := e.ne? | return none
  unless (← instantiateMVars t).isConstOf `Line do return none
  for (l, m, flip) in [(l, m, false), (m, l, true)] do
    for f in ctx.store.byHead.getD (some (`Point.onLine, true)) #[] do
      unless f.type.appArg! == l do continue
      let x := f.type.appFn!.appArg!
      let some hn ← tryRefute ctx (mkNot (mkApp2 (mkConst `Point.onLine) x m)) | continue
      let p := mkApp4 (mkConst `line_ne_of_on_line) x l m
        (mkApp4 (mkConst ``And.intro) f.type (mkNot (mkApp2 (mkConst `Point.onLine) x m)) f.proof hn)
      if flip then return some (← mkAppM ``Ne.symm #[p])
      return some p
  return none

mutual

/-- Prove a goal literal: a fact, metric, or by a backward rule. -/
partial def proveLit (ctx : Ctx) (depth : Nat) (e : Expr) :
    MetaM (Option Expr) := do
  let e ← instantiateMVars e
  if let some (r, d) := (← ctx.memo.get)[e]? then
    if r.isSome || depth ≤ d then return r
  ctx.calls.modify (· + 1)
  if (← ctx.calls.get) > maxCalls then return none
  Core.checkSystem "saturate"
  let r ← proveLitCore ctx depth e
  -- a failure after a cap was hit may not be final
  if r.isSome || ((← ctx.calls.get) ≤ maxCalls && (← ctx.ariths.get) ≤ maxAriths &&
      (← ctx.substs.get) ≤ maxSubsts) then
    ctx.memo.modify (·.insert e (r, depth))
  return r

partial def proveLitCore (ctx : Ctx) (depth : Nat) (e : Expr) : MetaM (Option Expr) := do
  if let some (_, x, y) := e.ne? then if x == y then return none
  if let some (_, x, y) := e.eq? then if x == y then return some (← mkEqRefl x)
  if let some p := ctx.store.map[e]? then return p
  let flip? := e.ne?.map fun (t, x, y) => mkApp3 e.getAppFn t y x
  if let some e' := flip? then
    if let some p := ctx.store.map[e']? then return some (← mkAppM ``Ne.symm #[p])
  if e.isConstOf ``False then
    -- a fact and its negation
    for f in ctx.facts do
      if let some p := ctx.store.map[← negLit f.type]? then return some (contra f.type f.proof p)
    -- a metric contradiction
    ctx.ariths.modify (· + 1)
    if let some p ← arith ctx.pool ctx.neFact e (lines := ctx.lines) then return some p
    -- expand at most `maxSubst` atoms, of the newest facts first
    let mut ts : Array Expr := #[]
    for (f, _) in ctx.pool.reverse do
      for a in atomTerms f.type do
        if !ts.contains a && ts.size < maxSubst then ts := ts.push a
    let seeds := ctx.pool.foldl (fun acc (_, ks) => acc ++ ks) #[]
    return ← arith (← metricFor ctx ts 0) ctx.neFact e seeds (lines := ctx.lines)
  if ← isArith e then
    ctx.ariths.modify (· + 1)
    if (← ctx.ariths.get) > maxAriths then return none
    -- side conditions `a ≠ b` of angle symmetry: facts only
    let ne := ctx.neFact
    -- expand the goal's atoms, then the atoms of the new facts
    if let some (_, x, y) := e.eq? then
      if let some p := ctx.store.map[← mkEq y x]? then return some (← mkEqSymm p)
    let t0 ← IO.monoNanosNow
    let mut r ← arith ctx.pool ne e (lines := ctx.lines)
    if r.isNone then
      let mut size := ctx.pool.size
      for level in [0:2] do
        let pool ← metricFor ctx (atomTerms e) level
        -- nothing new
        if pool.size == size then continue
        size := pool.size
        if let some p ← arith pool ne e (lines := ctx.lines) then r := some p; break
    if systemE.stats.get (← getOptions) then
      let dt := (← IO.monoNanosNow) - t0
      profRef.modify fun m => m.alter s!"arith {r.isSome}" fun v =>
        let (a, b) := v.getD (0, 0)
        some (a + dt, b + 1)
    return r
  if depth == 0 then return none
  -- at the top, by contradiction first: one saturation, often cheaper than search
  if depth == (← ctx.top.get) then
    if let some p ← tryRefute ctx e then return some p
    if let some p ← lineNe ctx e then return some p
  if let some (t, x, y) := e.ne? then
    if (← instantiateMVars t).isConstOf `Point && x.isFVar && y.isFVar then
      let t0 ← IO.monoNanosNow
      let r ← neByMetric ctx x y
      if systemE.stats.get (← getOptions) then
        let dt := (← IO.monoNanosNow) - t0
        profRef.modify fun m => m.alter s!"neByMetric {r.isSome}" fun v =>
          let (a, b) := v.getD (0, 0)
          some (a + dt, b + 1)
      if let some p := r then return some p
  if let some p ← backwardLit ctx depth e then return p
  if let some e' := flip? then
    if let some p ← backwardLit ctx depth e' then return some (← mkAppM ``Ne.symm #[p])
  -- by contradiction, in the top two levels
  if depth + 1 ≥ (← ctx.top.get) then
    if let some p ← tryRefute ctx e then return some p
  return none

/-- Prove `e` by a clause whose result matches it. -/
partial def backwardLit (ctx : Ctx) (depth : Nat) (e : Expr) :
    MetaM (Option Expr) := do
  -- shallow pass (bound diagram premises must be facts), then deep pass
  for deep in [false, true] do
    for cl in (← backwardClauses).getD (head e) #[] do
      -- contrapositives only in the first two levels
      if cl.drop.isSome && depth + 1 < (← ctx.top.get) then continue
      let some σ := pmatch cl.resT e {} | continue
      let cache ← IO.mkRef (#[] : Array Fact)
      let out ← IO.mkRef (none : Option Expr)
      let done ← IO.mkRef false
      let lits := (List.range cl.needT.size).zip cl.needT.toList
      let t0 ← IO.monoNanosNow
      let h0 ← IO.getNumHeartbeats
      let c0 ← ctx.calls.get
      searchBack ctx depth deep cl cache done (fun σ => do
        let leaf := fun l => do
          if let some p := ctx.store.map[l]? then return some p
          if let some p ← find (← cache.get) l then return some p
          proveLit ctx (depth - 1) l
        if let some pf ← cl.build σ leaf then
          out.set (some pf)
          done.set true) lits σ
      if systemE.stats.get (← getOptions) then
        let dt := (← IO.monoNanosNow) - t0
        let dh := (← IO.getNumHeartbeats) - h0
        let dc := (← ctx.calls.get) - c0
        profRef.modify fun m => m.alter s!"back {cl.rule} {cl.drop} {cl.concl} d{depth} {deep}" fun v =>
          let (a, b) := v.getD (0, 0)
          some (a + dt, b + dh / 1000 + 1000000 * dc)
      if let some pf ← out.get then return some pf
  return none

/-- Bind the needed templates: prove bound ones (recursively if `deep`, else
from facts; metric ones by `linarith`), match the most-bound unbound one
against facts; never invent objects. -/
partial def searchBack (ctx : Ctx) (depth : Nat) (deep : Bool) (cl : Clause)
    (cache : IO.Ref (Array Fact)) (done : IO.Ref Bool) (k : Subst → MetaM Unit) :
    List (Nat × Expr) → Subst → MetaM Unit
  | [], σ => k σ
  | ls, σ => do
    if ← done.get then return
    let n := cl.sorts.size
    -- bound diagram literals, then the most-bound unbound one, metric last
    let mut best : Option ((Nat × Expr) × Nat) := none
    for l in ls do
      if cl.arith[l.1]! then continue
      let u := unbound l.2 σ n
      if u == 0 then best := some (l, 0); break
      if best.all (u < ·.2) then best := some (l, u)
    if best.isNone then
      best := (ls.find? fun l => unbound l.2 σ n == 0).map (·, 0)
    let some ((pos, t), u) := best | return
    let rest := ls.filter (·.1 != pos)
    let go := searchBack ctx depth deep cl cache done k rest
    if u == 0 then
      let l := fill t σ
      if let some p ← ctx.fact? (← cache.get) l then
        cache.modify (·.push ⟨l, p⟩)
        go σ
      -- equalities of objects are used only as facts
      else if l.isEq && !cl.arith[pos]! then return
      -- below the top, metric premises only about quantities the context mentions
      else if cl.arith[pos]! && depth < (← ctx.top.get) && !(atoms l).all ctx.known.contains then
        return
      -- shallow pass: only facts and literals proved already
      else if !deep then
        let some (some p, _) := (← ctx.memo.get)[l]? | return
        cache.modify (·.push ⟨l, p⟩)
        go σ
      else if let some p ← proveLit ctx (depth - 1) l then
        cache.modify (·.push ⟨l, p⟩)
        go σ
    else
      for (f, _) in ctx.idx.cands t σ do
        if ← done.get then return
        if let some σ' := pmatch t f.type σ then go σ'

end

/-- Prove a top-level literal, by iterative deepening. -/
def proveTop (ctx : Ctx) (l : Expr) : MetaM (Option Expr) := do
  for d in [1:maxDepth + 1] do
    ctx.top.set d
    if let some p ← proveLit ctx d l then return some p
  return none

def contextObjects : MetaM Objects := do
  let mut objs : Objects := (← configRef.get).objectSorts.map (·, #[])
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some n := (← instantiateMVars d.type).constName? then
      objs := objs.map fun (m, xs) => if m == n then (m, xs.push d.toExpr) else (m, xs)
  return objs

def contextFacts : MetaM (Array Fact) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← isProp d.type then
      out := out ++ (← project (← instantiateMVars d.type) d.toExpr)
  return out


/-- Literal heads the rules can conclude. -/
def conclusionHeads : MetaM (Array (Name × Bool)) := do
  return (← clauses).filterMap (·.head)

/-- Worth trying: every goal literal is a fact, metric, or a rule conclusion. -/
partial def disjuncts (e : Expr) : MetaM (List Expr) := do
  -- `¬(p ∧ q)` and `¬¬p` are proved through `¬p`, `¬q` and `p`
  if let some (p, q) ← notAnd? e then return (← disjuncts (mkNot p)) ++ (← disjuncts (mkNot q))
  if let some x := e.not? then
    if let some p := x.not? then return ← disjuncts p
  match (← whnfR e).app2? ``Or with
  | some (p, q) => return (← (← literals p).flatMapM disjuncts) ++ (← (← literals q).flatMapM disjuncts)
  | none => return [e]

def worthTrying (facts : Array Fact) (goal : Expr) : MetaM Bool := do
  let heads ← conclusionHeads
  for l in ← (← literals goal).flatMapM disjuncts do
    if (← find facts l).isSome || (← isArith l) || l.isConstOf ``False then continue
    match head l with
    | some h => unless heads.contains h do return false
    | none => return false
  return true

def stat (m : MessageData) : MetaM Unit := do
  if systemE.stats.get (← getOptions) then logInfo m!"stats: {m}"

/-- A diagrammatic closure: its facts (type to proof) and objects, and the result. -/
structure Closure where
  inputs : Std.HashMap Expr Expr
  objs : Objects
  out : Array Fact
deriving Inhabited

/-- Closures computed in recent declarations (keyed by their start). -/
initialize closuresRef : IO.Ref (Std.HashMap Nat (Array Closure)) ← IO.mkRef {}

/-- The declaration being elaborated (its start heartbeats). -/
initialize declRef : IO.Ref Nat ← IO.mkRef 0

/-- Most closures kept per declaration. -/
def maxClosures : Nat := 16

/-- The diagrammatic closure of `facts0`: from the largest earlier closure of the
same declaration whose facts are all among them, only the consequences of the
new facts and objects are derived. Hypotheses reintroduced since (by `simp_all`)
are matched by type, and the closure's proofs moved to them. -/
def closure (objs : Objects) (facts0 : Array Fact) : MetaM (Array Fact) := do
  let decl ← declRef.get
  let have_ : Std.HashMap Expr Expr :=
    facts0.foldl (fun m f => if m.contains f.type then m else m.insert f.type f.proof) {}
  let sub := fun (a b : Objects) => a.all fun (n, xs) =>
    xs.all fun x => (b.find? (·.1 == n)).any (·.2.contains x)
  let cs := (← closuresRef.get).getD decl #[]
  let mut best : Option Closure := none
  for c in cs do
    if c.inputs.size > (best.map (·.inputs.size)).getD 0 &&
        c.inputs.toList.all (have_.contains ·.1) && sub c.objs objs then
      best := some c
  let mut out := #[]
  if let some c := best then
    let extra := facts0.filter fun f => !c.inputs.contains f.type
    let newObjs := !sub objs c.objs
    -- old proofs of the inputs to the current ones
    let moved : Std.HashMap Expr Expr := c.inputs.fold (fun m t p =>
      let q := have_[t]!
      if p == q then m else m.insert p q) {}
    out := if moved.isEmpty then c.out else
      c.out.map fun f => { f with proof := f.proof.replace (moved[·]?) }
    if !extra.isEmpty || newObjs then
      out ← saturate objs out (mkConst ``False) extra (conflict := true) (closed := true)
        (metric := false) (newObjs := newObjs)
  else
    out ← saturate objs facts0 (mkConst ``False) (conflict := true) (metric := false)
  let c : Closure := ⟨have_, objs, out⟩
  closuresRef.modify fun m =>
    let m := if m.size > 8 && !m.contains decl then {} else m
    m.insert decl (((m.getD decl #[]).push c).toList.drop
      (((m.getD decl #[]).size + 1) - maxClosures)).toArray
  return out

/-- Replace the result of the declaration's latest closure (extended by facts). -/
def setLastClosure (out : Array Fact) : MetaM Unit := do
  let decl ← declRef.get
  closuresRef.modify fun m => match m[decl]? with
    | some cs => if cs.isEmpty then m else
      m.insert decl (cs.set! (cs.size - 1) { cs.back! with out })
    | none => m

/-- An equality between distinct objects among the facts. -/
def objectEq? (facts : Array Fact) : MetaM (Option Fact) := do
  for f in facts do
    if let some (t, x, y) := f.type.eq? then
      if x.isFVar && y.isFVar && x != y then
        let t ← instantiateMVars t
        if t.isConstOf `Point || t.isConstOf `Line || t.isConstOf `Circle then return some f
  return none

/-- Saturate and prove `g`; if that fails and saturation found an equality of
two objects, substitute it and try again (`fuel` times). Assigns `g` on success. -/
partial def attempt (g : MVarId) (phase : IO.Ref MessageData) (last : IO.Ref Expr)
    (fuel : Nat) : MetaM Bool := g.withContext do
  let goal := (← instantiateMVars (← g.getType)).consumeMData
  let facts0 ← contextFacts
  let objs ← contextObjects
  phase.set m!"saturating {facts0.size} facts"
  let diag ← closure objs facts0
  -- contradictory facts (the closure stops at the first): the goal follows
  let dmap : Std.HashMap Expr Expr :=
    diag.foldl (fun m f => if m.contains f.type then m else m.insert f.type f.proof) {}
  for f in diag do
    if let some (_, x, y) := f.type.ne? then
      if x == y then
        g.assign (← mkAppOptM ``False.elim #[goal, mkApp f.proof (← mkEqRefl x)])
        return true
    if let some q := dmap[← negLit f.type]? then
      g.assign (← mkAppOptM ``False.elim #[goal, contra f.type f.proof q])
      return true
  let mut facts ← saturate objs diag goal (closed := true) (metric := true)
  let mut ctx ← Ctx.new facts objs
  let new ← guarded ctx
  unless new.isEmpty do
    phase.set m!"saturating {new.size} facts from guarded lemmas"
    facts ← saturate objs facts goal (← new.flatMapM fun f => project f.type f.proof)
    ctx ← Ctx.new facts objs
  let top := fun l => do
    last.set l
    ctx.calls.set 0
    ctx.ariths.set 0
    ctx.substs.set 0
    ctx.refutes.set 0
    phase.set m!"proving {l} from {facts.size} facts"
    if let some p ← findDefEq facts l then return some p
    -- settle the incidences of the literal's points and lines first; the
    -- results join the cached closure
    let new ← settle ctx l
    if new.isEmpty then return ← proveTop ctx l
    let diag' ← saturate objs diag goal new
    setLastClosure diag'
    let ctx' ← Ctx.new (diag' ++ facts.extract diag.size facts.size) objs
    proveTop ctx' l
  if let some pf ← prove top goal (fun l => findDefEq facts l) then
    g.assign pf
    return true
  if fuel == 0 then return false
  let some f ← objectEq? facts | return false
  let g1 ← g.assert `h f.type f.proof
  let (h, g2) ← g1.intro1P
  let g3 ← subst g2 h
  attempt g3 phase last (fuel - 1)

/-- Heartbeats saturation spent in the current declaration (keyed by its start). -/
initialize spentRef : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

/-- Try to close `g` by saturation; leave the state unchanged on failure. -/
def close (g : MVarId) : TacticM Bool := do
  let s ← Tactic.saveState
  let budget := systemE.saturateBudget.get (← getOptions)
  -- saturation may spend at most 30% of a declaration's heartbeats
  let core ← readThe Core.Context
  let (decl, spent) ← spentRef.get
  let spent := if decl == core.initHeartbeats then spent else 0
  declRef.set core.initHeartbeats
  let budget := if core.maxHeartbeats == 0 then budget else
    min budget ((3 * core.maxHeartbeats / 10 - min spent (3 * core.maxHeartbeats / 10)) / 1000)
  if budget * 10 < systemE.saturateBudget.get (← getOptions) then
    stat m!"capped"
    return false
  let start ← IO.getNumHeartbeats
  arithFails.set {}
  let phase ← IO.mkRef m!"start"
  let r ← tryCatchRuntimeEx (withoutRecover <| withCurrHeartbeats <|
      withTheReader Core.Context ({ · with maxHeartbeats := budget * 1000 }) do
    let g ← try substVars g catch _ => pure g
    let goal0 ← g.withContext (do return (← instantiateMVars (← g.getType)).consumeMData)
    let worth ← g.withContext (do worthTrying (← contextFacts) goal0)
    unless worth do
      s.restore
      return false
    let last ← IO.mkRef goal0
    if ← attempt g phase last 1 then return true
    s.restore
    stat m!"stuck {← last.get}"
    return false)
    fun _ => do
      s.restore
      stat m!"budget, {← phase.get}"
      return false
  let dh := (← IO.getNumHeartbeats) - start
  spentRef.set (core.initHeartbeats, spent + dh)
  stat m!"cost {r} {dh / 1000}"
  return r

/-- Log the clauses that took the most time in saturation so far. -/
def reportProfile : MetaM Unit := do
  let top := (← profRef.get).toArray.qsort (fun a b => a.2.1 > b.2.1)
  logInfo m!"stats: profile {top.toList.take 12 |>.map fun (n, t, k) => s!"{n} {t / 1000000}ms {k}"}"

elab "#saturate_profile" : command => Command.liftTermElabM reportProfile

def getSaturateOption : MetaM Bool := return (← getOptions).getBool `systemE.saturate true

def getSmtOption : MetaM Bool := return (← getOptions).getBool `systemE.smt true

syntax "euclid_saturate" : tactic

elab "euclid_saturate" : tactic => do
  unless ← close (← getMainGoal) do throwError "euclid_saturate failed"
  replaceMainGoal []

end SystemE.Saturate
