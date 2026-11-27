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
  defValue := 10000
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
  /-- Prove the goal from the given proofs by `linarith only`. -/
  linarith : List Expr → Expr → MetaM (Option Expr) := fun _ _ => pure none
deriving Inhabited

initialize configRef : IO.Ref Config ← IO.mkRef {}

/-- Depth of backward chaining. -/
def maxDepth : Nat := 4

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
  | none => return [e]

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

/-- Prove a conjunction, each literal by `leaf`. -/
partial def prove (leaf : Expr → MetaM (Option Expr)) (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  match (← whnfR e).and? with
  | some (p, q) =>
    let some hp ← prove leaf p | return none
    let some hq ← prove leaf q | return none
    return mkApp4 (mkConst ``And.intro) p q hp hq
  | none => leaf e

def isArith (e : Expr) : MetaM Bool := do
  match e.getAppFnArgs with
  | (``Eq, #[t, _, _]) | (``LT.lt, #[t, _, _, _]) | (``LE.le, #[t, _, _, _])
  | (``GT.gt, #[t, _, _, _]) | (``GE.ge, #[t, _, _, _]) =>
    return (← instantiateMVars t).isConstOf `Real
  | _ => return false

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

/-- Unordered key of a segment. -/
def segKey (p : Expr × Expr) : Expr × Expr :=
  if Expr.lt p.2 p.1 then (p.2, p.1) else p

/-- Metric atoms of `e` (segments, angles, triangle areas), each keyed up to
the symmetries of its points. -/
partial def atoms (e : Expr) (acc : Array (Array Expr) := #[]) : Array (Array Expr) :=
  let sort := fun (xs : Array Expr) => xs.qsort Expr.lt
  if e.isAppOfArity `Segment.length 1 then
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

/-- Metric facts with their atoms. -/
def metricPool (facts : Array Fact) : MetaM (Array (Fact × Array (Array Expr))) :=
  facts.filterMapM fun f => do
    return if ← isArith f.type then some (f, atoms f.type) else none

/-- Prove a metric literal by `linarith only`, over the metric facts connected
to it by shared atoms, plus `ab = ba` and `∠abc = ∠cba` where both orders occur. -/
def arith (pool : Array (Fact × Array (Array Expr))) (ne : Expr → MetaM (Option Expr))
    (e : Expr) : MetaM (Option Expr) := do
  let mut pool := pool
  let mut keys := atoms e
  let mut hyps := #[]
  if keys.isEmpty then
    hyps := pool.map (·.1)
  else
    let mut changed := true
    while changed do
      changed := false
      let mut rest := #[]
      for (f, ks) in pool do
        if ks.any keys.contains then
          hyps := hyps.push f
          keys := keys ++ ks.filter (!keys.contains ·)
          changed := true
        else rest := rest.push (f, ks)
      pool := rest
    if hyps.isEmpty then return none
    -- every atom of the goal must occur in some fact
    let seen := hyps.foldl (fun s f => (atoms f.type).foldl (·.insert ·) s) ({} : Std.HashSet (Array Expr))
    unless (atoms e).all seen.contains do return none
  let mut segs := segments e
  for f in hyps do segs := segments f.type segs
  let mut proofs := hyps.map (·.proof)
  let mut done : Array (Expr × Expr) := #[]
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
  (← configRef.get).linarith proofs.toList e

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
  return t.isConstOf `Point || t.isConstOf `Line || t.isConstOf `Circle

/-- Clauses needing more literals are used only backward. -/
def maxForwardNeeds : Nat := 6

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
  let fwd := !back && !arith.any id && !needT.isEmpty && needT.size ≤ maxForwardNeeds &&
    (drop.isNone || (List.range objs.size).all inNeed)
  let sorts ← objs.mapM inferType
  return some ⟨n, drop, j, head res, fwd, needT.map head, needT, resT, sorts, arith⟩

/-- The clauses of a rule. -/
def clausesOf (n : Name) : MetaM (Array Clause) := withNewMCtxDepth do
  let i ← inst n
  if i.prem.any compound then return #[]
  let objs ← i.args.filterM isObject
  let back := (← configRef.get).backwardLemmas.contains n
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
  return out ++ (cfg.lemmas ++ cfg.backwardLemmas).filter env.contains

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
    cfg.lemmas.contains cl.rule || cfg.backwardLemmas.contains cl.rule
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

/-- Facts by head, each with the round it was added in. -/
abbrev Index := Std.HashMap (Option (Name × Bool)) (Array (Fact × Nat))

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

/-- Bind the templates (with positions) to facts allowed by `ok` (position,
round), most-bound first (or `first`), then the remaining objects to context
objects; run `k` on each full binding. -/
partial def matchAll (idx : Index) (objs : Objects) (sorts : Array Expr)
    (ok : Nat → Nat → Bool) (k : Subst → MetaM Unit) (lits : List (Nat × Expr))
    (σ : Subst) (first : Option Nat := none) : MetaM Unit := do
  match lits with
  | _ :: _ =>
    let n := sorts.size
    let best := match first.bind fun p => lits.find? (·.1 == p) with
      | some l => l
      | none => lits.foldl (fun (b l : Nat × Expr) =>
          if unbound l.2 σ n < unbound b.2 σ n then l else b) lits.head!
    let rest := lits.filter (·.1 != best.1)
    for (f, r) in idx.getD (head best.2) #[] do
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
    (keep : Expr → Bool := fun _ => true) : MetaM (Array Fact) := do
  let out ← IO.mkRef (#[] : Array Fact)
  let k := fun (σ : Subst) => do
    let res := fill cl.resT σ
    -- skip `x = x`
    if let some (_, x, y) := res.eq? then if x == y then return
    unless keep res do return
    if let some pf ← cl.build σ (fun l => return map[l]?) then
      out.modify (·.push ⟨res, pf⟩)
  let lits := (List.range cl.needT.size).zip cl.needT.toList
  if round == 0 then
    matchAll idx objs cl.sorts (fun _ _ => true) k lits {}
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
  /-- Metric facts derived on demand, and the atoms already expanded. -/
  extra : IO.Ref (Array Fact)
  expanded : IO.Ref (Std.HashSet (Array Expr))
  idx : Index
  /-- Metric facts with their atoms, including the on-demand ones. -/
  pool : IO.Ref (Array (Fact × Array (Array Expr)))

def Ctx.new (facts : Array Fact) (objs : Objects) : MetaM Ctx :=
  return ⟨facts, Store.of facts, objs, ← IO.mkRef {}, ← IO.mkRef 0, ← IO.mkRef 0,
    ← IO.mkRef #[], ← IO.mkRef {},
    facts.foldl (fun m f => m.alter (head f.type) fun a => some ((a.getD #[]).push (f, 0))) {},
    ← IO.mkRef (← metricPool facts)⟩

/-- Metric forward clauses. -/
def metricClauses : MetaM (Array Clause) := do
  (← clauses).filterM fun cl => do return cl.forward && !cl.needs.isEmpty && (← isArith cl.resT)

/-- Fire the metric clauses whose results mention an atom of `e` not yet
expanded, then once more for the atoms of the new facts. -/
def expandMetric (ctx : Ctx) (e : Expr) : MetaM Unit := do
  let idx := ctx.idx
  let mut todo := atoms e
  for _ in [0:2] do
    let done ← ctx.expanded.get
    let new := todo.filter fun k => !done.contains k
    if new.isEmpty then return
    ctx.expanded.modify fun s => new.foldl (·.insert ·) s
    let keep := fun (r : Expr) => (atoms r).any new.contains
    todo := #[]
    for cl in ← metricClauses do
      unless cl.needs.all idx.contains do continue
      let fs ← fire ctx.store.map idx ctx.objs 0 {} cl keep
      ctx.extra.modify (· ++ fs)
      let mp ← metricPool fs
      ctx.pool.modify (· ++ mp)
      for f in fs do todo := todo ++ atoms f.type

/-- Recursive calls and `linarith` calls one attempt may make. -/
def maxCalls : Nat := 30000
def maxAriths : Nat := 400

/-- A fact stating `l`, or `b ≠ a` for `l = (a ≠ b)`. -/
def Ctx.fact? (ctx : Ctx) (cache : Array Fact) (l : Expr) : MetaM (Option Expr) := do
  if let some p := ctx.store.map[l]? then return some p
  if let some p ← find cache l then return some p
  if let some (t, x, y) := l.ne? then
    if let some p := ctx.store.map[mkApp3 l.getAppFn t y x]? then
      return some (← mkAppM ``Ne.symm #[p])
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
  let r ← proveLitCore ctx depth e
  ctx.memo.modify (·.insert e (r, depth))
  return r

partial def proveLitCore (ctx : Ctx) (depth : Nat) (e : Expr) : MetaM (Option Expr) := do
  if let some (_, x, y) := e.ne? then if x == y then return none
  if let some (_, x, y) := e.eq? then if x == y then return some (← mkEqRefl x)
  if let some p := ctx.store.map[e]? then return p
  let flip? := e.ne?.map fun (t, x, y) => mkApp3 e.getAppFn t y x
  if let some e' := flip? then
    if let some p := ctx.store.map[e']? then return some (← mkAppM ``Ne.symm #[p])
  if ← isArith e then
    ctx.ariths.modify (· + 1)
    if (← ctx.ariths.get) > maxAriths then return none
    expandMetric ctx e
    -- side conditions `a ≠ b` of angle symmetry: facts only
    let ne := fun (l : Expr) => do
      if let some p := ctx.store.map[l]? then return some p
      if let some (t, x, y) := l.ne? then
        if let some p := ctx.store.map[mkApp3 l.getAppFn t y x]? then
          return some (← mkAppM ``Ne.symm #[p])
      return none
    return ← arith (← ctx.pool.get) ne e
  if depth == 0 then return none
  if let some p ← backwardLit ctx depth e then return p
  if let some e' := flip? then
    if let some p ← backwardLit ctx depth e' then return some (← mkAppM ``Ne.symm #[p])
  return none

/-- Prove `e` by a clause whose result matches it. -/
partial def backwardLit (ctx : Ctx) (depth : Nat) (e : Expr) :
    MetaM (Option Expr) := do
  -- shallow pass (bound diagram premises must be facts), then deep pass
  for deep in [false, true] do
    for cl in (← backwardClauses).getD (head e) #[] do
      -- contrapositives only at the first level
      if cl.drop.isSome && depth < maxDepth then continue
      let some σ := pmatch cl.resT e {} | continue
      let cache ← IO.mkRef (#[] : Array Fact)
      let out ← IO.mkRef (none : Option Expr)
      let done ← IO.mkRef false
      let lits := (List.range cl.needT.size).zip cl.needT.toList
      searchBack ctx depth deep cl cache done (fun σ => do
        let leaf := fun l => do
          if let some p := ctx.store.map[l]? then return some p
          if let some p ← find (← cache.get) l then return some p
          proveLit ctx (depth - 1) l
        if let some pf ← cl.build σ leaf then
          out.set (some pf)
          done.set true) lits σ
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
      else if !deep && !cl.arith[pos]! then return
      else if let some p ← proveLit ctx (depth - 1) l then
        cache.modify (·.push ⟨l, p⟩)
        go σ
    else
      for f in ctx.store.byHead.getD (head t) #[] do
        if ← done.get then return
        if let some σ' := pmatch t f.type σ then go σ'

end

def contextObjects : MetaM Objects := do
  let mut objs : Objects := #[(`Point, #[]), (`Line, #[]), (`Circle, #[])]
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

/-- Per clause: time (ns) and facts produced; filled when `systemE.stats` is on. -/
initialize profRef : IO.Ref (Std.HashMap String (Nat × Nat)) ← IO.mkRef {}

/-- Close the facts under the forward clauses. -/
def saturate (objs : Objects) (facts0 : Array Fact) (goal : Expr) : MetaM (Array Fact) := do
  let prof := systemE.stats.get (← getOptions)
  let mut facts := facts0
  let mut idx : Index := {}
  for f in facts do idx := idx.alter (head f.type) fun a => some ((a.getD #[]).push (f, 0))
  let mut map : Std.HashMap Expr Expr :=
    facts.foldl (fun m f => if m.contains f.type then m else m.insert f.type f.proof) {}
  let mut cls := #[]
  let mut metric := #[]
  for cl in (← clauses).filter fun cl => cl.forward && !cl.needs.isEmpty do
    if ← isArith cl.resT then metric := metric.push cl else cls := cls.push cl
  let mut fresh : Std.HashSet (Option (Name × Bool)) := idx.keys.foldl (·.insert ·) {}
  for round in [0:maxRounds] do
    let mut added := false
    let mut new := #[]
    for cl in cls do
      unless cl.needs.all idx.contains && cl.needs.any fresh.contains do continue
      let t0 ← IO.monoNanosNow
      let fs ← fire map idx objs round fresh cl
      if prof then
        let dt := (← IO.monoNanosNow) - t0
        profRef.modify fun m => m.alter s!"{cl.rule} {cl.drop}" fun v =>
          some ((v.getD (0, 0)).1 + dt, (v.getD (0, 0)).2 + fs.size)
      for f in fs do
        unless map.contains f.type do
          map := map.insert f.type f.proof
          new := new.push f
          added := true
    fresh := new.foldl (fun s f => s.insert (head f.type)) {}
    for f in new do
      facts := facts.push f
      idx := idx.alter (head f.type) fun a => some ((a.getD #[]).push (f, round + 1))
    if !added || facts.size > maxFacts then break
  -- metric clauses: one pass, keeping results about atoms already mentioned
  let known : Std.HashSet (Array Expr) :=
    facts.foldl (fun s f => (atoms f.type).foldl (·.insert ·) s) ((atoms goal).foldl (·.insert ·) {})
  let keep := fun (e : Expr) => (atoms e).all known.contains
  for cl in metric do
    unless cl.needs.all idx.contains do continue
    for f in ← fire map idx objs 0 {} cl keep do
      unless map.contains f.type do
        map := map.insert f.type f.proof
        facts := facts.push f
  return facts

/-- Literal heads the rules can conclude. -/
def conclusionHeads : MetaM (Array (Name × Bool)) := do
  return (← clauses).filterMap (·.head)

/-- Worth trying: every goal literal is a fact, metric, or a rule conclusion. -/
def worthTrying (facts : Array Fact) (goal : Expr) : MetaM Bool := do
  let heads ← conclusionHeads
  for l in ← literals goal do
    if (← find facts l).isSome || (← isArith l) then continue
    match head l with
    | some h => unless heads.contains h do return false
    | none => return false
  return true

def stat (m : MessageData) : MetaM Unit := do
  if systemE.stats.get (← getOptions) then logInfo m!"stats: {m}"

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
  if core.maxHeartbeats > 0 && 10 * (spent + budget * 1000) > 3 * core.maxHeartbeats then
    return false
  let start ← IO.getNumHeartbeats
  let phase ← IO.mkRef m!"start"
  let r ← tryCatchRuntimeEx (withoutRecover <| withCurrHeartbeats <|
      withTheReader Core.Context ({ · with maxHeartbeats := budget * 1000 }) do
    let g ← try substVars g catch _ => pure g
    g.withContext do
      let goal ← instantiateMVars (← g.getType)
      let facts0 ← contextFacts
      unless ← worthTrying facts0 goal do
        s.restore
        return false
      let objs ← contextObjects
      phase.set m!"saturating {facts0.size} facts"
      let facts ← saturate objs facts0 goal
      let last ← IO.mkRef goal
      let ctx ← Ctx.new facts objs
      let top := fun l => do
        last.set l
        ctx.calls.set 0
        ctx.ariths.set 0
        phase.set m!"proving {l} from {facts.size} facts"
        if let some p ← findDefEq facts l then return some p
        proveLit ctx maxDepth l
      if let some pf ← prove top goal then
        g.assign pf
        return true
      let l ← last.get
      s.restore
      stat m!"stuck {l}"
      return false)
    fun _ => do
      s.restore
      stat m!"budget, {← phase.get}"
      return false
  spentRef.set (core.initHeartbeats, spent + ((← IO.getNumHeartbeats) - start))
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
