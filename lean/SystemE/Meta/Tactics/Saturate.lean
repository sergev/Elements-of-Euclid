import Mathlib.Tactic.Linarith
import SystemE.Theory

/-!
Saturation: a kernel-checked replacement for the SMT step.

Facts are literals from the context. Forward rules are axioms
`∀ objs, P₁ ∧ … → Q₁ ∧ …` (or curried premises) over diagrammatic literals;
they fire on every match until nothing new follows. Backward rules may have
metric premises; they are tried only on a goal literal, with metric premises
proved by `linarith only` over the metric facts. Metric goals go to
`linarith only` directly.
-/

open Lean Elab Tactic Meta

register_option systemE.saturate : Bool := {
  defValue := true
  descr := "Try saturation (kernel-checked) before the SMT solvers."
}

register_option systemE.saturateBudget : Nat := {
  defValue := 5000
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

theorem point_ne_symm : ∀ (a b : Point), a ≠ b → b ≠ a := fun _ _ h => h.symm

theorem length_pos_of_ne : ∀ (a b : Point), a ≠ b → 0 < |(a─b)| := fun a b h =>
  lt_of_le_of_ne (segment_gte_zero _) fun h0 => h (zero_segment_if a b h0.symm)

theorem ne_of_length_pos : ∀ (a b : Point), 0 < |(a─b)| → a ≠ b := by
  intro a b h e
  rw [zero_segment_onlyif a b e] at h
  exact lt_irrefl _ h

theorem not_inside_circle_of_ge : ∀ (a b c : Point) (α : Circle),
    (a.isCentre α) ∧ (b.onCircle α) ∧ |(a─b)| ≤ |(a─c)| → ¬(c.insideCircle α) := by
  intro a b c α ⟨ha, hb, h⟩ hc
  have := point_in_circle_onlyif a b c α ⟨ha, hb, hc⟩
  linarith

theorem not_on_circle_of_gt : ∀ (a b c : Point) (α : Circle),
    (a.isCentre α) ∧ (b.onCircle α) ∧ |(a─b)| < |(a─c)| → ¬(c.onCircle α) := by
  intro a b c α ⟨ha, hb, h⟩ hc
  have := point_on_circle_onlyif a b c α ⟨ha, hb, hc⟩
  linarith

theorem not_on_circle_of_lt : ∀ (a b c : Point) (α : Circle),
    (a.isCentre α) ∧ (b.onCircle α) ∧ |(a─c)| < |(a─b)| → ¬(c.onCircle α) := by
  intro a b c α ⟨ha, hb, h⟩ hc
  have := point_on_circle_onlyif a b c α ⟨ha, hb, hc⟩
  linarith

theorem ne_of_lines_ne : ∀ (a c b : Point) (L M : Line),
    a.onLine L ∧ b.onLine L ∧ b.onLine M ∧ c.onLine M ∧ a ≠ b ∧ L ≠ M → a ≠ c := by
  intro a c b L M ⟨haL, hbL, hbM, hcM, hab, hLM⟩ hac
  subst hac
  exact hLM (two_points_determine_line a b L M ⟨⟨haL, hbL, hab⟩, hcM, hbM⟩)

/-- A vertex of a triangle is not on the opposite side's line. -/
theorem not_on_line_of_triangle : ∀ (c a b : Point) (L M N : Line),
    a.onLine L ∧ b.onLine L ∧ c.onLine M ∧ b.onLine M ∧ c.onLine N ∧ a.onLine N ∧
    a ≠ b ∧ L ≠ M ∧ L ≠ N → ¬(c.onLine L) := by
  intro c a b L M N ⟨haL, hbL, hcM, hbM, hcN, haN, hab, hLM, hLN⟩ hcL
  have hac : a ≠ c := ne_of_lines_ne a c b L M ⟨haL, hbL, hbM, hcM, hab, hLM⟩
  exact hLN (two_points_determine_line a c L N ⟨⟨haL, hcL, hac⟩, haN, hcN⟩)

theorem not_between_of_same_side : ∀ (a b c : Point) (L : Line),
    a.sameSide c L ∧ b.onLine L → ¬(between a b c) :=
  fun a b c L ⟨h, hb⟩ hbtw => pasch_3 a b c L ⟨hbtw, hb⟩ h

/-- Points on the same ray from `d` at equal distances coincide. -/
theorem eq_of_same_ray : ∀ (x y d : Point) (L : Line),
    x.onLine L ∧ y.onLine L ∧ d.onLine L ∧ x ≠ d ∧ y ≠ d ∧ ¬(between x d y) ∧
    |(d─x)| = |(d─y)| → x = y := by
  intro x y d L ⟨hx, hy, hd, hxd, hyd, hb, h⟩
  by_contra hxy
  have := segment_symmetric d x
  have := segment_symmetric d y
  rcases between_points x d y L ⟨hxd, fun e => hyd e.symm, fun e => hxy e.symm, hx, hd, hy⟩
    with h1 | h1 | h1
  · exact hb h1
  · have := between_if d x y h1
    exact hxy (zero_segment_if x y (by linarith))
  · have := between_if x y d h1
    exact hxy (zero_segment_if x y (by linarith))

/-- Equal angles at `d` from line `L`, on the same side, lie on the same line. -/
theorem on_line_of_eq_angle : ∀ (c : Point) (M : Line) (d f e : Point) (L : Line),
    d.onLine M ∧ f.onLine M ∧ c.sameSide f L ∧ d.onLine L ∧ e.onLine L ∧
    d ≠ e ∧ d ≠ f ∧ d ≠ c ∧ ∠ e:d:c = ∠ e:d:f → c.onLine M := by
  intro c M d f e L ⟨hdM, hfM, hcf, hdL, heL, hde, hdf, hdc, hang⟩
  by_contra hcM
  have hfc := same_side_symm c f L hcf
  have hcL : ¬ c.onLine L := same_side_not_on_line c f L hcf
  have hfL : ¬ f.onLine L := same_side_not_on_line f c L hfc
  have hLM : L ≠ M := fun h => hfL (by rw [h]; exact hfM)
  obtain ⟨N, hdN, hcN⟩ := line_from_points d c hdc
  have hNM : N ≠ M := fun h => hcM (by rw [← h]; exact hcN)
  by_cases hs : e.sameSide c M
  · have hsum := sum_angles_onlyif d e f c L M
      ⟨hdL, hdM, heL, hfM, hde, hdf, hcL, hcM, hLM, hs, hfc⟩
    have h0 : ∠ c:d:f = 0 := by linarith
    have hfN := (degenerated_angle_onlyif d c f N ⟨hdc, hdf, hdN, hcN, h0⟩).1
    exact hNM (two_points_determine_line d f N M ⟨⟨hdN, hfN, hdf⟩, hdM, hfM⟩)
  · have hfN : ¬ f.onLine N := fun h =>
      hNM (two_points_determine_line d f N M ⟨⟨hdN, h, hdf⟩, hdM, hfM⟩)
    have hLN : L ≠ N := fun h => hcL (by rw [h]; exact hcN)
    have hef := triple_incidence_2 L M N d e f c
      ⟨hdL, hdM, hdN, heL, hfM, hcN, hfc, hs, hcM, fun h => hde h.symm⟩
    have hsum := sum_angles_onlyif d e c f L N
      ⟨hdL, hdN, heL, hcN, hde, hdc, hfL, hfN, hLN, hef, hcf⟩
    have h0 : ∠ f:d:c = 0 := by linarith
    exact hcM (degenerated_angle_onlyif d f c M ⟨hdf, hdc, hdM, hfM, h0⟩).1

namespace SystemE.Saturate

/-- Head relation of a literal, with its polarity. -/
def head (e : Expr) : Option (Name × Bool) :=
  match e.not? with
  | some p => p.getAppFn.constName?.map (·, false)
  | none => e.getAppFn.constName?.map (·, true)

structure Fact where
  type : Expr
  proof : Expr

/-- Facts whose head can match `e`'s. -/
def candidates (facts : Array Fact) (e : Expr) : Array Fact :=
  match head e with
  | some h => facts.filter fun f => head f.type == some h
  | none => facts

/-- Rules fired forward; premises are diagrammatic. -/
def forward : Array Name := #[
  ``point_ne_symm,
  ``length_pos_of_ne,
  ``center_inside_circle,
  ``inside_not_on_circle,
  ``between_symm,
  ``between_if,
  ``intersection_circle_circle_2,
  ``point_on_circle_onlyif]

/-- Rules tried backward from a goal literal; premises may be metric. -/
def backward : Array Name := #[
  ``ne_of_length_pos,
  ``point_in_circle_if,
  ``not_inside_circle_of_ge,
  ``not_on_circle_of_gt,
  ``not_on_circle_of_lt,
  ``ne_of_lines_ne,
  ``not_between_of_same_side,
  ``not_on_line_of_triangle,
  ``eq_of_same_ray,
  ``two_points_determine_line,
  ``on_line_of_eq_angle]

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

def find (facts : Array Fact) (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  if let some f := facts.find? (·.type == e) then return some f.proof
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
    return (← instantiateMVars t).isConstOf ``Real
  | _ => return false

/-- Segments `|(x─y)|` occurring in `e`, as endpoint pairs. -/
partial def segments (e : Expr) (acc : Array (Expr × Expr) := #[]) : Array (Expr × Expr) :=
  if e.isAppOfArity ``Segment.length 1 then
    match e.appArg!.getAppFnArgs with
    | (``Segment.endpoints, #[x, y]) => acc.push (x, y)
    | _ => acc
  else match e with
    | .app f a => segments a (segments f acc)
    | _ => acc

/-- Angles `∠ x:y:z` occurring in `e`. -/
partial def angles (e : Expr) (acc : Array (Expr × Expr × Expr) := #[]) :
    Array (Expr × Expr × Expr) :=
  if e.isAppOfArity ``Angle.degree 1 then
    match e.appArg!.getAppFnArgs with
    | (``Angle.ofPoints, #[x, y, z]) => acc.push (x, y, z)
    | _ => acc
  else match e with
    | .app f a => angles a (angles f acc)
    | _ => acc

/-- Unordered key of a segment. -/
def segKey (p : Expr × Expr) : Expr × Expr :=
  if Expr.lt p.2 p.1 then (p.2, p.1) else p

/-- Prove a metric literal by `linarith only`, over the metric facts connected
to it by shared segments, plus `ab = ba` where both orders occur. -/
def arith (facts : Array Fact) (ne : Expr → MetaM (Option Expr)) (e : Expr) :
    MetaM (Option Expr) := do
  let mut pool := #[]
  for f in facts do
    if ← isArith f.type then pool := pool.push (f, (segments f.type).map segKey)
  let mut keys := (segments e).map segKey
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
  let mut segs := segments e
  for f in hyps do segs := segments f.type segs
  let mut proofs := hyps.map (·.proof)
  let mut done : Array (Expr × Expr) := #[]
  for (x, y) in segs do
    if segs.contains (y, x) && x != y && !done.contains (segKey (x, y)) then
      done := done.push (segKey (x, y))
      proofs := proofs.push (mkApp2 (mkConst ``segment_symmetric) x y)
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
        (mkApp4 (mkConst ``angle_symm) x y z (mkApp4 (mkConst ``And.intro) t1 t2 h1 h2))
  let m ← mkFreshExprMVar e
  try
    Mathlib.Tactic.Linarith.linarith true proofs.toList {} m.mvarId!
    return some (← instantiateMVars m)
  catch _ => return none

/-- Ground objects (points, lines, circles) of the context, by sort. -/
abbrev Objects := Array (Name × Array Expr)

def objectsOf (objs : Objects) (ty : Expr) : Array Expr :=
  match ty.constName? with
  | some n => (objs.find? (·.1 == n)).map (·.2) |>.getD #[]
  | none => #[]

/-- Match literals against facts, enumerate unbound objects, then run `k`;
stop once `done` is set. -/
partial def search (facts : Array Fact) (objs : Objects) (done : IO.Ref Bool)
    (k : MetaM Unit) : List Expr → List Expr → MetaM Unit
  | l :: ls, vs => do
    for f in candidates facts (← instantiateMVars l) do
      if ← done.get then return
      let s ← saveState
      if ← withReducible (isDefEq l f.type) then search facts objs done k ls vs
      s.restore
  | [], v :: vs => do
    if (← instantiateMVars v).isMVar then
      for o in objectsOf objs (← inferType v) do
        if ← done.get then return
        let s ← saveState
        if ← isDefEq v o then search facts objs done k [] vs
        s.restore
    else search facts objs done k [] vs
  | [], [] => k

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

/-- All conclusions of a forward rule. -/
def fire (facts : Array Fact) (objs : Objects) (rule : Name) : MetaM (Array Fact) := do
  let c := mkConst rule
  let (args, _, concl) ← forallMetaTelescope (← inferType c)
  let (lits, vars) ← premises args false
  let out ← IO.mkRef (#[] : Array Fact)
  let done ← IO.mkRef false
  withoutModifyingState <| search facts objs done (do
    if let some pf ← apply c args (find facts) then
      let ty ← instantiateMVars concl
      out.modify (·.push ⟨ty, pf⟩)) lits vars
  let mut res := #[]
  for f in ← out.get do
    res := res ++ (← project f.type f.proof)
  return res

/-- Literals a backward search binds by matching facts. -/
def matchable (e : Expr) : MetaM Bool := do
  return e.not?.isNone && !e.isAppOf ``Ne && !(← isArith e)

/-- An unassigned object metavariable of `e`. -/
def objectMVar? (e : Expr) : MetaM (Option Expr) := do
  for m in ← getMVars e do
    let t ← instantiateMVars (← m.getType)
    if t.isConstOf ``Point || t.isConstOf ``Line || t.isConstOf ``Circle then
      return some (mkMVar m)
  return none

structure Ctx where
  facts : Array Fact
  objs : Objects
  memo : IO.Ref (Std.HashMap (Expr × Nat) (Option Expr))

mutual

/-- Prove a goal literal: a fact, metric, or by a backward rule. -/
partial def proveLit (ctx : Ctx) (depth : Nat) (e : Expr) :
    MetaM (Option Expr) := do
  let e ← instantiateMVars e
  if let some r := (← ctx.memo.get)[(e, depth)]? then return r
  let r ← proveLitCore ctx depth e
  ctx.memo.modify (·.insert (e, depth) r)
  return r

partial def proveLitCore (ctx : Ctx) (depth : Nat) (e : Expr) : MetaM (Option Expr) := do
  let facts := ctx.facts
  if let some p ← find facts e then return p
  let flip? := e.ne?.map fun (t, x, y) => mkApp3 e.getAppFn t y x
  if let some e' := flip? then
    if let some p ← find facts e' then return some (← mkAppM ``Ne.symm #[p])
  if ← isArith e then
    return ← arith facts (proveLit ctx (depth - 1)) e
  if depth == 0 then return none
  if let some p ← backwardLit ctx depth e then return p
  if let some e' := flip? then
    if let some p ← backwardLit ctx depth e' then return some (← mkAppM ``Ne.symm #[p])
  return none

/-- Prove `e` by a backward rule whose conclusion matches it. -/
partial def backwardLit (ctx : Ctx) (depth : Nat) (e : Expr) :
    MetaM (Option Expr) := do
  let facts := ctx.facts
  for r in backward do
    unless (← getEnv).contains r do continue
    let s ← saveState
    let c := mkConst r
    let (args, _, concl) ← forallMetaTelescope (← inferType c)
    if ← withReducible (isDefEq concl e) then
      let (lits, _) ← premises args false
      let cache ← IO.mkRef (#[] : Array Fact)
      let res ← IO.mkRef (none : Option Expr)
      let done ← IO.mkRef false
      searchBack ctx depth cache done (do
        let leaf := fun l => do
          if let some p ← find ((← cache.get) ++ facts) l then return some p
          proveLit ctx (depth - 1) l
        if let some pf ← apply c args leaf then
          unless pf.hasExprMVar do
            res.set (some pf)
            done.set true) lits
      if let some pf ← res.get then
        s.restore
        return some pf
    s.restore
  return none

/-- Bind premises: match unbound ones against facts (or enumerate objects),
prove bound ones recursively. -/
partial def searchBack (ctx : Ctx) (depth : Nat)
    (cache : IO.Ref (Array Fact)) (done : IO.Ref Bool) (k : MetaM Unit) :
    List Expr → MetaM Unit
  | [] => k
  | l :: ls => do
    let facts := ctx.facts
    let objs := ctx.objs
    if ← done.get then return
    let l' ← instantiateMVars l
    if !l'.hasExprMVar then
      if (← find ((← cache.get) ++ facts) l').isSome then
        searchBack ctx depth cache done k ls
      else if let some p ← proveLit ctx (depth - 1) l' then
        cache.modify (·.push ⟨l', p⟩)
        searchBack ctx depth cache done k ls
    else if ← matchable l' then
      for f in candidates facts l' do
        if ← done.get then return
        let s ← saveState
        if ← withReducible (isDefEq l' f.type) then searchBack ctx depth cache done k ls
        s.restore
    else if let some v ← objectMVar? l' then
      for o in objectsOf objs (← inferType v) do
        if ← done.get then return
        let s ← saveState
        if ← isDefEq v o then searchBack ctx depth cache done k (l :: ls)
        s.restore

end

def contextObjects : MetaM Objects := do
  let mut objs : Objects := #[(``Point, #[]), (``Line, #[]), (``Circle, #[])]
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

/-- Close the facts under the forward rules. -/
def saturate (objs : Objects) (facts0 : Array Fact) : MetaM (Array Fact) := do
  let mut facts := facts0
  let mut seen : Std.HashSet Expr := facts.foldl (fun s f => s.insert f.type) {}
  for _ in [0:maxRounds] do
    let mut added := false
    for r in forward do
      unless (← getEnv).contains r do continue
      for f in ← fire facts objs r do
        unless seen.contains f.type do
          seen := seen.insert f.type
          facts := facts.push f
          added := true
    if !added || facts.size > maxFacts then break
  return facts

/-- Literal heads the rules can conclude. -/
def conclusionHeads : MetaM (Array (Name × Bool)) := do
  let mut out := #[]
  for r in forward ++ backward do
    unless (← getEnv).contains r do continue
    let (_, _, concl) ← forallMetaTelescope (← inferType (mkConst r))
    for l in ← literals concl do
      if let some h := head l then out := out.push h
  return out

/-- Worth trying: every goal literal is a fact, metric, or a rule conclusion. -/
def worthTrying (facts : Array Fact) (goal : Expr) : MetaM Bool := do
  let heads ← conclusionHeads
  for l in ← literals goal do
    if (← find facts l).isSome || (← isArith l) then continue
    match head l with
    | some h => unless heads.contains h do return false
    | none => return false
  return true

/-- Try to close `g` by saturation; leave the state unchanged on failure. -/
def close (g : MVarId) : TacticM Bool := do
  let s ← Tactic.saveState
  let budget := systemE.saturateBudget.get (← getOptions)
  -- leave the declaration's second half of heartbeats to the rest of the proof
  let core ← readThe Core.Context
  let used := (← IO.getNumHeartbeats) - core.initHeartbeats
  if core.maxHeartbeats > 0 && 2 * (used + budget * 1000) > core.maxHeartbeats then
    return false
  tryCatchRuntimeEx (withoutRecover <| withCurrHeartbeats <|
      withTheReader Core.Context ({ · with maxHeartbeats := budget * 1000 }) do
    let g ← try substVars g catch _ => pure g
    g.withContext do
      let goal ← instantiateMVars (← g.getType)
      let facts0 ← contextFacts
      unless ← worthTrying facts0 goal do
        s.restore
        return false
      let objs ← contextObjects
      let facts ← saturate objs facts0
      if let some pf ← prove (proveLit ⟨facts, objs, ← IO.mkRef {}⟩ maxDepth) goal then
        g.assign pf
        return true
      s.restore
      return false)
    fun _ => do
      s.restore
      return false

def getSaturateOption : MetaM Bool := return (← getOptions).getBool `systemE.saturate true

def getSmtOption : MetaM Bool := return (← getOptions).getBool `systemE.smt true

syntax "euclid_saturate" : tactic

elab "euclid_saturate" : tactic => do
  unless ← close (← getMainGoal) do throwError "euclid_saturate failed"
  replaceMainGoal []

end SystemE.Saturate
