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
  defValue := 3000
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
  ``not_on_circle_of_lt]

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

/-- Unordered key of a segment. -/
def segKey (p : Expr × Expr) : Expr × Expr :=
  if Expr.lt p.2 p.1 then (p.2, p.1) else p

/-- Prove a metric literal by `linarith only`, over the metric facts connected
to it by shared segments, plus `ab = ba` where both orders occur. -/
def arith (facts : Array Fact) (e : Expr) : MetaM (Option Expr) := do
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

/-- Prove a goal literal: a fact, metric, or by a backward rule. -/
partial def proveLit (facts : Array Fact) (objs : Objects) (depth : Nat) (e : Expr) :
    MetaM (Option Expr) := do
  if let some p ← find facts e then return p
  if ← isArith e then return ← arith facts e
  if depth == 0 then return none
  for r in backward do
    unless (← getEnv).contains r do continue
    let s ← saveState
    let c := mkConst r
    let (args, _, concl) ← forallMetaTelescope (← inferType c)
    if ← withReducible (isDefEq concl e) then
      let (lits, vars) ← premises args true
      let res ← IO.mkRef (none : Option Expr)
      let done ← IO.mkRef false
      search facts objs done (do
        if let some pf ← apply c args (proveLit facts objs (depth - 1)) then
          res.set (some pf)
          done.set true) lits vars
      if let some pf ← res.get then
        s.restore
        return some pf
    s.restore
  return none

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
      if let some pf ← prove (proveLit facts objs 1) goal then
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
