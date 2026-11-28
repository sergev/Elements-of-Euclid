import SystemE

/-
A tactic for Book 6's areas.
-/

open Lean Elab Tactic Meta

/-- `linarith`, with the area of each triangle in the goal and the hypotheses the same in
any order of its vertices (`area_symm_1`, `area_symm_2`). -/
elab "area_linarith" : tactic => withMainContext do
  let tris ← IO.mkRef (#[] : Array (Expr × Expr × Expr))
  let visit (e : Expr) : MetaM Unit := do
    Meta.forEachExpr (← instantiateMVars e) fun s => do
      if s.isAppOfArity ``Triangle.ofPoints 3 then
        let t := (s.getAppArgs[0]!, s.getAppArgs[1]!, s.getAppArgs[2]!)
        unless (← tris.get).contains t do tris.modify (·.push t)
  visit (← getMainTarget)
  for d in ← getLCtx do
    if !d.isImplementationDetail then visit d.type
  let mut g ← getMainGoal
  for (a, b, c) in ← tris.get do
    for (x, y, z) in [(a, b, c), (b, c, a), (c, a, b), (a, c, b), (c, b, a), (b, a, c)] do
      for n in [``area_symm_1, ``area_symm_2] do
        let p ← mkAppM n #[x, y, z]
        let (_, g') ← (← g.assert `h (← inferType p) p).intro1P
        g := g'
  replaceMainGoal [g]
  evalTactic (← `(tactic| linarith))

