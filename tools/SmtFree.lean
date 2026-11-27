-- List theorems of Elements that do not depend on SMT_VERIF.
-- Run after `make check`: cd lean && lake env lean ../tools/SmtFree.lean
import Elements
open Lean Elab Command

elab "#smt_free" : command => do
  let env ← getEnv
  let mut free := #[]
  let mut smt := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless (`Elements).isPrefixOf n do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    let axs ← liftCoreM (collectAxioms n)
    if axs.any (·.toString.endsWith "SMT_VERIF") || axs.contains ``sorryAx then
      smt := smt.push n
    else free := free.push n
  let s := fun (a : Array Name) => (a.map toString).qsort (· < ·)
  logInfo m!"SMT-free {free.size}: {s free}\nwith SMT {smt.size}: {s smt}"

#smt_free
