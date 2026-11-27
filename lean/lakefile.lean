import Lake
open Lake DSL

-- SystemE and Smt are copied from LeanEuclid (MIT) and lean-smt (Apache 2.0)
package elements where
  leanOptions := #[⟨`relaxedAutoImplicit, true⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.36.0"

lean_lib Smt

lean_lib SystemE

@[default_target]
lean_lib Elements
