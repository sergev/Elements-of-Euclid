import Lake
open Lake DSL

-- Book 1 proofs from LeanEuclid (MIT), checked against its System E
package elements where
  leanOptions := #[⟨`relaxedAutoImplicit, true⟩]

require lib from git "https://github.com/loganrjmurphy/LeanEuclid" @ "33a72c0fa83914202532998a2e7b8771295c3cc7"

@[default_target]
lean_lib Elements
