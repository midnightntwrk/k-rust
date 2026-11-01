import Lake
open Lake DSL

/-- The two-layer prototype under a weaker legality, `wfOut` (the fixture `twolayer`): `wf` without the
spends' claims. Under it the race of two resumes spending one output remains, and a program it admits
refutes it by two runs, while every other slot is proved. Its own project: the library
`twolayerout`, generated with `--invariant wfOut@T`, has the module names of `twolayer`. -/
package «TwoOutConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «TwoLayer» from "../../generated/twolayerout"

@[default_target]
lean_lib TwoOutConf
