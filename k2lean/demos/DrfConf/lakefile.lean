import Lake
open Lake DSL

/-- The fixture `drf` (workers writing one cell): the slot of two writes is refuted by two runs of a
program that end with different `<acc>`. -/
package «DrfConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «Drf» from "../../generated/drf"

@[default_target]
lean_lib DrfConf
