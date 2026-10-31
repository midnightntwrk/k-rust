import Lake
open Lake DSL

/-- The two-layer prototype's parameterized form (`docs/direction.md` §8 step 4), the fixture
`twoparam`: twolayer's coordination script with a segment's register and code left as parameters
(`TwoParam.Hooks`). Under the script's well-formedness `wf` every slot is proved, for every instance. -/
package «TwoParamConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «TwoParam» from "../../generated/twoparam"

@[default_target]
lean_lib TwoParamConf
