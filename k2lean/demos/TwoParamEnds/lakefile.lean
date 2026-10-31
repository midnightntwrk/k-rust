import Lake
open Lake DSL

/-- Every segment of the parameterized form ends: corout's measure (`gen --measure`), lowered by
every rule, so the hooks of `TwoParamInst` always have a value. -/
package «TwoParamEnds» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «TwoParam» from "../../generated/twoparam"
require «Corout» from "../../generated/corout"
require «TwoParamConf» from "../TwoParamConf"
require «TwoParamInst» from "../TwoParamInst"

@[default_target]
lean_lib TwoParamEnds
