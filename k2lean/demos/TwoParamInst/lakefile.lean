import Lake
open Lake DSL

/-- The parameterized form's segments run by the coroutine language, the fixture `corout`: the hooks
of `twoparam` from corout's run to a segment's end, unique since corout is deterministic, and
`TwoParamConf.terminal_unique` at that instance. -/
package «TwoParamInst» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «TwoParam» from "../../generated/twoparam"
require «Corout» from "../../generated/corout"
require «TwoParamConf» from "../TwoParamConf"

@[default_target]
lean_lib TwoParamInst
