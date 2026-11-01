import Lake
open Lake DSL

/-- `vmpop` (`pop` in two steps) and `vmpop1` (`pop` in one) are stuttering bisimilar, with the
priority ranks of `vmpri`. -/
package «VmPopRefine» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KVmPop» from "../../generated/vmpop"
require «KVmPop1» from "../../generated/vmpop1"

@[default_target]
lean_lib VmPopRefine
