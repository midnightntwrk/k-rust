import Lake
open Lake DSL

/-- `vmpop` (`pop` in two steps) and `vmpop1` (in one) stuttering bisimilar under `vmpop`'s
invariant (`kOk`): `VmPopRefine`'s split with the legality threaded through its parts. -/
package «VmPopLegal» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KVmPopInv» from "../../generated/vmpopinv"
require «KVmPop1» from "../../generated/vmpop1"

@[default_target]
lean_lib VmPopLegal
