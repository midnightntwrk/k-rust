import Lake
open Lake DSL

/-- `vmpri` with a cache `<empty>` of whether the stack is empty, and the same whose underflow
rules read the cache instead of the stack (`tests/refine-mutant.py vm-empty`, `vm-empty-opt`):
stuttering bisimilar under the invariant that the cache is right (`emptyOk`). -/
package «VmEmptyRefine» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KVmEmpty» from "../../generated/vmempty"
require «KVmEmptyOpt» from "../../generated/vmemptyopt"

@[default_target]
lean_lib VmEmptyRefine
