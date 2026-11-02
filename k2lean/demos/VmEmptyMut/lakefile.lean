import Lake
open Lake DSL

/-- `vmpri` with a cache `<empty>` of whether the stack is empty, and the same whose underflow
rules read the cache and whose `pop` leaves it stale (`tests/refine-mutant.py vm-empty`,
`vm-empty-stale`): a program refutes the refinement under the invariant that the cache is right. -/
package «VmEmptyMut» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KVmEmpty» from "../../generated/vmempty"
require «KVmEmptyStale» from "../../generated/vmemptystale"

@[default_target]
lean_lib VmEmptyMut
