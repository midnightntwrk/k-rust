import Lake
open Lake DSL

/-- `vmpri` with a cache `<empty>` of whether the stack is empty, and the same whose underflow
rules read the cache instead of the stack (`tests/refine-mutant.py vm-empty`, `vm-empty-opt`),
related with no legality: a configuration whose cache is wrong refutes the parts that need one
(`VmEmptyRefine` states it). -/
package «VmEmptyOpen» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KVmEmpty» from "../../generated/vmempty"
require «KVmEmptyOpt» from "../../generated/vmemptyopt"

@[default_target]
lean_lib VmEmptyOpen
