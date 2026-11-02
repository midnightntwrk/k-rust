import Lake
open Lake DSL

/-- `vmpop` and `vmpop1` whose `pop` on an empty stack does nothing (`tests/refine-mutant.py`):
the parts of that rule are open, and a program that pops too often refutes them. -/
package «VmPopMut» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KVmPop» from "../../generated/vmpop"
require «KVmPop1Skip» from "../../generated/vmpop1skip"

@[default_target]
lean_lib VmPopMut
