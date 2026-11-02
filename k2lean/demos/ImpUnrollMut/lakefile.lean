import Lake
open Lake DSL

/-- kimp and the variant whose `while` unrolls in one step less, with `<=` read as `<` there
(`tests/refine-mutant.py`): the parts of `<=` are open, and a loop on which the two disagree
refutes them. -/
package «ImpUnrollMut» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KImp» from "../../generated/kimp"
require «KUnrollLe» from "../../generated/kunrollle"

@[default_target]
lean_lib ImpUnrollMut
