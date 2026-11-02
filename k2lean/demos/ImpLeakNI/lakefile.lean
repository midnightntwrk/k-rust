import Lake
open Lake DSL

/-- kimp's noninterference refuted by two runs, under a checker that misses a flow
(`tests/imp-sec-leaky.py`), over kimpni: kimp with what a store is (`k/imp-ni.k`). -/
package «ImpLeakNI» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KImpNI» from "../../generated/kimpni"
require «KImpSecLeak» from "../../generated/impsecleak"

@[default_target]
lean_lib ImpLeakNI
