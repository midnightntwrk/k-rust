import Lake
open Lake DSL

/-- kimp with `print` to K's stdout stream and the same with a `while` that unrolls in one step
less are stuttering bisimilar, with the stream rules' priority ranks before kimp's. -/
package «ImpPrintRefine» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KImpPrint» from "../../generated/kprint"
require «KImpPrintU» from "../../generated/kprintu"

@[default_target]
lean_lib ImpPrintRefine
