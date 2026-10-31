import Lake
open Lake DSL

/-- kimp's noninterference for the security checker `k/imp-sec.k`, over kimpni: kimp with what a
store is (`k/imp-ni.k`), which the statement reads. -/
package «ImpNI» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KImpNI» from "../../generated/kimpni"
require «KImpSec» from "../../generated/impsec"

@[default_target]
lean_lib ImpNI
