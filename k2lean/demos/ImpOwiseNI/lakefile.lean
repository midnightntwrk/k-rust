import Lake
open Lake DSL

/-- ImpNI with priority ranks: kimp's noninterference for the security checker `k/imp-sec.k`, over
kimpowni, kimp with `owise` rules (`tests/kimp-owise.py`) and what a store is (`k/imp-ni.k`). -/
package «ImpOwiseNI» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KImpOwNI» from "../../generated/kimpowni"
require «KImpSec» from "../../generated/impsec"

@[default_target]
lean_lib ImpOwiseNI
