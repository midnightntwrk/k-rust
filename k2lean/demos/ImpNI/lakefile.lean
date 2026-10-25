import Lake
open Lake DSL

/-- kimp's noninterference for the security checker `k/imp-sec.k`, as a scaffold. -/
package «ImpNI» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require KPrelude from "../../lean/prelude"
require «KImp» from "../../generated/kimp-ps"
require «KImpSec» from "../../generated/impsec"

@[default_target]
lean_lib ImpNI
