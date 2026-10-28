import Lake
open Lake DSL

/-- The KRS IMP port and kimp are bisimilar (`k2lean relate`). -/
package «ImpRel» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KImp» from "../../generated/kimp"
require «KrsImp» from "../../generated/krsimp"

@[default_target]
lean_lib ImpRel
