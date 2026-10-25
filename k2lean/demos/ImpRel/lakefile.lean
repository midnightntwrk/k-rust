import Lake
open Lake DSL

/-- The KRS IMP port and kimp are bisimilar (`k2lean relate`). -/
package «ImpRel» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require KPrelude from "../../lean/prelude"
require «KImp» from "../../generated/kimp-ps"
require «KrsImp» from "../../generated/krsimp-ps"

@[default_target]
lean_lib ImpRel
