import Lake
open Lake DSL

/-- A K claim proved once on kimp holds for the KRS IMP port, through `relate`'s bisimulation. -/
package «ImpRelClaims» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «ImpRel» from "../ImpRel"
require «KImpClaims» from "../../generated/kimp-claims"

@[default_target]
lean_lib ImpRelClaims
