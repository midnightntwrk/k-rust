import Lake
open Lake DSL

/-- kimp's claims carried to its variant whose `while` unrolls in one step less, along the
stuttering bisimulation of `demos/ImpUnroll`, as one-path claims (`k2lean claims --transfer
ImpUnroll --transfer-kind stutter`, which writes `ImpUnrollClaims/Transfers.lean`). -/
package «ImpUnrollClaims» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require KClaims from "../../lean/claims"
require «ImpUnroll» from "../ImpUnroll"
require «KImpClaims» from "../../generated/kimp-claims"

@[default_target]
lean_lib ImpUnrollClaims
