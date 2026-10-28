import Lake
open Lake DSL

/-- kimp's claims carried to its variant whose `while` unrolls in one step less, along the
stuttering bisimulation of `demos/ImpUnroll`, each with its own modality since `KUnroll.Step` is
deterministic (`k2lean claims --transfer ImpUnroll --transfer-kind stutter --transfer-det
KUnroll.Determinism`, which writes `ImpUnrollClaims/Transfers.lean`). -/
package «ImpUnrollClaims» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «ImpUnroll» from "../ImpUnroll"
require «KImpClaims» from "../../generated/kimp-claims"

@[default_target]
lean_lib ImpUnrollClaims
