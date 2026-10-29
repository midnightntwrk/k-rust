import Lake
open Lake DSL

/-- The freeze fixture (CT-3): `run.sh` records its frozen part and checks edits against it. -/
package «Frz» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../../lean"

@[default_target]
lean_lib Frz

lean_lib FrzTest where
  roots := #[`FrzTest.Axioms]
