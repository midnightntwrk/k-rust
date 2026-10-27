import Lake
open Lake DSL

/-- kimp and a variant whose `while` unrolls in one step less are stuttering bisimilar. -/
package «ImpUnroll» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require KPrelude from "../../lean/prelude"
require «KImp» from "../../generated/kimp"
require «KUnroll» from "../../generated/kunroll"

@[default_target]
lean_lib ImpUnroll
