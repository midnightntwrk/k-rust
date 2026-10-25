import Lake
open Lake DSL

/-- kimp is type-sound for the K type checker
`k/imp-typing.k`. -/
package «ImpTypes» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require KPrelude from "../../lean/prelude"
require «KImp» from "../../generated/kimp-ps"
require «KImpTypes» from "../../generated/imptypes-ps"

@[default_target]
lean_lib ImpTypes
