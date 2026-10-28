import Lake
open Lake DSL

/-- kimp is type-sound for the K type checker
`k/imp-typing.k`. -/
package «ImpTypes» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KImp» from "../../generated/kimp"
require «KImpTypes» from "../../generated/imptypes"

@[default_target]
lean_lib ImpTypes
