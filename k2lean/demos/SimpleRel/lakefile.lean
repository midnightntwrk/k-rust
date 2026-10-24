import Lake
open Lake DSL

/-- SIMPLE and a variant of it (constructors renamed, rules reordered) are bisimilar (`k2lean relate`). -/
package «SimpleRel» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require KPrelude from "../../lean/prelude"
require «KSimple» from "../../generated/simple"
require «KSimpleV» from "../../generated/simplev"

@[default_target]
lean_lib SimpleRel
