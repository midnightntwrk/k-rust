import Lake
open Lake DSL

/-- The fixture `peano` (an `owise` priority, recursive and mutual functions) is bisimilar to itself under two namespaces (`k2lean relate`). -/
package «PeanoRel» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «Peano» from "../../generated/peano"
require «PeanoB» from "../../generated/peanob"

@[default_target]
lean_lib PeanoRel
