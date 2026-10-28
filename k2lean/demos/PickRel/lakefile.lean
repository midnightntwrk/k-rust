import Lake
open Lake DSL

/-- The fixture `pick` (functions with free-key map patterns, one with two free keys, and a free-key rule) is bisimilar to itself under two namespaces (`k2lean relate`). -/
package «PickRel» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «Pick» from "../../generated/pick"
require «PickB» from "../../generated/pickb"

@[default_target]
lean_lib PickRel
