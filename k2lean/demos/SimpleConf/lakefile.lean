import Lake
open Lake DSL

/-- SIMPLE's threads: two steps of different threads join, given the joins left open (`k2lean
confluence --threads`). -/
package «SimpleConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KSimple» from "../../generated/simple"

@[default_target]
lean_lib SimpleConf
