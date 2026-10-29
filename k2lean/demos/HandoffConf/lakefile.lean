import Lake
open Lake DSL

/-- The fixture `handoff` (a coordination script's tasks run when their inputs are ready; a resume
runs a process's whole segment as one step): steps of two tasks join generically, given the joins
left open (`k2lean confluence --threads tasks`). -/
package «HandoffConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «Handoff» from "../../generated/handoff"

@[default_target]
lean_lib HandoffConf
