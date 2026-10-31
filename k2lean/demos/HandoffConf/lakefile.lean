import Lake
open Lake DSL

/-- The fixture `handoff` (a coordination script's tasks run when their inputs are ready; a resume
runs a process's whole segment as one step): steps of two tasks join generically under the script's
well-formedness `wf` (`k2lean confluence --threads tasks --assume-invariant Handoff.Invariant`). -/
package «HandoffConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «Handoff» from "../../generated/handoff"

@[default_target]
lean_lib HandoffConf
