import Lake
open Lake DSL

/-- The fixture `handoff` without its script's well-formedness: two tasks may create one process or
take one segment of it, and those races are refuted by programs that have them, run at an instance
of the definition's parameters (`HandoffRaceConf.sum`, a running sum). Every other slot is proved
for every instance. -/
package «HandoffRaceConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «Handoff» from "../../generated/handoff"

@[default_target]
lean_lib HandoffRaceConf
