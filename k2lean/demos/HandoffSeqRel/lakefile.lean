import Lake
open Lake DSL

/-- The fixture `handoffseq` (the coordination script run in its order) into the fixture `handoff`
(any ready task runs): a script that runs to completion in order ends with the bindings that every
run of `handoff` to a terminal configuration ends with. -/
package «HandoffSeqRel» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «Handoff» from "../../generated/handoff"
require «HandoffSeq» from "../../generated/handoffseq"
require «HandoffConf» from "../HandoffConf"

@[default_target]
lean_lib HandoffSeqRel
