import Lake
open Lake DSL

/-- The transaction statement of the combined form: a script with one run to no task left ends in
that run's configuration in every order, a segment's small steps interleaved with the other tasks
(the work measure, `gen --measure`, with TwoConf's legal `terminal_unique`). -/
package «TwoLayerTx» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «TwoLayer» from "../../generated/twolayer"
require «TwoConf» from "../TwoConf"

@[default_target]
lean_lib TwoLayerTx
