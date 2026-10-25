import Lake
open Lake DSL

/-- The fixture `race` (workers in a cell map): every schedule ends in one configuration. -/
package «RaceConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require KPrelude from "../../lean/prelude"
require «Race» from "../../generated/race"

@[default_target]
lean_lib RaceConf
