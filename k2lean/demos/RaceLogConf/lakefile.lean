import Lake
open Lake DSL

/-- The fixture `racelog` (workers adding to a shared accumulator, each step logged): by equality the
slot of two workers' steps is refuted at a peak of a program (`RaceLogConf`), and every schedule ends
in one configuration up to the order of `<log>` and the last writer `<last>` (`--equiv`,
`RaceLogConf.Equiv`). -/
package «RaceLogConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «RaceLog» from "../../generated/racelog"

@[default_target]
lean_lib RaceLogConf
