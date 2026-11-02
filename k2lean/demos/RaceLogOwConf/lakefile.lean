import Lake
open Lake DSL

/-- The fixture `racelog` with an `owise` rule (`tests/racelog-owise.py`: a spawn of no work skipped,
two priority ranks): every schedule ends in one configuration up to the order of `<log>` and the
last writer `<last>` (`--equiv`), every slot and every rule's lemma generic. -/
package «RaceLogOwConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «RaceLogOw» from "../../generated/racelogow"

@[default_target]
lean_lib RaceLogOwConf
