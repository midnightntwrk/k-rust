import Lake
open Lake DSL

/-- The fixture `jobs` with an `owise` rule (`tests/jobs-owise.py`: a job that is not positive run
last, untotalled, two priority ranks): every order of the jobs ends in one configuration up to the
order of `<done>` (`--equiv`), every slot and every rule's lemma generic. -/
package «JobsOwConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «JobsOw» from "../../generated/jobsow"

@[default_target]
lean_lib JobsOwConf
