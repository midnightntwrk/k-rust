import Lake
open Lake DSL

/-- The fixture `jobs` with a job dropped from the map once it has run (`tests/jobs-remove.py`,
mode `drop`): every order of the runs and drops ends in one configuration up to the order of `<done>`
(`--equiv`), a removal commuting with a removal or an update at another binding; every slot and
every rule's lemma generic. -/
package «JobsDropConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «JobsDrop» from "../../generated/jobsdrop"

@[default_target]
lean_lib JobsDropConf
