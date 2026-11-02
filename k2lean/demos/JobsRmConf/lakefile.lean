import Lake
open Lake DSL

/-- The fixture `jobs` with each job removed from the map when it runs (`tests/jobs-remove.py`,
mode `remove`): every order of the jobs ends in one configuration up to the order of `<done>`
(`--equiv`), two removals at two bindings commuting; every slot and every rule's lemma generic. -/
package «JobsRmConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «JobsRm» from "../../generated/jobsrm"

@[default_target]
lean_lib JobsRmConf
