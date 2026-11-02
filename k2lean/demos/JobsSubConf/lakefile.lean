import Lake
open Lake DSL

/-- The fixture `jobs` with each job removed when it runs and jobs submitted by two counters
(`tests/jobs-remove.py`, mode `submit`): every order of the runs and submissions ends in one
configuration up to the order of `<done>` (`--equiv`), a removal commuting with an insertion and
two insertions at two keys; every slot and every rule's lemma generic. -/
package «JobsSubConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «JobsSub» from "../../generated/jobssub"

@[default_target]
lean_lib JobsSubConf
