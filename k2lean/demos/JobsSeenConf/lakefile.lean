import Lake
open Lake DSL

/-- The fixture `jobs` with a job run when it is not yet in `<done>` (`tests/jobs-remove.py`, mode
`seen`): every order of the runs ends in one configuration up to the order of `<done>` (`--equiv`),
though the rule reads `<done>`; its lemma `equiv.sim.run` is generic (`in` is kept by a
permutation), and the slot of two runs at two jobs is the hand module's. -/
package «JobsSeenConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «JobsSeen» from "../../generated/jobsseen"

@[default_target]
lean_lib JobsSeenConf
