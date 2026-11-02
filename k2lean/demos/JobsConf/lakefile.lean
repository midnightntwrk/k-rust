import Lake
open Lake DSL

/-- The fixture `jobs` (a map of jobs run in any order, each logged): by equality two runs of a program
end apart, refuting the open slot of two jobs' steps (`JobsConf`), and every order ends in one
configuration up to the order of `<done>` (`--equiv`, `JobsConf.Equiv`). -/
package «JobsConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «Jobs» from "../../generated/jobs"

@[default_target]
lean_lib JobsConf
