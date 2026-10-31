import Lake
open Lake DSL

/-- The two-layer prototype (`docs/direction.md` §8 step 4), the fixture `twolayer`: a coordination
script's tasks, each resume running a coroutine's segment in the resuming task. The races of two tasks
for one creation, resume or spend are refuted together by two runs of a program, and under the
script's well-formedness `wf` every slot is proved (`TwoConf.Legal`). -/
package «TwoConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «TwoLayer» from "../../generated/twolayer"

@[default_target]
lean_lib TwoConf
