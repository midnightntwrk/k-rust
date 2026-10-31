import Lake
open Lake DSL

/-- IMP++ (the library `impplus`): steps of two threads join generically up to the flush of K's
stdout stream, given the joins left open (`k2lean confluence --threads threads --obs output`). -/
package «ImpPlusConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KImpPlus» from "../../generated/impplus"

@[default_target]
lean_lib ImpPlusConf
