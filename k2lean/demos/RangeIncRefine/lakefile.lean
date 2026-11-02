import Lake
open Lake DSL

/-- `range` with `inc(L)`, and the same without `inc`'s check that the value is nonnegative
(`tests/refine-mutant.py range-inc`, `range-inc-opt`): stuttering bisimilar under the fixture's
invariant, every stored value is a nonnegative integer (`storeNat`). -/
package «RangeIncRefine» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KRangeInc» from "../../generated/rangeinc"
require «KRangeIncOpt» from "../../generated/rangeincopt"

@[default_target]
lean_lib RangeIncRefine
