import Lake
open Lake DSL

/-- A rule whose closers reach `k2l_preserve`'s per-rule heartbeat budget is left open, and the
other rules are still proved (`k2lean/docs/invariants.md`, §5.1; the light library `range`); a
closer step that reaches the recursion-depth limit fails like any other step. -/
package «InvBudget» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KRange» from "../../generated/range"

@[default_target]
lean_lib InvBudget
