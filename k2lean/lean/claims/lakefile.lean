import Lake
open Lake DSL

/-- Reachability claims over an arbitrary transition relation: K's
`weakAlwaysFinally` / `weakExistsFinally` as greatest fixpoints, their path readings, the
step-indexed approximation, guarded circularities, and tactics for generated K semantics. -/
package «KClaims» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require KPrelude from "../prelude"

@[default_target]
lean_lib KClaims
