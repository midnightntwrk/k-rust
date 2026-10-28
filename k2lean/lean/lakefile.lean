import Lake
open Lake DSL

/-- The k2lean package: the hand-written prelude and hook library that every generated library
imports (`KPrelude`), and the reachability claims over a transition relation (`KClaims`). A
generated library, and a project that uses one, requires this package (PKG-1). -/
package «k2lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- Everything a generated project needs that is not specific to one K definition. -/
@[default_target]
lean_lib KPrelude where
  srcDir := "prelude"

/-- K's `weakAlwaysFinally` / `weakExistsFinally` as greatest fixpoints, their path readings, the
step-indexed approximation, guarded circularities, and tactics for generated K semantics. -/
@[default_target]
lean_lib KClaims where
  srcDir := "claims"

/-- Checks of the library's interface for importers (`KClaimsTest.Keywords`). -/
lean_lib KClaimsTest where
  srcDir := "claims"
  roots := #[`KClaimsTest.Keywords]
