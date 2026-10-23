import Lake
open Lake DSL

/-- Hand-written prelude and hook library for k2lean-generated projects.
Everything a generated project needs that is not specific to one K definition lives here. -/
package «KPrelude» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib KPrelude
