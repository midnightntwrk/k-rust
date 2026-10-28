import Lake
open Lake DSL

/-- A stand-in for an external library (a hash, an encoding): it knows nothing of K or k2lean. -/
package «HexLib» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib HexLib
