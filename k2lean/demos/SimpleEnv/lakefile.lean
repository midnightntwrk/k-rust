import Lake
open Lake DSL

/-- A kind 2 invariant of `KSimple`: a predicate written in Lean, proved to be kept by every rule
(skeleton written by `k2lean new-invariant`; every file is hand-written from here on). -/
package «SimpleEnv» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require KPrelude from "../../lean/prelude"
require «KSimple» from "../../generated/simple-ps"

@[default_target]
lean_lib SimpleEnv
