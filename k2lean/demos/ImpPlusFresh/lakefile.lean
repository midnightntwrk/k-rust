import Lake
open Lake DSL

/-- A kind 2 invariant of IMP++ (K's tutorial): every location of `<store>` is below K's generated
counter and every thread's `<id>` at most it, so the next fresh value is not already a key
(`k2lean/docs/invariants.md`, §4). -/
package «ImpPlusFresh» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require KPrelude from "../../lean/prelude"
require «KImpPlus» from "../../generated/impplus"

@[default_target]
lean_lib ImpPlusFresh
