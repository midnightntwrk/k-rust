import Lake
open Lake DSL

/-- A kind 2 invariant of kimp that walks the `<k>` cell: no pending statement, and no value of
the store, assigns a given identifier (`k2lean/docs/invariants.md`, §11). -/
package «ImpWrites» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KImp» from "../../generated/kimp"

@[default_target]
lean_lib ImpWrites
