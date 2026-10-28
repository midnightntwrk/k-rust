import Lake
open Lake DSL

/-- A mutant of kimp diverges from kimp, proved. -/
package «ImpMut» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KImp» from "../../generated/kimp"
require «KMut» from "../../generated/kmut"

@[default_target]
lean_lib ImpMut
