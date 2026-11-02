import Lake
open Lake DSL

/-- kimp's noninterference with output: kimp with `print ( E ) ;` appending to a plain `<output>`
cell (`tests/kimp-print.py`, plain), over kimpoutni (with what a store is, `k/imp-ni.k`), for the
checker `k/imp-sec.k` with `print` (`tests/imp-sec-print.py`). The store is observed by `lowEq G`
and the output by equality. -/
package «ImpOutNI» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KImpOutNI» from "../../generated/kimpoutni"
require «KImpSecP» from "../../generated/impsecp"

@[default_target]
lean_lib ImpOutNI
