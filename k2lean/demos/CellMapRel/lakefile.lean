import Lake
open Lake DSL

/-- The fixture `cellmap` (a free-key rule over the typed cell map of `<worker>`s) is bisimilar to itself under two namespaces (`k2lean relate`). -/
package «CellMapRel» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «CellMap» from "../../generated/cellmap"
require «CellMapB» from "../../generated/cellmapb"

@[default_target]
lean_lib CellMapRel
