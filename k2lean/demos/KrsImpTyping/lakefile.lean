import Lake
open Lake DSL

/-- The typing invariant of the KRS IMP port: every KRS IMP rule preserves the
declared cell type `env: Map<Id, Value>` (`Step.wt`), and the typed view loses no step. -/
package «KrsImpTyping» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KrsImp» from "../../generated/krsimp"

@[default_target]
lean_lib KrsImpTyping
