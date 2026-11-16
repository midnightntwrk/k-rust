/-
  KCore. The prelude modules every KORE text holds before its main module: `BASIC-K`, `KSEQ`,
  `INJ` and `K` (prelude/kmodules.kore, as krust writes them). Reviewed layer; their axioms enter
  Γ_D (KCORE-AUDIT.md). The builtin modules a definition imports are in its main module
  (Builtins.lean).
-/
import KcoreSpec.Kore.Import
import KcoreSpec.Definition

set_option autoImplicit false

namespace KCore

set_option maxRecDepth 100000 in
kore_definition kPrelude from "prelude/kmodules.kore"
attribute [irreducible] kPrelude

/-- The prelude modules, emitted before the user module. Irreducible for the elaborator, which
otherwise unfolds the text when it compares two lists of modules; the kernel unfolds it. -/
@[irreducible] def preludeModules : List Kore.Module := kPrelude.modules

end KCore
