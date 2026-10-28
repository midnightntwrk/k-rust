import Lake
open Lake DSL

/-- IMP++ (K's tutorial, `pl-tutorial/1_k/4_imp++/lesson_7/imp.k`) is type-sound for the K type
checker `k/impplus-typing.k`. -/
package «ImpPlusTypes» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KImpPlus» from "../../generated/impplus"
require «KImpPlusTypes» from "../../generated/impplustypes"

@[default_target]
lean_lib ImpPlusTypes
