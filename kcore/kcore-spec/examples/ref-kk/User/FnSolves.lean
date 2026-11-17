/-
  kore.k's functions at the interpretation `HookParams.none`: every function has at most one
  result (`KK.fnDet : FnDet c₀`, from `KK.coherent`).
-/
import User.Coherent

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KK

open KCore KCore.Det RefKk

/-- **Every function of kore.k has at most one result at `HookParams.none`.** -/
theorem fnDet : FnDet c₀ := fnDet_of_coherent coherent

end KK
