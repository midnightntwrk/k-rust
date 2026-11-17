/-
  KCore. `Semantics.RightHeld` does not read the interpretation of the parameters: it reads the
  clauses and `sortOf`, which `withHooks` leaves alone where no parameter is an open generator
  (`Semantics.sortOf_withHooks`).
-/
import KcoreSpec.RightHeld
import KcoreSpec.Params

set_option autoImplicit false

namespace KCore

/-- `RightHeld` under every interpretation of the parameters, from `RightHeld` of the data, where
no parameter is an open generator (`raw`): the sort of an open generator's application is read
from the interpretation. Without `hr` the statement is false (test/WithHooksRaw.lean,
`rightHeld_withHooks_needs_hr`); `rightHeld_withHooks_of_valued` has no such hypothesis. -/
theorem Semantics.rightHeld_withHooks {c : Semantics} (h : c.RightHeld) (H : HookParams)
    (hr : ∀ k ∈ c.params, k.raw = false) : (c.withHooks H).RightHeld := by
  intro f hf cl hcl i s hs
  rw [Semantics.sortOf_withHooks _ _ hr]
  exact h f hf cl hcl i s hs

/-- `rightValued` of the data gives `RightHeld` under every interpretation of the parameters, with
no hypothesis on the parameters: the values `valued_value` exhibits apply no open generator. -/
theorem Semantics.rightHeld_withHooks_of_valued {c : Semantics} (h : c.rightValued = true) (H : HookParams) :
    (c.withHooks H).RightHeld :=
  Semantics.rightHeld_of_valued ((Semantics.rightValued_withHooks c H).trans h)

end KCore
