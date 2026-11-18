/-
  KCore. The theory of a definition whose rules may have existential variables is consistent: the
  value model (`stdI_model_ex`).
-/
import KcoreSpec.ExChoice
import KcoreSpec.SoundDefs

set_option autoImplicit false

namespace KCore

open Faithful.Model

/-- **The theory of a definition whose rules may have existential variables is consistent**: for a
semantics that `coreOK` accepts, whose functions have at most one result (`FnDet`), whose
evaluation solves the equations (`FnSolves`) and whose clauses' predicates have a truth value
wherever their patterns match (`ClausePreDecided`), and whose rules have `ruleSorted` and
`rulePlainEx`, `Γc c` with the step's closure has a model: the value model (`stdI_model_ex`). -/
theorem consistent_ex (c : Semantics) (h : c.coreOK = true) (hd : FnDet c) (hs : FnSolves c)
    (hp : ClausePreDecided c) (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true) : Consistent c :=
  ⟨Elem, inferInstance, stdI c, stdI_model_ex c h (hypModel_of_fn h hd hs) hp hl hrules⟩

end KCore
