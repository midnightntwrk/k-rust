/-
  KCore. The outcomes of a match, for a definition whose rules' left sides need not bind every
  variable.

  `famOpen c r σ` reads σ only through `fixK c r σ (varOccs r.lhs)`, that is at the variables of
  the left side (`fixK_congrOpen`): two substitutions that agree there give one pattern
  (`famOpen_congrOpen`).
-/
import KcoreSpec.OpenSplit
import KcoreSpec.FaithfulFamilies
import KcoreSpec.StepOld

set_option autoImplicit false

namespace KCore

namespace Faithful

/-- `fixK` reads σ at the listed variables only. -/
theorem fixK_congrOpen (c : Semantics) (r : Rule) {σ σ' : Subst} {is : List Nat}
    (h : ∀ i ∈ is, σ'.lookup i = σ.lookup i) : fixK c r σ' is = fixK c r σ is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have ht := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
    unfold fixK at ht ⊢
    simp only [List.filterMap_cons, h i (List.mem_cons_self ..)] at ht ⊢
    rw [ht]

/-- **The outcomes of a match depend on the match at the left side's variables only**: two
substitutions that agree on the variables of r's left side give one pattern `famOpen`. -/
theorem famOpen_congrOpen (c : Semantics) (r : Rule) {σ σ' : Subst}
    (h : ∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) : famOpen c r σ' = famOpen c r σ := by
  unfold famOpen
  rw [fixK_congrOpen c r h]

end Faithful

open ML Faithful

end KCore
