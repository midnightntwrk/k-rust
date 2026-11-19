/-
  KCore. A binder in a clause's predicate makes the definition read a confined sort
  (`readsConfined_of_clausePre`): what `preReadAll_of_core` (PreReadBound.lean) reads to give the
  binders' facts in a model of `Γc`.
-/
import KcoreSpec.ClausePreTie
import KcoreSpec.HoldsFactsCore

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

open ML Faithful

namespace HoldsShape

section Core
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- A clause of the definition whose predicate has a binder makes the definition read a confined
sort. -/
theorem readsConfined_of_clausePre {fn : Fn} (hfn : fn ∈ c.fns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hb : hasBinder cl.pre = true) : c.readsConfined = true := by
  simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨fn, hfn, cl, hcl, by simp [hb]⟩

end Core

end HoldsShape

end KCore
