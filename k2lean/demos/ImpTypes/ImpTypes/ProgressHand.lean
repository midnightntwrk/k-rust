import ImpTypes.ProgressDefs
import KImp.Adequacy
import ImpTypes.Store

/-! Hand-written proofs of the cases of `progress` listed in `open-progress-cases.txt`.

`k2lean gen` wrote this file once, because it did not exist, and never changes it. The one case here
is the head `X:Id`, whose rule `CALC.var` reads `<env>`: the store typing `envTy` gives the
identifier a value, as in `soundness`'s own hand case, which it reuses. -/

set_option linter.unusedVariables false

namespace KImp

open KPrelude

/-- `CALC.var` at a typed identifier: the store typing gives it a value
(`ImpTypes.hand.progress.«CALC.var»`). -/
theorem Progress.hand.inj_Id : Progress.case.inj_Id.statement := by
  rintro x K env g ⟨G, hk, he⟩ -
  k2l_cases env with ⟨E⟩
  all_goals k2l_norm_idx
  exact ImpTypes.hand.progress.«CALC.var» G x K E g ⟨hk, he⟩

end KImp
