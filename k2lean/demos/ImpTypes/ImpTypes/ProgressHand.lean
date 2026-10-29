import ImpTypes.ProgressDefs
import KImp.Adequacy
import ImpTypes.Store

/-! Hand-written proofs of the cases of `progress` listed in `open-progress-cases.txt`.

`k2lean gen` wrote this file once, because it did not exist, and never changes it. The one case here
is the head `X:Id`, whose rule `CALC.var` reads `<env>`: the store typing `envTy` gives the
identifier a value. -/

set_option linter.unusedVariables false

namespace KImp

open KPrelude

/-- `CALC.var` at a typed identifier: the typing of `<k>` gives `X` a type, and the store typing
`envTy` a value at `X`, so the rule's match `X |-> V` of `<env>` holds. -/
theorem Progress.hand.inj_Id : Progress.case.inj_Id.statement := by
  rintro x K env g ⟨G, hk, he⟩ -
  k2l_cases env with ⟨E⟩
  all_goals k2l_norm_idx
  simp only [ImpTypes.kOf, ImpTypes.envOf, ImpTypes.envCellTy, ImpTypes.kty_kseq, ImpTypes.item_none,
    ImpTypes.item0_inj_Id] at hk he
  cases ht : ImpTypes.typeOf G (.inj_Id x) with
  | none => simp [ht] at hk
  | some t =>
    obtain ⟨v, hl, -⟩ := he.2 x t ht
    exact App.«CALC.var» x K g E v _ (MapHook.concat_element_remove he.1 hl)

end KImp
