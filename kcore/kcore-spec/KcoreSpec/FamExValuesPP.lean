/-
  KCore. The instances of an application of a rule with a `pre` and a `post`: the pattern.

  `famEx c r σ` is `∃v̄. (v̄ = ⟦σ⟧ ∧ ∃ē. (rhs ∧ ⌈ens = true⌉ ∧ post))`, v̄ the variables other than
  the existential ones ē (`famEx_eqPPx`). That a value in it is a step by the rule
  (`famEx_value_heldCEx`) is FamValuesCE.lean's.
-/
import KcoreSpec.ModelChoicePP
import KcoreSpec.FamExPost
import KcoreSpec.HoldsCongr
import KcoreSpec.StepValuesPP
import KcoreSpec.ExFamValues

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK VarTable)
open HoldsShape (hasBinder)

/-- The pattern `famEx` reads, for a rule whose `post` need not be `\top`: the variables other than
the existential ones are fixed to their values under σ, the existential ones bound around the right
side, the `ensures` and `post`. -/
theorem famEx_eqPPx {c : Semantics} {r : Rule} (hlt : ∀ i ∈ r.exs, i < r.vars.length) (σ : Subst) :
    famEx c r σ = KoreAML.denB (KoreAML.existsAll (srtOf c topCellSort)
      (((List.range r.vars.length).filter fun i => !r.exs.contains i).map
        fun i => ((canonVars c r.vars).getD i default).kore)
      (.and (srtOf c topCellSort) (fixK c r σ ((List.range r.vars.length).filter fun i => !r.exs.contains i) ++
        [KoreAML.existsAll (srtOf c topCellSort) (Model.ruleExBinders c r) (Model.ruleRightBodyPP c r)]))) := by
  unfold famEx
  dsimp only
  rw [Model.ruleRight_eqPP hlt, filterMap_getElem?_of_lt _ _ (fun i hi => by
    rw [canonVars_length]; exact List.mem_range.mp (List.mem_filter.mp hi).1), List.map_map]
  rfl

end Faithful

open ML Faithful Faithful.Model

end KCore
