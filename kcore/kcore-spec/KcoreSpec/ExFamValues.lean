/-
  KCore. The instances of an application, for a rule with existential variables: the pattern.

  `famEx c r σ` is `∃ō. (ō = σ(ō) ∧ ∃ē. (rhs ∧ ens))`, ō the variables other than the existential
  ones ē (`famEx_eqEx`).
-/
import KcoreSpec.ExChoice
import KcoreSpec.OpenSplit
import KcoreSpec.OpenCompete
import KcoreSpec.OpenClauseFn
import KcoreSpec.ClausePreCore
import KcoreSpec.RhsValues
import KcoreSpec.Totals

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)

section
variable {c : Semantics}

/-- The pattern `famEx` reads, for a rule whose `post` is `\top`: the variables other than the
existential ones bound and fixed to their values under σ, the right side `∃ē. (rhs ∧ ens)`. -/
theorem famEx_eqEx {r : Rule} (hpost : r.post = .top) (hlt : ∀ i ∈ r.exs, i < r.vars.length) (σ : Subst) :
    famEx c r σ = KoreAML.denB (KoreAML.existsAll (srtOf c topCellSort)
      (((List.range r.vars.length).filter fun i => !r.exs.contains i).map
        fun i => ((canonVars c r.vars).getD i default).kore)
      (.and (srtOf c topCellSort) (fixK c r σ ((List.range r.vars.length).filter fun i => !r.exs.contains i) ++
        [KoreAML.existsAll (srtOf c topCellSort) (Model.ruleExBinders c r) (Model.ruleRightBody c r)]))) := by
  unfold famEx
  dsimp only
  rw [Model.ruleRight_eqEx hpost hlt, filterMap_getElem?_of_lt _ _ (fun i hi => by
    rw [canonVars_length]; exact List.mem_range.mp (List.mem_filter.mp hi).1), List.map_map]
  rfl

end

end Faithful

open ML Faithful Faithful.Model

end KCore
