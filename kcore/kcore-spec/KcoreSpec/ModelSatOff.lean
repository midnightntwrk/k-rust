/-
  KCore. The value model off some functions: `Faithful.Model.sat_off`.

  The value model at its own step, `stdI_T c (StepV c)`, is the model `consistent_of_coreEx` gives.
  That evaluation solves the equations (`FnSolves`) is read there by the functions' equations only,
  and by each function's equations of that function alone (`AtT.sat_fnEqsEx`, `FnSolvesAt`). So
  where `FnSolvesAt` is known of the functions outside a list `D` of labels, the value model
  satisfies every item of the theory but the equations of the functions of `D`: the signature, the
  constructors, the domains, the collections, the rules, the step's closure and the values at
  silent points read `FnDet` and no more of the functions.

  An item is left out by its pattern: one that is an equation of a function of `D` and also an
  item of another part of the theory is not concluded.
-/
import KcoreSpec.HypModelCoreEx

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- **The value model satisfies every item of the theory but the equations of the functions of
`D`**, for a semantics `coreOKEx` accepts whose functions have one result (`FnDet`), where
evaluation solves the equations of each function of the definition outside `D` (`FnSolvesAt`),
the clauses' predicates have truth values (`ClausePreDecided`, `ClausePostDecided`) and the open
generators meet their laws (`OpenLaws`). Nothing is asked of evaluation at a function of `D`
beyond `FnDet`. -/
theorem sat_off {D : List Sym} (h : c.coreOKEx = true) (hd : FnDet c)
    (hs : ∀ fn ∈ c.fns, fn.label ∉ D → FnSolvesAt c fn)
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c) :
    ∀ φ, φ ∈ (Γc c ∪ Γstep c) →
      (∀ fn ∈ c.fns, fn.label ∈ D → ∀ it ∈ kernelItems (fnEquationsK c fn), φ ≠ it.pat) →
      stdI_T c (StepV c) ⊧ᴵ φ := by
  intro φ hφ hoff
  have hm := hypModelCore_of_coreEx h hd
  rcases hφ with (hφ | hφ) | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact AtT.satSigGoal hm φ hφ
    · exact AtT.satConsGoal hm hl φ hφ
    · exact AtT.satDomainsGoal hm φ hφ
    · exact AtT.satCollsGoal hm φ hφ
    · rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
      · obtain ⟨fn, hfn, hit⟩ := List.mem_flatMap.mp hit
        refine AtT.sat_fnEqsEx hm hfn (fun hu => ?_) (hypModelCore_clsFactsCe hm) hp hq it hit
        by_cases hD : fn.label ∈ D
        · exact absurd rfl (hoff fn hu hD it hit)
        · exact hs fn hu hD
      · exact AtT.model_sat_definedness c x
    · exact satRulesGoal_held hm hm.ruleFactsHeld (StepV c) (fun r σ _ _ hb _ => ⟨r, σ, hb⟩)
        (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, ⟨r, σ, hb⟩⟩) φ hφ
    · exact AtT.satFallbackGoal hm φ hφ
  · obtain ⟨-, hlit, rfl⟩ := hφ
    exact boolClosed_modelClT hm hlit
  · exact satStepGoal_held hm hm.ruleFactsHeld (StepV c) (fun _ _ _ _ hT => hT) φ hφ

/-- `sat_off` at no function: where evaluation solves the equations (`FnSolves`), the value model
at its own step satisfies the theory. -/
theorem sat_off_nil (h : c.coreOKEx = true) (hd : FnDet c) (hs : FnSolves c)
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c) :
    stdI_T c (StepV c) ⊧ᴵP (Γc c ∪ Γstep c) := fun φ hφ =>
  sat_off (D := []) h hd (fun fn hfn _ => hs fn hfn) hp hq hl φ hφ
    (fun _ _ hD => absurd hD List.not_mem_nil)

end Model

end Faithful

end KCore
