/-
  KCore. The value model at its own step is a model of the theory where a clause may hold
  existential variables: `stdI_V_model_core` and `consistent_ofCl`'s conclusion with the functions'
  equations read by `AtT.satFnsGoalEx`, which takes every fact of a clause's existential variables
  and of its right side's predicate from a hypothesis on the clauses (`hcls`) and the truth values
  of the right sides' predicates from `ClausePostDecided`.

  The other items of the theory are read as `stdI_V_model_core` reads them, from `HypModelCore`.
-/
import KcoreSpec.ModelFnsExGoal
import KcoreSpec.OpenClauseConsistent

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- **The value model at its own step satisfies `Γ` with the step's closure where a clause may
hold existential variables**: `stdI_V_model_core` with the functions' equations by
`AtT.satFnsGoalEx`. -/
theorem stdI_V_model_coreEx (h : HypModelCore c)
    (hcls : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.clauseSortedOpen fn (c.fns.map Fn.sig) cl = true ∧
      c.clauseExOK cl = true ∧ (cl.exs = [] → cl.post = .top))
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c) :
    stdI_T c (StepV c) ⊧ᴵP (Γ c ∪ Γstep c) := by
  intro φ hφ
  rcases hφ with hφ | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact AtT.satSigGoal h φ hφ
    · exact AtT.satConsGoal h hl φ hφ
    · exact AtT.satDomainsGoal h φ hφ
    · exact AtT.satCollsGoal h φ hφ
    · exact AtT.satFnsGoalEx h hcls hp hq φ hφ
    · exact satRulesGoal_held h h.ruleFactsHeld (StepV c) (fun r σ _ _ hb _ => ⟨r, σ, hb⟩)
        (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, ⟨r, σ, hb⟩⟩) φ hφ
    · exact AtT.satFallbackGoal h φ hφ
  · exact satStepGoal_held h h.ruleFactsHeld (StepV c) (fun _ _ _ _ hT => hT) φ hφ

end Model

end Faithful

open ML Faithful Faithful.Model

/-- **The theory is consistent where a clause may hold existential variables**, under
`HypModelCore`, the clauses' facts (`hcls`), `ClausePreDecided`, `ClausePostDecided` and
`OpenLaws`: the value model at its own step (`stdI_V_model_coreEx`), with the closure axiom where
Bool holds only its literals. -/
theorem consistent_of_modelEx (c : Semantics) (hm : HypModelCore c)
    (hcls : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.clauseSortedOpen fn (c.fns.map Fn.sig) cl = true ∧
      c.clauseExOK cl = true ∧ (cl.exs = [] → cl.post = .top))
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c) : Consistent c := by
  refine ⟨Elem, inferInstance, stdI_T c (StepV c), fun φ hφ => ?_⟩
  rcases hφ with (hφ | hφ) | hφ
  · exact stdI_V_model_coreEx hm hcls hp hq hl φ (Or.inl hφ)
  · obtain ⟨-, hlit, rfl⟩ := hφ
    exact boolClosed_modelClT hm hlit
  · exact stdI_V_model_coreEx hm hcls hp hq hl φ (Or.inr hφ)

end KCore
