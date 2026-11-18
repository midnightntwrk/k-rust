/-
  KCore. The theory of a semantics whose clauses are asked CN-4's bodies (`Semantics.sortedOKCl`) is
  consistent where its functions have one result and its evaluation solves the equations
  (`consistent_ofCl`): `consistent_of`'s conclusion, with no hypothesis on the sorts of the
  variables a clause's patterns and conditions do not hold.

  The model is the value model at its own step (`stdI_V_model_core`): `Γ` by the goals over `HypModelCore`, which
  reads `sortedOKCl` (`hypModel_ofCl`); a clause's equation in particular by `satFnsGoal`
  (ModelFnsCl.lean), whose valuations give each variable of the clause an element of its sort,
  which in the value model is a value of it. The closure axiom `boolClosed` holds where Bool holds
  only its literals (`boolClosed_modelClT`). The rules' predicates are not read. Of `coreOK` the proof reads the conjuncts other than
  `sortedOK`, and `srReady`, `OvlOK` and `patHooksApart`, which `coreOK` gives through `sortedOK`.
-/
import KcoreSpec.Sound
import KcoreSpec.ModelHas
import KcoreSpec.HypWf
import KcoreSpec.BoolClosedCl

set_option autoImplicit false

namespace KCore

open ML Faithful Faithful.Model

/-- **The value model satisfies `Γc c` with the step's closure** for a semantics with
`HypModelCore` (whose clauses are asked `sortedOKCl`) and rules with `ruleSorted` and
`rulePlainOpen`: `stdI_modelOpen` with `boolClosed_modelCl` for the closure axiom. -/
theorem stdI_modelOpenCl (c : Semantics) (hm : HypModelCore c) (hne : c.FnsNoExs) (hp : ClausePreDecided c) (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true) :
    stdI c ⊧ᴵP (Γc c ∪ Γstep c) := by
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact satSigGoal hm φ hφ
    · exact satConsGoal hm hl φ hφ
    · exact satDomainsGoal hm φ hφ
    · exact satCollsGoal hm φ hφ
    · exact satFnsGoal_decided hm hne hp φ hφ
    · exact satRulesGoal_open hm hrules φ hφ
    · exact satFallbackGoal hm φ hφ
  · obtain ⟨-, hl, rfl⟩ := hφ
    exact boolClosed_modelCl hm hl
  · exact satStepGoal_open hm hrules φ hφ

/-- **The value model satisfies `Γc c` with the step's closure** for a semantics with
`HypModelCore` and rules with `ruleSorted` and `rulePlainEx`: `stdI_modelOpenCl` with the rules'
axioms and the step's closure at `T := StepM c` (`satRulesGoal_StepM`, `satStepGoal_StepM`). -/
theorem stdI_modelExCl (c : Semantics) (hm : HypModelCore c) (hne : c.FnsNoExs) (hp : ClausePreDecided c) (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true) :
    stdI c ⊧ᴵP (Γc c ∪ Γstep c) := by
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact satSigGoal hm φ hφ
    · exact satConsGoal hm hl φ hφ
    · exact satDomainsGoal hm φ hφ
    · exact satCollsGoal hm φ hφ
    · exact satFnsGoal_decided hm hne hp φ hφ
    · exact satRulesGoal_StepM hm hrules φ hφ
    · exact satFallbackGoal hm φ hφ
  · obtain ⟨-, hl, rfl⟩ := hφ
    exact boolClosed_modelCl hm hl
  · exact satStepGoal_StepM hm hrules φ hφ

/-- **The theory of a semantics whose clauses are asked CN-4's bodies is consistent**:
`consistent_of`'s conclusion for a semantics with `sortedOKCl` in place of `sortedOK`, `srReady`,
`OvlOK`, `faithCoreOK`, `patHooksApart` and `idsOK`, whose functions have at most one result
(`FnDet`), whose evaluation solves the equations (`FnSolves`), whose clauses' predicates have a
truth value wherever their patterns match (`ClausePreDecided`) and whose interpretation satisfies
the open generators' laws (`OpenLaws`): the value model at its own step. Nothing is asked
of the sorts of the variables a clause's patterns and conditions do not hold. -/
theorem consistent_ofCl (c : Semantics) (hok : c.sortedOKCl = true) (_htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top) (hsr : c.srReady = true) [hov : OvlOK c]
    (hfa : c.faithCoreOK = true) (hph : patHooksApart c = true) (hids : c.idsOK = true)
    (hd : FnDet c) (hs : FnSolves c) (hp : ClausePreDecided c) (hl : OpenLaws c) : Consistent c := by
  have hm := hypModel_ofCl hok hsr hov hfa hph hids hd hs
  have hne := Semantics.fnsNoExs_of_sortedOKCl hok
  refine ⟨Elem, inferInstance, stdI_T c (StepV c), fun φ hφ => ?_⟩
  rcases hφ with (hφ | hφ) | hφ
  · exact stdI_V_model_core hm hne hp hl φ (Or.inl hφ)
  · obtain ⟨-, hlit, rfl⟩ := hφ
    exact boolClosed_modelClT hm hlit
  · exact stdI_V_model_core hm hne hp hl φ (Or.inr hφ)

end KCore
