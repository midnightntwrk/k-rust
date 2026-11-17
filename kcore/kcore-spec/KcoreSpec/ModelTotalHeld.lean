/-
  KCore. The totality axioms in the value model, for rules with `rulePlainHeldH`.

  `has_model_total_core_held`, `has_model_total_held` and `sound_total_held` are
  `has_model_total_core`, `has_model_total_pp` and `sound_total_pp` with the per-rule fact
  `rulePlainHeldH c H` in place of `rulePlainPP`; the conjunct is carried, so H is any set of
  symbols.
-/
import KcoreSpec.ModelFunctional
import KcoreSpec.ModelChoiceHeld

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

variable {H : Sym → Bool}

/-- **`Γ` with the step's closure and the totality axioms has a model** under `HypModelCore`, for
rules with `ruleSorted` and `rulePlainHeldH`: the value model at a transition `T` that holds only steps
of `StepV` between configurations, every `StepVBy` step of a rule without existential variables,
and for each `StepVBy` step of a rule with existential variables one of its instances. -/
theorem has_model_total_core_held (h : HypModelCore c) (hl : OpenLaws c)
    (hv : ∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v))
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true)
    (T : GroundTerm → GroundTerm → Prop)
    (hsub : ∀ x y, c.sortOf x = some topCellSort → c.sortOf y = some topCellSort → T x y → StepV c x y)
    (hall : ∀ r σ x y, StepVBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ r σ x y, StepVBy c r σ x y → r.exs ≠ [] → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepVBy c r σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵP (Γ c ∪ Γstep c ∪ ΓTotal c) := by
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact AtT.satSigGoal h φ hφ
    · exact AtT.satConsGoal h hl φ hφ
    · exact AtT.satDomainsGoal h φ hφ
    · exact AtT.satCollsGoal h φ hφ
    · exact AtT.satFnsGoal h φ hφ
    · exact satRulesGoal_held h hrules T hall hsome φ hφ
    · exact AtT.satFallbackGoal h φ hφ
  · exact satStepGoal_held h hrules T hsub φ hφ
  · exact AtT.sat_total h hv φ hφ

end Model

/-- **The value model satisfies `Γ`, the step's closure and the totality axioms**, for a semantics
that `coreOK` accepts whose functions meet `FnHyp` and whose rules have `ruleSorted` and
`rulePlainHeldH`: under `FnHyp` the value model's step `StepV` is `StepM`, the transition of `stdI`. -/
theorem has_model_total_held {c : Semantics} {H : Sym → Bool} (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) :
    Model.stdI c ⊧ᴵP (Γ c ∪ Γstep c ∪ Model.ΓTotal c) := by
  have hiff : ∀ {x y : GroundTerm}, Model.StepV c x y ↔ Model.StepM c x y :=
    Model.stepV_iff_stepM h (fnModel_of_fnHyp h hf).1 hf.1 (fun r hr => (hrules r hr).1)
  exact Model.has_model_total_core_held (hypModel_of_fnHyp h hf) hf.2.2.2.2.2 hf.2.1 hrules (Model.StepM c)
    (fun _ _ _ _ hT => hiff.mpr hT) (fun r σ _ _ hb _ => hiff.mp ⟨r, σ, hb⟩)
    (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, hiff.mp ⟨r, σ, hb⟩⟩)

/-- **Soundness with the totality axioms, for rules with `pre` and `post`**: `sound_total`'s
statement from the per-rule facts `ruleSorted` and `rulePlainHeldH`. The model is the value model at
its own step, `stdI_T c (StepV c)`. -/
theorem sound_total_held {c : Semantics} {H : Sym → Bool} (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) :
    (∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      I ⊧ᴵP (Γc c ∪ Γstep c ∪ Model.ΓTotal c)) ∧
    ∀ (x y : Config c) (r : Rule) (σ : Subst), StepBy c r σ x y →
      ((Γc c ∪ Model.ΓTotal c) ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧
      ((Γc c ∪ Model.ΓTotal c) ⊧ (den c y.val ⇒ famEx c r σ)) := by
  have hm : Model.stdI_T c (Model.StepV c) ⊧ᴵP (Γc c ∪ Γstep c ∪ Model.ΓTotal c) := by
    intro φ hφ
    rcases hφ with hφ | hφ
    · exact stdI_T_model_held c h (hypModel_of_fnHyp h hf) hf.2.2.2.2.2 hrules (Model.StepV c)
        (fun _ _ _ _ hT => hT) (fun r σ _ _ hb _ => ⟨r, σ, hb⟩)
        (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, ⟨r, σ, hb⟩⟩) φ hφ
    · exact Model.AtT.sat_total (hypModel_of_fnHyp h hf) hf.2.1 φ hφ
  refine ⟨⟨_, inferInstance, _, hm⟩, fun x y r σ hs => ?_⟩
  obtain ⟨h1, h2⟩ := (sound_hyp c h hf).2 x y r σ hs
  refine ⟨?_, ?_⟩
  · intro M _ I hI
    exact h1 (fun φ hφ => hI φ (Or.inl hφ))
  · intro M _ I hI
    exact h2 (fun φ hφ => hI φ (Or.inl hφ))

end Faithful

end KCore
