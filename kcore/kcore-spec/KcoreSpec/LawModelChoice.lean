/-
  KCore. The choice among instances, in a model that also satisfies the laws of functions.

  `law_model_choice` is `has_model_choice`'s statement with one more conjunct of its model: where
  the interpretation satisfies, at values, the laws the text writes for its functions (`FnLaws`),
  each of them sorted (`lawSorted`), the model whose transition at values is T also satisfies each
  law's sentence (`lawPattern`). The model is `has_model_choice`'s, the value model at the
  transition `liftT_ex c T`; a law's sentence does not read the transition, and the value model
  satisfies it at every transition (`Model.AtT.sat_lawPattern`).
-/
import KcoreSpec.LawConsistent

set_option autoImplicit false

namespace KCore

open ML Faithful Faithful.Model

/-- **The choice among instances is free, in a model of the laws.** For a semantics that
`coreOK` accepts whose functions meet `FnHyp` and whose interpretation satisfies at values the
sorted laws `ls`, and for a relation T that holds only steps of `Step`, every step of a rule
without existential variables, and for each application of a rule with existential variables at
least one of its instances: a model whose transition at values is T and which satisfies each law's
sentence. -/
theorem law_model_choice (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    {ls : List LawEq} (hl : FnLaws c ls) (hsort : ∀ l ∈ ls, lawSorted c l = true)
    (T : Config c → Config c → Prop)
    (hsub : ∀ x y, T x y → Step c x y)
    (hall : ∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y') :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)))) ∧
      ∀ l ∈ ls, I ⊧ᴵ lawPattern c l := by
  have hm := hypModel_of_fnHyp h hf
  have hfd := (fnModel_of_fnHyp h hf).1
  have hrules := Semantics.ruleFactsHeld_of_core h
  have hsr : ∀ r ∈ c.rules, c.ruleSorted r = true := fun r hr => (hrules r hr).1
  refine ⟨Elem, inferInstance, stdI_T c (liftT_ex c T),
    stdI_T_model_heldCEx c hm (clausePreDecided_of_fnHyp h hf) (clausePostDecided_of_fnHypCEx (Semantics.coreOK_iff_ex.mp h) hf) hf.2.2.2.2.2 hrules (liftT_ex c T) ?_ ?_ ?_,
    fun x y => (liftT_ex_iff T x y).symm.trans (step_iff_stdI_T c hm _ x y), fun l hmem => ?_⟩
  · intro x y hx hy hT
    obtain ⟨r, σ, hb⟩ := step_iff_by.mp (hsub ⟨x, hx⟩ ⟨y, hy⟩ (hT hx hy))
    exact ⟨r, σ, stepVBy_of_stepBy hfd hb⟩
  · intro r σ x y hb hex hx hy
    exact hall ⟨x, hx⟩ ⟨y, hy⟩ r σ (stepBy_of_stepVBy (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hfd hf.1 hsr hb) hex
  · intro r σ x y hb _
    by_cases hx : c.sortOf x = some topCellSort
    · have hy := rhs_sorted_open hm (hrules r hb.1).1 hb.2.1 hb.2.2.2.2.2.1
      obtain ⟨y', σ', hag, hb', hT⟩ :=
        hsome ⟨x, hx⟩ ⟨y, hy⟩ r σ (stepBy_of_stepVBy (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hfd hf.1 hsr hb)
      exact ⟨y'.val, σ', hag, stepVBy_of_stepBy hfd hb', fun _ _ => hT⟩
    · exact ⟨y, σ, fun _ _ => rfl, hb, fun hx' => absurd hx' hx⟩
  · obtain ⟨s, hls, hrs, hs, hb⟩ := lawSorted_parts (hsort l hmem)
    exact AtT.sat_lawPattern (T := liftT_ex c T) hm (hl l hmem) hls hrs hs hb

end KCore
