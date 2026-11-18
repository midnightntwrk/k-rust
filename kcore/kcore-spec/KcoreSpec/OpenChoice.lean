/-
  KCore. The choice among instances, for a definition whose rules' left sides need not bind every
  variable: the value model.

  A rule with `rulePlainOpen` has no existential variable, so a relation T that holds only steps of
  `Step` and every step of a rule without existential variables is `Step`. The value model (`stdI`)
  is a model of `Γc` with the step's closure (`stdI_modelOpen`), and its transition at values is
  `StepM`: `Step` with "no rule of a smaller priority applies" (`RuleApplies`) in place of
  `NotApplies`. The two agree:
  - a competitor that does not apply (`NotApplies`), its premise predicate `\top`, has no match
    under which its `requires` evaluates to `true`, where a term has at most one result
    (`FnDet`): `not_ruleApplies_ofChoice`;
  - a competitor with no such match, where its conditions have results at its matches (the first
    conjunct of `StepDecided`), does not apply: `notApplies_ofChoice`.
  So in the value model x has y's element as a successor exactly where `Step c x y`
  (`step_iff_stdIChoice`), and `has_model_choice_open` is `has_model_choice`'s conclusion.
-/
import KcoreSpec.OpenConsistent
import KcoreSpec.ModelFnsDecided

set_option autoImplicit false

namespace KCore

open ML Faithful Faithful.Model

/-- **A competitor that does not apply does not apply under any match**: for a rule whose premise
predicate is `\top`, where a term has at most one result under each substitution (`FnDet`),
`NotApplies` excludes `RuleApplies`. -/
theorem not_ruleApplies_ofChoice {c : Semantics} (hfd : FnDet c) {r : Rule} (hpre : r.pre = .top)
    {x : GroundTerm} (hna : NotApplies c r x) : ¬ RuleApplies c r x := by
  rintro ⟨σ, hσ, hm, hq, -⟩
  obtain ⟨_, _, ht, he, hv⟩ := (hna σ hσ hm).req_of_top hpre
  exact hv (EvalTerm.functional_of_fnDet hfd he (hq _ ht))

/-- **A rule that applies under no match does not apply**, where its conditions have results at
each match of its left side: at each match a `requires` evaluates to a result other than `true`, or
the premise predicate is false. -/
theorem notApplies_ofChoice {c : Semantics} {r : Rule} {x : GroundTerm}
    (hdec : ∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b)
    (hna : ¬ RuleApplies c r x) : NotApplies c r x := by
  intro σ hσ hm
  obtain ⟨hq, b, hb⟩ := hdec σ hσ hm
  cases b with
  | false => exact .pre hb
  | true =>
    by_cases hall : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true))
    · exact absurd ⟨σ, hσ, hm, hall, hb⟩ hna
    · obtain ⟨t, hnt⟩ := Classical.not_forall.mp hall
      obtain ⟨ht, hnt⟩ := Classical.not_imp.mp hnt
      obtain ⟨v, hv⟩ := hq t ht
      exact .intro ht hv fun hveq => hnt (hveq ▸ hv)

/-- **In the value model the steps at values are `Step`**, for a semantics that `coreOK` accepts
whose functions meet `FnHyp` and whose rules have `ruleSorted` and `rulePlainOpen`: x has y's
element as a successor exactly where `Step c x y`. -/
theorem step_iff_stdIChoice (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true) (x y : Config c) :
    Step c x y ↔ ¬ (stdI c ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  have hm := hypModel_of_fnHyp h hf
  have hfd := (fnModel_of_fnHyp h hf).1
  have hd := stepDecided_of_rules (hypSound_of_core h) hf.1 hrules x.val
  constructor
  · intro hs hsat
    obtain ⟨r, σ, hb⟩ := step_iff_by.mp hs
    have hM : StepM c x.val y.val := ⟨r, hb.mem, σ, hb.hσ, hb.hmatch, hb.hreq, hb.hpre, hb.heval, hb.hens, hb.hpost,
      fun r' hr' hlt => not_ruleApplies_ofChoice hfd (Semantics.rulePlainOpen_top (hrules r' hr').2).2.1
        (hb.hprio r' hr' hlt)⟩
    have h1 := hsat KoreAML.val0 (.val x.val)
    rw [interpret_impl] at h1
    have h2 := h1 ((den_val hm x.val x.property _ _).mpr rfl)
    rw [interpret_neg] at h2
    exact h2 ((sNext_iff _ _ _).mpr ⟨y.val, (den_val hm y.val y.property _ _).mpr rfl, x.property, y.property, hM⟩)
  · intro hn
    simp only [Interpretation.satisfies, Valuation.satifies] at hn
    obtain ⟨e, hn⟩ := Classical.not_forall.mp hn
    obtain ⟨m, hn⟩ := Classical.not_forall.mp hn
    rw [interpret_impl] at hn
    have h1 : (den c x.val).interpret (stdI c) e m := Classical.byContradiction fun hc => hn fun h => absurd h hc
    have h2 : (KoreAML.sNext (den c y.val)).interpret (stdI c) e m :=
      Classical.byContradiction fun hc => hn fun _ => interpret_neg.mpr hc
    rw [(den_val hm x.val x.property e m).mp h1] at h2
    obtain ⟨y', hy', hst⟩ := (sNext_iff _ e x.val).mp h2
    have hyy : Elem.val y' = .val y.val := (den_val hm y.val y.property e _).mp hy'
    cases hyy
    obtain ⟨-, -, r, hr, σ, hσ, hpv, hreq, hpre, hev, hens, hpost, hno⟩ := hst
    exact .rule r hr σ hσ hpv hreq hpre hev hens hpost fun r' hr' hlt =>
      notApplies_ofChoice (hd r' hr' fun r'' hr'' hlt' => hno r'' hr'' (Nat.lt_trans hlt' hlt)).1 (hno r' hr' hlt)

/-- **The choice among instances is free, for a definition whose rules' left sides need not bind
every variable**: `has_model_choice`'s conclusion, for a semantics that `coreOK` accepts whose
functions meet `FnHyp` and whose rules have `ruleSorted` and `rulePlainOpen`. Its rules have no
existential variable, so T is `Step`; the value model's transition at values is `Step`
(`step_iff_stdIChoice`). -/
theorem has_model_choice_open (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true)
    (T : Config c → Config c → Prop)
    (hsub : ∀ x y, T x y → Step c x y)
    (hall : ∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y)
    (_hsome : ∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y') :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  refine ⟨Elem, inferInstance, stdI c, stdI_modelOpen c h (hypModel_of_fnHyp h hf) hf.2.2.2.2.2 hrules
    (satFnsGoal_decided (hypModel_of_fnHyp h hf) (clausePreDecided_of_fnHyp h hf)), fun x y => ?_⟩
  rw [← step_iff_stdIChoice c h hf hrules x y]
  refine ⟨hsub x y, fun hs => ?_⟩
  obtain ⟨r, σ, hb⟩ := step_iff_by.mp hs
  exact hall x y r σ hb (Semantics.rulePlainOpen_top (hrules r hb.mem).2).1

end KCore
