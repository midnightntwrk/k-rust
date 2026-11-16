/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Andrei Burdușa, Horațiu Cheval, Bogdan Macovei
-/
import MatchingLogic.Semantics

set_option autoImplicit false

namespace ML


  variable {𝕊 : Type} {M : Type}
  variable {I : Interpretation 𝕊 M} {e : Valuation M}
  variable {Γ : Premises 𝕊} {φ ψ : Pattern 𝕊}


  -- Similar to Proposition 3.7 (vii)
  theorem v_sat_conj:
    Valuation.satifies I e (φ ⋀ ψ) ↔
      (Valuation.satifies I e φ ∧ Valuation.satifies I e ψ)
  := by
    simp only [Valuation.satifies, interpret_conj]
    constructor
    . intro
      constructor <;> (intro; simp only [*])
    . intro ⟨_, _⟩ _
      simp [*]

  -- Similar to Proposition 3.7 (xi)
  theorem v_sat_equiv:
    Valuation.satifies I e (φ ⇔ ψ) ↔
      ( (Valuation.satifies I e (φ ⇒ ψ)) ∧
        (Valuation.satifies I e (ψ ⇒ φ ))
      )
  := by
    simp only [Pattern.equivalence]
    apply v_sat_conj

  theorem weakening_disj_sound : Γ ⊧ φ ⇒ φ ⋁ ψ := by
    intros _ _ _ _ _ _ _
    simp [*]

  theorem weakening_conj_sound : Γ ⊧ φ ⋀ ψ ⇒ φ := by
    intros _ _ _ _ _ _ h
    rw [interpret_conj] at h
    cases h <;> assumption

  theorem contraction_disj_sound : Γ ⊧ φ ⋁ φ ⇒ φ := by
    intros _ _ _ _ _ _ h
    rw [interpret_disj] at h
    cases h <;> assumption

  theorem contraction_conj_sound : Γ ⊧ φ ⇒ φ ⋀ φ := by
    intros _ _ _ _ _ _ h
    rw [interpret_conj] at *
    simp at *
    assumption

  theorem permutation_disj_sound : Γ ⊧ φ ⋁ ψ ⇒ ψ ⋁ φ := by
    intros _ _ _ _ _ _ h
    rw [interpret_disj]
    rwa [interpret_disj, Or.comm] at h

  theorem permutation_conj_sound : Γ ⊧ φ ⋀ ψ ⇒ ψ ⋀ φ := by
    intros _ _ _ _ _ _ h
    rw [interpret_conj] at h
    rw [And.comm] at h
    rw [interpret_conj] at *
    assumption

  theorem exFalso_sound : Γ ⊧ ⊥ ⇒ φ := by
    intros _ _ _ _ _ _ h
    rw [interpret_bottom] at h
    exact False.elim h

  theorem excluddedMiddle_sound : Γ ⊧ φ ⋁ ∼φ := by
    intros _ _ _ _ _ _ h
    rw [interpret_neg] at h
    assumption

  theorem modus_ponens_sound : Γ ⊧ φ → Γ ⊧ φ ⇒ ψ → Γ ⊧ ψ := by
    intros h₁ h₂ M _ I hΓ e m
    specialize h₁ hΓ e m
    specialize h₂ hΓ e m
    rw [interpret_impl] at h₂
    exact h₂ h₁

  theorem syllogism_sound { χ : Pattern 𝕊 } : Γ ⊧ φ ⇒ ψ → Γ ⊧ ψ ⇒ χ → Γ ⊧ φ ⇒ χ := by
    intros h₁ h₂ M _ I hΓ e m
    specialize h₁ hΓ e m
    specialize h₂ hΓ e m
    rw [interpret_impl] at h₁
    rw [interpret_impl] at h₂
    rw [interpret_impl] at *
    exact λ x => h₂ $ h₁ x

  theorem importation_sound { χ : Pattern 𝕊 } : Γ ⊧ φ ⇒ ψ ⇒ χ → Γ ⊧ (φ ⋀ ψ) ⇒ χ := by
    intros h₀ _ _ _ I eval h
    rw [interpret_impl]
    rw [interpret_conj]
    exact λ x => And.elim (h₀ I eval h) x

  theorem exportation_sound { χ : Pattern 𝕊 } : Γ ⊧ (φ ⋀ ψ) ⇒ χ → Γ ⊧ φ ⇒ ψ ⇒ χ := by
    intros h₀ _ _ I hΓ eval h
    specialize h₀ hΓ eval h
    rw [interpret_impl, interpret_conj] at h₀
    rw [interpret_impl, interpret_impl] at *
    intros hφ hψ
    exact h₀ $ And.intro hφ hψ

  theorem expansion_sound { χ : Pattern 𝕊 } : Γ ⊧ φ ⇒ ψ → Γ ⊧ χ ⋁ φ ⇒ χ ⋁ ψ := by
    intros h₀ _ _ I hΓ eval h
    specialize h₀ hΓ eval h
    rw [interpret_impl] at h₀
    rw [interpret_impl, interpret_disj, interpret_disj] at *
    intro hφorψ
    apply Or.elim hφorψ
    . exact Or.inl
    . intro hφ
      exact Or.inr $ h₀ hφ

  open Classical

  syntax "simp_fv_decide_or" : tactic
  macro_rules
  | `(tactic| simp_fv_decide_or) =>
     `( tactic|
          simp only
            [ *
            , Bool.decide_iff, Pattern.isFreeEvar, Pattern.isFreeSvar
            , Or.inl, Or.inr
            ]
      )

  -- Similar to Proposition 3.8
  set_option Pattern.pp_interpret_hiding false in
  theorem only_free_var_relevant : ∀ (fe₁ fe₂ : EVar → M) (fs₁ fs₂ : SVar → Set M),
    (∀ x, φ.isFreeEvar x → fe₁ x = fe₂ x) →
    (∀ X, φ.isFreeSvar X → fs₁ X = fs₂ X) →
    ∀ m,
      φ.interpret I ⟨ fe₁, fs₁ ⟩ m ↔
      φ.interpret I ⟨ fe₂, fs₂ ⟩ m
  := by
    induction φ with
    | evar x =>
      intro fe₁ fe₂ fs₁ fs₂ H₁ _ m
      simp only [Pattern.interpret]
      rw [H₁ x (by simp)]
    | svar X =>
      intro fe₁ fe₂ fs₁ fs₂ _ H₂ m
      simp only [Pattern.interpret]
      rw [H₂ X (by simp)]
    | bottom => intros; exact Iff.rfl
    | symbol => intros; exact Iff.rfl
    | application ψ χ ih₁ ih₂ =>
      intro fe₁ fe₂ fs₁ fs₂ H₁ H₂ m
      have h₁ := ih₁ fe₁ fe₂ fs₁ fs₂
        (fun x h => H₁ x (by simp [h])) (fun X h => H₂ X (by simp [h]))
      have h₂ := ih₂ fe₁ fe₂ fs₁ fs₂
        (fun x h => H₁ x (by simp [h])) (fun X h => H₂ X (by simp [h]))
      simp only [Pattern.interpret, h₁, h₂]
    | implication ψ χ ih₁ ih₂ =>
      intro fe₁ fe₂ fs₁ fs₂ H₁ H₂ m
      have h₁ := ih₁ fe₁ fe₂ fs₁ fs₂
        (fun x h => H₁ x (by simp [h])) (fun X h => H₂ X (by simp [h]))
      have h₂ := ih₂ fe₁ fe₂ fs₁ fs₂
        (fun x h => H₁ x (by simp [h])) (fun X h => H₂ X (by simp [h]))
      simp only [Pattern.interpret, h₁, h₂]
    | existential a ψ ih =>
      intro fe₁ fe₂ fs₁ fs₂ H₁ H₂ m
      simp only [Pattern.interpret]
      apply exists_congr
      intro b
      apply ih
      · intro x h
        simp only [Function.update_apply]
        by_cases hxa : x = a
        · rw [if_pos hxa, if_pos hxa]
        · rw [if_neg hxa, if_neg hxa]
          exact H₁ x (by simp [hxa, h])
      · intro X h
        exact H₂ X (by simpa using h)
    | mu X ψ ih =>
      intro fe₁ fe₂ fs₁ fs₂ H₁ H₂ m
      simp only [Pattern.interpret]
      apply forall_congr'
      intro B
      have h := ih fe₁ fe₂ (Function.update fs₁ X B) (Function.update fs₂ X B)
        (fun x h => H₁ x (by simpa using h))
        (fun Y h => by
          simp only [Function.update_apply]
          by_cases hYX : Y = X
          · rw [if_pos hYX, if_pos hYX]
          · rw [if_neg hYX, if_neg hYX]
            exact H₂ Y (by simp [hYX, h]))
      simp only [h]

  set_option Pattern.pp_interpret_hiding false in
  @[simp]
  -- Similar to Proposition 3.70, for δ := y
  theorem subf_xy_eq_eval_xey {x y : EVar}  : ∀ (m : M) (e : Valuation M),
    Pattern.substitutableForEvarIn x y φ →
    Pattern.interpret I e (Pattern.substEvar φ x y) m
      =
      φ.interpret I ⟨ Function.update e.evalEvar x (e.evalEvar y), e.evalSvar ⟩ m
  := by
    intro m e hs
    induction φ generalizing m e with
    | evar z =>
      by_cases h : x = z
      · subst h
        simp [Pattern.interpret, Function.update_apply]
      · simp [Pattern.interpret, Function.update_apply, h, Ne.symm h]
    | svar => rfl
    | bottom => rfl
    | symbol => rfl
    | application ψ χ ih₁ ih₂ =>
      simp only [Pattern.substitutableForEvarIn] at hs
      simp only [Pattern.substEvar, Pattern.interpret, ih₁ _ _ hs.1, ih₂ _ _ hs.2]
    | implication ψ χ ih₁ ih₂ =>
      simp only [Pattern.substitutableForEvarIn] at hs
      simp only [Pattern.substEvar, Pattern.interpret, ih₁ _ _ hs.1, ih₂ _ _ hs.2]
    | existential z ψ ih =>
      by_cases hxz : x = z
      · subst hxz
        simp [Pattern.interpret, Function.update_idem]
      · by_cases hfv : ψ.isFreeEvar x
        · have hs' : ¬(Pattern.evar y : Pattern 𝕊).isFreeEvar z ∧ Pattern.substitutableForEvarIn x y ψ := by
            simpa [Pattern.substitutableForEvarIn, hxz, hfv] using hs
          have hyz : y ≠ z := by
            intro h; apply hs'.1; simp [h]
          simp only [Pattern.substEvar, if_neg hxz, Pattern.interpret, ih _ _ hs'.2,
            Function.update_noteq hyz, Function.update_comm (Ne.symm hxz)]
        · exact case_not_fv (∃∃ z ψ) (by simp [hxz, hfv]) m e hs
    | mu X ψ ih =>
      simp only [Pattern.substitutableForEvarIn] at hs
      simp only [Pattern.substEvar, Pattern.interpret, ih _ _ hs]
  where
    case_not_fv {x y : EVar} φ (Hnot_fv : ¬Pattern.isFreeEvar φ x = true) m e :
      Pattern.substitutableForEvarIn x y φ →
      Pattern.interpret I e (Pattern.substEvar φ x y) m
        =
        φ.interpret I ⟨Function.update e.evalEvar x (e.evalEvar y), e.evalSvar⟩ m
    := by
      intro _
      rw [Pattern.subst_not_free_evar _ _ _ Hnot_fv]
      apply propext
      apply only_free_var_relevant
      · intro x' h
        rw [Function.update_noteq]
        intro hx'; subst hx'; exact Hnot_fv h
      · intros; rfl

  -- #exit

  set_option Pattern.pp_interpret_hiding false in
  theorem existQuan_sound {x y : EVar} :
    Pattern.substitutableForEvarIn x y φ → Γ ⊧ φ[x ⇐ᵉ Pattern.evar y] ⇒ ∃∃ x φ
  := by
      intros h₁ M _ I _ eval m hₘ
      simp only [Pattern.interpret]
      exists eval.evalEvar y
      -- Corollary 3.71
      rw [subf_xy_eq_eval_xey _ _ h₁] at hₘ
      apply hₘ

  theorem propagationBottomLeft_sound {c : Pattern 𝕊} : Γ ⊧ c ⬝ ⊥ ⇒ ⊥ := by
    intros _ _ _ _ _ _ h
    match h with
    | ⟨_, _, _, _, _⟩ =>
    assumption

  theorem propagationBottomRight_sound {c : Pattern 𝕊} : Γ ⊧ ⊥ ⬝ c ⇒ ⊥ := by
    intros _ _ _ _ _ _ h
    match h with
    | ⟨_, _, _, _, _⟩ =>
    assumption

  set_option Pattern.pp_interpret_hiding false in
  theorem framing_right_sound {χ} : Γ ⊧ φ ⇒ ψ → Γ ⊧ χ ⬝ φ ⇒ χ ⬝ ψ := by
    intros H
    intros M _ I hΓ e m hφ
    dsimp at hφ ⊢
    match hφ with
    | ⟨a, b, ha, hb, happ⟩ =>
    exists a; exists b
    apply And.intro
    . exact ha
    . dsimp at H
      specialize H hΓ e b
      rw [interpret_impl] at H
      exact ⟨H hb, happ⟩

  set_option Pattern.pp_interpret_hiding false in
  theorem framing_left_sound {χ} : Γ ⊧ φ ⇒ ψ → Γ ⊧ φ ⬝ χ ⇒ ψ ⬝ χ := by
    intros h
    intros M _ I hΓ e m hφ
    dsimp at hφ ⊢
    match hφ with
    | ⟨a, b, ha, hb, happ⟩ =>
    exists a; exists b
    apply And.intro
    . specialize h hΓ e a
      dsimp at h
      exact h ha
    . apply And.intro <;> assumption

  theorem implies_false_implies_is_disj { p q : Prop } : ((p → False) → q) ↔ p ∨ q := by
    apply Iff.intro <;> intro h
    . exact (Classical.em p).elim .inl (fun hnp => .inr (h hnp))
    . intro hnp
      exact h.elim (fun hp => absurd hp hnp) id

  set_option Pattern.pp_interpret_hiding false in
  theorem propagationDisjLeft_sound {c : Pattern 𝕊} :
    Γ ⊧ c ⬝ (φ ⋁ ψ) ⇒ (c ⬝ φ) ⋁ (c ⬝ ψ)
  := by
      intros _ _ _ _ _ _ h
      dsimp at *
      simp only [implies_false_implies_is_disj] at *
      match h with
      | ⟨a, b, h₁, h₂, h₃⟩ =>
      apply Or.elim h₂
      . intro
        apply Or.inl
        exists a; exists b
      . intro
        apply Or.inr
        exists a; exists b

  set_option Pattern.pp_interpret_hiding false in
  theorem propagationDisjRight_sound {c : Pattern 𝕊}
    : Γ ⊧ (φ ⋁ ψ) ⬝ c ⇒ (φ ⬝ c) ⋁ (ψ ⬝ c)
  := by
    intros _ _ _ _ _ _ h
    dsimp at *
    simp only [implies_false_implies_is_disj] at *
    match h with
    | ⟨a, b, h₁, h₂, h₃⟩ =>
    apply Or.elim h₁
    . intro
      apply Or.inl
      exists a; exists b
    . intro
      apply Or.inr
      exists a; exists b

  instance : Morphism (Pattern.interpret I e) where
    morphism_false := fun _ => interpret_bottom
    morphism_impl := fun _ _ _ => interpret_impl

  theorem tautology_sound : Tautology φ → Γ ⊧ φ := by
    intro htaut
    intros _ _ _ _ _ m
    exact htaut _ m

  theorem premise_sound : φ ∈ Γ → Γ ⊧ φ := by
    intro h
    intros _ _ _ morphism m
    exact morphism φ h m

  theorem existence_sound {x : EVar} : Γ ⊧ ∃∃ x (Pattern.evar x) := by
    intro _ _ _ _ _ h
    simp only [Pattern.interpret, Function.update_same]
    exact ⟨h, rfl⟩

  set_option Pattern.pp_interpret_hiding false in
  theorem existGen_sound {x : EVar} (Hnfv : ¬ψ.isFreeEvar x) :
    Γ ⊧ φ ⇒ ψ → Γ ⊧ ∃∃ x φ ⇒ ψ
  := by
    intros h M _ I hΓ e m
    simp only [Pattern.interpret] at *
    intro ⟨a, hφ⟩
    let e' : Valuation M := ⟨Function.update e.evalEvar x a, e.evalSvar⟩
    specialize h hΓ e' m
    have hψ := h hφ
    rw
      [ only_free_var_relevant
          (Function.update e.evalEvar x a)
          e.evalEvar
          e.evalSvar
          e.evalSvar
      ] at hψ
    assumption
    { intros x₀ Hfv
      simp only [Function.update]
      apply @Classical.byCases (x₀ = x) <;> (intro; simp [dif_neg, *] at *)
    }
    { intros; rfl }

  set_option Pattern.pp_interpret_hiding false in
  theorem union_of_app_left {m m₁ m₂ : M} {x : EVar} : ((φ.interpret I e m₁) ∧ (∃ a, ψ.interpret I { evalEvar := Function.update e.evalEvar x a, evalSvar := e.evalSvar } m₂) ∧ (Interpretation.evalApp I m₁ m₂ m)) ↔
     (∃ a, (φ.interpret I e m₁) ∧ (ψ.interpret I { evalEvar := Function.update e.evalEvar x a, evalSvar := e.evalSvar } m₂) ∧ Interpretation.evalApp I m₁ m₂ m) := by
      apply Iff.intro <;> intros h
      . simp [*] at *
      . simp [*] at *
        exact h

  set_option Pattern.pp_interpret_hiding false in
  theorem union_of_app_right {m m₁ m₂ : M} {x : EVar} : ((∃ a, φ.interpret I { evalEvar := Function.update e.evalEvar x a, evalSvar := e.evalSvar } m₁) ∧ (ψ.interpret I e m₂) ∧ (Interpretation.evalApp I m₁ m₂ m)) ↔
     (∃ a, (φ.interpret I { evalEvar := Function.update e.evalEvar x a, evalSvar := e.evalSvar } m₁) ∧ (ψ.interpret I e m₂) ∧ Interpretation.evalApp I m₁ m₂ m) := by
      apply Iff.intro <;> intros h
      . simp [*] at *
      . simp [*] at *
        exact h


  set_option Pattern.pp_interpret_hiding false in
  theorem propagationExistLeft_sound
    {ψ : Pattern 𝕊} {x : EVar} (Hnfv : ¬ψ.isFreeEvar x) :
      Γ ⊧ ψ ⬝ ∃∃ x φ ⇒ ∃∃ x (ψ ⬝ φ)
  := by
    intros M _ I _ e m
    simp only [Pattern.interpret]
    intro ⟨a₁, a₂, Hψ, ⟨a₃, Hφ⟩, He⟩
    exists a₃; exists a₁; exists a₂
    simp only [*, and_true]
    rw
      [ only_free_var_relevant
          (Function.update e.evalEvar x a₃)
          e.evalEvar
          e.evalSvar
          e.evalSvar
      ]; assumption
    { intros x₀ Hfv
      simp only
        [Function.update_apply, ite_eq_right_iff]
      intros; simp_all
    }
    { simp only [implies_true] }

  set_option Pattern.pp_interpret_hiding false in
  theorem propagationExistRight_sound
    {ψ : Pattern 𝕊} {x : EVar} (Hnfv : ¬ψ.isFreeEvar x) :
      Γ ⊧ ∃∃ x φ ⬝ ψ ⇒ ∃∃ x (φ ⬝ ψ)
  := by
    intros M _ I _ e m
    simp only [Pattern.interpret]
    intro ⟨a₁, a₂, ⟨a₃, Hφ⟩, ⟨Hψ, He⟩⟩
    exists a₃; exists a₁; exists a₂
    simp only [*, and_true, true_and]
    rw
      [ only_free_var_relevant
          (Function.update e.evalEvar x a₃)
          e.evalEvar
          e.evalSvar
          e.evalSvar
      ]; assumption
    { intros x₀ Hfv
      simp only
        [Function.update_apply, ite_eq_right_iff]
      intros; simp_all
    }
    { simp only [implies_true] }

  theorem dni { p : Prop } : p → ¬¬p :=
    fun hp : p =>
    fun hnp : ¬p =>
    absurd hp hnp

  theorem dne { p : Prop } : ¬¬p → p :=
    fun hnnp : ¬¬p =>
    Or.elim (Classical.em p)
    ( fun hp : p => show p from hp )
    ( fun hnp : ¬p =>
      have hf : False := absurd hnp hnnp
      show p from False.elim hf
    )

  @[simp]
  theorem dn { p : Prop } : ¬¬p ↔ p := by
    apply Iff.intro <;> intros h
    . exact dne h
    . exact dni h

  @[simp]
  theorem neg_of_impl_left { p q : Prop } : ¬(p → q) → (p ∧ ¬q) := by
    intro h
    simp [*] at h
    exact h

  @[simp]
  theorem neg_of_impl_right { p q : Prop } : (p ∧ ¬q) → ¬(p → q) := by
    intro h
    simp [*]

  @[simp]
  theorem neg_of_impl { p q : Prop } : ¬(p → q) ↔ p ∧ ¬q := by
    apply Iff.intro <;> intros h
    . exact neg_of_impl_left h
    . exact neg_of_impl_right h

  set_option Pattern.pp_interpret_hiding false in
  -- Similar to Proposition 3.95
  theorem context_impl {C : AppContext 𝕊} :
    Valuation.satifies I e (φ ⇒ ψ) → Valuation.satifies I e (C[φ] ⇒ C[ψ])
  := by
    simp only [Valuation.satifies]
    intro H
    induction C with
    | empty => simpa only [AppContext.insert]
    | left χ C' ih =>
      simp only [AppContext.insert, Pattern.interpret] at *
      -- dsimp at *
      intro m ⟨a₁, a₂, h₁, h₂, h₃⟩
      exists a₁; exists a₂
      simp [*]
    | right χ C' ih =>
      simp only [AppContext.insert, Pattern.interpret] at *
      intro m ⟨a₁, a₂, h₁, h₂, h₃⟩
      exists a₁; exists a₂
      simp [*]

  set_option Pattern.pp_interpret_hiding false in
  -- Similar to Proposition 3.95
  theorem context_equiv {C : AppContext 𝕊} :
    Valuation.satifies I e (φ ⇔ ψ) → Valuation.satifies I e (C[φ] ⇔ C[ψ])
  := by
    simp only [v_sat_equiv]
    intro ⟨H₁, H₂⟩
    constructor <;> (apply context_impl; assumption)

  set_option Pattern.pp_interpret_hiding false in
  -- Similar to Proposition 3.94 (96)
  theorem context_bottom {C : AppContext 𝕊} : ∀ m,
    Pattern.interpret I e (C[⊥]) m ↔ Pattern.interpret I e ⊥ m
  := by
    induction C with
    | empty => intro m; simp only [AppContext.insert]
    | left χ C' ih =>
      intro m
      simp only [AppContext.insert, Pattern.interpret]
      constructor
      . intro ⟨_, _, _, contra, _⟩
        simp only [ih, Pattern.interpret] at contra
      . exact False.elim
    | right χ C' ih =>
      intro m
      simp only [AppContext.insert, Pattern.interpret]
      constructor
      . intro ⟨_, _, contra, _, _⟩
        simp only [ih, Pattern.interpret] at contra
      . exact False.elim

  set_option Pattern.pp_interpret_hiding false in
  -- Similar to Lemma 3.99
  theorem context_empty {C : AppContext 𝕊} :
    (∀ m, Pattern.interpret I e    φ   m ↔ False) →
    (∀ m, Pattern.interpret I e (C[φ]) m ↔ False)
  := by
    intro H
    have H₁ : Valuation.satifies I e (φ ⇔ ⊥) := by
      simp only [Valuation.satifies, interpret_equiv]
      intro m
      rw [H]; rfl
    have H₂ : Valuation.satifies I e (C[φ] ⇔ C[⊥]) := context_equiv H₁
    intro m
    simp only [Valuation.satifies, interpret_equiv] at H₂
    simp only [H₂, context_bottom, Pattern.interpret]

  set_option Pattern.pp_interpret_hiding false in
  -- Similar to Proposition 3.100
  theorem singleton_sound {C₁ C₂ : AppContext 𝕊} {x : EVar} :
    Γ ⊧ ∼(C₁[Pattern.evar x ⋀ φ] ⋀ C₂[Pattern.evar x ⋀ ∼φ])
  := by
    intro M _ I _ e m h
    rw [interpret_conj] at h
    simp only [Pattern.interpret]
    apply @Classical.byCases ((Pattern.interpret I e φ) (e.evalEvar x))
    . intro he
      have
        H_empty : ∀ m, Pattern.interpret I e (Pattern.evar x ⋀ ∼φ) m ↔ False
      := by
        intro m'
        rw [interpret_conj]
        simp only [Pattern.interpret]
        apply @Classical.byCases (m' = (Valuation.evalEvar e x))
        . intro Heq; simp [Heq, he, and_false]
        . intro Hneq; constructor
          . intro ⟨_, _⟩; apply Hneq; assumption
          . exact False.elim
      rw [@context_empty _ _ _ _ _ C₂] at h <;> try assumption
      simp only [h]
    . intro he
      have
        H_empty : ∀ m, Pattern.interpret I e (Pattern.evar x ⋀ φ) m ↔ False
      := by
        intro m'
        rw [interpret_conj]
        simp only [Pattern.interpret]
        apply @Classical.byCases (m' = (Valuation.evalEvar e x))
        . intro Heq; simp only [Heq, he, and_false]
        . intro Hneq; constructor
          . intro ⟨_, _⟩; apply Hneq; assumption
          . exact False.elim
      rw [@context_empty _ _ _ _ _ C₁] at h <;> try assumption
      simp only [h]

  def 𝓕
    (I : Interpretation 𝕊 M) (e : Valuation M) (φ : Pattern 𝕊) (X : SVar)
    (B : Set M) :
    Set M
  :=
    φ.interpret I ⟨ e.evalEvar, Function.update e.evalSvar X B ⟩

  def 𝓖
    (I : Interpretation 𝕊 M) (e : Valuation M) (φ : Pattern 𝕊) (X : SVar)
    (B : Set M) :
    Set M
  :=
    λ a => ¬ (φ.interpret I ⟨ e.evalEvar, Function.update e.evalSvar X B ⟩) a

  def monotone (F : Set M → Set M) :=
    ∀ (B C : Set M), (∀ m, B m → C m) → ∀ m, (F B m) → (F C m)

  set_option Pattern.pp_interpret_hiding false in
  -- Similar to Proposition 3.79
  theorem 𝓕𝓖_monotone :
    ∀ (φ : Pattern 𝕊) (X : SVar),
      ((¬Pattern.hasFreeNegativeOcc φ X = true) ->
        (∀ (I : Interpretation 𝕊 M) e, monotone (𝓕 I e φ X))
      )
      ∧
      ((¬Pattern.hasFreePositiveOcc φ X = true) ->
        (∀ (I : Interpretation 𝕊 M) e, monotone (𝓖 I e φ X))
      )
  := by
    intros φ X
    simp only [monotone, 𝓕, 𝓖]
    induction φ with
    | evar _ => exact ⟨fun _ _ _ _ _ _ _ h => h, fun _ _ _ _ _ _ _ h => h⟩
    | bottom => exact ⟨fun _ _ _ _ _ _ _ h => h, fun _ _ _ _ _ _ _ h => h⟩
    | symbol _ => exact ⟨fun _ _ _ _ _ _ _ h => h, fun _ _ _ _ _ _ _ h => h⟩
    | svar Y =>
      constructor
      · intro _ I e B C hBC m h
        simp only [Pattern.interpret, Function.update_apply] at h ⊢
        by_cases hY : Y = X
        · rw [if_pos hY] at h ⊢; exact hBC m h
        · rw [if_neg hY] at h ⊢; exact h
      · intro hpos I e B C _ m h
        have hYX : ¬Y = X := fun hYX => hpos (by simp [hYX])
        simp only [Pattern.interpret, Function.update_apply, if_neg hYX] at h ⊢
        exact h
    | application ψ χ ih₁ ih₂ =>
      constructor
      · intro hneg I e B C hBC m
        rw [Pattern.has_free_negative_occ_application, not_or] at hneg
        simp only [Pattern.interpret]
        intro ⟨a, b, ha, hb, happ⟩
        exact ⟨a, b, ih₁.1 hneg.1 I e B C hBC a ha, ih₂.1 hneg.2 I e B C hBC b hb, happ⟩
      · intro hpos I e B C hBC m
        rw [Pattern.has_free_positive_occ_application, not_or] at hpos
        simp only [Pattern.interpret]
        intro hB ⟨a, b, ha, hb, happ⟩
        exact hB ⟨a, b,
          Classical.byContradiction fun hn => ih₁.2 hpos.1 I e B C hBC a hn ha,
          Classical.byContradiction fun hn => ih₂.2 hpos.2 I e B C hBC b hn hb, happ⟩
    | implication ψ χ ih₁ ih₂ =>
      constructor
      · intro hneg I e B C hBC m
        rw [Pattern.has_free_negative_occ_implication, not_or] at hneg
        simp only [Pattern.interpret]
        intro h hψC
        have hψB := Classical.byContradiction fun hn => ih₁.2 hneg.1 I e B C hBC m hn hψC
        exact ih₂.1 hneg.2 I e B C hBC m (h hψB)
      · intro hpos I e B C hBC m
        rw [Pattern.has_free_positive_occ_implication, not_or] at hpos
        simp only [Pattern.interpret]
        intro hB hC
        apply hB
        intro hψB
        have hχC := hC (ih₁.1 hpos.1 I e B C hBC m hψB)
        exact Classical.byContradiction fun hn => ih₂.2 hpos.2 I e B C hBC m hn hχC
    | existential z ψ ih =>
      constructor
      · intro hneg I e B C hBC m
        rw [Pattern.has_free_negative_occ_existential] at hneg
        simp only [Pattern.interpret]
        intro ⟨a, ha⟩
        exact ⟨a, ih.1 hneg I ⟨Function.update e.evalEvar z a, e.evalSvar⟩ B C hBC m ha⟩
      · intro hpos I e B C hBC m
        rw [Pattern.has_free_positive_occ_existential] at hpos
        simp only [Pattern.interpret]
        intro hB ⟨a, ha⟩
        exact hB ⟨a, Classical.byContradiction fun hn =>
          ih.2 hpos I ⟨Function.update e.evalEvar z a, e.evalSvar⟩ B C hBC m hn ha⟩
    | mu Z ψ ih =>
      by_cases hZX : Z = X
      · subst hZX
        constructor <;>
        ( intro _ I e B C _ m
          simp only [Pattern.interpret, Function.update_idem]
          exact id )
      · constructor
        · intro hneg I e B C hBC m
          have hneg' : ¬ψ.hasFreeNegativeOcc X = true := by
            simpa [Ne.symm hZX] using hneg
          simp only [Pattern.interpret, Function.update_comm (Ne.symm hZX)]
          intro H D hD
          exact H D (fun m' hm' =>
            hD m' (ih.1 hneg' I ⟨e.evalEvar, Function.update e.evalSvar Z D⟩ B C hBC m' hm'))
        · intro hpos I e B C hBC m
          have hpos' : ¬ψ.hasFreePositiveOcc X = true := by
            simpa [Ne.symm hZX] using hpos
          simp only [Pattern.interpret, Function.update_comm (Ne.symm hZX)]
          intro hB hC
          apply hB
          intro D hD
          exact hC D (fun m' hm' => hD m' (Classical.byContradiction fun hn =>
            ih.2 hpos' I ⟨e.evalEvar, Function.update e.evalSvar Z D⟩ B C hBC m' hn hm'))
-- #exit
  set_option Pattern.pp_interpret_hiding false in
  -- Similar to Proposition 3.75
  theorem subf_Xδ_eq_eval_Xeδ {X : SVar} {δ : Pattern 𝕊} :
    ∀ (m : M) (e : Valuation M),
    Pattern.substitutableForSvarIn X δ φ →
    Pattern.interpret I e (Pattern.substSvar φ X δ) m
      =
      φ.interpret I
        ⟨ e.evalEvar, Function.update e.evalSvar X (Pattern.interpret I e δ) ⟩
        m
  := by
    intro m e hs
    induction φ generalizing m e with
    | evar _ => rfl
    | svar Y =>
      by_cases h : X = Y
      · subst h
        simp [Pattern.interpret, Function.update_apply]
      · simp [Pattern.interpret, Function.update_apply, h, Ne.symm h]
    | bottom => rfl
    | symbol => rfl
    | application ψ χ ih₁ ih₂ =>
      simp only [Pattern.substitutableForSvarIn, Bool.and_eq_true, decide_eq_true_eq] at hs
      simp only [Pattern.substSvar, Pattern.interpret, ih₁ _ _ hs.1, ih₂ _ _ hs.2]
    | implication ψ χ ih₁ ih₂ =>
      simp only [Pattern.substitutableForSvarIn, Bool.and_eq_true, decide_eq_true_eq] at hs
      simp only [Pattern.substSvar, Pattern.interpret, ih₁ _ _ hs.1, ih₂ _ _ hs.2]
    | existential z ψ ih =>
      by_cases hfv : ψ.isFreeSvar X
      · have hs' : ¬δ.isFreeEvar z ∧ Pattern.substitutableForSvarIn X δ ψ := by
          simpa [hfv] using hs
        have hδ : ∀ a, Pattern.interpret I ⟨Function.update e.evalEvar z a, e.evalSvar⟩ δ
            = Pattern.interpret I e δ := by
          intro a
          funext m'
          apply propext
          apply only_free_var_relevant
          · intro x' hx'
            rw [Function.update_noteq]
            intro h; subst h; exact hs'.1 hx'
          · intros; rfl
        simp only [Pattern.substSvar, Pattern.interpret, ih _ _ hs'.2, hδ]
      · exact case_not_fv (∃∃ z ψ) (by simpa using hfv) m e hs
    | mu Z ψ ih =>
      by_cases hXZ : X = Z
      · subst hXZ
        exact case_not_fv (μ X ψ) (by simp) m e hs
      · by_cases hfv : ψ.isFreeSvar X
        · have hs' : ¬δ.isFreeSvar Z ∧ Pattern.substitutableForSvarIn X δ ψ := by
            simpa [hXZ, hfv] using hs
          have hδ : ∀ B, Pattern.interpret I ⟨e.evalEvar, Function.update e.evalSvar Z B⟩ δ
              = Pattern.interpret I e δ := by
            intro B
            funext m'
            apply propext
            apply only_free_var_relevant
            · intros; rfl
            · intro Y hY
              rw [Function.update_noteq]
              intro h; subst h; exact hs'.1 hY
          simp only [Pattern.substSvar, if_neg hXZ, Pattern.interpret, ih _ _ hs'.2, hδ,
            Function.update_comm (Ne.symm hXZ)]
        · exact case_not_fv (μ Z ψ) (by simp [hXZ, hfv]) m e hs
  where
    case_not_fv {X : SVar} {δ : Pattern 𝕊}
      φ (Hnot_fv : ¬Pattern.isFreeSvar φ X = true) m e :
    Pattern.substitutableForSvarIn X δ φ →
    Pattern.interpret I e (Pattern.substSvar φ X δ) m
      =
      φ.interpret I
        ⟨ e.evalEvar, Function.update e.evalSvar X (Pattern.interpret I e δ) ⟩
        m
    := by
      intro _
      rw [Pattern.subst_not_free_svar _ _ _ Hnot_fv]
      apply propext
      apply only_free_var_relevant
      · intros; rfl
      · intro Y hY
        rw [Function.update_noteq]
        intro h; subst h; exact Hnot_fv hY
-- Port: upstream had a live `#exit` here, so nothing below (including `Proof.soundness`) was checked upstream.
  set_option Pattern.pp_interpret_hiding false in
  theorem prefixpoint_sound {X : SVar}
    (φ_pos_X: ¬Pattern.hasFreeNegativeOcc φ X = true)
    (sfi : Pattern.substitutableForSvarIn X (μ X φ) φ = true) :
    Γ ⊧ φ[X ⇐ˢ μ X φ] ⇒ μ X φ
  := by
    intros
    intro M _ I _ e m
    simp only [Pattern.interpret]
    intro 𝓕_μ𝓕
    rw [subf_Xδ_eq_eval_Xeδ] at 𝓕_μ𝓕 <;> try assumption

    have monotone𝓕 : monotone (𝓕 I e φ X) := by
      apply (𝓕𝓖_monotone φ X).1; assumption

    -- Case "⊆" of Claim 1 from the Knaster-Tarski Theorem
    intro B
    rw [← 𝓕]
    intro HB
    rw [← 𝓕] at 𝓕_μ𝓕
    apply HB
    apply monotone𝓕 (Pattern.interpret I e (μ X φ))
    simp only [Pattern.interpret]
    intro m Hμ
    apply Hμ
    intros m' Hm'
    rw [← 𝓕] at Hm'
    apply HB; apply Hm'; exact 𝓕_μ𝓕

  set_option Pattern.pp_interpret_hiding false in
  theorem substitution_sound {X : SVar} (sfi : ψ.substitutableForSvarIn X φ) :
    Γ ⊧ φ → Γ ⊧ Pattern.substSvar φ X ψ
  := by
    intros h M inst I hΓ e m
    let
      e' : Valuation M :=
        ⟨e.evalEvar, Function.update e.evalSvar X (Pattern.interpret I e ψ)⟩
    specialize h hΓ e' m
    rw [subf_Xδ_eq_eval_Xeδ] <;> assumption

  set_option Pattern.pp_interpret_hiding false in
  -- Similar to Proposition 3.106
  theorem subf_impl_mu_implₗ {X : SVar}
    (sfi : Pattern.substitutableForSvarIn X ψ φ) : ∀ I (e : Valuation M),
      (Valuation.satifies I e (φ[X ⇐ˢ ψ] ⇒ ψ) → Valuation.satifies I e (μ X φ ⇒ ψ))
  := by
    simp only [Valuation.satifies]
    intros I e H
    intro m
    simp only [interpret_impl]
    intro Hμ
    simp only [Pattern.interpret] at Hμ H
    apply Hμ
    intro m₀
    specialize H m₀
    rw [subf_Xδ_eq_eval_Xeδ] at H
    apply H; assumption

  set_option Pattern.pp_interpret_hiding false in
  -- Similar to Proposition 3.108
  theorem subf_impl_mu_impl {X : SVar}
    (sfi : Pattern.substitutableForSvarIn X ψ φ) : ∀ I : Interpretation 𝕊 M,
      (I.satisfies (φ[X ⇐ˢ ψ] ⇒ ψ) → I.satisfies (μ X φ ⇒ ψ))
  := by
    simp only [Interpretation.satisfies]
    intros I H e
    apply subf_impl_mu_implₗ; assumption
    apply H e

  set_option Pattern.pp_interpret_hiding false in
  -- Similar to Proposition 3.109
  theorem knasterTarski_sound {X : SVar}
    (sfi : Pattern.substitutableForSvarIn X ψ φ) :
      (ps : Γ ⊧ φ[X ⇐ˢ ψ] ⇒ ψ) → (Γ ⊧ μ X φ ⇒ ψ)
  := by
    simp only [entails]
    intros H m _ I a
    apply subf_impl_mu_impl; assumption
    apply H; assumption

  -- TODO (Andrei B): Global?
  theorem Proof.soundness {φ : Pattern 𝕊} : Γ ⊢ φ → Γ ⊧ φ
  | premise _ prf => premise_sound prf
  | tautology taut => tautology_sound taut
  | existQuan sfi => existQuan_sound sfi
  | propagationBottomLeft => propagationBottomLeft_sound
  | propagationBottomRight => propagationBottomRight_sound
  | propagationDisjLeft => propagationDisjLeft_sound
  | propagationDisjRight => propagationDisjRight_sound
  | propagationExistLeft nfv => propagationExistLeft_sound nfv
  | propagationExistRight nfv => propagationExistRight_sound nfv
  | @prefixpoint _ _ ψ X wf sfi => by
    cases wf with
    | mu _ φ_pos_X =>
    apply prefixpoint_sound φ_pos_X sfi
  | existence => existence_sound
  | singleton => singleton_sound

  | modusPonens prf₁ prf₂ => modus_ponens_sound prf₁.soundness prf₂.soundness
  | existGen Hnfv prf => existGen_sound Hnfv prf.soundness
  | framingLeft prf => framing_left_sound prf.soundness
  | framingRight prf => framing_right_sound prf.soundness
  | substitution sfi prf => substitution_sound sfi prf.soundness
  | knasterTarski sfi prf => knasterTarski_sound sfi prf.soundness

end ML
