/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Horațiu Cheval
-/

import MatchingLogic.Definedness
import MatchingLogic.Substitution

set_option autoImplicit false

namespace ML

variable {𝕊 : Type} [HasDefined 𝕊]

/-
  TODO:
  We have two options:
  - require the decidability of `∈` in the definition of `Premises`
  - have `noncomputable` definitions throughot
  TO DECIDE
-/
noncomputable instance {φ : Pattern 𝕊} {Γ : Premises 𝕊} : Decidable (φ ∈ Γ) := @default _ (Classical.decidableInhabited _)

/-
  We should do it first for closed `ψ` and no knaster-tarksi
-/

/--
  NOT USED YET.

  Describes the conditions on a proof of `Γ ∪ {ψ} ⊢ φ` for the deduction theorem to be applicable on it.
  At the time this means that the proof does not use the Knaster-Tarski rule and that `ψ` is `μ`- and `∃`-closed.
  In the future we should generalize the conditions.
-/
structure AdmissibleForDeductionTheorem {Γ} {φ ψ : Pattern 𝕊} (prf : Γ ∪ {ψ} ⊢ φ) where
  mu_closed : ψ.muClosed
  exist_closed : ψ.existClosed
  no_kt : ¬prf.usesKnasterTarski


section
  open Proof

  variable {Γ : Premises 𝕊} [HasDefinedness Γ] {ψ χ₁ χ₂ c : Pattern 𝕊}

  def deductionTheoremFramingRightAux1 : Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ → Γ ⊢ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉ :=
    fun l₁ :  Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ =>
    let l₁' : Γ ⊢ ⌈∼ψ⌉ ⋁ ∼⌈∼ψ⌉ := (excluddedMiddle)
    let l₂' : Γ ⊢ ⌈∼ψ⌉ ⋁ (χ₁ ⇒ χ₂) := l₁
    let l₃' : Γ ⊢ ⌈∼ψ⌉ ⇒ (χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉) :=
      let l₁'' : Γ ⊢ ⌈∼ψ⌉ ⇒ χ₂ ⋁ ⌈∼ψ⌉ := (disjIntroRight)
      let l₂'' : Γ ⊢ ⌈∼ψ⌉ ⋀ χ₁ ⇒ ⌈∼ψ⌉ := (conjElimLeft)
      let l₃'' : Γ ⊢ ⌈∼ψ⌉ ⋀ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉ := (syllogism) l₂'' l₁''
      let l₄'' : Γ ⊢ ⌈∼ψ⌉ ⇒ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉ := (exportation) l₃''
      l₄''
    let l₄' : Γ ⊢ ∼⌈∼ψ⌉ ⇒ (χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉) :=
      let l₁'' : Γ ⊢ (⌊ψ⌋ ⇒ χ₁ ⇒ χ₂) ⋁ (⌊ψ⌋ ⇒ χ₁ ⇒ ⌈∼ψ⌉) := toRule (disjIntroLeft) l₁
      let l₂'' : Γ ⊢ (⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉) := toRule (disjImpl2) l₁''
      l₂''
    let l₅' : Γ ⊢ ⌈∼ψ⌉ ⋁ ∼⌈∼ψ⌉ ⇒ (χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉) := (disjIntroAtHyp) l₃' l₄'
    let l₆' : Γ ⊢ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉ := modusPonens l₁' l₅'
    l₆'

  def deductionTheoremFramingRightAux : Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ → Γ ⊢ ⌊ψ⌋ ⇒ c ⬝ χ₁ ⇒ c ⬝ χ₂ :=
    fun l₁ :  Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ =>
    let l₂ : Γ ⊢ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉ := (deductionTheoremFramingRightAux1) l₁
    let l₃_aux := (@ctxImplDefined _ _ Γ _ (∼ψ) (AppContext.left c .CtxDefined))
    let l₃ : Γ ⊢ c ⬝ ⌈∼ψ⌉ ⇒ ⌈∼ψ⌉ := l₃_aux
    let l₄ : Γ ⊢ c ⬝ χ₁ ⇒ c ⬝ (χ₂ ⋁ ⌈∼ψ⌉) := (framingRight) l₂
    let l₅ : Γ ⊢ c ⬝ χ₁ ⇒ c ⬝ χ₂ ⋁ c ⬝ ⌈∼ψ⌉ := (syllogism) l₄ (propagationDisjLeft)
    let l₆ : Γ ⊢ c ⬝ χ₂ ⋁ c ⬝ ⌈∼ψ⌉ ⇒ c ⬝ χ₂ ⋁ ⌈∼ψ⌉ := (expansion) l₃
    let l₇ : Γ ⊢ c ⬝ χ₁ ⇒ c ⬝ χ₂ ⋁ ⌈∼ψ⌉ := (syllogism) l₅ l₆
    let l₈ : Γ ⊢ ⌊ψ⌋ ⇒ c ⬝ χ₁ ⇒ c ⬝ χ₂ :=
      let l₁' : Γ ⊢ c ⬝ χ₁ ⇒ ⌈∼ψ⌉ ⋁ c ⬝ χ₂ := (syllogism) l₇ (permutationDisj)
      let l₂' : Γ ⊢ c ⬝ χ₁ ⇒ ∼⌈∼ψ⌉ ⇒ c ⬝ χ₂ := l₁'
      let l₃' : Γ ⊢ ∼⌈∼ψ⌉ ⇒ c ⬝ χ₁ ⇒ c ⬝ χ₂ := (permuteHyps) l₂'
      let l₄' : Γ ⊢ ⌊ψ⌋ ⇒ c ⬝ χ₁ ⇒ c ⬝ χ₂ := l₃'
      l₄'
    l₈


  def deductionTheoremFramingLeftAux : Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ → Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⬝ c ⇒ χ₂ ⬝ c :=
    fun l₁ :  Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ =>
    let l₂ : Γ ⊢ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉ := (deductionTheoremFramingRightAux1) l₁
    let l₃_aux := (@ctxImplDefined _ _ Γ _ (∼ψ) (AppContext.right c .CtxDefined))
    let l₃ : Γ ⊢ ⌈∼ψ⌉ ⬝ c⇒ ⌈∼ψ⌉ := l₃_aux
    let l₄ : Γ ⊢ χ₁ ⬝ c ⇒ (χ₂ ⋁ ⌈∼ψ⌉) ⬝ c := (framingLeft) l₂
    let l₅ : Γ ⊢ χ₁ ⬝ c ⇒ χ₂ ⬝ c ⋁ ⌈∼ψ⌉ ⬝ c := (syllogism) l₄ (propagationDisjRight)
    let l₆ : Γ ⊢ χ₂ ⬝ c ⋁ ⌈∼ψ⌉ ⬝ c ⇒ χ₂ ⬝ c ⋁ ⌈∼ψ⌉ := (expansion) l₃
    let l₇ : Γ ⊢ χ₁ ⬝ c ⇒ χ₂ ⬝ c ⋁ ⌈∼ψ⌉ := (syllogism) l₅ l₆
    let l₈ : Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⬝ c ⇒ χ₂ ⬝ c :=
      let l₁' : Γ ⊢ χ₁ ⬝ c ⇒ ⌈∼ψ⌉ ⋁ χ₂ ⬝ c := (syllogism) l₇ (permutationDisj)
      let l₂' : Γ ⊢ χ₁ ⬝ c ⇒ ∼⌈∼ψ⌉ ⇒ χ₂ ⬝ c := l₁'
      let l₃' : Γ ⊢ ∼⌈∼ψ⌉ ⇒ χ₁ ⬝ c ⇒ χ₂ ⬝ c := (permuteHyps) l₂'
      let l₄' : Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⬝ c ⇒ χ₂ ⬝ c := l₃'
      l₄'
    l₈

end


-- Port: upstream's `simp [*] at *` calls no longer close the goals about `⌊ψ⌋` below; the port states these two facts explicitly.
theorem total_muClosed {ψ : Pattern 𝕊} (h : ψ.muClosed) : ⌊ψ⌋.muClosed := by
  intro X; have := h X; simp_all [total, Pattern.negation]

theorem total_not_free_evar {ψ : Pattern 𝕊} {x : EVar} (h : ¬ψ.isFreeEvar x) : ¬⌊ψ⌋.isFreeEvar x := by
  simp_all [total, Pattern.negation]

open Proof in
noncomputable def Proof.deductionTheorem {Γ : Premises 𝕊} [HasDefinedness Γ] {φ ψ : Pattern 𝕊}
  (hψ_mu : ψ.muClosed) (hψ_exist : ψ.existClosed) (prf : Γ ∪ {ψ} ⊢ φ) (no_kt : ¬prf.usesKnasterTarski) :
  Γ ⊢ ⌊ψ⌋ ⇒ φ :=
match prf with
| premise wf hmem =>
  if hmem_φ_Γ : φ ∈ Γ then
    let p₁ : Γ ⊢ φ := .premise wf hmem_φ_Γ
    (extraPremise) p₁
  else
    have h_φ_eq_ψ : φ = ψ := by
      cases hmem
      . contradiction
      . assumption
    let l : Γ ⊢ ⌊ψ⌋ ⇒ ψ := (totalImpl)
    h_φ_eq_ψ ▸ (totalImpl)
| tautology h => tautology <| by
    intros M _ f _ m
    simp only [Morphism.morphism_impl]
    intros _
    exact h _ _
| existQuan sfi => (extraPremise) (existQuan sfi)
| existence => (extraPremise) existence
| singleton => (extraPremise) <| singleton
| propagationBottomLeft => (extraPremise) <| propagationBottomLeft
| propagationBottomRight  => (extraPremise) <| propagationBottomRight
| propagationDisjLeft => (extraPremise) <| propagationDisjLeft
| propagationDisjRight => (extraPremise) <| propagationDisjRight
| propagationExistLeft not_fv  => (extraPremise) <| propagationExistLeft not_fv
| propagationExistRight not_fv => (extraPremise) <| propagationExistRight not_fv
| prefixpoint wf sfi => (extraPremise) <| prefixpoint wf sfi
| @modusPonens _ _ χ χ' prf₁ prf₂ =>
  let prf₁' := prf₁.deductionTheorem hψ_mu hψ_exist (by simp at no_kt ; simp [no_kt])
  let prf₂' := prf₂.deductionTheorem hψ_mu hψ_exist (by simp at no_kt ; simp [no_kt])
  (modusPonensExtraHyp) prf₁' prf₂'
| @framingRight _ _ χ₁ χ₂ c prf =>
  let l₁ : Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ := prf.deductionTheorem hψ_mu hψ_exist (by simp [*] at * ; assumption)
  (deductionTheoremFramingRightAux) l₁
| @framingLeft _ _ χ₁ χ₂ c prf =>
  let l₁ : Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ := prf.deductionTheorem hψ_mu hψ_exist (by simp [*] at * ; assumption)
  (deductionTheoremFramingLeftAux) l₁
| @existGen _ _ χ₁ χ₂ x not_fv prf =>
  let l₁ : Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ := prf.deductionTheorem hψ_mu hψ_exist (by simp [*] at * ; assumption)
  let l₂ : Γ ⊢ χ₁ ⇒ ⌊ψ⌋ ⇒ χ₂ := (permuteHyps) l₁
  let l₃ : Γ ⊢ ∃∃ x χ₁ ⇒ ⌊ψ⌋ ⇒ χ₂ := existGen (by simp only [Pattern.isFreeEvar, Bool.or_eq_true, decide_eq_true_eq, not_or]; exact ⟨total_not_free_evar (hψ_exist x), not_fv⟩) l₂
  let l₄ := (permuteHyps) l₃
  l₄
| knasterTarski _ prf => False.elim (by simp at no_kt)
| @substitution _ _ χ₁ χ₂ X sfi prf =>
  let l₁ := prf.deductionTheorem hψ_mu hψ_exist (by simp [*] at * ; assumption)
  let l₂ : Γ ⊢ (⌊ψ⌋ ⇒ χ₁).substSvar X χ₂ := @substitution _ _ _ _ X (by simp only [Pattern.substitutableForSvarIn, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Pattern.substitutable_svar_into_closed (total_muClosed hψ_mu), sfi⟩) l₁
  have : (⌊ψ⌋ ⇒ χ₁).substSvar X χ₂ = ⌊ψ⌋.substSvar X χ₂ ⇒ χ₁.substSvar X χ₂ := by rfl
  let l₃ := this ▸ l₂
  have : ⌊ψ⌋.substSvar X χ₂ = ⌊ψ⌋ := by
    have : ⌊ψ⌋.muClosed := total_muClosed hψ_mu
    exact Pattern.subst_not_free_svar ⌊ψ⌋ X χ₂ (this X)
  let l₄ := this ▸ l₃
  l₄
  -- termination_by _ _ prf _ => prf.size



#print axioms Proof.deductionTheorem
