/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Horațiu Cheval
-/

import MatchingLogic.Pattern
import MatchingLogic.Substitution
import Lean.Elab.Tactic

set_option autoImplicit false

namespace ML.Pattern



/-
  Find if the set variable `i` has a positive resp. a negative occurence in `φ`
  (no matter if the occurence is bound or free)

  **WARNING**: conjunction and disjunction are **not** yet implemented
-/
mutual
  @[simp]
  def hasPositiveOcc {𝕊} (φ : Pattern 𝕊) (X : SVar) : Bool :=
  match φ with
  | φ ⇒ ψ =>
    -- have : φ.size < (φ ⇒ ψ).size := sorry
    -- have : ψ.size < (φ ⇒ ψ).size := sorry
    φ.hasNegativeOcc X ∨ ψ.hasPositiveOcc X
  | svar Y => if X = Y then true else false
  | φ ⬝ ψ => φ.hasPositiveOcc X ∨ ψ.hasPositiveOcc X
  | μ Y φ =>
    have : φ.size < (μ Y φ).size := by simp [Pattern.size]
    φ.hasPositiveOcc X
  | ∃∃ _ φ => φ.hasPositiveOcc X
  | _ => false

  @[simp]
  def hasNegativeOcc {𝕊} (φ : Pattern 𝕊) (X : SVar) : Bool :=
  match φ with
  | φ ⇒ ψ => φ.hasPositiveOcc X ∨ ψ.hasNegativeOcc X
  | φ ⬝ ψ => φ.hasNegativeOcc X ∨ ψ.hasNegativeOcc X
  | μ _ φ | ∃∃ _ φ => φ.hasNegativeOcc X
  | _ => false
end
  -- termination_by _ φ _ => φ.size




section variable {𝕊 : Type} {φ ψ : Pattern 𝕊} {X : SVar}

  @[simp] theorem has_positive_occ_implication :
    (φ ⇒ ψ).hasPositiveOcc X ↔ φ.hasNegativeOcc X ∨ ψ.hasPositiveOcc X := by simp

  @[simp] theorem has_positive_occ_application :
    (φ ⬝ ψ).hasPositiveOcc X ↔ φ.hasPositiveOcc X ∨ ψ.hasPositiveOcc X := by simp

  @[simp] theorem has_positive_occ_existential {x : EVar} :
    (∃∃ x φ).hasPositiveOcc X ↔ φ.hasPositiveOcc X := by simp

  @[simp] theorem has_negative_occ_implication :
    (φ ⇒ ψ).hasNegativeOcc X ↔ φ.hasPositiveOcc X ∨ ψ.hasNegativeOcc X := by simp

  @[simp] theorem has_negative_occ_application :
    (φ ⬝ ψ).hasNegativeOcc X ↔ φ.hasNegativeOcc X ∨ ψ.hasNegativeOcc X := by simp

  @[simp] theorem has_negative_occ_existential {x : EVar} :
    (∃∃ x φ).hasNegativeOcc X ↔ φ.hasNegativeOcc X := by simp

  @[simp] theorem has_negative_occ_mu {Y : SVar} :
    (μ Y φ).hasNegativeOcc X ↔ φ.hasNegativeOcc X := by simp

end

mutual
  @[simp]
  def hasFreePositiveOcc {𝕊} (φ : Pattern 𝕊) (X : SVar) : Bool :=
  match φ with
  | φ ⇒ ψ => φ.hasFreeNegativeOcc X ∨ ψ.hasFreePositiveOcc X
  | svar Y => if X = Y then true else false
  | φ ⬝ ψ => φ.hasFreePositiveOcc X ∨ ψ.hasFreePositiveOcc X
  | μ Y φ => if X = Y then false else φ.hasFreePositiveOcc X
  | ∃∃ _ φ => φ.hasFreePositiveOcc X
  | _ => false

  @[simp]
  def hasFreeNegativeOcc {𝕊} (φ : Pattern 𝕊) (X : SVar) : Bool :=
  match φ with
  | φ ⇒ ψ => φ.hasFreePositiveOcc X ∨ ψ.hasFreeNegativeOcc X
  | φ ⬝ ψ => φ.hasFreeNegativeOcc X ∨ ψ.hasFreeNegativeOcc X
  | μ Y φ => if X = Y then false else φ.hasFreeNegativeOcc X
  | ∃∃ _ φ => φ.hasFreeNegativeOcc X
  | _ => false
end
  -- termination_by _ φ _ => φ.size

section variable {𝕊 : Type} {φ ψ : Pattern 𝕊} {X : SVar}
  @[simp] theorem has_free_positive_occ_implication :
    (φ ⇒ ψ).hasFreePositiveOcc X ↔ φ.hasFreeNegativeOcc X ∨ ψ.hasFreePositiveOcc X := by simp

  @[simp] theorem has_free_positive_occ_application :
    (φ ⬝ ψ).hasFreePositiveOcc X ↔ φ.hasFreePositiveOcc X ∨ ψ.hasFreePositiveOcc X := by simp

  @[simp] theorem has_free_positive_occ_existential {x : EVar} :
    (∃∃ x φ).hasFreePositiveOcc X ↔ φ.hasFreePositiveOcc X := by simp

  @[simp] theorem has_free_negative_occ_implication :
    (φ ⇒ ψ).hasFreeNegativeOcc X ↔ φ.hasFreePositiveOcc X ∨ ψ.hasFreeNegativeOcc X := by simp

  @[simp] theorem has_free_negative_occ_application :
    (φ ⬝ ψ).hasFreeNegativeOcc X ↔ φ.hasFreeNegativeOcc X ∨ ψ.hasFreeNegativeOcc X := by simp

  @[simp] theorem has_free_negative_occ_existential {x : EVar} :
    (∃∃ x φ).hasFreeNegativeOcc X ↔ φ.hasFreeNegativeOcc X := by simp

end

mutual
  @[simp]
  def hasBoundPositiveOcc {𝕊} (φ : Pattern 𝕊) (X : SVar) (scope : List SVar := []) : Bool :=
  match φ with
  | φ ⇒ ψ => φ.hasBoundNegativeOcc X scope ∨ ψ.hasBoundPositiveOcc X scope
  | svar Y => if X = Y ∧ X ∈ scope then true else false
  | φ ⬝ ψ => φ.hasBoundPositiveOcc X scope ∨ ψ.hasBoundPositiveOcc X scope
  | μ Y φ => φ.hasBoundPositiveOcc X (Y :: scope)
  | ∃∃ _ φ => φ.hasBoundPositiveOcc X scope
  | _ => false

  @[simp]
  def hasBoundNegativeOcc {𝕊} (φ : Pattern 𝕊) (X : SVar) (scope : List SVar := []) : Bool :=
  match φ with
  | φ ⇒ ψ => φ.hasBoundPositiveOcc X scope ∨ ψ.hasBoundNegativeOcc X scope
  | φ ⬝ ψ => φ.hasBoundNegativeOcc X scope ∨ ψ.hasBoundNegativeOcc X scope
  | μ Y φ => φ.hasBoundNegativeOcc X (Y :: scope)
  | ∃∃ _ φ => φ.hasBoundNegativeOcc X
  | _ => false
end
  -- termination_by _ φ _ _ => φ.size

/-
  Inductive definition of well formedness.
  A pattern is well formed iff no bound set variable occurs under an odd number of implications.
-/
inductive Positive {𝕊} : Pattern 𝕊 → Prop where
| mu {X} {φ} : Positive φ → ¬φ.hasFreeNegativeOcc X → Positive (μ X φ)
| implication {φ ψ} : Positive φ → Positive ψ → Positive (φ ⇒ ψ)
| application {φ ψ} : Positive φ → Positive ψ → Positive (φ ⬝ ψ)
| existential {x} {φ} : Positive φ → Positive (∃∃ x φ)
| bottom : Positive (⊥ : Pattern 𝕊)
| svar {i} : Positive (svar i)
| evar {i} : Positive (evar i)
| symbol {σ} : Positive (symbol σ)

/-
  Compute if a pattern is well formed, as a decision procedure for `Positive`
-/
@[simp]
def isPositive {𝕊} (φ : Pattern 𝕊) : Bool :=
match φ with
| μ X φ => φ.isPositive ∧ ¬φ.hasFreeNegativeOcc X
| φ ⬝ ψ | φ ⇒ ψ => φ.isPositive ∧ ψ.isPositive
| ∃∃ x φ => φ.isPositive
| _ => true

section variable {𝕊 : Type} {φ ψ : Pattern 𝕊}

  @[simp] theorem is_positive_mu {X : SVar} :
    (μ X φ).isPositive ↔ φ.isPositive ∧ φ.hasFreeNegativeOcc X = false := by simp

  @[simp] theorem is_positive_application : (φ ⬝ ψ).isPositive ↔ φ.isPositive ∧ ψ.isPositive := by simp

  @[simp] theorem is_positive_implication : (φ ⇒ ψ).isPositive ↔ φ.isPositive ∧ ψ.isPositive := by simp

  @[simp] theorem is_positive_existential {x : EVar} : (∃∃ x φ).isPositive ↔ φ.isPositive := by simp

end

/-- Free negative and positive occurrences are free. -/
theorem fv_of_free_positive_free_negative_occ {𝕊} (φ : Pattern 𝕊) (X : SVar) :
  (φ.hasFreePositiveOcc X → φ.isFreeSvar X) ∧ (φ.hasFreeNegativeOcc X → φ.isFreeSvar X) := by
  induction φ with
  | svar Y =>
    by_cases h : X = Y <;> apply And.intro <;> intros h' <;> simp [*] at *
  | mu Y φ' ih =>
    by_cases h : X = Y <;> apply And.intro <;> intros h' <;> simp_all
  | implication φ₁ φ₂ ih₁ ih₂ =>
    apply And.intro <;> intros h
    . rw [has_free_positive_occ_implication] at h
      cases h
      case inl h =>
        have := ih₁.2 h
        simp [*]
      case inr h =>
        have := ih₂.1 h
        simp [*]
    . rw [has_free_negative_occ_implication] at h
      cases h
      case inl h =>
        have := ih₁.1 h
        simp [*]
      case inr h =>
        have := ih₂.2 h
        simp [*]
  | application φ₁ φ₂ ih₁ ih₂ =>
    apply And.intro <;> intros h
    . rw [has_free_positive_occ_application] at h
      cases h
      case inl h =>
        have := ih₁.1 h
        simp [*]
      case inr h =>
        have := ih₂.1 h
        simp [*]
    . rw [has_free_negative_occ_application] at h
      cases h
      case inl h =>
        have := ih₁.2 h
        simp [*]
      case inr h =>
        have := ih₂.2 h
        simp [*]
  | existential y φ' ih =>
    apply And.intro <;> intros h
    . rw [has_free_positive_occ_existential] at h
      have := ih.1 h
      simp [*]
    . rw [has_free_negative_occ_existential] at h
      have := ih.2 h
      simp [*]
  | _ => simp? [*] at *

  /-- If `X` has a free positive occurrences in `φ` then it has a free occurrence in `φ` -/
  theorem fv_of_free_positive_occ {𝕊} (φ : Pattern 𝕊) (X : SVar) :
    φ.hasFreePositiveOcc X → φ.isFreeSvar X := (fv_of_free_positive_free_negative_occ _ _).1

  /-- If `X` has a free negative occurrences in `φ` then it has a free occurrence in `φ` -/
  theorem fv_of_free_negative_occ {𝕊} (φ : Pattern 𝕊) (X : SVar) :
    φ.hasFreeNegativeOcc X → φ.isFreeSvar X := (fv_of_free_positive_free_negative_occ _ _).2

/-- `positive` is a correct decision procedure for `Positive` -/
theorem positive_equivalent {𝕊} {φ : Pattern 𝕊} : φ.Positive ↔ φ.isPositive := by
  apply Iff.intro
  . intros h
    induction h
    all_goals (simp [*])
  . intros h
    induction φ with
    | mu X φ' ih =>
      constructor
      . rw [is_positive_mu] at h -- TODO: squeeze
        exact ih h.1
      . rw [is_positive_mu] at h
        simp [*]
    | implication ψ₁ ψ₂ ih₁ ih₂ | application ψ₁ ψ₂ ih₁ ih₂ =>
      constructor
      . try rw [is_positive_application] at h
        try rw [is_positive_implication] at h
        exact ih₁ h.1
      . try rw [is_positive_application] at h
        try rw [is_positive_implication] at h
        exact ih₂ h.2
    | existential x ψ ih =>
      constructor
      rw [is_positive_existential] at h
      exact ih h
    | _ => constructor


section
  variable {𝕊 : Type} {φ ψ χ : Pattern 𝕊} {x y : EVar} {X Y : SVar}

  /--
    Like `repeat` but with an upper limit.
  -/
  syntax "repeat_bounded" num tacticSeq : tactic
  macro_rules
  | `(tactic| repeat_bounded $n:num $seq:tacticSeq) =>
    open Lean in
      let n := Syntax.toNat n
      if n == 0 then
        `(tactic| skip)
      else
        `(tactic| first | ($seq) ; repeat_bounded $(quote (n - 1)) $seq | skip)

  -- TODO use a settable option instead of hardcoded constant

  /--
    Tries to prove the well-formedness of a pattern by brute-force, unintelligent means.
  -/
  syntax "autopos" : tactic
  macro_rules | `(tactic| autopos) => `(tactic| (repeat_bounded 300 (constructor <;> try assumption)) ; done)
  macro_rules | `(tactic| autopos) => `(tactic| assumption)
  macro_rules | `(tactic| autopos) => `(tactic| (simp only [positive_equivalent] at * ; simp [*] at *) ; done)

  syntax "autoposc" : tactic
  macro_rules | `(tactic| autoposc) => `(tactic| (apply ML.AppContext.wf_insert <;> autopos) ; done)

  @[simp] theorem positive_implication : Positive (φ ⇒ ψ) ↔ Positive φ ∧ Positive ψ := by
    apply Iff.intro <;> intros h
    . cases h
      constructor <;> assumption
    . cases h ; autopos

  @[simp] theorem positive_application : Positive (φ ⬝ ψ) ↔ Positive φ ∧ Positive ψ := by
    apply Iff.intro <;> intros h
    . cases h
      constructor <;> assumption
    . cases h ; autopos

  @[simp] theorem positive_existential : Positive (∃∃ x φ) ↔ Positive φ := by
    apply Iff.intro <;> intros h
    . cases h ; assumption
    . autopos

  @[simp] theorem positive_symbol {σ : 𝕊} : Positive (symbol σ) := by autopos

  @[simp] theorem positive_evar : Positive (@evar 𝕊 x) := by autopos

  @[simp] theorem positive_svar : Positive (@svar 𝕊 X) := by autopos

  @[simp] theorem positive_bottom : Positive (⊥ : Pattern 𝕊) := by autopos

  @[simp] theorem positive_negation : Positive (∼φ) ↔ Positive φ := by
    apply Iff.intro <;> intros h
    . cases h
      assumption
    . autopos

  @[simp] theorem positive_disjunction : Positive (φ ⋁ ψ) ↔ Positive φ ∧ Positive ψ := by
    apply Iff.intro <;> intros h
    . cases h
      rw [positive_negation] at *
      constructor <;> assumption
    . cases h
      autopos

  @[simp] theorem positive_conjunction : Positive (φ ⋀ ψ) ↔ Positive φ ∧ Positive ψ := by
    apply Iff.intro <;> intros h
    . cases h
      rw [positive_disjunction, positive_negation, positive_negation] at *
      assumption
    . cases h
      autopos

  set_option maxHeartbeats 500000
  theorem no_negative_positive_occ_subst_evar (x y : EVar) (X : SVar) :
    (¬φ.hasNegativeOcc X /-∧-/ → ¬(φ.substEvar x y).hasNegativeOcc X) ∧
    (¬φ.hasPositiveOcc X → ¬(φ.substEvar x y).hasPositiveOcc X) := by
    induction φ with
    | evar z =>
      by_cases h : x = z
      . simp [*]
      . simp [*]
    | implication φ₁ φ₂ ih₁ ih₂ =>
      cases ih₁ with | intro ih₁₁ ih₁₂ =>
      cases ih₂ with | intro ih₂₁ ih₂₂ =>
      apply And.intro
      . intros h
        simp only [Bool.not_eq_true] at *
        rw [← Bool.not_eq_true, has_negative_occ_implication, not_or, Bool.not_eq_true, Bool.not_eq_true] at h
        specialize ih₁₂ h.1
        specialize ih₂₁ h.2
        rw [substEvar, ← Bool.not_eq_true, has_negative_occ_implication, not_or, Bool.not_eq_true, Bool.not_eq_true]
        exact And.intro ih₁₂ ih₂₁
      . intros h
        simp only [Bool.not_eq_true] at *
        rw [← Bool.not_eq_true, has_positive_occ_implication, not_or, Bool.not_eq_true, Bool.not_eq_true] at h
        specialize ih₁₁ h.1
        specialize ih₂₂ h.2
        rw [substEvar, ← Bool.not_eq_true, has_positive_occ_implication, not_or, Bool.not_eq_true, Bool.not_eq_true]
        exact And.intro ih₁₁ ih₂₂
    | application φ₁ φ₂ ih₁ ih₂ =>
      cases ih₁ with | intro ih₁₁ ih₁₂ =>
      cases ih₂ with | intro ih₂₁ ih₂₂ =>
      apply And.intro <;> intros h <;> simp? [*] at *
      . exact And.intro (ih₁₁ h.1) (ih₂₁ h.2)
      . exact And.intro (ih₁₂ h.1) (ih₂₂ h.2)
    | existential z φ' ih =>
      apply And.intro <;>
      simp [*] at * <;>
      intros h <;>
      by_cases h' : x = z <;>
      simp [*]
    | mu Y φ' ih =>
      apply And.intro <;> intros h
      . cases ih with | intro ih₁ ih₂ =>
        simp [*] at *
        exact ih₁ h
      . cases ih with | intro ih₁ ih₂ =>
        simp [*] at *
        exact ih₂ h
    | _ => simp [*] at *


  theorem no_negative_occ_subst_evar (x y : EVar) (X : SVar) :
    ¬φ.hasNegativeOcc X → ¬(φ.substEvar x y).hasNegativeOcc X :=
    (no_negative_positive_occ_subst_evar _ _ _).1

  theorem no_positive_occ_subst_evar (x y : EVar) (X : SVar) :
    ¬φ.hasPositiveOcc X → ¬(φ.substEvar x y).hasPositiveOcc X := (no_negative_positive_occ_subst_evar _ _ _).2



  theorem no_free_negative_positive_occ_subst_evar (x y : EVar) (X : SVar) :
    (¬φ.hasFreeNegativeOcc X /-∧-/ → ¬(φ.substEvar x y).hasFreeNegativeOcc X) ∧
    (¬φ.hasFreePositiveOcc X → ¬(φ.substEvar x y).hasFreePositiveOcc X) := by
    induction φ with
    | evar z =>
      by_cases h : x = z
      . simp [*]
      . simp [*]
    | implication φ₁ φ₂ ih₁ ih₂ =>
      cases ih₁ with | intro ih₁₁ ih₁₂ =>
      cases ih₂ with | intro ih₂₁ ih₂₂ =>
      apply And.intro
      . intros h
        simp [*] at *
        specialize ih₁₂ h.1
        specialize ih₂₁ h.2
        exact And.intro ih₁₂ ih₂₁
      . intros h
        simp [*] at *
        specialize ih₁₁ h.1
        specialize ih₂₂ h.2
        exact And.intro ih₁₁ ih₂₂
    | application φ₁ φ₂ ih₁ ih₂ =>
      cases ih₁ with | intro ih₁₁ ih₁₂ =>
      cases ih₂ with | intro ih₂₁ ih₂₂ =>
      apply And.intro <;> intros h <;> simp [*] at *
      . exact And.intro (ih₁₁ h.1) (ih₂₁ h.2)
      . exact And.intro (ih₁₂ h.1) (ih₂₂ h.2)
    | existential z φ' ih =>
      apply And.intro <;>
      simp [*] at * <;>
      intros h <;>
      by_cases h' : x = z <;>
      simp [*]
    | mu Y φ' ih =>
      apply And.intro <;> intros h
      . cases ih with | intro ih₁ ih₂ =>
        by_cases h' : X = Y
        . simp [*] at *
        . simp [*] at *
          exact ih₁ h
      . cases ih with | intro ih₁ ih₂ =>
        by_cases h' : X = Y
        . simp [*] at *
        . simp [*] at *
          exact ih₂ h
    | _ => simp [*] at *


  theorem no_free_negative_occ_subst_evar (x y : EVar) (X : SVar) :
    ¬φ.hasFreeNegativeOcc X → ¬(φ.substEvar x y).hasFreeNegativeOcc X :=
    (no_free_negative_positive_occ_subst_evar _ _ _).1

  theorem no_free_positive_occ_subst_evar (x y : EVar) (X : SVar) :
    ¬φ.hasFreePositiveOcc X → ¬(φ.substEvar x y).hasFreePositiveOcc X :=
    (no_free_negative_positive_occ_subst_evar _ _ _).2

  theorem positive_subst_evar (x y : EVar) : Positive φ → Positive (φ.substEvar x y) := by
    intros wf
    induction φ with
    | evar z =>
      by_cases h : x = z
      . simp [*]
      . simp [*]
    | implication φ₁ φ₂ ih₁ ih₂ | application φ₁ φ₂ ih₁ ih₂ =>
      cases wf
      specialize ih₁ (by assumption)
      specialize ih₂ (by assumption)
      simp [*]
    | existential z φ' ih =>
      cases wf
      specialize ih (by assumption)
      by_cases h : x = z
      . simp [*]
      . simp [*]
    | mu X φ' ih =>
      cases wf
      specialize ih (by assumption)
      constructor
      . assumption
      . apply no_free_negative_occ_subst_evar
        assumption
    | _ =>
      constructor


  set_option maxHeartbeats 1000000 in
  theorem no_free_negative_positive_occ_subst_svar (X Y : SVar) (φ ψ : Pattern 𝕊) (no_neg_occ : ¬ψ.isFreeSvar Y) (hXY : X ≠ Y) (sfi : ψ.substitutableForSvarIn X φ) :
    (¬φ.hasFreeNegativeOcc Y → ¬(φ.substSvar X ψ).hasFreeNegativeOcc Y) ∧
    (¬φ.hasFreePositiveOcc Y → ¬(φ.substSvar X ψ).hasFreePositiveOcc Y) := by
    induction φ with
    | svar Z =>
      by_cases h : X = Z <;> by_cases h' : Y = Z
      . simp [*] at *
      . simp [*] at *
        apply And.intro
        . have := (contraposition.1 <| fv_of_free_negative_occ ψ Y)
          simp at this
          exact this no_neg_occ
        . have := (contraposition.1 <| fv_of_free_positive_occ ψ Y)
          simp at this
          exact this no_neg_occ
      . simp [*] at *
      . simp [*] at *
    | implication φ₁ φ₂ ih₁ ih₂ =>
      simp at sfi
      cases sfi with | intro sfi₁ sfi₂ =>
      specialize ih₁ sfi₁
      specialize ih₂ sfi₂
      cases ih₁ with | intro ih₁₁ ih₁₂ =>
      cases ih₂ with | intro ih₂₁ ih₂₂ =>
      apply And.intro
      . intros h
        simp [*] at *
        specialize ih₁₂ h.1
        specialize ih₂₁ h.2
        exact And.intro ih₁₂ ih₂₁
      . intros h
        simp [*] at *
        specialize ih₁₁ h.1
        specialize ih₂₂ h.2
        exact And.intro ih₁₁ ih₂₂
    | mu Z φ' ih =>
      by_cases h : X = Z
      . simp [*] at *
      . have := substitutable_svar_of_mu h sfi
        specialize ih this
        cases ih with | intro ih₁ ih₂ =>
        apply And.intro
        . intros h
          by_cases h' : Y = Z
          . simp [*] at *
          . simp [*] at *
            exact ih₁ h
        . intros h
          by_cases h' : Y = Z
          . simp [*] at *
          . simp [*] at *
            exact ih₂ h
    | application φ₁ φ₂ ih₁ ih₂ =>
      simp at sfi
      cases sfi with | intro sfi₁ sfi₂ =>
      specialize ih₁ sfi₁
      specialize ih₂ sfi₂
      cases ih₁ with | intro ih₁₁ ih₁₂ =>
      cases ih₂ with | intro ih₂₁ ih₂₂ =>
      apply And.intro <;> intros h <;> simp [*] at *
      . exact And.intro (ih₁₁ h.1) (ih₂₁ h.2)
      . exact And.intro (ih₁₂ h.1) (ih₂₂ h.2)
    | existential x φ' ih =>
      have := substitutable_evar_of_exist sfi
      by_cases h' : isFreeSvar φ' X
      .
        simp [*] at *
        cases ih with | intro ih₁ ih₂ =>
        apply And.intro
        . intros h
          simp [*] at *
        . intros h
          simp [*] at *
      . simp [*] at * --mindfuck

    | _ => simp [*] at *



  theorem positive_subst_svar (X : SVar) (ψ : Pattern 𝕊) (sfi : ψ.substitutableForSvarIn X φ) (wfψ : ψ.Positive) :
    Positive φ → Positive (φ.substSvar X ψ) := by
    intros h
    induction φ with
    | svar Y =>
      by_cases h' : X = Y
      . simp [*]
      . simp [*]
    | implication φ₁ φ₂ ih₁ ih₂ =>
      cases h with
      | implication h₁ h₂ =>
      simp at sfi
      constructor
      . exact ih₁ sfi.1 h₁
      . exact ih₂ sfi.2 h₂
    | mu Y φ' ih =>
      by_cases h' : X = Y
      . simpa [h']
      .
        have sfi' : substitutableForSvarIn X ψ φ' := substitutable_svar_of_mu h' sfi
        by_cases h'' : φ'.isFreeSvar X
        . simp [*] at sfi
          simp [*]
          cases h with | mu h nonneg =>
          constructor
          . exact ih sfi' h
          . have := no_free_negative_positive_occ_subst_svar X Y φ' ψ
            simp at this nonneg
            specialize this sfi h' sfi'
            have := this.1 nonneg
            simp [*]
        . simp [*]
    | application φ₁ φ₂ ih₁ ih₂ =>
      cases h with | application h₁ h₂ =>
      simp at sfi
      specialize ih₁ sfi.1 h₁
      specialize ih₂ sfi.2 h₂
      simp [*]
    | existential x φ' ih =>
      by_cases h' : φ'.isFreeSvar X
      . simp [*] at sfi
        cases h with | existential h =>
        specialize ih sfi.2 h
        simp [*]
      . simp_all
    | _ => simp [*] at *





  macro_rules
  | `(tactic| autopos) => `(tactic| simp [*, positive_subst_evar] at * ; done)

end

/-
  Sanity checks
-/
namespace Hidden
  def X : SVar := ⟨0⟩
  def Y : SVar := ⟨1⟩

  def φ₀ : Pattern Empty := μ X X
  def φ₁ : Pattern Empty := μ X (X ⇒ ⊥)
  def φ₂ : Pattern Empty := (μ X (X ⇒ ⊥)) ⇒ ⊥
  def φ₃ : Pattern Empty := μ X (μ Y (Y ⇒ X))

  #eval φ₁.isPositive

  example : φ₀.isPositive = true := by decide
  example : φ₁.isPositive = false := by decide
  example : φ₂.isPositive = false := by decide
  example : φ₃.isPositive = false := by decide
end Hidden
