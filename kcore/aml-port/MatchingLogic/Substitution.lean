/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Horațiu Cheval, Bogdan Macovei
-/

import MatchingLogic.Pattern

set_option autoImplicit false

namespace ML.Pattern



section EVarSubstitution
  variable {𝕊 : Type}


  @[simp]
  def substEvar (φ : Pattern 𝕊) (x : EVar) (χ : Pattern 𝕊) : Pattern 𝕊 :=
  match φ with
  | evar y => if x = y then χ else evar y
  | v@(svar _) => v
  | ∃∃ y φ =>
    if x = y then
      ∃∃ y φ -- don't substitute a bound variable
    else
      ∃∃ y (φ.substEvar x χ)
  | μ Y φ => μ Y (φ.substEvar x χ)
  | φ ⬝ ψ => (φ.substEvar x χ) ⬝ (ψ.substEvar x χ)
  | φ ⇒ ψ => (φ.substEvar x χ) ⇒ (ψ.substEvar x χ)
  | σ@(symbol _) => σ
  | ⊥ => bottom

  -- WHICH IS BETTER?
  notation φ "[" x " ⇐ " ψ "]ᵉ" => substEvar φ x ψ
  notation φ "[" x " ⇐ᵉ " ψ "]" => substEvar φ x ψ

  section variable {φ ψ : Pattern 𝕊} {x : EVar} {χ : Pattern 𝕊}

  -- Definitional lemmas

  @[simp] theorem subst_evar_implication :
      (φ ⇒ ψ)[x ⇐ᵉ χ] = φ[x ⇐ᵉ χ] ⇒ ψ[x ⇐ᵉ χ] := by rfl

  @[simp] theorem subst_evar_application :
      (φ ⬝ ψ)[x ⇐ᵉ χ] = φ[x ⇐ᵉ χ] ⬝ ψ[x ⇐ᵉ χ] := by rfl

  @[simp] theorem subst_evar_symbol {σ : 𝕊} :
    (.symbol σ)[x ⇐ᵉ χ] = (.symbol σ) := by rfl

  @[simp] theorem subst_evar_svar {X : SVar} :
    X[x ⇐ᵉ χ] = X := by rfl

  @[simp] theorem subst_evar_same {x : EVar} :
    x[x ⇐ᵉ χ] = χ := by simp

  @[simp] theorem subst_evar_distinct {x y : EVar} :
    x ≠ y → y[x ⇐ᵉ χ] = y := by intros h; simp [h]

  @[simp] theorem subst_evar_exist_same  :
    (∃∃ x φ)[x ⇐ᵉ χ] = ∃∃ x φ := by simp

  @[simp] theorem subst_evar_exist_distinct {y : EVar }:
    x ≠ y → (∃∃ y φ)[x ⇐ᵉ χ] = ∃∃ y (φ[x ⇐ᵉ χ]) := by intros h; simp [h]

  @[simp] theorem subst_evar_mu {X : SVar }:
    (μ X φ)[x ⇐ᵉ χ] = μ X (φ[x ⇐ᵉ χ]) := by rfl

  end

  -- inductive SubstitutableEvar (x : EVar) (ψ : Pattern 𝕊) : Pattern 𝕊 → Prop where
  -- | existential (y : EVar) (φ : Pattern 𝕊) : (∃∃ y φ).isFreeEvar x → ¬φ.isFreeEvar x ∧ SubstitutableEvar x ψ φ → SubstitutableEvar x ψ (∃∃ y φ)

  -- **WARNING** This definition only makes sense when `psi` is of the form `evar y`.
  @[simp]
  def substitutableForEvarIn (x : EVar) (ψ : Pattern 𝕊) : Pattern 𝕊 → Prop
  | ∃∃ y φ =>
    if (∃∃ y φ).isFreeEvar x then
      ¬ψ.isFreeEvar y ∧ substitutableForEvarIn x ψ φ
    else
      true
  | μ _ φ => substitutableForEvarIn x ψ φ
  | φ₁ ⬝ φ₂ | φ₁ ⇒ φ₂ => substitutableForEvarIn x ψ φ₁ ∧ substitutableForEvarIn x ψ φ₂
  | _ => true

  -- Definitional lemmas

  -- @[simp] theorem substitutable_evar_of_exist : False := sorry

  theorem substitutable_evar_of_not_free_occ {φ ψ : Pattern 𝕊} {x : EVar} : ¬φ.isFreeEvar x → substitutableForEvarIn x ψ φ := by
    intros h
    induction φ with
    | existential y φ' ih =>
      -- simp at *
      -- specialize ih h
      by_cases h' : x = y
      . simp_all
      . simp_all
    | implication φ₁ φ₂ ih₁ ih₂ | application φ₁ φ₂ ih₁ ih₂ =>
      simp_all
    | mu _ φ' ih =>
      simp only [substitutableForEvarIn] at *
      exact ih h
    | _ => simp

  theorem substitutable_evar_same (x : EVar) (φ : Pattern 𝕊) : substitutableForEvarIn x x φ := by
    induction φ with
    | evar y =>
      by_cases h : x = y
      . simp [*] at *
      . simp [*] at *
    | existential y φ' ih =>
      by_cases h : (∃∃ y φ').isFreeEvar x
      . by_cases h' : y = x
        . simp [*] at *
        . simp [*] at *
      . have := @substitutable_evar_of_not_free_occ _ _ x _ h
        exact this
    | _ => simp [*] at *

  theorem substitutable_evar_of_not_occ {φ ψ : Pattern 𝕊} {x : EVar} : ¬φ.isEvar x → substitutableForEvarIn x ψ φ :=
    fun h => substitutable_evar_of_not_free_occ <| contraposition.1 evar_of_free_evar h


  @[simp]
  theorem subst_var_var_eq_self_evar (φ : Pattern 𝕊) (x : EVar) : φ.substEvar x (.evar x) = φ := by
    induction φ with
    | evar y =>
      by_cases h : x = y <;> simp [*]
    | _ => simp [*]


  @[simp]
  theorem subst_not_free_evar (φ : Pattern 𝕊) (x : EVar) (ψ : Pattern 𝕊) (not_fv : ¬φ.isFreeEvar x) : φ.substEvar x ψ = φ := by
    induction φ with
    | evar y =>
      by_cases h : x = y
      . simp [*] at *
      . simp [*] at *
    | existential y φ' ih =>
      by_cases h : x = y
      . simp [*] at *
      . simp only [*, substEvar, Bool.not_eq_true, ite_false, existential.injEq, true_and, isFreeEvar] at *
        specialize ih not_fv
        simp [*] at *
    | implication φ' φ'' ih' ih'' | application φ' φ'' ih' ih'' =>
      simp_all only [Bool.not_eq_true, isFreeEvar, Bool.decide_or, Bool.decide_coe, Bool.or_eq_true, not_or, substEvar]
    | mu X φ' ih' =>
      simp_all only [Bool.not_eq_true, isFreeEvar, substEvar]
    | _ => simp [*]


  -- TO DECIDE BETWEEN THE FOLLOWING DEFINITIONS

  @[simp]
  def renameEvar (φ : Pattern 𝕊) (x : EVar) (y : EVar) (boundOcc : Bool := false) : Pattern 𝕊 :=
  match φ with
  | evar z =>
    if boundOcc then
      if x = z then evar y else evar z
    else evar z
  | ∃∃ z φ => if x = z then ∃∃ y (φ.renameEvar x y true) else ∃∃ z (φ.renameEvar x y boundOcc)
  | μ X φ => μ X $ φ.renameEvar x y boundOcc
  | φ ⇒ ψ => φ.renameEvar x y boundOcc ⇒ ψ.renameEvar x y boundOcc
  | φ ⬝ ψ => φ.renameEvar x y boundOcc ⬝ ψ.renameEvar x y boundOcc
  | φ@_ => φ

  @[simp]
  def renameEvar' (φ : Pattern 𝕊) (x : EVar) (y : EVar) : Pattern 𝕊 :=
  match φ with
  | ∃∃ z φ =>
    if x = z then
      ∃∃ y (((φ.renameEvar' x y)).substEvar x y)
    else
      ∃∃ z (φ.renameEvar' x y)
  | μ X φ => μ X $ φ.renameEvar x y
  | φ ⇒ ψ => φ.renameEvar x y ⇒ ψ.renameEvar x y
  | φ ⬝ ψ => φ.renameEvar x y ⬝ ψ.renameEvar x y
  | φ@_ => φ

end EVarSubstitution











section SVarSubstitution
  variable {𝕊 : Type}

  @[simp]
  def substSvar (φ : Pattern 𝕊) (X : SVar) (χ : Pattern 𝕊) : Pattern 𝕊 :=
  match φ with
  | svar Y => if X = Y then χ else svar Y
  | v@(evar _) => v
  | μ Y φ => if X = Y then μ Y φ else μ Y (φ.substSvar X χ)
  | ∃∃ x φ => ∃∃ x (φ.substSvar X χ)
  | φ ⬝ ψ => (φ.substSvar X χ) ⬝ (ψ.substSvar X χ)
  | φ ⇒ ψ => (φ.substSvar X χ) ⇒ (ψ.substSvar X χ)
  | σ@(symbol _) => σ
  | ⊥ => bottom

  notation φ "[" x " ⇐ " ψ "]ˢ" => substSvar φ x ψ
  notation φ "[" x " ⇐ˢ " ψ "]" => substSvar φ x ψ

  section variable {φ ψ : Pattern 𝕊} {X : SVar} {χ : Pattern 𝕊}

    @[simp] theorem subst_svar_implication :
        (φ ⇒ ψ)[X ⇐ˢ χ] = φ[X ⇐ˢ χ] ⇒ ψ[X ⇐ˢ χ] := by rfl

    @[simp] theorem subst_svar_application :
        (φ ⬝ ψ)[X ⇐ˢ χ] = φ[X ⇐ˢ χ] ⬝ ψ[X ⇐ˢ χ] := by rfl

    @[simp] theorem subst_svar_symbol {σ : 𝕊} :
      (.symbol σ)[X ⇐ˢ χ] = (.symbol σ) := by rfl

    @[simp] theorem subst_svar_same :
      X[X ⇐ˢ χ] = χ := by simp

    @[simp] theorem subst_svar_distinct {Y : SVar} :
      X ≠ Y → Y[X ⇐ˢ χ] = Y := by intros h; simp [h]

    @[simp] theorem subst_svar_mu_same  :
      (μ X φ)[X ⇐ˢ χ] = μ X φ := by simp

    @[simp] theorem subst_svar_exist_distinct {Y : SVar}:
      X ≠ Y → (μ Y φ)[X ⇐ˢ χ] = μ Y (φ[X ⇐ˢ χ]) := by intros h; simp [h]

    @[simp] theorem subst_svar_exist {x : EVar}:
      (∃∃ x φ)[X ⇐ˢ χ] = ∃∃ x (φ[X ⇐ˢ χ]) := by rfl

  end

  /-- `substitutableForSvarIn X ψ φ ` means that `ψ` is substiutable for `X` in `φ`,
      in other words the substitution `φ[X ⇐ ψ]` is capture-avoiding.
  -/
  @[simp]
  def substitutableForSvarIn (X : SVar) (ψ : Pattern 𝕊) : Pattern 𝕊 → Bool
  | μ Y φ =>
    if (μ Y φ).isFreeSvar X then
      ¬ψ.isFreeSvar Y ∧ substitutableForSvarIn X ψ φ
    else
      true
  | ∃∃ y φ =>
    if (∃∃ y φ).isFreeSvar X then
      ¬ψ.isFreeEvar y ∧ substitutableForSvarIn X ψ φ
    else
      true
  | φ₁ ⬝ φ₂ | φ₁ ⇒ φ₂ => substitutableForSvarIn X ψ φ₁ ∧ substitutableForSvarIn X ψ φ₂
  | _ => true

  theorem substitutable_svar_of_not_free_occ {φ ψ : Pattern 𝕊} {X : SVar} : ¬φ.isFreeSvar X → substitutableForSvarIn X ψ φ := by
    intros h
    induction φ with
    | mu Y φ' ih =>
      -- simp at *
      -- specialize ih h
      by_cases h' : X = Y
      . simp [*]
      . simp [*] at *
        simp [*]
    | implication φ₁ φ₂ ih₁ ih₂ | application φ₁ φ₂ ih₁ ih₂ =>
      simp at *
      exact ⟨ih₁ h.1, ih₂ h.2⟩
    | existential y φ' ih =>
      simp [*] at * -- why is simp
      simp [*] at *
    | _ => simp

  theorem substitutable_svar_of_not_occ {φ ψ : Pattern 𝕊} {X : SVar} : ¬φ.isSvar X → substitutableForSvarIn X ψ φ :=
    fun h => substitutable_svar_of_not_free_occ <| contraposition.1 svar_of_free_svar h

  theorem substitutable_svar_into_closed {φ ψ : Pattern 𝕊} {X : SVar} : φ.muClosed → ψ.substitutableForSvarIn X φ :=
    fun h => substitutable_svar_of_not_free_occ <| h _

  theorem substitutable_svar_of_closed {φ ψ : Pattern 𝕊} {X : SVar} : ψ.muClosed ∧ ψ.existClosed → ψ.substitutableForSvarIn X φ := by
    intros h
    cases h with | intro h₁ h₂ =>
    induction φ with
    | mu Y φ' ih =>
      by_cases h' : X = Y
      . simp [*]
      . specialize h₁ Y
        simp [*]
    | existential y φ' ih =>
      specialize h₂ y
      by_cases h' : φ'.isFreeSvar X
      . simp [*] at *
      . simp [*] at *
    | _ => simp [*] at *


  theorem substitutable_evar_of_exist {φ ψ : Pattern 𝕊} {X : SVar} {x : EVar} : ψ.substitutableForSvarIn X (∃∃ x φ) → ψ.substitutableForSvarIn X φ := by
    intros h
    by_cases hfv : φ.isFreeSvar X
    . simp_all [substitutableForSvarIn]
    . exact substitutable_svar_of_not_free_occ hfv


  theorem substitutable_svar_of_mu {φ ψ : Pattern 𝕊} {X Y : SVar} : X ≠ Y → ψ.substitutableForSvarIn X (μ Y φ) → ψ.substitutableForSvarIn X φ := by
    intros hXY h
    by_cases hfv : φ.isFreeSvar X
    . simp_all [substitutableForSvarIn]
    . exact substitutable_svar_of_not_free_occ hfv


  @[simp]
  theorem subst_var_var_eq_self_svar (φ : Pattern 𝕊) (X : SVar) : φ.substSvar X (.svar X) = φ := by
    induction φ with
    | svar Y =>
      by_cases h : X = Y <;> simp [*]
    | _ => simp [*]


  @[simp]
  theorem subst_not_free_svar (φ : Pattern 𝕊) (X : SVar) (ψ : Pattern 𝕊) (not_fv : ¬φ.isFreeSvar X) : φ.substSvar X ψ = φ := by
    induction φ with
    | svar Y =>
      by_cases h : X = Y
      . simp [*] at *
      . simp [*] at *
    | mu Y φ' ih =>
      by_cases h : X = Y
      . simp [*] at *
      . simp only [*, isFreeSvar, substSvar, Bool.not_eq_true, ite_false, mu.injEq, true_and] at *
        specialize ih not_fv
        simp [*] at *
    | implication φ' φ'' ih' ih'' | application φ' φ'' ih' ih'' =>
      simp_all only [Bool.not_eq_true, isFreeSvar, Bool.decide_or, Bool.decide_coe, Bool.or_eq_true, not_or, substSvar]
    | existential _ φ' ih' =>
      simp only [substSvar, Bool.not_eq_true, existential.injEq, true_and] at *
      specialize ih' not_fv
      simp [*]
    | _ => simp [*]


end SVarSubstitution
