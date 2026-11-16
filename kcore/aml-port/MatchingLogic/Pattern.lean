/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Horațiu Cheval
-/

import MatchingLogic.Variable

set_option autoImplicit false

namespace ML
/--
  Given a signature `𝕊 : Type`,
  `Pattern 𝕊` is the type of applicative matching μ-logic patterns over a signature `𝕊`.
  It is defined as a parametrized inductive type.
  The signature `𝕊` can be any type, intended to be read as the "type of symbols".
-/
inductive Pattern (𝕊 : Type) where
| evar : EVar → Pattern 𝕊
| svar : SVar → Pattern 𝕊
| /-- `Pattern.bottom` represents logical falsehood. -/
  bottom : Pattern 𝕊
| /-- `Pattern.symbol σ` is the pattern over signature `𝕊` constructed from a symbol `σ`, where `σ : 𝕊` -/
  symbol : 𝕊 → Pattern 𝕊
| /-- `Pattern.application φ ψ` is the application of `φ` in `ψ` -/
  application : Pattern 𝕊 → Pattern 𝕊 → Pattern 𝕊
| /-- `Pattern.implication φ ψ` is the implication from `φ` to `ψ` -/
  implication : Pattern 𝕊 → Pattern 𝕊 → Pattern 𝕊
| existential : EVar → Pattern 𝕊 → Pattern 𝕊
| mu : SVar → Pattern 𝕊 → Pattern 𝕊
deriving DecidableEq, Inhabited, Repr

namespace Pattern

section NotationsAndAbbreviations

  variable {𝕊 : Type} (φ ψ : Pattern 𝕊)

  /-- Notation for `Pattern.bottom` -/
  notation "⊥" => bottom

  /-- Notation for `Pattern.implication` -/
  infixr:60 (priority := high) " ⇒ " => implication

  /-- Notation for `Pattern.application` -/
  infixl:80 " ⬝ " => application

  /-- Notation for `Pattern.existential -/
  notation "∃∃" => existential

  /-- Notation for `Pattern.mu` -/
  notation "μ " => mu

  /-- Negation of a pattern. -/
  @[match_pattern] def negation := φ ⇒ ⊥
  prefix:70 "∼" => negation

  /-- Disjunction of two patterns. -/
  @[match_pattern] def disjunction := ∼φ ⇒ ψ
  /-- Notation for `Pattern.disjunction -/
  infixl:65 " ⋁ " => disjunction

  /-- Conjunction of two patterns. -/
  @[match_pattern] def conjunction := ∼(∼φ ⋁ ∼ψ)
  /-- Notation for `Pattern.conjunction` -/
  infixl:65 " ⋀ " => conjunction

  /-- The canonical "true" pattern, defined as the negation of `⊥`. -/
  @[match_pattern] def top : Pattern 𝕊 := ∼⊥
  /-- Notation for `Pattern.top` -/
  notation "⊤" => top

  /-- The equivalence (or bidirectional implication) of two patterns. -/
  @[match_pattern] def equivalence := (φ ⇒ ψ) ⋀ (ψ ⇒ φ)
  /-- Notation for `Pattern.equivalence` -/
  infix:50 " ⇔ " => equivalence

  /-- Universal quantification over a pattern. -/
  @[match_pattern] def universal (x : EVar) (φ : Pattern 𝕊) := ∼(∃∃ x (∼φ))
  /-- Notation for `Pattern.universal` -/
  notation "∀∀ " => universal

  instance : Coe EVar (Pattern 𝕊) := ⟨evar⟩

  instance : Coe SVar (Pattern 𝕊) := ⟨svar⟩

end NotationsAndAbbreviations


section Variables

  variable {𝕊 : Type}

  /--
    Returns all the element variables occuring in a pattern, as a list.
    The `x` in `∃∃ x φ` **is not** included
  -/
  @[simp]
  def evars : Pattern 𝕊 → List EVar
  | evar x => [x]
  | svar _ => []
  | ∃∃ _ φ => φ.evars
  | μ _ φ => φ.evars
  | φ ⇒ ψ | φ ⬝ ψ => φ.evars ++ ψ.evars
  | _ => []

  /--
    Returns all the element variables occuring in a pattern, as a list.
    The `x` in `∃∃ x φ` **is** included
  -/
  def allEVars : Pattern 𝕊 → List EVar
  | .evar x => [x]
  | .svar X => []
  | φ ⇒ ψ | φ ⬝ ψ => φ.allEVars ++ ψ.allEVars
  | ∃∃ x φ => x :: φ.allEVars
  | μ X φ => φ.allEVars
  | _ => []

  /-- Answers whether an element variable occurs in a pattern. -/
  @[simp]
  def isEvar (φ : Pattern 𝕊) (x : EVar) : Bool :=
  match φ with
  | evar y => if x = y then true else false
  | ∃∃ _ φ | μ _ φ => φ.isEvar x
  | φ ⬝ ψ | φ ⇒ ψ => φ.isEvar x ∨ ψ.isEvar x
  | _ => false

  theorem evar_equiv_def (φ : Pattern 𝕊) (x : EVar) : x ∈ φ.evars ↔ φ.isEvar x := by
    induction φ with
    | evar y =>
      by_cases h : x = y
      . simp_all
      . simp_all
    | _ => simp [*]

  def countEVar {𝕊} (x : EVar) (φ : Pattern 𝕊) : ℕ :=
    match φ with
    | evar y => if x = y then 1 else 0
    | svar _ => 0
    | ⊥ => 0
    | symbol _ => 0
    | φ ⇒ ψ => φ.countEVar x + ψ.countEVar x
    | φ ⬝ ψ => φ.countEVar x + ψ.countEVar x
    | ∃∃ _ φ => φ.countEVar x
    | μ _ φ => φ.countEVar x

  /-- Returns all element variables occurring free in a pattern, as a list. -/
  @[simp]
  def freeEvars : Pattern 𝕊 → List EVar
  | evar x => [x]
  | svar _ => []
  | ∃∃ x φ => φ.freeEvars.filter (. ≠ x)
  | μ _ φ => φ.freeEvars
  | φ ⇒ ψ | φ ⬝ ψ => φ.freeEvars ++ ψ.freeEvars
  | _ => []

  /-- Answers whether an element variable occurs free in a pattern. -/
  @[simp]
  def isFreeEvar (φ : Pattern 𝕊) (x : EVar) : Bool :=
  match φ with
  | evar y => if x = y then true else false
  | svar _ => false
  | ∃∃ y φ => if x = y then false else φ.isFreeEvar x
  | μ _ φ => φ.isFreeEvar x
  | φ ⇒ ψ | φ ⬝ ψ => φ.isFreeEvar x ∨ ψ.isFreeEvar x
  | _ => false

  theorem free_evar_equiv_def (φ : Pattern 𝕊) (x : EVar) : x ∈ φ.freeEvars ↔ φ.isFreeEvar x := by
    induction φ with
    | evar y =>
      by_cases h : x = y
      . simp_all
      . simp_all
    | existential y φ' ih =>
      apply Iff.intro <;> intros h
      . by_cases h' : x = y <;> simp_all
      . by_cases h' : x = y <;> simp_all
    | _ => simp_all

  theorem evar_of_free_evar {φ : Pattern 𝕊} {x : EVar} : φ.isFreeEvar x → φ.isEvar x := by
    induction φ with
    | existential y φ' ih =>
      by_cases h' : x = y <;> simp_all
    | implication φ₁ φ₂ ih₁ ih₂ | application φ₁ φ₂ ih₁ ih₂ =>
      intro h
      simp only [isFreeEvar, Bool.decide_or, decide_eq_true_eq, Bool.or_eq_true] at h
      simp only [isEvar, Bool.decide_or, decide_eq_true_eq, Bool.or_eq_true]
      exact h.elim (fun h => .inl (ih₁ h)) (fun h => .inr (ih₂ h))
    | _ => simp_all

  @[simp]
  theorem free_var_appl (φ ψ : Pattern 𝕊) (x : EVar) : (φ ⬝ ψ).isFreeEvar x ↔ φ.isFreeEvar x ∨ ψ.isFreeEvar x := by
    simp only [isFreeEvar, Bool.decide_or, Bool.decide_coe, Bool.or_eq_true]

  theorem exists_binds (φ : Pattern 𝕊) (x : EVar) : ¬(∃∃ x φ).isFreeEvar x := by
    simp_all

  @[simp]
  def hasBinderOnEvar (φ : Pattern 𝕊) (x : EVar) : Bool :=
  match φ with
  | ∃∃ y φ => if x = y then true else φ.hasBinderOnEvar x
  | μ _ φ => φ.hasBinderOnEvar x
  | φ ⬝ ψ | φ ⇒ ψ => φ.hasBinderOnEvar x ∨ ψ.hasBinderOnEvar x
  | _ => false

  -- we could also give a recursive definition for this,
  -- but that's a somewhat complicated definition.
  -- TO DECIDE
  @[simp]
  def isBoundEvar (φ : Pattern 𝕊) (x : EVar) : Bool := φ.isEvar x ∧ ¬φ.isFreeEvar x

  instance {φ : Pattern Empty} {x : EVar} : Decidable (isFreeEvar φ x) := inferInstance

  @[simp]
  theorem not_free_evar_exist (φ : Pattern 𝕊) (x : EVar) : ¬(∃∃ x φ).isFreeEvar x := by
    intros h
    induction φ <;> simp at h



  @[simp]
  def svars : Pattern 𝕊 → List SVar
  | evar _ => []
  | svar X => [X]
  | ∃∃ _ φ | μ _ φ => φ.svars
  | φ ⇒ ψ | φ ⬝ ψ => φ.svars ++ ψ.svars
  | _ => []

  def allSVars : Pattern 𝕊 → List SVar
  | .evar x => []
  | .svar X => [X]
  | φ ⇒ ψ | φ ⬝ ψ => φ.allSVars ++ ψ.allSVars
  | ∃∃ x φ => φ.allSVars
  | μ X φ => X :: φ.allSVars
  | _ => []

  @[simp]
  def isSvar (φ : Pattern 𝕊) (X : SVar) : Bool :=
  match φ with
  | svar Y => if X = Y then true else false
  | ∃∃ _ φ | μ _ φ => φ.isSvar X
  | φ ⬝ ψ | φ ⇒ ψ => φ.isSvar X ∨ ψ.isSvar X
  | _ => false



  @[simp]
  def freeSvars : Pattern 𝕊 → List SVar
  | evar _ => []
  | svar X => [X]
  | ∃∃ _ φ => φ.freeSvars
  | μ X φ => φ.freeSvars.filter (. ≠ X)
  | φ ⇒ ψ | φ ⬝ ψ => φ.freeSvars ++ ψ.freeSvars
  | _ => []

  @[simp]
  def isFreeSvar (φ : Pattern 𝕊) (X : SVar) : Bool :=
  match φ with
  | svar Y => if X = Y then true else false
  | evar _ => false
  | μ Y φ => if X = Y then false else φ.isFreeSvar X
  | ∃∃ _ φ => φ.isFreeSvar X
  | φ ⇒ ψ | φ ⬝ ψ => φ.isFreeSvar X ∨ ψ.isFreeSvar X
  | _ => false

  @[simp]
  theorem not_free_svar_mu (φ : Pattern 𝕊) (X : SVar) : ¬(μ X φ).isFreeSvar X := by
    intros h
    induction φ <;> simp at h

  theorem svar_of_free_svar {φ : Pattern 𝕊} {X : SVar} : φ.isFreeSvar X → φ.isSvar X := by
    induction φ with
    | mu Y φ' ih =>
      by_cases h' : X = Y <;> simp_all
    | implication φ₁ φ₂ ih₁ ih₂ | application φ₁ φ₂ ih₁ ih₂ =>
      intro h
      simp only [isFreeSvar, Bool.decide_or, decide_eq_true_eq, Bool.or_eq_true] at h
      simp only [isSvar, Bool.decide_or, decide_eq_true_eq, Bool.or_eq_true]
      exact h.elim (fun h => .inl (ih₁ h)) (fun h => .inr (ih₂ h))
    | _ => simp_all

  @[simp]
  def getFreshEvar : Pattern 𝕊 → EVar
  | φ => .getFresh φ.evars

  -- there are various equivalent definitions of closedness that can be given.
  @[simp]
  def existClosed : Pattern 𝕊 → Prop
  | φ => ∀ x : EVar, ¬φ.isFreeEvar x

  @[simp]
  def muClosed : Pattern 𝕊 → Prop
  | φ => ∀ X : SVar, ¬φ.isFreeSvar X

  /-- Returns the number of `μ`'s present in a pattern. -/
  @[simp]
  def muCount : Pattern 𝕊 → ℕ
  | μ _ φ => φ.muCount + 1
  | φ ⬝ ψ | φ ⇒ ψ => φ.muCount + ψ.muCount
  | ∃∃ _ φ => φ.muCount
  | _ => 0

  /-- Returns the number of `∃`'s present in a pattern. -/
  @[simp]
  def existCount : Pattern 𝕊 → ℕ
  | ∃∃ _ φ => φ.existCount + 1
  | φ ⬝ ψ | φ ⇒ ψ => φ.existCount + ψ.existCount
  | μ _ φ => φ.existCount
  | _ => 0

  /-- Returns the highest number of nested `μ`'s in a pattern. -/
  @[simp]
  def muDepth : Pattern 𝕊 → ℕ
  | μ _ φ => φ.muDepth + 1
  | φ ⬝ ψ | φ ⇒ ψ => max φ.muDepth ψ.muDepth
  | ∃∃ _ φ => φ.muDepth
  | _ => 0

  /-- Returns the highest number of nested `∃`'s in a pattern. -/
  @[simp]
  def existDepth : Pattern 𝕊 → ℕ
  | ∃∃ _ φ => φ.existDepth + 1
  | φ ⬝ ψ | φ ⇒ ψ => max φ.existDepth ψ.existDepth
  | μ _ φ => φ.existDepth
  | _ => 0

end Variables


variable {𝕊 : Type}

@[simp]
def size {𝕊} : Pattern 𝕊 → ℕ
| evar _ | svar _ | ⊥ | symbol _ => 1
| φ ⇒ ψ | φ ⬝ ψ => φ.size + ψ.size + 1
| μ _ φ | ∃∃ _ φ => φ.size + 1

protected def toString [ToString 𝕊] (φ : Pattern 𝕊) : String :=
  match φ with
  | evar x => toString x
  | svar X => toString X
  | ⊥ => "⊥"
  | φ ⇒ ψ => s!"({φ.toString} ⇒ {ψ.toString})"
  | φ ⬝ ψ => s!"({φ.toString} ⬝ {ψ.toString})"
  | ∃∃ x φ => s!"(∃∃{toString x} {φ.toString})"
  | μ X φ => s!"(μ{toString X} {φ.toString})"
  | symbol σ => toString σ

-- theorem size_impl_left {φ ψ : Pattern 𝕊} : φ.size < (φ ⇒ ψ).size := by dsimp [size] ; linarith
-- theorem size_impl_right {φ ψ : Pattern 𝕊} : ψ.size < (φ ⇒ ψ).size := by dsimp [size] ; linarith
