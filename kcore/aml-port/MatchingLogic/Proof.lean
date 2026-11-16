/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Horațiu Cheval
-/

import MatchingLogic.Pattern
import MatchingLogic.Substitution
import MatchingLogic.Positivity
import MatchingLogic.AppContext
import MatchingLogic.Premises
import MatchingLogic.Tautology

set_option autoImplicit false

namespace ML

/--
  `Proof Γ φ` is the type of proof of pattern `φ` from the set of premises `Γ`.
  It is defined as an induction type, with constructors for each axiom and rule.
-/
inductive Proof {𝕊 : Type} (Γ : Premises 𝕊) : Pattern 𝕊 → Type where
| premise {φ : Pattern 𝕊} (hpos : φ.Positive) : φ ∈ Γ → Proof Γ φ
-- Propositional Axioms
| tautology {φ} (_ : Tautology φ)
  : Proof Γ φ
-- Propositional rules
| modusPonens {φ ψ}
  : Proof Γ φ → Proof Γ (φ ⇒ ψ) → Proof Γ ψ
-- FOL
-- We need to figure out how to properly do it.
| existQuan {φ} {x y} (sfi : (Pattern.evar y).substitutableForEvarIn x φ)
  : Proof Γ (φ.substEvar x (.evar y) ⇒ ∃∃ x φ)
| existGen {φ ψ} {x} (not_fv : ¬ψ.isFreeEvar x)
  : Proof (Γ) (φ ⇒ ψ) → Proof Γ ((∃∃ x φ) ⇒ ψ)
-- Technical rules
| existence {x}
  : Proof Γ $ ∃∃ x (.evar x)
| singleton {C₁ C₂ : AppContext 𝕊} {x : EVar} {φ}
  : Proof Γ $ ∼((C₁.insert $ .evar x ⋀ φ) ⋀ (C₂.insert $ .evar x ⋀ ∼φ))
-- Frame reasoning
| propagationBottomLeft {c}
  : Proof Γ $ c ⬝ ⊥ ⇒ ⊥
| propagationBottomRight {c}
  : Proof Γ $ ⊥ ⬝ c ⇒ ⊥
| propagationDisjLeft {φ ψ} {c}
  : Proof Γ $ (c ⬝ (φ ⋁ ψ)) ⇒ (c ⬝ φ) ⋁ (c ⬝ ψ)
| propagationDisjRight {φ ψ} {c}
  : Proof Γ $ ((φ ⋁ ψ) ⬝ c) ⇒ (φ ⬝ c) ⋁ (ψ ⬝ c)
| propagationExistLeft {φ} {x} {c} (not_fv : ¬c.isFreeEvar x)
  : (Proof Γ $ c ⬝ (∃∃ x φ) ⇒ ∃∃ x (c ⬝ φ))
| propagationExistRight {φ} {x} {c} (not_fv : ¬c.isFreeEvar x)
  : (Proof Γ $ (∃∃ x φ) ⬝ c ⇒ ∃∃ x (φ ⬝ c))
| framingLeft {φ ψ χ : Pattern 𝕊}
  : Proof Γ (φ ⇒ ψ) → Proof Γ (φ ⬝ χ ⇒ ψ ⬝ χ)
| framingRight {φ ψ χ : Pattern 𝕊} : Proof Γ (φ ⇒ ψ) → Proof Γ (χ ⬝ φ ⇒ χ ⬝ ψ)
-- Fixed point reasoning
| substitution {φ} {ψ} {X}
  : ψ.substitutableForSvarIn X φ → Proof Γ φ → Proof Γ (φ.substSvar X ψ)
| prefixpoint {φ} {X} (hpos : (μ X φ).Positive)
  : (μ X φ).substitutableForSvarIn X φ → Proof Γ ((φ.substSvar X (μ X φ)) ⇒ μ X φ)
| knasterTarski {φ ψ} {X}
  : ψ.substitutableForSvarIn X φ → Proof Γ ((φ.substSvar X ψ) ⇒ ψ) → Proof Γ (μ X φ ⇒ ψ)

infix:(arrow_precedence + 1) " ⊢ " => Proof

prefix:max "ᴹ" => Proof.modusPonens

namespace Proof

@[simp]
def size {𝕊} {Γ : Premises 𝕊} {φ : Pattern 𝕊} : Proof Γ φ → ℕ
| premise _ _ => 1
| tautology h  => 1
| modusPonens prf₁ prf₂ => prf₁.size + prf₂.size + 1
| existQuan _ => 1
| existGen _ prf => prf.size + 1
| existence => 1
| singleton => 1
| propagationBottomLeft => 1
| propagationBottomRight => 1
| propagationDisjLeft => 1
| propagationDisjRight => 1
| propagationExistLeft _ => 1
| propagationExistRight _ => 1
| framingLeft prf => prf.size + 1
| framingRight prf => prf.size + 1
| substitution _ prf => prf.size + 1
| prefixpoint _ _ => 1
| knasterTarski _ prf => prf.size + 1

/--
  Returns `true` iff a proof uses the the `knasterTarksi` rule.
-/
@[simp]
def usesKnasterTarski {𝕊} {Γ : Premises 𝕊} {φ : Pattern 𝕊} (prf : Proof Γ φ) : Bool :=
match prf with
-- The Axioms
| premise _ _ | tautology _
| existQuan _ | existence | singleton | propagationBottomLeft
| propagationBottomRight | propagationDisjLeft | propagationDisjRight
| propagationExistLeft _ | propagationExistRight _ | prefixpoint _ _
  => false
  -- Binary rules
| modusPonens prf₁ prf₂
  => prf₁.usesKnasterTarski ∨ prf₂.usesKnasterTarski
-- Unary rules
| existGen _ prf | framingLeft prf | framingRight prf
| substitution _ prf
  => prf.usesKnasterTarski
| knasterTarski _ _ => true

-- This has a very finicky termination proof.
-- Expect it to break on seemingly unrelated changes.
/--
  If `Γ ⊢ φ` and `Γ ⊆ Δ`, then `Δ ⊢ φ`
-/
def weaken {𝕊} {φ : Pattern 𝕊} {Γ Δ : Premises 𝕊} (h : Γ ⊆ Δ) : Γ ⊢ φ → Δ ⊢ φ
| premise hpos hmem => premise hpos (h hmem)
| tautology htauto => tautology htauto
| modusPonens prf₁ prf₂ =>
  have : prf₁.size < (modusPonens prf₁ prf₂).size := by simp [size, lt_add_succ_left, lt_add_succ_right]
  have : prf₂.size < (modusPonens prf₁ prf₂).size := by simp [size, lt_add_succ_left, lt_add_succ_right]
  modusPonens (prf₁.weaken h) (prf₂.weaken h)
| existQuan sfi => existQuan sfi
| existGen not_fv prf =>
  have : prf.size < (existGen not_fv prf).size := by simp [size, Nat.lt_succ_self]
  existGen not_fv (prf.weaken h)
| existence => existence
| singleton => singleton
| propagationBottomLeft => propagationBottomLeft
| propagationBottomRight => propagationBottomRight
| propagationDisjLeft => propagationDisjLeft
| propagationDisjRight => propagationDisjRight
| propagationExistLeft not_fv => propagationExistLeft not_fv
| propagationExistRight not_fv => propagationExistRight not_fv
| @framingLeft _ _ φ ψ χ prf =>
  have : prf.size < (@framingLeft _ _ φ ψ χ prf).size := by simp [size, Nat.lt_succ_self]
  framingLeft $ prf.weaken h
| @framingRight _ _ φ ψ χ prf =>
  have : prf.size < (@framingRight _ _ φ ψ χ prf).size := by simp [size, Nat.lt_succ_self]
  framingRight $ prf.weaken h
| substitution sfi prf =>
  have : prf.size < (substitution sfi prf).size := by simp [size, Nat.lt_succ_self]
  substitution sfi $ prf.weaken h
| prefixpoint hpos sfi => prefixpoint hpos sfi
| knasterTarski sfi prf =>
  have : prf.size < (knasterTarski sfi prf).size := by simp [size, Nat.lt_succ_self]
  knasterTarski sfi $ prf.weaken h
-- termination_by _ _ prf => prf.size
/-
  TODO: establish a naming convention for ML proofs
-/

section TheoremsAndRules

  section Propositional

    variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ θ : Pattern 𝕊}

    def weakeningDisj
      : Γ ⊢ φ ⇒ φ ⋁ ψ := tautology <| by
      intros M _ f _ m
      simp only [Morphism.morphism_impl, Morphism.morphism_disj]
      exact .inl

    def weakeningConj
      : Γ ⊢ φ ⋀ ψ ⇒ φ := tautology <| by
      intros M _ f _ m
      simp only [Morphism.morphism_impl, Morphism.morphism_conj]
      exact And.left

    def contractionDisj
      : Γ ⊢ φ ⋁ φ ⇒ φ := tautology <| by
      intros M _ f _ m
      simp only [Morphism.morphism_impl, Morphism.morphism_disj]
      intros h
      exact Or.elim h id id

    def contractionConj
      : Γ ⊢ φ ⇒ φ ⋀ φ := tautology <| by
      intros M _ f _ m
      simp only [Morphism.morphism_impl, Morphism.morphism_conj]
      intros h
      exact .intro h h

    def permutationDisj
      : Γ ⊢ φ ⋁ ψ ⇒ ψ ⋁ φ := tautology <| by
      intros M _ f _ m
      simp only [Morphism.morphism_impl, Morphism.morphism_disj]
      exact Or.comm.1

    def permutationConj
      : Γ ⊢ φ ⋀ ψ ⇒ ψ ⋀ φ := tautology <| by
      intros M _ f _ m
      simp only [Morphism.morphism_impl, Morphism.morphism_conj]
      exact And.comm.1

    def exFalso
      : Γ ⊢ ⊥ ⇒ φ := tautology <| by
      intros M _ f _ m
      simp only [Morphism.morphism_impl, Morphism.morphism_false]
      exact False.elim

    def excluddedMiddle
      : Γ ⊢ φ ⋁ ∼φ := tautology <| by
      intros M _ f _ m
      simp only [Morphism.morphism_disj, Morphism.morphism_neg]
      exact Classical.em _


    /--
      The same as `modusPonens`, but with the premises in a different order.
    -/
    def toRule (prf : Γ ⊢ φ ⇒ ψ) : Γ ⊢ φ → Γ ⊢ ψ :=
      fun prf' => modusPonens prf' prf

    /--
      `toRule` applied twice. Turns an implication with two hypotheses into a rule with two premises.
    -/
    def toRule2 (prf : Γ ⊢ φ ⇒ ψ ⇒ χ) : Γ ⊢ φ → Γ ⊢ ψ → Γ ⊢ χ :=
      fun prf' prf'' => toRule (toRule prf prf') prf''

    def syllogism : Γ ⊢ φ ⇒ ψ → Γ ⊢ ψ ⇒ χ → Γ ⊢ φ ⇒ χ :=
      let thm : Γ ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ (φ ⇒ χ) := tautology <| by
        intros _ _ _ _ _
        taut_morphism
      toRule2 thm

    def importation : Γ ⊢ φ ⇒ ψ ⇒ χ → Γ ⊢ φ ⋀ ψ ⇒ χ :=
      let thm : Γ ⊢ (φ ⇒ ψ ⇒ χ) ⇒ (φ ⋀ ψ ⇒ χ) := tautology <| by
        intros _ _ _ _ _
        taut_morphism

      toRule thm

    def exportation : Γ ⊢ φ ⋀ ψ ⇒ χ → Γ ⊢ φ ⇒ ψ ⇒ χ :=
      let thm : Γ ⊢ (φ ⋀ ψ ⇒ χ) ⇒ (φ ⇒ ψ ⇒ χ) := tautology <| by
        intros _ _ _ _ _
        taut_morphism
        -- exact h ⟨h', h''⟩
      toRule thm

    def expansion : Γ ⊢ φ ⇒ ψ → Γ ⊢ χ ⋁ φ ⇒ χ ⋁ ψ :=
      let thm : Γ ⊢ (φ ⇒ ψ) ⇒ (χ ⋁ φ ⇒ χ ⋁ ψ) := tautology <| by
        intros _ _ _ _ _
        taut_morphism
      toRule thm

    def disjIntroLeft
      : Γ ⊢ φ ⇒ φ ⋁ ψ :=
      weakeningDisj

    def disjIntroRight
      : Γ ⊢ φ ⇒ ψ ⋁ φ :=
      (syllogism) disjIntroLeft permutationDisj

    def disjImpl
      : Γ ⊢ (φ ⇒ ψ) ⋁ (φ ⇒ χ) ⇒ (φ ⇒ ψ ⋁ χ) := tautology <| by
      intros M _ f _ m
      taut_morphism

    def disjImpl2
      : Γ ⊢ (φ ⇒ ψ ⇒ χ) ⋁ (φ ⇒ ψ ⇒ θ) ⇒ (φ ⇒ ψ ⇒ χ ⋁ θ) := tautology <| by
      intros M _ f _ m
      taut_morphism

    def disjIntroAtHyp
      : Γ ⊢ φ ⇒ χ → Γ ⊢ ψ ⇒ χ → Γ ⊢ φ ⋁ ψ ⇒ χ :=
      fun l₁ : Γ ⊢ φ ⇒ χ =>
      let l₂ : Γ ⊢ χ ⋁ φ ⇒ χ ⋁ χ := (expansion) l₁
      let l₃ : Γ ⊢ χ ⋁ χ ⇒ χ := contractionDisj
      fun l₄ : Γ ⊢ ψ ⇒ χ =>
      let l₅ : Γ ⊢ φ ⋁ χ ⇒ χ ⋁ φ := permutationDisj
      let l₆ : Γ ⊢ χ ⋁ φ ⇒ χ := (syllogism) l₂ l₃
      let l₇ : Γ ⊢ φ ⋁ ψ ⇒ φ ⋁ χ := (expansion) l₄
      let l₈ : Γ ⊢ φ ⋁ χ ⇒ χ := (syllogism) l₅ l₆
      (syllogism) l₇ l₈

    def conjElimLeft
      : Γ ⊢ φ ⋀ ψ ⇒ φ := weakeningConj

    def conjElimRight
      : Γ ⊢ φ ⋀ ψ ⇒ ψ := (syllogism) permutationConj conjElimLeft

    def conjIntro
      : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ χ) ⇒ (φ ⇒ ψ ⋀ χ) := tautology <| by
      intros M _ f _ m
      taut_morphism

    def implProjLeft
      : Γ ⊢ φ ⇒ (ψ ⇒ φ) :=
      (exportation) weakeningConj

    def implProjRight
      : Γ ⊢ φ ⇒ ψ ⇒ ψ :=
      (exportation) conjElimRight

    def implSelf
      : Γ ⊢ φ ⇒ φ :=
      (syllogism) contractionConj weakeningConj

    def extraPremise
      : Γ ⊢ φ → Γ ⊢ ψ ⇒ φ := fun p =>
      modusPonens p implProjLeft

    def conjIntroRule
      : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ ⇒ χ → Γ ⊢ φ ⇒ ψ ⋀ χ :=
      let l₁ : Γ ⊢ ψ ⋀ χ ⇒ ψ ⋀ χ := implSelf
      let l₂ : Γ ⊢ ψ ⇒ χ ⇒ ψ ⋀ χ := (exportation) l₁
      fun l₃ : Γ ⊢ φ ⇒ ψ =>
      let l₄ : Γ ⊢ φ ⇒ χ ⇒ ψ ⋀ χ := (syllogism) l₃ l₂
      let l₅ : Γ ⊢ χ ⋀ φ ⇒ φ ⋀ χ := permutationConj
      let l₆ : Γ ⊢ φ ⋀ χ ⇒ ψ ⋀ χ := (importation) l₄

      let l₇ : Γ ⊢ χ ⋀ φ ⇒ ψ ⋀ χ := (syllogism) l₅ l₆
      fun l₈ : Γ ⊢ φ ⇒ χ =>
      let l₉ : Γ ⊢ χ ⇒ (φ ⇒ ψ ⋀ χ) := (exportation) l₇
      let l₁₀ : Γ ⊢ φ ⇒ φ ⇒ ψ ⋀ χ := (syllogism) l₈ l₉
      let l₁₁ : Γ ⊢ φ ⋀ φ ⇒ ψ ⋀ χ := (importation) l₁₀
      (syllogism) contractionConj l₁₁



    def conjIntroHypConcLeft
      : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ ⋀ χ ⇒ ψ ⋀ χ :=
      fun l₁ : Γ ⊢ φ ⇒ ψ =>
      let l₂ : Γ ⊢ φ ⋀ χ ⇒ χ := conjElimRight
      let l₃ : Γ ⊢ φ ⋀ χ ⇒ ψ := (syllogism) conjElimLeft l₁
      (conjIntroRule) l₃ l₂


    def modusPonensExtraHyp : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ ⇒ ψ ⇒ χ → Γ ⊢ φ ⇒ χ :=
      fun l₁ l₂ => (syllogism) ((conjIntroRule) implSelf l₁) ((importation) l₂)

    -- bad name
    def modusPonensThm : Γ ⊢ (φ ⇒ ψ ⇒ χ) ⋀ (φ ⇒ ψ) ⋀ φ ⇒ χ :=
      let ψ' := (φ ⇒ ψ ⇒ χ) ⋀ (φ ⇒ ψ)
      let φ' := ψ' ⋀ φ
      let l₁ : Γ ⊢ φ' ⇒ ψ' := conjElimLeft
      let l₂ : Γ ⊢ ψ' ⇒ φ ⇒ ψ := conjElimRight
      let l₃ : Γ ⊢ φ' ⇒ φ := conjElimRight
      let l₄ : Γ ⊢ φ' ⇒ φ ⇒ ψ := (syllogism) l₁ l₂
      let l₅ : Γ ⊢ φ' ⇒ ψ := (modusPonensExtraHyp) l₃ l₄
      let l₆ : Γ ⊢ ψ' ⇒ φ ⇒ ψ ⇒ χ := conjElimLeft
      let l₇ : Γ ⊢ φ' ⇒ φ ⇒ ψ ⇒ χ := (syllogism) l₁ l₆
      let l₈ : Γ ⊢ φ' ⇒ ψ ⇒ χ := (modusPonensExtraHyp) l₃ l₇
      let l₉ : Γ ⊢ φ' ⇒ χ := (modusPonensExtraHyp) l₅ l₈
      l₉

    def implDistribLeft : Γ ⊢ (φ ⇒ ψ ⇒ χ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ χ) :=
      (exportation) $ (exportation) modusPonensThm

    def implDistribRight : Γ ⊢ ((φ ⇒ ψ) ⇒ (φ ⇒ χ)) ⇒ (φ ⇒ ψ ⇒ χ) := tautology <| by
      intros M _ f _ m
      taut_morphism

    def syllogismExtraHyp : Γ ⊢ φ ⇒ ψ ⇒ χ → Γ ⊢ φ ⇒ χ ⇒ θ → Γ ⊢ φ ⇒ ψ ⇒ θ :=
      fun l₁ : Γ ⊢ φ ⇒ ψ ⇒ χ =>
      let l₂ : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ χ) := toRule implDistribLeft l₁
      fun l₃ : Γ ⊢ φ ⇒ χ ⇒ θ =>
      let l₄ : Γ ⊢ (φ ⇒ χ) ⇒ (φ ⇒ θ) := toRule implDistribLeft l₃
      let l₅ : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ θ) := (syllogism) l₂ l₄
      let l₆ : Γ ⊢ φ ⇒ ψ ⇒ θ := toRule implDistribRight l₅
      l₆

    def permuteHyps : Γ ⊢ φ ⇒ ψ ⇒ χ → Γ ⊢ ψ ⇒ φ ⇒ χ :=
      fun l₁ : Γ ⊢ φ ⇒ ψ ⇒ χ =>
      let l₂ : Γ ⊢ φ ⋀ ψ ⇒ χ := (importation) l₁
      let l₃ : Γ ⊢ ψ ⋀ φ ⇒ χ := (syllogism) permutationConj l₂
      (exportation) l₃


    def disjIntroAtHypThm : Γ ⊢ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ (φ ⋁ ψ ⇒ χ) :=
      let l₁ : Γ ⊢ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ φ ⇒ χ := conjElimLeft
      let l₂ : Γ ⊢ φ ⇒ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ χ := (permuteHyps) l₁
      let l₃ : Γ ⊢ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ ψ ⇒ χ := conjElimRight
      let l₄ : Γ ⊢ ψ ⇒ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ χ := (permuteHyps) l₃
      let l₅ : Γ ⊢ φ ⋁ ψ ⇒ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ χ := (disjIntroAtHyp) l₂ l₄
      (permuteHyps) l₅

    def conjIntroAtConclThm : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ χ) ⇒ (φ ⇒ ψ ⋀ χ) :=
      let l₁ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ φ := conjElimRight
      let l₂ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ (φ ⇒ ψ) := (syllogism) conjElimLeft conjElimLeft
      let l₃ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ ψ := (modusPonensExtraHyp) l₁ l₂
      let l₄ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ (φ ⇒ χ) := (syllogism) conjElimLeft conjElimRight
      let l₅ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ χ := (modusPonensExtraHyp) l₁ l₄
      let l₆ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ ψ ⋀ χ := (conjIntroRule) l₃ l₅
      (exportation) $ (exportation) l₆


    def negImplIntro : Γ ⊢ φ ⇒ ψ → Γ ⊢ ∼ψ ⇒ ∼φ :=
      let thm : Γ ⊢ (φ ⇒ ψ) ⇒ (∼ψ ⇒ ∼φ) := tautology <| by
        intros _ _ _ _ _
        taut_morphism
      toRule thm

    def negConjAsImpl : Γ ⊢ ∼(φ ⋀ ψ) ⇒ φ ⇒ ∼ψ := tautology <| by
      intros M _ f _ m
      taut_morphism



    def doubleNegIntro : Γ ⊢ φ ⇒ ∼∼φ := tautology <| by
      intros M _ f _ m
      taut_morphism

    def doubleNegElim : Γ ⊢ ∼∼φ ⇒ φ := tautology <| by
      intros _ _ _ _ _
      taut_morphism

    -- Why doesn't `unfold_tautology` work anymore???
    def equivSelf : Γ ⊢ φ ⇔ φ := tautology <| by
      intros _ _ _ _ _
      simp only [Morphism.morphism_equiv]

    def topImplSelfImplSelf : Γ ⊢ (⊤ ⇒ φ) ⇒ φ := tautology <| by
      intros _ _ _ _ _
      taut_morphism

    def selfImplTopImplSelf : Γ ⊢ φ ⇒ (⊤ ⇒ φ) := tautology <| by
      intros _ _ _ _ _
      taut_morphism

    def conjIntroRule' : Γ ⊢ φ → Γ ⊢ ψ → Γ ⊢ φ ⋀ ψ :=
      fun l₁ l₂ =>
      let l₃ := toRule selfImplTopImplSelf l₁
      let l₄ := toRule selfImplTopImplSelf l₂
      let l₅ := conjIntroRule l₃ l₄
      toRule topImplSelfImplSelf l₅

    def implPreservesEquiv {δ} : Γ ⊢ (φ ⇔ ψ) ⇒ (χ ⇔ δ) ⇒ ((φ ⇒ χ) ⇔ (ψ ⇒ δ)) :=
      tautology <| by
        intros _ _ _ _ _
        taut_morphism

    def implPreservesEquivLeft : Γ ⊢ (φ ⇔ ψ) ⇒ ((χ ⇒ φ) ⇔ (χ ⇒ ψ)) :=
      tautology <| by
        intros _ _ _ _ _
        taut_morphism

    def implPreservesEquivRight : Γ ⊢ (φ ⇔ ψ) ⇒ ((φ ⇒ χ) ⇔ (ψ ⇒ χ)) :=
      tautology <| by
        intros _ _ _ _ _
        taut_morphism

  end Propositional


  section FirstOrder

    variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ θ : Pattern 𝕊} {x y : EVar}

    def implExistSelf : Γ ⊢ φ ⇒ ∃∃ x φ :=
      let l₁ : Γ ⊢ φ[x ⇐ x]ᵉ ⇒ ∃∃ x φ := existQuan (Pattern.substitutable_evar_same _ _)
      by rw [Pattern.subst_var_var_eq_self_evar] at l₁ ; exact l₁

    def existSelfImpl (not_fv : ¬φ.isFreeEvar x) : Γ ⊢ ∃∃ x φ ⇒ φ :=
      let l₁ : Γ ⊢ φ ⇒ φ := (implSelf)
      existGen not_fv l₁

    def pushExistInConj (not_fv : ¬ψ.isFreeEvar x) : Γ ⊢ ∃∃ x (φ ⋀ ψ) ⇒ ∃∃ x φ ⋀ ψ :=
      let l₁ : Γ ⊢ φ ⇒ ∃∃ x φ := implExistSelf
      let l₂ : Γ ⊢ φ ⋀ ψ ⇒ ∃∃ x φ ⋀ ψ := (conjIntroHypConcLeft) l₁
      existGen (by simp [*] at *) l₂

    def univQuan (sfi : (Pattern.evar y).substitutableForEvarIn x φ)
      : Γ ⊢ ∀∀ x φ ⇒ φ[x ⇐ᵉ y] :=
      let l₁ : Γ ⊢ ∀∀ x φ ⇒ ∼∼φ[x ⇐ᵉ y] := (negImplIntro) <| @existQuan _ _ (∼φ) _ _ (by simp [*] at *)
      (syllogism) l₁ (doubleNegElim)

    def univImplSelf : Γ ⊢ ∀∀ x φ ⇒ φ :=
      let l₁ : Γ ⊢ ∀∀ x φ ⇒ φ[x ⇐ᵉ x] := univQuan (Pattern.substitutable_evar_same _ _)
      by rw [Pattern.subst_var_var_eq_self_evar] at l₁ ; exact l₁

    def univGen (not_fv : ¬φ.isFreeEvar x) : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ ⇒ ∀∀ x ψ :=
      fun l₁ : Γ ⊢ φ ⇒ ψ =>
      let l₂ : Γ ⊢ ∼ψ ⇒ ∼φ := (negImplIntro) l₁
      let l₃ : Γ ⊢ ∃∃ x (∼ψ) ⇒ ∼φ := existGen (by simp [*]) l₂
      let l₄ : Γ ⊢ ∼∼φ ⇒ ∼(∃∃ x (∼ψ)) := (negImplIntro) l₃
      let l₅ : Γ ⊢ ∼∼φ ⇒ (∀∀ x ψ) := l₄
      (syllogism) (doubleNegIntro) l₅

    def univGeneralization : Γ ⊢ φ → Γ ⊢ ∀∀ x φ :=
      fun l₁ : Γ ⊢ φ =>
      let l₁ : Γ ⊢ ⊤ ⇒ φ := toRule (selfImplTopImplSelf) l₁
      let l₂ : Γ ⊢ ⊤ ⇒ ∀∀ x φ := (univGen) (by simp [*] at *) l₁
      toRule (topImplSelfImplSelf) l₂

    def pushConjInExist (not_fv : ¬ψ.isFreeEvar x) : Γ ⊢ ∃∃ x φ ⋀ ψ ⇒ ∃∃ x (φ ⋀ ψ) :=
      let l₁ : Γ ⊢ φ ⋀ ψ ⇒ ∃∃ x (φ ⋀ ψ) := (implExistSelf)
      let l₂ : Γ ⊢ φ ⇒ ψ ⇒ ∃∃ x (φ ⋀ ψ) := (exportation) l₁
      let l₃ : Γ ⊢ ∃∃ x φ ⇒ ψ ⇒ ∃∃ x (φ ⋀ ψ) := (existGen) (by simp [*, Pattern.exists_binds]) l₂
      let l₄ : Γ ⊢  ∃∃ x φ ⋀ ψ ⇒ ∃∃ x (φ ⋀ ψ) := (importation) l₃
      l₄

    def existPreservesEquiv : Γ ⊢ φ ⇔ ψ → Γ ⊢ ∃∃ x φ ⇔ ∃∃ x ψ :=
      fun l₁ =>
      let l₂ : Γ ⊢ ψ ⇒ ∃∃ x ψ := implExistSelf
      let l₃ : Γ ⊢ φ ⇒ ∃∃ x ψ := syllogism (conjElimLeft.toRule l₁) l₂
      let l₄ : Γ ⊢ ∃∃ x φ ⇒ ∃∃ x ψ := existGen (by simp) l₃
      let l₅ : Γ ⊢ ∃∃ x ψ ⇒ ∃∃ x φ := existGen (by simp) (syllogism (conjElimRight.toRule l₁) implExistSelf)
      conjIntroRule' l₄ l₅

  end FirstOrder



  section ContextReasoning

    variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ θ : Pattern 𝕊} {C : AppContext 𝕊} {x : EVar}

    def propagationBottom {C : AppContext 𝕊} : Γ ⊢ C[⊥] ⇒ ⊥ :=
    match C with
    | .empty => implSelf
    | .left χ C' =>
      let l₁ : Γ ⊢ C'[⊥] ⇒ ⊥ := @propagationBottom C'
      let l₂ : Γ ⊢ (C'.left χ) [⊥] ⇒ χ ⬝ ⊥ := framingRight l₁
      let l₃ : Γ ⊢ χ ⬝ ⊥ ⇒ ⊥ := propagationBottomLeft
      syllogism
          l₂ l₃
    | .right χ C' =>
      let l₁ : Γ ⊢ C'[⊥] ⇒ ⊥ := @propagationBottom C'
      let l₂ : Γ ⊢ (C'.right χ)[⊥] ⇒ ⊥ ⬝ χ := framingLeft l₁
      let l₃ : Γ ⊢ ⊥ ⬝ χ ⇒ ⊥ := propagationBottomRight
      syllogism
        l₂ l₃

    def propagationBottomR : Γ ⊢ ⊥ ⇒ C[⊥] := exFalso

    def propagationDisj {C : AppContext 𝕊} : Γ ⊢ C[φ ⋁ ψ] ⇒ C[φ] ⋁ C[ψ] :=
    match C with
    | .empty => implSelf
    | .left χ C' =>
      let l₁ : Γ ⊢ C'[φ ⋁ ψ] ⇒ C'[φ] ⋁ C'[ψ] := @propagationDisj C'
      let l₂ : Γ ⊢ (C'.left χ)[φ ⋁ ψ] ⇒ χ ⬝ (C'[φ] ⋁ C'[ψ]) := (framingRight) l₁
      let l₃ : Γ ⊢ χ ⬝ (C'[φ] ⋁ C'[ψ]) ⇒ (χ ⬝ C'[φ]) ⋁ (χ ⬝ C'[ψ]) := (propagationDisjLeft)
      (syllogism) l₂ l₃
    | .right χ C' =>
      let l₁ : Γ ⊢ C'[φ ⋁ ψ] ⇒ C'[φ] ⋁ C'[ψ] := @propagationDisj C'
      let l₂ : Γ ⊢ (C'.right χ)[φ ⋁ ψ] ⇒ (C'[φ] ⋁ C'[ψ]) ⬝ χ := (framingLeft) l₁
      let l₃ : Γ ⊢ (C'[φ] ⋁ C'[ψ]) ⬝ χ ⇒ (C'[φ] ⬝ χ) ⋁ (C'[ψ] ⬝ χ) := (propagationDisjRight)
      (syllogism) l₂ l₃

    def propagationDisjR {C : AppContext 𝕊} : Γ ⊢ C[φ] ⋁ C[ψ] ⇒ C[φ ⋁ ψ] :=
    match C with
    | .empty => implSelf
    | .left χ C' =>
      let l₁ : Γ ⊢ C'[φ] ⋁ C'[ψ] ⇒ C'[φ ⋁ ψ] := @propagationDisjR C'
      let l₂ : Γ ⊢ C'[φ] ⇒ C'[φ ⋁ ψ] := (syllogism) (disjIntroLeft) l₁
      let l₃ : Γ ⊢ χ ⬝ C'[φ] ⇒ χ ⬝ C'[φ ⋁ ψ] := (framingRight) l₂
      let l₄ : Γ ⊢ (C'.left χ)[φ] ⇒ (C'.left χ)[φ ⋁ ψ] := l₃
      let l₂' : Γ ⊢ C'[ψ] ⇒ C'[φ ⋁ ψ] := (syllogism) (disjIntroRight) l₁
      let l₃' : Γ ⊢ χ ⬝ C'[ψ] ⇒ χ ⬝ C'[φ ⋁ ψ] := (framingRight) l₂'
      let l₄' : Γ ⊢ (C'.left χ)[ψ] ⇒ (C'.left χ)[φ ⋁ ψ] := l₃'
      (disjIntroAtHyp) l₄ l₄'
    | .right χ C' =>
      let l₁ : Γ ⊢ C'[φ] ⋁ C'[ψ] ⇒ C'[φ ⋁ ψ] := @propagationDisjR C'
      let l₂ : Γ ⊢ C'[φ] ⇒ C'[φ ⋁ ψ] := (syllogism) (disjIntroLeft) l₁
      let l₃ : Γ ⊢ C'[φ] ⬝ χ ⇒ C'[φ ⋁ ψ] ⬝ χ := (framingLeft) l₂
      let l₄ : Γ ⊢ (C'.right χ)[φ] ⇒ (C'.right χ)[φ ⋁ ψ] := l₃
      let l₂' : Γ ⊢ C'[ψ] ⇒ C'[φ ⋁ ψ] := (syllogism) (disjIntroRight) l₁
      let l₃' : Γ ⊢ C'[ψ] ⬝ χ ⇒ C'[φ ⋁ ψ] ⬝ χ := (framingLeft) l₂'
      let l₄' : Γ ⊢ (C'.right χ)[ψ] ⇒ (C'.right χ)[φ ⋁ ψ] := l₃'
      (disjIntroAtHyp) l₄ l₄'

    def propagationExist {C : AppContext 𝕊} (not_fv : ¬C.isFreeEvar x) : Γ ⊢ (C[∃∃ x φ]) ⇒ (∃∃ x (C [φ])) :=
    match h:C with
    | .empty => implSelf
    | .left χ C' =>
      have not_fvχ : ¬χ.isFreeEvar x := by simp [*] at * ; exact not_fv.1
      let l₁ : Γ ⊢ (C'[∃∃ x φ]) ⇒ (∃∃ x (C'[φ])) := @propagationExist C' (by simp [h] at not_fv ; simp [not_fv.2])
      let l₂ : Γ ⊢ χ ⬝ (C'[∃∃ x φ]) ⇒ χ ⬝ (∃∃ x (C'[φ])) := (framingRight) l₁
      let l₃ : Γ ⊢ χ ⬝ (∃∃ x (C'[φ])) ⇒ (∃∃ x (χ ⬝ C'[φ])) := (propagationExistLeft) (by assumption)
      let l₄ : Γ ⊢ χ ⬝ (C'[∃∃ x φ]) ⇒ (∃∃ x (χ ⬝ C'[φ])) := (syllogism) l₂ l₃
      l₄
    | .right χ C' =>
      have not_fvχ : ¬χ.isFreeEvar x := by simp [*] at * ; exact not_fv.1
      let l₁ : Γ ⊢ (C'[∃∃ x φ]) ⇒ (∃∃ x (C'[φ])) := @propagationExist C' (by simp [h] at not_fv ; simp [not_fv.2])
      let l₂ : Γ ⊢ (C'[∃∃ x φ]) ⬝ χ ⇒ (∃∃ x (C'[φ])) ⬝ χ := (framingLeft) l₁
      let l₃ : Γ ⊢ (∃∃ x (C'[φ])) ⬝ χ ⇒ (∃∃ x (C'[φ] ⬝ χ)) := (propagationExistRight) (by assumption)
      let l₄ : Γ ⊢ (C'[∃∃ x φ]) ⬝ χ ⇒ (∃∃ x (C'[φ] ⬝ χ)) := (syllogism) l₂ l₃
      l₄

    def propagationExistR {C : AppContext 𝕊} (not_fv : ¬C.isFreeEvar x) : Γ ⊢ (∃∃ x (C[φ])) ⇒ (C[∃∃ x φ]) :=
    match h:C with
    | .empty => implSelf
    | .left χ C' =>
      have not_fvEφ : ¬(∃∃ x φ).isFreeEvar x := Pattern.exists_binds _ _
      have not_fvCEφ : ¬((C'.left χ)[∃∃ x φ]).isFreeEvar x := by
        rw [AppContext.no_free_occ_evar_insert]
        exact And.intro not_fvEφ not_fv
      let l₁ : Γ ⊢ (∃∃ x (C'[φ])) ⇒ (C'[∃∃ x φ]) := @propagationExistR C' (by simp [h] at not_fv ; simp [not_fv.2])
      let l₂ : Γ ⊢ C'[φ][x ⇐ .evar x]ᵉ ⇒ ∃∃ x (C'[φ]) := (existQuan) (Pattern.substitutable_evar_same _ _)
      let l₃ : Γ ⊢ C'[φ][x ⇐ .evar x]ᵉ ⇒ C'[∃∃ x φ] := (syllogism) l₂ l₁
      let l₄ : Γ ⊢ (C'.substEvar x (.evar x))[φ[x ⇐ .evar x]ᵉ] ⇒ C'[∃∃ x φ] := by
        rw [AppContext.subst_evar_insert] at l₃ ; exact l₃
      let l₄ : Γ ⊢ C'[φ[x ⇐ .evar x]ᵉ] ⇒ C'[∃∃ x φ] := by rw [AppContext.subst_var_var_eq_self_evar] at l₄ ; exact l₄
      let l₅ : Γ ⊢ C'[φ] ⇒ C'[∃∃ x φ] := by rw [Pattern.subst_var_var_eq_self_evar] at l₄ ; exact l₄
      let l₆ : Γ ⊢ χ ⬝ (C'[φ]) ⇒ χ ⬝ (C'[∃∃ x φ]) := (framingRight) l₅
      let l₇ : Γ ⊢ (C'.left χ)[φ] ⇒ (C'.left χ)[∃∃ x φ] := by simpa [*] -- to prove more elementary
      let l₉ : Γ ⊢ ∃∃ x ((C'.left χ)[φ]) ⇒ (C'.left χ)[∃∃ x φ] := existGen (not_fvCEφ) l₇
      l₉
    | .right χ C' =>
      have not_fvEφ : ¬(∃∃ x φ).isFreeEvar x := Pattern.exists_binds _ _
      have not_fvCEφ : ¬((C'.right χ)[∃∃ x φ]).isFreeEvar x := by
        rw [AppContext.no_free_occ_evar_insert]
        exact And.intro not_fvEφ not_fv
      let l₁ : Γ ⊢ (∃∃ x (C'[φ])) ⇒ (C'[∃∃ x φ]) := @propagationExistR C' (by simp [h] at not_fv ; simp [not_fv.2])
      let l₂ : Γ ⊢ C'[φ][x ⇐ .evar x]ᵉ ⇒ ∃∃ x (C'[φ]) := (existQuan) (Pattern.substitutable_evar_same _ _)
      let l₃ : Γ ⊢ C'[φ][x ⇐ .evar x]ᵉ ⇒ C'[∃∃ x φ] := (syllogism) l₂ l₁
      let l₄ : Γ ⊢ (C'.substEvar x (.evar x))[φ[x ⇐ .evar x]ᵉ] ⇒ C'[∃∃ x φ] := by
        rw [AppContext.subst_evar_insert] at l₃ ; exact l₃
      let l₄ : Γ ⊢ C'[φ[x ⇐ .evar x]ᵉ] ⇒ C'[∃∃ x φ] := by
        rw [AppContext.subst_var_var_eq_self_evar] at l₄ ; exact l₄
      let l₅ : Γ ⊢ C'[φ] ⇒ C'[∃∃ x φ] := by rw [Pattern.subst_var_var_eq_self_evar] at l₄ ; exact l₄
      let l₆ : Γ ⊢ (C'[φ]) ⬝ χ ⇒ (C'[∃∃ x φ]) ⬝ χ := (framingLeft) l₅
      let l₇ : Γ ⊢ (C'.right χ)[φ] ⇒ (C'.right χ)[∃∃ x φ] := by simpa [*] -- to prove more elementary
      let l₉ : Γ ⊢ ∃∃ x ((C'.right χ)[φ]) ⇒ (C'.right χ)[∃∃ x φ] := existGen not_fvCEφ l₇
      l₉  -- this is stupid, we just rewrite left to then rewrite right

    def framing {C : AppContext 𝕊} : Γ ⊢ φ ⇒ ψ → Γ ⊢ C[φ] ⇒ C[ψ] :=
    fun l₁ : Γ ⊢ φ ⇒ ψ =>
    match h:C with
    | .empty => l₁
    | .left χ C' =>
      let l₂ : Γ ⊢ C'[φ] ⇒ C'[ψ] := framing l₁
      let l₃ : Γ ⊢ χ ⬝ C'[φ] ⇒ χ ⬝ C'[ψ] := (framingRight) l₂
      l₃
    | .right χ C' =>
      let l₂ : Γ ⊢ C'[φ] ⇒ C'[ψ] := framing l₁
      let l₃ : Γ ⊢ C'[φ] ⬝ χ ⇒ C'[ψ] ⬝ χ := (framingLeft) l₂
      l₃

    def framingEquiv {C : AppContext 𝕊} : Γ ⊢ φ ⇔ ψ → Γ ⊢ C[φ] ⇔ C[ψ] :=
      fun l₁ =>
      let l₂ : Γ ⊢ φ ⇒ ψ := toRule conjElimLeft l₁
      let l₃ : Γ ⊢ ψ ⇒ φ := toRule conjElimRight l₁
      let l₄ : Γ ⊢ C[φ] ⇒ C[ψ] := framing l₂
      let l₅ : Γ ⊢ C[ψ] ⇒ C[φ] := framing l₃
      conjIntroRule' l₄ l₅

    def doubleNegCtx :
      Γ ⊢ φ →
      Γ ⊢ ∼C[∼φ]
      :=
      fun l₁ : Γ ⊢ φ =>
      let l₂ : Γ ⊢ ∼φ ⇒ ⊥ := modusPonens l₁ doubleNegIntro
      let l₃ : Γ ⊢ C[∼φ] ⇒ C[⊥] := (framing) l₂
      let l₄ : Γ ⊢ C[⊥] ⇒ ⊥ := (propagationBottom)
      let l₅ : Γ ⊢ C[∼φ] ⇒ ⊥ := (syllogism) l₃ l₄
      let l₆ : Γ ⊢ ∼C[∼φ] := l₅
      l₆

    def propagationBottom' : Γ ⊢ C[⊥] ⇒ ⊥ :=
      let x : EVar := ⟨default⟩
      let l₁ : Γ ⊢ ⊥ ⇒ x ⋀ ⊥ := exFalso
      let l₂ : Γ ⊢ ⊥ ⇒ x ⋀ ∼⊥ := exFalso
      let l₃ : Γ ⊢ C[⊥] ⇒ C[x ⋀ ⊥] := framing l₁
      let l₄ : Γ ⊢ C[⊥] ⇒ C[x ⋀ ∼⊥] := framing l₂
      let l₅ : Γ ⊢ C[⊥] ⇒ C[x ⋀ ⊥] ⋀ C[x ⋀ ∼⊥] := conjIntroRule l₃ l₄
      let l₆ : Γ ⊢ ∼(C[x ⋀ ⊥] ⋀ C[x ⋀ ∼⊥]) := singleton
      syllogism l₅ l₆


  end ContextReasoning




end TheoremsAndRules


section FixpointReasoning

  variable {𝕊 : Type} {Γ : Premises 𝕊} {X : SVar} {φ ψ : Pattern 𝕊}

  def exfalsoMu : Γ ⊢ μ X X ⇒ φ :=
    let l₁ : Γ ⊢ φ ⇒ φ := implSelf
    have : ((Pattern.svar X).substSvar X φ ⇒ φ) = (φ ⇒ φ) := by simp
    let l₂ : Γ ⊢ μ X X ⇒ φ := Proof.knasterTarski (by simp) (by rw [← this] at l₁; exact l₁)
    l₂

  -- the substitutability condition can probably be relaxed
  def muMonotone (hpos : (μ X ψ).Positive) (hsubst : Pattern.substitutableForSvarIn X (μ X ψ) (φ ⇒ ψ)): Γ ⊢ φ ⇒ ψ → Γ ⊢ (μ X φ ⇒ μ X ψ) :=
    fun l₁ =>
    let l₂ : Γ ⊢ (φ ⇒ ψ)[X ⇐ˢ μ X ψ] := substitution hsubst l₁
    let l₃ : Γ ⊢ φ[X ⇐ˢ μ X ψ] ⇒ ψ[X ⇐ˢ μ X ψ] := by rw [Pattern.subst_svar_implication] at l₂; exact l₂
    let l₄ : Γ ⊢ ψ[X ⇐ˢ μ X ψ] ⇒ μ X ψ := prefixpoint hpos (by simp at hsubst; exact hsubst.2)
    let l₅ : Γ ⊢ φ[X ⇐ˢ μ X ψ] ⇒ μ X ψ := syllogism l₃ l₄
    knasterTarski (by simp at hsubst; exact hsubst.1) l₅


end FixpointReasoning

def add_eq_one_xor_psum {x y : ℕ} : (x + y) = 1 → (x = 1 ∧ y = 0) ⊕' (y = 1 ∧ x = 0) := by
  intros h
  cases x with
  | zero =>
    apply PSum.inr
    omega
  | succ x' =>
    cases y with
    | zero =>
      apply PSum.inl
      omega
    | succ y' =>
      omega


-- example {𝕊} (Γ : Premises 𝕊) (x : EVar) (φ ψ χ : Pattern 𝕊) (hc : χ.countEVar x = 1) : Γ ⊢ φ ⇔ ψ → Γ ⊢ (χ[x ⇐ᵉ φ] ⇔ χ[x ⇐ᵉ ψ]) := by
--   intros h
--   induction χ with
--   | evar y =>
--     by_cases hxy : x = y
--     . rw [hxy, Pattern.subst_evar_same, Pattern.subst_evar_same]
--       exact h
--     . rw [Pattern.subst_evar_distinct hxy, Pattern.subst_evar_distinct hxy]
--       exact equivSelf
--   | svar X =>
--     simp
--     exact equivSelf
--   | bottom =>
--     simp
--     exact equivSelf
--   | implication χ₁ χ₂ =>
--     rw [Pattern.subst_evar_implication, Pattern.subst_evar_implication]
--     sorry --fol
--   | application χ₁ χ₂ ih₁ ih₂ =>
--     rw [Pattern.subst_evar_application, Pattern.subst_evar_application]
--     simp [Pattern.countEVar] at hc
--     have := add_eq_one_xor_psum hc
--     cases this with
--     | inl hc =>
--       have : χ₂[x ⇐ᵉ φ] = χ₂ := sorry
--       rw [this]; clear this
--       have : χ₂[x ⇐ᵉ ψ] = χ₂ := sorry
--       rw [this]; clear this
--       specialize ih₁ hc.1
--       sorry
--     | inr hc =>
--       have : χ₁[x ⇐ᵉ φ] = χ₁ := sorry
--       rw [this]; clear this
--       have : χ₁[x ⇐ᵉ ψ] = χ₁ := sorry
--       rw [this]; clear this
--       specialize ih₂ hc.1
--       sorry
--   | existential y φ ih =>
--     simp [Pattern.countEVar] at hc
--     specialize ih hc
--     sorry
--   | mu X φ ih =>
--     simp [Pattern.countEVar] at hc
--     specialize ih hc
--     sorry
