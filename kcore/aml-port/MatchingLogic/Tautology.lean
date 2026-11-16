/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Horațiu Cheval
-/

import MatchingLogic.Pattern

set_option autoImplicit false

namespace ML

variable {𝕊 : Type} {M : Type}

@[simp]
def FalseMorphism (f : Pattern 𝕊 → Set M) : Prop :=
  ∀ m : M, f ⊥ m ↔ False

@[simp]
def ImplMorphism (f : Pattern 𝕊 → Set M) : Prop :=
  ∀ (φ ψ : Pattern 𝕊) (m : M), f (φ ⇒ ψ) m ↔ f φ m → f ψ m

class Morphism (f : Pattern 𝕊 → Set M) : Prop where
  morphism_false : ∀ m : M, f ⊥ m ↔ False
  morphism_impl : ∀ (φ ψ : Pattern 𝕊) (m : M), f (φ ⇒ ψ) m ↔ f φ m → f ψ m

attribute [simp] Morphism.morphism_false
attribute [simp] Morphism.morphism_impl

namespace Morphism

  attribute [simp] Pattern.top Pattern.negation Pattern.conjunction Pattern.disjunction in
  section
    variable {f : Pattern 𝕊 → Set M} [Morphism f] (φ ψ : Pattern 𝕊)

    @[simp] theorem morphism_true : ∀ m : M, f ⊤ m ↔ True := by intros m ; simp

    @[simp] theorem morphism_neg : ∀ m : M, f (∼φ) m ↔ ¬(f φ) m := by intros m ; simp

    @[simp] theorem morphism_disj : ∀ m : M, f (φ ⋁ ψ) m ↔ f φ m ∨ f ψ m := by intros m ; simp [or_def_imp_neg]

    @[simp] theorem morphism_conj : ∀ m : M, f (φ ⋀ ψ) m ↔ f φ m ∧ f ψ m := by
      intros m
      have : ∀ p q : Prop, (((p → False) → False) → q → False) → False ↔ p ∧ q := by
        intros p q
        have : ∀ p, p → False ↔ ¬p := fun _ => Iff.rfl
        repeat rw [this]
        simp
      simp [this]

    @[simp] theorem morphism_equiv : ∀ m : M, f (φ ⇔ ψ) m ↔ (f φ m ↔ f ψ m) := by
      intros m
      -- have : ∀ p q : Prop, ((((p → q) → False) → False) → (q → p) → False) → False ↔ (p ↔ q) := by
      --   intros p q
      --   have :  ∀ p, p → False ↔ ¬p := fun _ => Iff.rfl
      --   repeat rw [this]
      --   simp
      --   apply Iff.intro
      --   . intros h ; exact Iff.intro h.1 h.2
      --   . intros h ; exact And.intro h.1 h.2
      simp only [Pattern.equivalence, morphism_conj, morphism_impl]
      exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩



  end
end Morphism

def Tautology (φ : Pattern 𝕊) : Prop :=
  ∀ {M : Type} [Inhabited M] (f : Pattern 𝕊 → Set M) [Morphism f], ∀ m : M, f φ m

macro "unfold_tautology" : tactic =>
  `(tactic| simp only [ML.Morphism.morphism_conj, ML.Morphism.morphism_disj, ML.Morphism.morphism_impl, ML.Morphism.morphism_neg, ML.Morphism.morphism_equiv, Morphism.morphism_true])
macro "unfold_tautology!" : tactic =>
  `(tactic| try intros _ _ _ _ _ ; unfold_tautology)

/--
  Port replacement for upstream's uses of Mathlib's `aesop`/`tauto` on propositional tautologies:
  unfolds the morphism laws, then closes the propositional goal with `grind`.
-/
macro "taut_morphism" : tactic =>
  `(tactic| ((try simp only [ML.Morphism.morphism_conj, ML.Morphism.morphism_disj, ML.Morphism.morphism_impl, ML.Morphism.morphism_neg, ML.Morphism.morphism_equiv, ML.Morphism.morphism_true, ML.Morphism.morphism_false] at *) ; all_goals grind))
