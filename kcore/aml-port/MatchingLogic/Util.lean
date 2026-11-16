/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Horațiu Cheval
-/

import MatchingLogic.Prelude

set_option autoImplicit false

macro "assert" sig:optDeclSig : command => `(example $sig := by rfl)

macro "ls" : tactic => `(tactic| exact?)

example (a b c : ℕ) : a < b → b ≤ c → a < c := Nat.lt_of_lt_of_le

theorem lt_of_add_lt {x y z : ℕ} : x + y < z → x < z ∧ y < z :=
  fun h => ⟨Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h, Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h⟩


theorem succ_to_end {x y : ℕ} : x + 1 + y = x + y + 1 := by rw [Nat.add_assoc, Nat.add_comm 1 y, ←Nat.add_assoc]

def typeof {α : Sort _} (_ : α) := α

@[simp]
def Prod.fold {α : Sort _} (f : α → α → α) : α × α → α × α → α × α
| (x₁, y₁), (x₂, y₂) => (f x₁ x₂, f y₁ y₂)

-- this has to be in the standard library
theorem contraposition {p q : Prop} : p → q ↔ (¬q → ¬p) := by
  apply Iff.intro
  . intros hnp hnq; exact hnq ∘ hnp
  . intros hnqnp hp
    have := Classical.em q
    cases this with
    | inl h => exact h
    | inr h => exact False.elim (hnqnp h hp)


macro "arrow_precedence" : prec => `(prec| 24)

attribute [simp] not_or
attribute [simp] Nat.not_lt_zero

def shiftSequence {α : Type} (a : α) (f : ℕ → α) : ℕ → α
| 0 => a
| n + 1 => f n

theorem or_def_imp_neg {p q : Prop} : p ∨ q ↔ (¬p → q) := by
  apply Iff.intro
  . intros h h'
    cases h with
    | inl h'' => exact False.elim (h' h'')
    | inr _ => assumption
  . intros h
    have := Classical.em p
    cases this with
    | inl h' => exact .inl h'
    | inr h' => exact .inr (h h')


theorem lt_add_succ_left (a b : ℕ) : a < a + b + 1 := by
  omega

theorem lt_add_succ_right (a b : ℕ) : b < a + b + 1 := by
  omega
