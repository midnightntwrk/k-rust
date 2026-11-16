/-
New in the Lean v4.34.0 port (not part of upstream aml-lean); see README.md.
The definitions restate the corresponding Mathlib definitions (Mathlib is Apache-2.0).
-/

/-!
# Local replacements for the Mathlib pieces used by this library

Upstream imports all of Mathlib from `MatchingLogic/Util.lean`.
This module replaces exactly the Mathlib definitions the reachable modules use,
with the same definitions Mathlib gives them:

* `ℕ` is notation for `Nat`;
* `Set α` is `α → Prop`, with membership `a ∈ s := s a`,
  `s ⊆ t := ∀ ⦃a⦄, a ∈ s → a ∈ t`, `s ∪ t := fun a => a ∈ s ∨ a ∈ t`,
  `{a} := fun b => b = a`, and `Set.image f s := fun b => ∃ a, a ∈ s ∧ f a = b`;
* `Function.update f a' v` is the dependent point update
  `fun a => if h : a = a' then Eq.ndrec v h.symm else f a`.

The lemmas below are the few facts about these definitions that the proofs use.
-/

set_option autoImplicit false

universe u v w

/-- Mathlib's `ℕ` notation for the natural numbers. -/
notation "ℕ" => Nat

/-- A set of elements of `α`, represented by its membership predicate (as in Mathlib). -/
def Set (α : Type u) : Type u := α → Prop

/-- Turns a predicate into a set (as in Mathlib). -/
def setOf {α : Type u} (p : α → Prop) : Set α := p

namespace Set

variable {α : Type u} {β : Type v}

/-- Membership in a set: `a ∈ s` is `s a`. -/
protected def Mem (s : Set α) (a : α) : Prop := s a

instance : Membership α (Set α) := ⟨Set.Mem⟩

/-- `s ⊆ t` iff every element of `s` belongs to `t`. -/
protected def Subset (s₁ s₂ : Set α) : Prop := ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

instance : HasSubset (Set α) := ⟨Set.Subset⟩

/-- Binary union of sets. -/
protected def union (s₁ s₂ : Set α) : Set α := setOf fun a => a ∈ s₁ ∨ a ∈ s₂

instance : Union (Set α) := ⟨Set.union⟩

/-- The singleton set `{a}`. -/
protected def singleton (a : α) : Set α := setOf fun b => b = a

instance : Singleton α (Set α) := ⟨Set.singleton⟩

/-- The image of a set under a function. -/
def image (f : α → β) (s : Set α) : Set β := setOf fun b => ∃ a, a ∈ s ∧ f a = b

@[simp] theorem mem_setOf_eq {p : α → Prop} {a : α} : (a ∈ setOf p) = p a := rfl

@[simp] theorem mem_union {a : α} {s t : Set α} : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := Iff.rfl

@[simp] theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b := Iff.rfl

end Set

namespace Function

variable {α : Sort u} {β : α → Sort v}

/-- Replacing the value of a function at a given point by a given value (as in Mathlib). -/
def update [DecidableEq α] (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a

@[simp] theorem update_same [DecidableEq α] (a : α) (v : β a) (f : ∀ a, β a) :
    update f a v a = v := by
  simp [update]

theorem update_noteq [DecidableEq α] {a a' : α} (h : a ≠ a') (v : β a') (f : ∀ a, β a) :
    update f a' v a = f a := by
  simp [update, h]

/-- Non-dependent unfolding of `update`. -/
theorem update_apply {γ : Sort w} [DecidableEq α] (f : α → γ) (a' : α) (v : γ) (a : α) :
    update f a' v a = if a = a' then v else f a := by
  unfold update
  by_cases h : a = a'
  · subst h; simp
  · simp [h]

theorem update_comm {γ : Sort w} [DecidableEq α] {a b : α} (h : a ≠ b) (v w : γ) (f : α → γ) :
    update (update f a v) b w = update (update f b w) a v := by
  funext c
  simp only [update_apply]
  by_cases h₁ : c = b
  · subst h₁; simp [Ne.symm h]
  · by_cases h₂ : c = a
    · subst h₂; simp [h₁]
    · simp [h₁, h₂]

theorem update_idem {γ : Sort w} [DecidableEq α] (a : α) (v w : γ) (f : α → γ) :
    update (update f a v) a w = update f a w := by
  funext c
  simp only [update_apply]
  by_cases h : c = a <;> simp [h]

end Function

/-- Contraposition, as Mathlib's `not_imp_not` (classical). -/
theorem not_imp_not {a b : Prop} : ¬a → ¬b ↔ b → a :=
  ⟨fun h hb => Classical.byContradiction fun ha => h ha hb, fun h hna hb => hna (h hb)⟩
