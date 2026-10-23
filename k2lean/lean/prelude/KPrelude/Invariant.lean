/-!
# Preserved invariants of a transition relation (prelude-independent)

A preserved invariant of a relation `S` is a predicate `P` with
`Preserved S P := ∀ c c', P c → S c c' → P c'`: every step from a configuration satisfying `P`
reaches one satisfying `P`.
For a generated K semantics `S` is `Step`, and `Preserved Step P` is proved by one case per rule
(`k2l_preserve`, `KPrelude.InvTactic`).

This module depends on nothing but Lean core.
It gives:

- `Preserved` and its closure properties (conjunction, families, implication, a smaller relation);
- relative preservation (`PreservedUnder`): `Q` is kept by the steps from configurations that
  satisfy an already preserved `P`, which is how an invariant is strengthened in stages;
- preservation along the reflexive-transitive closure `Star` and along core's `TransGen`;
- the typed view `{c // P c}` with its step `TStep`, which loses no step of `S` (`TStep_iff`);
- `OnCell proj Q`: a predicate on one cell lifted to the configuration.
-/

namespace KPrelude

universe u v

section

variable {α : Type u}

/-- `P` is preserved by every step of `S`. -/
def Preserved (S : α → α → Prop) (P : α → Prop) : Prop :=
  ∀ c c', P c → S c c' → P c'

/-- `Q` is preserved by the steps of `S` from configurations satisfying `P`. -/
def PreservedUnder (S : α → α → Prop) (P Q : α → Prop) : Prop :=
  ∀ c c', P c → Q c → S c c' → Q c'

/-- Reflexive-transitive closure of a relation (a path of zero or more steps, head first). -/
inductive Star (S : α → α → Prop) : α → α → Prop where
  | refl (c : α) : Star S c c
  | step {c c' c'' : α} : S c c' → Star S c' c'' → Star S c c''

end

variable {α : Type u} {S S' : α → α → Prop} {P Q : α → Prop}

namespace Preserved

theorem true_ : Preserved S (fun _ => True) := fun _ _ _ _ => trivial

theorem false_ : Preserved S (fun _ => False) := fun _ _ h _ => h

/-- A conjunction of preserved predicates is preserved. -/
theorem and (hP : Preserved S P) (hQ : Preserved S Q) : Preserved S (fun c => P c ∧ Q c) :=
  fun c c' h hs => ⟨hP c c' h.1 hs, hQ c c' h.2 hs⟩

/-- A disjunction of preserved predicates is preserved. -/
theorem or (hP : Preserved S P) (hQ : Preserved S Q) : Preserved S (fun c => P c ∨ Q c) :=
  fun c c' h hs => h.elim (fun h => .inl (hP c c' h hs)) (fun h => .inr (hQ c c' h hs))

/-- A family of preserved predicates is preserved jointly. -/
theorem forall_ {ι : Sort v} {F : ι → α → Prop} (h : ∀ i, Preserved S (F i)) :
    Preserved S (fun c => ∀ i, F i c) :=
  fun c c' hc hs i => h i c c' (hc i) hs

/-- Preservation transfers along a pointwise equivalence of predicates. -/
theorem of_iff (hP : Preserved S P) (he : ∀ c, P c ↔ Q c) : Preserved S Q :=
  fun c c' h hs => (he c').1 (hP c c' ((he c).2 h) hs)

/-- A predicate preserved by `S` is preserved by every smaller relation. -/
theorem mono_rel (hS : ∀ c c', S' c c' → S c c') (hP : Preserved S P) : Preserved S' P :=
  fun c c' h hs => hP c c' h (hS c c' hs)

/-- Strengthening in stages: if `P` is preserved and `Q` is preserved from `P`-configurations,
`P ∧ Q` is preserved. -/
theorem and_under (hP : Preserved S P) (hQ : PreservedUnder S P Q) :
    Preserved S (fun c => P c ∧ Q c) :=
  fun c c' h hs => ⟨hP c c' h.1 hs, hQ c c' h.1 h.2 hs⟩

theorem toUnder (hQ : Preserved S Q) : PreservedUnder S P Q :=
  fun c c' _ h hs => hQ c c' h hs

/-- Along a path. -/
theorem star (hP : Preserved S P) {c c' : α} (h : Star S c c') (hc : P c) : P c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (hP _ _ hc hs)

/-- Along a nonempty path (core's transitive closure). -/
theorem transGen (hP : Preserved S P) {c c' : α} (h : Relation.TransGen S c c') (hc : P c) :
    P c' := by
  induction h with
  | single hs => exact hP _ _ hc hs
  | tail _ hs ih => exact hP _ _ ih hs

/-- `P` is preserved by the closure itself. -/
theorem star_rel (hP : Preserved S P) : Preserved (Star S) P :=
  fun _ _ hc h => hP.star h hc

end Preserved

namespace Star

theorem single {c c' : α} (h : S c c') : Star S c c' := .step h (.refl _)

theorem trans {a b c : α} (h₁ : Star S a b) (h₂ : Star S b c) : Star S a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem tail {a b c : α} (h : Star S a b) (hs : S b c) : Star S a c := h.trans (single hs)

theorem of_transGen {a b : α} (h : Relation.TransGen S a b) : Star S a b := by
  induction h with
  | single hs => exact single hs
  | tail _ hs ih => exact ih.tail hs

end Star

/-! ## The typed view -/

/-- The configurations satisfying `P`. -/
abbrev TConfig (P : α → Prop) := { c : α // P c }

/-- The step of `S` between configurations satisfying `P`. -/
def TStep (S : α → α → Prop) (P : α → Prop) (t t' : TConfig P) : Prop := S t.1 t'.1

/-- The successor of a step from a typed configuration, typed. -/
def TConfig.next (hP : Preserved S P) (t : TConfig P) {c' : α} (h : S t.1 c') : TConfig P :=
  ⟨c', hP _ _ t.2 h⟩

/-- The typed view loses no step: every successor of a configuration satisfying a preserved `P`
satisfies `P`, so `S` from `t` is `TStep` from `t`. -/
theorem TStep_iff (hP : Preserved S P) (t : TConfig P) (c' : α) :
    S t.1 c' ↔ ∃ t' : TConfig P, t'.1 = c' ∧ TStep S P t t' :=
  ⟨fun h => ⟨⟨c', hP _ _ t.2 h⟩, rfl, h⟩, fun ⟨_, he, h⟩ => he ▸ h⟩

/-- Paths agree too: a path of `S` from a typed configuration is a path of `TStep`. -/
theorem TStar_iff (hP : Preserved S P) (t : TConfig P) (c' : α) :
    Star S t.1 c' ↔ ∃ t' : TConfig P, t'.1 = c' ∧ Star (TStep S P) t t' := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := t
    simp only at h
    induction h with
    | refl => exact ⟨⟨_, hc⟩, rfl, .refl _⟩
    | step hs _ ih =>
      obtain ⟨t', he, ht⟩ := ih (hP _ _ hc hs)
      exact ⟨t', he, .step (show TStep S P ⟨_, hc⟩ ⟨_, hP _ _ hc hs⟩ from hs) ht⟩
  · rintro ⟨t', rfl, h⟩
    induction h with
    | refl => exact .refl _
    | step hs _ ih => exact .step hs ih

/-- A configuration is terminal in the typed view exactly when it is terminal for `S`. -/
theorem TStep_terminal_iff (hP : Preserved S P) (t : TConfig P) :
    (∀ t', ¬ TStep S P t t') ↔ (∀ c', ¬ S t.1 c') := by
  constructor
  · intro h c' hs; exact h ⟨c', hP _ _ t.2 hs⟩ hs
  · intro h t' hs; exact h t'.1 hs

/-! ## Cell predicates -/

/-- A predicate `Q` on one cell, read through a projection `proj` of the configuration
(for example the store `<env>`). Keeping the projection a separate function makes `OnCell proj Q c`
reduce whenever the configuration is a constructor application, even when the cell's content
is a variable. -/
def OnCell {β : Type v} (proj : α → β) (Q : β → Prop) (c : α) : Prop := Q (proj c)

section OnCell

variable {β : Type v} {proj : α → β} {Q : β → Prop}

/-- A step that leaves the cell unchanged keeps the cell predicate. -/
theorem OnCell.of_proj_eq {c c' : α} (he : proj c' = proj c) (h : OnCell proj Q c) :
    OnCell proj Q c' := by
  unfold OnCell at *; rw [he]; exact h

/-- A cell predicate is preserved when every step keeps the cell or maps a cell satisfying `Q`
to one satisfying `Q`. -/
theorem OnCell.preserved
    (h : ∀ c c', S c c' → Q (proj c) → Q (proj c')) : Preserved S (OnCell proj Q) :=
  fun c c' hc hs => h c c' hs hc

/-- Two cell predicates on the same cell combine into one. -/
theorem OnCell.and_iff {Q₁ Q₂ : β → Prop} {c : α} :
    (OnCell proj Q₁ c ∧ OnCell proj Q₂ c) ↔ OnCell proj (fun x => Q₁ x ∧ Q₂ x) c := Iff.rfl

end OnCell

end KPrelude
