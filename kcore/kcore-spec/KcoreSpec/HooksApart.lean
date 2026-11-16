/-
  KCore. `hooksApart` (Tie.lean) and evaluation's `isHook` (checked layer): the names `isHook`
  accepts are exactly those of `hookSigs`, so in a definition `wf` accepts no user constructor or
  function is evaluated as a hook.
-/
import KcoreSpec.Tie
import KcoreSpec.Evaluation

set_option autoImplicit false

namespace KCore

/-- The interpreted symbols' names, in the table and in the signatures, are the same list. -/
theorem hookTable_names : hookTable.map (·.1) = hookSigs.map (·.name) := by decide +kernel

theorem isHook_iff (f : Sym) : isHook f = true ↔ hookSigs.any (·.name == f) = true := by
  have h1 : isHook f = hookTable.any (·.1 == f) := by
    unfold isHook
    rw [hook_eq, Option.isSome_map]
    induction hookTable with
    | nil => rfl
    | cons e es ih =>
      simp only [List.find?_cons, List.any_cons]
      cases h : (e.1 == f) <;> simp [ih]
  have h2 : hookTable.any (·.1 == f) = (hookTable.map (·.1)).any (· == f) := by
    simp [List.any_map, Function.comp_def]
  have h3 : hookSigs.any (·.name == f) = (hookSigs.map (·.name)).any (· == f) := by
    simp [List.any_map, Function.comp_def]
  rw [h1, h2, h3, hookTable_names]

/-- In a definition whose core is `hooksApart`, no user constructor or function is a hook. -/
theorem Semantics.not_isHook_of_hooksApart {c : Semantics} (h : c.hooksApart = true) :
    (∀ k ∈ c.ctors, isHook k.name = false) ∧ (∀ fn ∈ c.fns, isHook fn.label = false) := by
  unfold Semantics.hooksApart at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun k hk => ?_, fun fn hf => ?_⟩
  · cases e : isHook k.name
    · rfl
    · exact absurd (h.1 k hk) (by simp [(isHook_iff _).mp e])
  · cases e : isHook fn.label
    · rfl
    · exact absurd (h.2 fn hf) (by simp [(isHook_iff _).mp e])

theorem Definition.hooksApart_of_wf {d : Definition} (h : wf d = true) : d.sem.hooksApart = true := by
  unfold wf Definition.namesOK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.2

end KCore
