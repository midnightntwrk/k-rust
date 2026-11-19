/-
  KCore. `hooksApart` (Tie.lean) and evaluation's `isHook` (checked layer): the names `isHook`
  accepts are exactly those of `hookSigs`, so in a definition `wf` accepts no user constructor or
  function is evaluated as a hook; and `faithCoreOK` implies `hooksApart`
  (`Semantics.hooksApart_of_faithCoreOK`).
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

/-- **`faithCoreOK` gives `hooksApart`**: no constructor of the definition is named like an
interpreted hook, since `kindsApart` says that no hook is a constructor and each constructor of the
definition is one (`isCtor`, which finds it by its name); and no function of the definition is,
since `fnsApart` says that no function of `allFns` is a hook (`isHook_iff`). -/
theorem Semantics.hooksApart_of_faithCoreOK {c : Semantics} (h : c.faithCoreOK = true) :
    c.hooksApart = true := by
  simp only [Semantics.faithCoreOK, Bool.and_eq_true] at h
  have hka := h.1.1.2
  have hfa := h.2
  unfold Faithful.Model.kindsApart at hka
  unfold Faithful.Model.fnsApart at hfa
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hka hfa
  unfold Semantics.hooksApart
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
  refine ⟨fun k hk s hs heq => ?_, fun fn hfn s hs heq => ?_⟩
  · have hc : c.isCtor k.name = true := by
      unfold Semantics.isCtor
      rw [lookupSig_eq]
      cases hf : c.ctorSigs.find? (·.name == k.name) with
      | none =>
        exact absurd (List.find?_eq_none.mp hf k
          (by simp only [Semantics.ctorSigs, List.mem_append]; exact .inr hk)) (by simp)
      | some _ => rfl
    rw [← heq, hka.1 s hs] at hc
    cases hc
  · have hh : hookSigs.any (·.name == fn.label) = true := List.any_eq_true.mpr ⟨s, hs, beq_iff_eq.mpr heq⟩
    have := (isHook_iff fn.label).mpr hh
    rw [(hfa fn (by simp only [Semantics.allFns, List.mem_append]; exact .inl hfn)).1.2] at this
    cases this

theorem Definition.hooksApart_of_wf {d : Definition} (h : wf d = true) : d.sem.hooksApart = true := by
  unfold wf Definition.namesOK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.2

end KCore
