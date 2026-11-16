/-
  KCore. First lemmas toward `Exec.step_iff` (checked layer; Exec.lean).

  - `same_iff`: `same` is equality (the order's `.eq` holds exactly on equal terms, OrderLaws.lean);
  - `isTrue_iff`, `wellSorted_iff`: the executable tests are the relations' conditions;
  - `Ext`, `bindVar_ext`, `PatVal.mono`: the matcher only extends a substitution, and a pattern's
    value survives extension, so a match found under an intermediate σ holds under the final one;
  - `mapM_mono`: a step of `mapM` that keeps its defined results keeps the list's. (More
    evaluation fuel gives the same defined result only where clauses of one priority are coherent:
    `evalT_mono`, EvalComplete.lean.)
-/
import KcoreSpec.Exec
import KcoreSpec.OrderLaws

set_option autoImplicit false

namespace KCore.Exec

open KCore

theorem same_iff {v w : GroundTerm} : same v w = true ↔ v = w := by
  unfold same
  constructor
  · intro h; exact GroundTerm.cmp_eq v w (by simpa using h)
  · rintro rfl; simp [GroundTerm.cmp_refl]

theorem isTrue_iff {r : Option GroundTerm} : isTrue r = true ↔ r = some (bool true) := by
  have hb : bool true = .dv Srt.bool (.bool true) := rfl
  rw [hb]
  constructor
  · intro h
    unfold isTrue at h
    split at h
    · rw [beq_iff_eq.mp h]
    · cases h
  · rintro rfl; rfl

variable {c : Semantics}

theorem wellSorted_iff {vars : List Srt} {σ : Subst} :
    wellSorted c vars σ = true ↔ c.WellSorted vars σ := by
  unfold wellSorted Semantics.WellSorted
  rw [List.all_eq_true]
  constructor
  · intro h i s hs
    have hi : i < vars.length := (List.getElem?_eq_some_iff.mp hs).1
    have := h i (List.mem_range.mpr hi)
    split at this
    · rename_i v hv
      rw [hs, beq_iff_eq] at this
      exact ⟨v, hv, this⟩
    · cases this
  · intro h i hi
    have hi' := List.mem_range.mp hi
    obtain ⟨v, hv, hs⟩ := h i vars[i] (List.getElem?_eq_getElem hi')
    simp [hv, hs, List.getElem?_eq_getElem hi']

/-! ## Extending substitutions -/

/-- σ' extends σ: every binding of σ is in σ'. -/
def Ext (σ σ' : Subst) : Prop := ∀ i w, σ.lookup i = some w → σ'.lookup i = some w

theorem Ext.refl (σ : Subst) : Ext σ σ := fun _ _ h => h

theorem Ext.trans {σ σ' σ'' : Subst} (h : Ext σ σ') (h' : Ext σ' σ'') : Ext σ σ'' :=
  fun i w hw => h' i w (h i w hw)

theorem bindVar_ext {σ σ' : Subst} {i : Nat} {v : GroundTerm} (h : bindVar σ i v = some σ') :
    Ext σ σ' ∧ σ'.lookup i = some v := by
  unfold bindVar at h
  split at h
  · rename_i w hw
    split at h
    · rename_i hs
      cases h
      exact ⟨Ext.refl _, by rw [hw, same_iff.mp hs]⟩
    · cases h
  · rename_i hn
    cases h
    refine ⟨fun j w hw => ?_, by simp [List.lookup]⟩
    simp only [List.lookup]
    cases hj : (j == i) with
    | true =>
      rw [beq_iff_eq] at hj
      subst hj
      rw [hn] at hw; cases hw
    | false => exact hw

mutual
  theorem PatVal.mono {σ σ' : Subst} (hx : Ext σ σ') : ∀ {p : Term} {v : GroundTerm},
      PatVal c σ p v → PatVal c σ' p v
    | _, _, .var h => .var (hx _ _ h)
    | _, _, .dv => .dv
    | _, _, .ctor h hs => .ctor h (PatVals.mono hx hs)
    | _, _, .hook hp hs hv => .hook hp (PatVals.mono hx hs) hv
    | _, _, .coll hc hp hs hv => .coll hc hp (PatVals.mono hx hs) hv
    | _, _, .inj h => .inj (PatVal.mono hx h)
    | _, _, .as h hi => .as (PatVal.mono hx h) (hx _ _ hi)
    | _, _, .ovl hc ho hs hv => .ovl hc ho (PatVals.mono hx hs) hv
  theorem PatVals.mono {σ σ' : Subst} (hx : Ext σ σ') : ∀ {ps : List Term} {vs : List GroundTerm},
      PatVals c σ ps vs → PatVals c σ' ps vs
    | _, _, .nil => .nil
    | _, _, .cons h hs => .cons (PatVal.mono hx h) (PatVals.mono hx hs)
end

/-! ## Monotone steps -/

theorem mapM_mono {α β : Type} {g g' : α → Option β} (hg : ∀ a b, g a = some b → g' a = some b) :
    ∀ {l : List α} {bs : List β}, l.mapM g = some bs → l.mapM g' = some bs
  | [], bs, h => by simpa using h
  | a :: l, bs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h ⊢
    obtain ⟨b, hb, bs', hbs', rfl⟩ := h
    exact ⟨b, hg a b hb, bs', mapM_mono hg hbs', rfl⟩

end KCore.Exec
