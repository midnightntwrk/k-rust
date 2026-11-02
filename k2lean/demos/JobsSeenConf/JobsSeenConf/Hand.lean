import JobsSeenConf.Views

/-! The slot of `JobsSeenConf.Slots` that the generic attempts leave, proved by hand: two runs, of
one job (one step), or of two, each still not in `<done>` after the other's run, so that they
commute up to the order of `<done>`. -/

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace JobsSeenConf

open KPrelude

/-- A job not in a list is not in it with another job appended. -/
theorem notIn_append {x y : JobsSeen.SortKItem} {D : JobsSeen.SortList} (hxy : x ≠ y)
    (h : BoolHook.not (ListHook.inList x D) = true) :
    BoolHook.not (ListHook.inList x (ListHook.concat D (ListHook.element y))) = true := by
  simp only [BoolHook.not, ListHook.inList, ListHook.concat, ListHook.element, ListIso.toList_ofList,
    List.contains_append, Bool.not_eq_true', Bool.or_eq_false_iff] at h ⊢
  refine ⟨h, ?_⟩
  simp [hxy]

theorem hand.join.open.run.run : join.open.run.run.statement := by
  intro c c₁ c₂ s₁ s₂
  obtain ⟨T, D, DotVar0, m, v, DotVar2, J, hm, hreq, rfl, rfl⟩ := Inst.of s₁
  obtain ⟨T_r, D_r, DotVar0_r, m_r, v_r, DotVar2_r, J_r, hm_r, hreq_r, e, rfl⟩ := Inst.of s₂
  cases e
  by_cases hJ : J = J_r
  · subst hJ
    exact ⟨_, _, Or.inl rfl, Or.inl rfl, Equiv.refl' _⟩
  · have ne : JobsSeen.SortKItem.inj_Int J ≠ JobsSeen.SortKItem.inj_Int J_r :=
      fun h => hJ (by cases h; rfl)
    exact ⟨_, _, Or.inr (JobsSeen.Step.run (hm := hm_r) (hreq := notIn_append (Ne.symm ne) hreq_r) ..),
      Or.inr (JobsSeen.Step.run (hm := hm) (hreq := notIn_append ne hreq) ..), by k2l_equiv_close⟩

end JobsSeenConf
