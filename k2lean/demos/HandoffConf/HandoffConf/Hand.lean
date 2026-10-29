import HandoffConf.Views
import HandoffConf.Claims

/-! The slots of `HandoffConf.Slots` that the generic attempts leave, proved by hand: two steps of
two tasks at one binding of `<procs>` or `<vals>`, two creations of one process or two of its
resumes at one turn. The generic attempt's steps (`k2l_keyed`) leave the two tasks claiming one
thing, which the script's well-formedness excludes (`one_task`: `wf` in K, the generated
`Handoff.Invariant`, read order-free by `HandoffConf.Claims`); one task takes one step (`k2l_det`). -/

set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HandoffConf

variable [Handoff.Hooks]

open KPrelude

/-- Two tasks of one configuration that claim the same, at least one thing, are one task (`wf`). -/
theorem one_task {c : Handoff.SortGeneratedTopCell} (hinv : Handoff.Invariant c) {k₁ k₂ : Handoff.SortTidCell}
    {t₁ t₂ : Handoff.SortTaskCell} {D₁ D₂ : Handoff.SortTaskCellMap}
    (h₁ : MapHook.concat (MapHook.element k₁ t₁) D₁ = some (tasks c))
    (h₂ : MapHook.concat (MapHook.element k₂ t₂) D₂ = some (tasks c)) {l : List Claim}
    (e₁ : claims t₁ = l) (e₂ : claims t₂ = l) (hl : l ≠ []) : k₁ = k₂ := by
  have w := wf_of_invariant hinv
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  exact w.2 _ _ _ _ hne (MapHook.lookup_of_concat_element h₁) (MapHook.lookup_of_concat_element h₂) x
    (by rw [e₁]; simp) (by rw [e₂]; simp)

theorem hand.join.key.new.new : join.key.new.new.statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ o₁ o₂ hk
  have x₁ := ChOf.cells o₁
  have x₂ := ChOf.cells o₂
  have i₁ := o₁.2.2
  have i₂ := o₂.2.2
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, D2, D1, D0, kk, D3, G5, Q, S, r, r2, hm, hr, hr3, rfl, rfl⟩ := Inst.of s₁
  obtain ⟨m', D2', D1', D0', kk', D3', G5', Q', S', r', r2', hm', hr', hr3', e, rfl⟩ := Inst.of s₂
  cases e
  simp only [procsOf, valsOf] at x₁ x₂
  k2l_keyed hk
  all_goals
    cases one_task hinv hm hm' rfl rfl (by simp [claims, iclaims])
    k2l_det
    all_goals exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩

theorem hand.join.key.«resume-lit».«resume-lit» : join.key.«resume-lit».«resume-lit».statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ o₁ o₂ hk
  have x₁ := ChOf.cells o₁
  have x₂ := ChOf.cells o₂
  have i₁ := o₁.2.2
  have i₂ := o₂.2.2
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, m2, D3, D0, kk, D4, G6, Q, N, V, D2, S, r, x9, r9, y13, r11, hm, hm5, hr, fn10, hr10, fo14, hr12, rfl, rfl⟩ := Inst.of s₁
  obtain ⟨m', m2', D3', D0', kk', D4', G6', Q', N', V', D2', S', r', x9', r9', y13', r11', hm', hm5', hr', fn10', hr10', fo14', hr12', e, rfl⟩ := Inst.of s₂
  cases e
  simp only [procsOf, valsOf] at x₁ x₂
  k2l_keyed hk
  all_goals
    cases one_task hinv hm hm' rfl rfl (by simp [claims, iclaims])
    k2l_det
    all_goals exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩

theorem hand.join.key.«resume-lit».«resume-oid» : join.key.«resume-lit».«resume-oid».statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ o₁ o₂ hk
  have x₁ := ChOf.cells o₁
  have x₂ := ChOf.cells o₂
  have i₁ := o₁.2.2
  have i₂ := o₂.2.2
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, m2, D3, D0, kk, D4, G6, Q, N, V, D2, S, r, x9, r9, y13, r11, hm, hm5, hr, fn10, hr10, fo14, hr12, rfl, rfl⟩ := Inst.of s₁
  obtain ⟨m', m2', m3', D0', kk', D4', G6', Q', N', I', D2', S', D3', V', r', x15', r15', y19', r17', r19', hm', hm6', hm13', hr', fn16', hr16', fo20', hr18', hr20', e, rfl⟩ := Inst.of s₂
  cases e
  simp only [procsOf, valsOf] at x₁ x₂
  k2l_keyed hk
  all_goals
    cases one_task hinv hm hm' rfl rfl (by simp [claims, iclaims])
    k2l_det
    all_goals exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩

theorem hand.join.key.«resume-oid».«resume-lit» : join.key.«resume-oid».«resume-lit».statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ o₁ o₂ hk
  have x₁ := ChOf.cells o₁
  have x₂ := ChOf.cells o₂
  have i₁ := o₁.2.2
  have i₂ := o₂.2.2
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, m2, m3, D0, kk, D4, G6, Q, N, I, D2, S, D3, V, r, x15, r15, y19, r17, r19, hm, hm6, hm13, hr, fn16, hr16, fo20, hr18, hr20, rfl, rfl⟩ := Inst.of s₁
  obtain ⟨m', m2', D3', D0', kk', D4', G6', Q', N', V', D2', S', r', x9', r9', y13', r11', hm', hm5', hr', fn10', hr10', fo14', hr12', e, rfl⟩ := Inst.of s₂
  cases e
  simp only [procsOf, valsOf] at x₁ x₂
  k2l_keyed hk
  all_goals
    cases one_task hinv hm hm' rfl rfl (by simp [claims, iclaims])
    k2l_det
    all_goals exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩

theorem hand.join.key.«resume-oid».«resume-oid» : join.key.«resume-oid».«resume-oid».statement := by
  intro c c₁ c₂ ch₁ ch₂ hinv s₁ s₂ o₁ o₂ hk
  have x₁ := ChOf.cells o₁
  have x₂ := ChOf.cells o₂
  have i₁ := o₁.2.2
  have i₂ := o₂.2.2
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, m2, m3, D0, kk, D4, G6, Q, N, I, D2, S, D3, V, r, x15, r15, y19, r17, r19, hm, hm6, hm13, hr, fn16, hr16, fo20, hr18, hr20, rfl, rfl⟩ := Inst.of s₁
  obtain ⟨m', m2', m3', D0', kk', D4', G6', Q', N', I', D2', S', D3', V', r', x15', r15', y19', r17', r19', hm', hm6', hm13', hr', fn16', hr16', fo20', hr18', hr20', e, rfl⟩ := Inst.of s₂
  cases e
  simp only [procsOf, valsOf] at x₁ x₂
  k2l_keyed hk
  all_goals
    cases one_task hinv hm hm' rfl rfl (by simp [claims, iclaims])
    k2l_det
    all_goals exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩

end HandoffConf
