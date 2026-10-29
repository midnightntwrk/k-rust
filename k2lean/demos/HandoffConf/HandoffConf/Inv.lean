import Handoff.Preserves
import KPrelude.Scaffold

/-! The script's well-formedness: no two pending tasks name one resume of a process, or one
creation of a process, and no task names one twice. A task whose `<k>` is one instruction claims
what it names: `resume(Q, N, _)` the `N`-th resume of `Q`, `new(Q, _)` the creation of `Q`; a task
whose `<k>` is a program claims what its instructions name; any other task claims nothing. Every
step keeps it: `fork` moves the first claim of the root to a new task at a key no task has, the
other rules leave a task with nothing to claim or remove it. -/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HandoffConf

variable [Handoff.Hooks]

open KPrelude

/-- A claim: the `N`-th resume of the process `Q` (`inl (Q, N)`), or the creation of `Q` (`inr Q`). -/
abbrev Claim := (Int × Int) ⊕ Int

/-- The claim of one instruction. -/
def iclaims : Handoff.SortInstr → List Claim
  | .«new(_,_)» Q _ => [.inr Q]
  | .«resume(_,_,_)» Q N _ => [.inl (Q, N)]
  | _ => []

/-- The claims of the instructions of a program. -/
def pclaims : Handoff.SortPgm → List Claim
  | .«_;_» I P => iclaims I ++ pclaims P
  | _ => []

/-- The claims of a task: those of the instruction or program its `<k>` holds. -/
def claims : Handoff.SortTaskCell → List Claim
  | .«<task>» _ _ (.«<k>» (.kseq (.inj_Instr I) .dotk)) => iclaims I
  | .«<task>» _ _ (.«<k>» (.kseq (.inj_Pgm P) .dotk)) => pclaims P
  | _ => []

/-- The tasks of a configuration. -/
def tasks : Handoff.SortGeneratedTopCell → Handoff.SortTaskCellMap
  | .«<generatedTop>» (.«<T>» (.«<tasks>» m) _ _) _ => m

/-- No claim occurs twice in a map of tasks: not within one task, not in two tasks. -/
def WfM (m : Handoff.SortTaskCellMap) : Prop :=
  (∀ k t, MapHook.lookup m k = some t → (claims t).Nodup) ∧
  (∀ k₁ k₂ t₁ t₂, k₁ ≠ k₂ → MapHook.lookup m k₁ = some t₁ → MapHook.lookup m k₂ = some t₂ →
    ∀ x ∈ claims t₁, x ∉ claims t₂)

/-- The invariant: the tasks' claims are pairwise distinct. -/
def Wf (c : Handoff.SortGeneratedTopCell) : Prop := WfM (tasks c)

/-- A map each of whose tasks claims nothing or is one of `m`'s at its key keeps `WfM`. -/
theorem wfM_mono {m m' : Handoff.SortTaskCellMap}
    (h : ∀ j u, MapHook.lookup m' j = some u → claims u = [] ∨ MapHook.lookup m j = some u)
    (w : WfM m) : WfM m' := by
  refine ⟨fun k t hk => ?_, fun k₁ k₂ t₁ t₂ hne h₁ h₂ x hx hx' => ?_⟩
  · rcases h k t hk with e | e
    · rw [e]; exact List.nodup_nil
    · exact w.1 k t e
  · rcases h _ _ h₁ with e | e
    · rw [e] at hx; cases hx
    rcases h _ _ h₂ with e' | e'
    · rw [e'] at hx'; cases hx'
    exact w.2 _ _ _ _ hne e e' x hx hx'

/-- A step that replaces one task by one that claims nothing. -/
theorem replace_sub {k : Handoff.SortTidCell} {t t' : Handoff.SortTaskCell} {D m m' : Handoff.SortTaskCellMap}
    (hm : MapHook.concat (MapHook.element k t) D = some m)
    (hr : MapHook.concat (MapHook.element k t') D = some m') (e : claims t' = []) :
    ∀ j u, MapHook.lookup m' j = some u → claims u = [] ∨ MapHook.lookup m j = some u := by
  intro j u hu
  by_cases hj : j = k
  · subst hj
    rw [MapHook.lookup_of_concat_element hr] at hu
    cases hu; exact Or.inl e
  · right
    rw [MapHook.lookup_concat_right hr (MapHook.lookup_element_ne hj)] at hu
    rw [MapHook.lookup_concat_right hm (MapHook.lookup_element_ne hj)]
    exact hu

/-- A step that removes one task. -/
theorem remove_sub {k : Handoff.SortTidCell} {t : Handoff.SortTaskCell} {D m : Handoff.SortTaskCellMap}
    (hm : MapHook.concat (MapHook.element k t) D = some m) :
    ∀ j u, MapHook.lookup D j = some u → claims u = [] ∨ MapHook.lookup m j = some u := by
  intro j u hu
  right
  by_cases hj : j = k
  · subst hj
    rw [(MapHook.concat_element_iff.1 hm).2.1] at hu; cases hu
  · rw [MapHook.lookup_concat_right hm (MapHook.lookup_element_ne hj)]; exact hu

/-- `fork` keeps `WfM`: the root's claims are split between the root and the new task, whose key
no task has. -/
theorem fork_wf {k₀ kN : Handoff.SortTidCell} {root root' task : Handoff.SortTaskCell}
    {D m r r₂ : Handoff.SortTaskCellMap}
    (hm : MapHook.concat (MapHook.element k₀ root) D = some m)
    (hr : MapHook.concat (MapHook.element k₀ root') (MapHook.element kN task) = some r)
    (hr₂ : MapHook.concat r D = some r₂)
    (split : claims root = claims task ++ claims root') (w : WfM m) : WfM r₂ := by
  have nd : (claims task ++ claims root').Nodup := split ▸ w.1 _ _ (MapHook.lookup_of_concat_element hm)
  have hD : ∀ j u, MapHook.lookup D j = some u → MapHook.lookup m j = some u ∧ j ≠ k₀ := by
    intro j u hu
    by_cases hj : j = k₀
    · subst hj; rw [(MapHook.concat_element_iff.1 hm).2.1] at hu; cases hu
    · exact ⟨by rw [MapHook.lookup_concat_right hm (MapHook.lookup_element_ne hj)]; exact hu, hj⟩
  have k0 := MapHook.lookup_of_concat_element hm
  -- every task of `r₂` is the root, the new task, or one of `D`
  have cls : ∀ j u, MapHook.lookup r₂ j = some u →
      (j = k₀ ∧ u = root') ∨ (j = kN ∧ u = task) ∨ (MapHook.lookup m j = some u ∧ j ≠ k₀) := by
    intro j u hu
    rw [MapHook.lookup_concat hr₂] at hu
    cases e : MapHook.lookup r j with
    | none => rw [e] at hu; exact Or.inr (Or.inr (hD j u hu))
    | some v =>
      rw [e] at hu; cases hu
      have := ((MapHook.binds_pair hr) j _).1 e
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  have ab := (List.nodup_append.1 nd).2.2
  refine ⟨fun k t hk => ?_, fun k₁ k₂ t₁ t₂ hne h₁ h₂ x hx hx' => ?_⟩
  · rcases cls k t hk with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨e, -⟩
    · exact (List.nodup_append.1 nd).2.1
    · exact (List.nodup_append.1 nd).1
    · exact w.1 _ _ e
  · rcases cls _ _ h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨e₁, n₁⟩ <;>
      rcases cls _ _ h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨e₂, n₂⟩
    · exact hne rfl
    · exact ab x hx' x hx rfl
    · exact w.2 _ _ _ _ (Ne.symm n₂) k0 e₂ x (split ▸ List.mem_append_right _ hx) hx'
    · exact ab x hx x hx' rfl
    · exact hne rfl
    · exact w.2 _ _ _ _ (Ne.symm n₂) k0 e₂ x (split ▸ List.mem_append_left _ hx) hx'
    · exact w.2 _ _ _ _ n₁ e₁ k0 x hx (split ▸ List.mem_append_right _ hx')
    · exact w.2 _ _ _ _ n₁ e₁ k0 x hx (split ▸ List.mem_append_left _ hx')
    · exact w.2 _ _ _ _ hne e₁ e₂ x hx hx'

theorem Wf.preserved : Preserved Handoff.Step Wf := by
  apply Handoff.Step.preserves_of
  · intro m G3 G4 D0 D2 y N I P r r2 hm hlit hr hr3 w
    exact fork_wf hm hr hr3 (by simp [claims, pclaims]) w
  · intro m G4 G5 D0 k D2 G6 r hm hr w
    exact wfM_mono (replace_sub hm hr rfl) w
  · intro m D2 D1 D0 k D3 G5 Q S r r2 hm hr hr3 w
    exact wfM_mono (replace_sub hm hr rfl) w
  · intro m m2 D3 D0 k D4 G6 Q N V D2 S r x9 r9 y13 r11 hm hm5 hr fn10 hr10 fo14 hr12 w
    exact wfM_mono (replace_sub hm hr rfl) w
  · intro m m2 m3 D0 k D4 G6 Q N I D2 S D3 V r x15 r15 y19 r17 r19 hm hm6 hm13 hr fn16 hr16 fo20 hr18 hr20 w
    exact wfM_mono (replace_sub hm hr rfl) w
  · intro m G4 G5 D0 D2 G0 D3 hm w
    exact wfM_mono (remove_sub hm) w

end HandoffConf
