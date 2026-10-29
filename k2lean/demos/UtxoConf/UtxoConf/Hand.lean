import UtxoConf.Views

/-! The slot of `UtxoConf.Slots` that the generic attempts leave, proved by hand: two spawns, of
one process (one step), or of two, whose new keys differ since a child's id names its parent, so
that they commute. -/

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace UtxoConf

open KPrelude

theorem hand.join.open.spawn.spawn : join.open.spawn.spawn.statement := by
  intro c c₁ c₂ s₁ s₂
  obtain ⟨m, L0, G0, D2, P, N, Gp, D3, r, r3, hm, hr, hr4, e, e'⟩ := Inst.of s₁
  obtain ⟨m', L0', G0', D2', P', N', Gp', D3', r', r3', hm', hr', hr4', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  by_cases eP : Utxo.SortPidCell.«<pid>» P = Utxo.SortPidCell.«<pid>» P'
  · cases eP
    k2l_det
    all_goals exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  · -- each parent is a key of the map, each child is not
    have old₁ : MapHook.lookup m (Utxo.SortPidCell.«<pid>» P) ≠ none := by
      rw [MapHook.lookup_of_concat_element hm]; simp
    have old₂ : MapHook.lookup m (Utxo.SortPidCell.«<pid>» P') ≠ none := by
      rw [MapHook.lookup_of_concat_element hm']; simp
    have new₁ : MapHook.lookup m (Utxo.SortPidCell.«<pid>» (Utxo.SortPid.«child(_,_)» P N)) = none := by
      rw [MapHook.lookup_concat_right hm (MapHook.lookup_element_ne (by k2l_ne))]
      exact MapHook.lookup_right_none hr4 (by rw [MapHook.lookup_of_concat_element_right hr]; simp)
    have new₂ : MapHook.lookup m (Utxo.SortPidCell.«<pid>» (Utxo.SortPid.«child(_,_)» P' N')) = none := by
      rw [MapHook.lookup_concat_right hm' (MapHook.lookup_element_ne (by k2l_ne))]
      exact MapHook.lookup_right_none hr4' (by rw [MapHook.lookup_of_concat_element_right hr']; simp)
    obtain ⟨R₁₂, R₂₁, m₀, e₁, e₂, e₃, e₄⟩ := MapHook.concat_frame_b hm hr4 hm' hr4'
      (fun k => by
        by_cases ek : k = Utxo.SortPidCell.«<pid>» P
        · subst ek; exact Or.inr (MapHook.lookup_element_ne eP)
        · exact Or.inl (MapHook.lookup_element_ne ek))
      (fun k => by
        by_cases h₁ : MapHook.lookup r k = none
        · exact Or.inl h₁
        refine Or.inr (Classical.byContradiction fun h₂ => ?_)
        rcases MapHook.key_of_lookup_pair hr h₁ with rfl | rfl <;>
          rcases MapHook.key_of_lookup_pair hr' h₂ with e | e
        · exact eP e
        · rw [e] at old₁; exact old₁ new₂
        · rw [e] at new₁; exact old₂ new₁
        · cases e; exact eP rfl)
    exact ⟨_, _, Or.inr (Utxo.Step.spawn _ _ _ _ _ _ _ _ _ _ e₁ hr' e₂),
      Or.inr (Utxo.Step.spawn _ _ _ _ _ _ _ _ _ _ e₃ hr e₄), rfl⟩

end UtxoConf
