import UtxoConf.Views

/-! The slots of `UtxoConf.Slots` that the generic attempts leave, proved by hand: two spawns (of one
process, one step; of two, new keys that differ since a child's id names its parent, so they
commute), and the races at one binding of the ledger (two creates or two spends of one output are
steps of one process, so one step; a create and a spend of one output cannot both be enabled). -/

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace UtxoConf

open KPrelude

/-- Two values that differ: by constructors, or by a term inside itself. -/
local macro "k2l_ne" : tactic => `(tactic| first
  | (simp; done)
  | (intro h; cases h)
  | (simp; intro h; cases h)
  | (simp; intro _ h; cases h)
  | (intro h; have := congrArg sizeOf h; simp at this; omega))

/-- What a step does to the ledger, read off a view's change (`ChOf`): the change applies at the
ledger before and gives the ledger after. -/
theorem ledger_step {ch : Change} {c c₁ : Utxo.SortGeneratedTopCell}
    (o : (∃ a b, MStep a b ch c c₁) ∨ SStep ch c c₁) {p p' : Utxo.SortProcsCell} {L L' : Utxo.SortMap}
    {g g' : Utxo.SortGeneratedCounterCell}
    (e : c = Utxo.SortGeneratedTopCell.«<generatedTop>» (Utxo.SortTCell.«<T>» p (Utxo.SortLedgerCell.«<ledger>» L)) g)
    (e' : c₁ = Utxo.SortGeneratedTopCell.«<generatedTop>» (Utxo.SortTCell.«<T>» p' (Utxo.SortLedgerCell.«<ledger>» L')) g') :
    ch.ledger.pre L ∧ ch.ledger.apply L = L' := by
  subst e e'
  rcases o with ⟨a, b, m, R, r, ⟨sl, sg⟩, e1, -, -, hp, e2⟩ | ⟨tc, ⟨sl, sg⟩, e1, hp, e2⟩
  all_goals
    simp only [mk, mkc] at e1 e2
    cases e1
    refine ⟨hp.1, ?_⟩
    cases e2
    rfl

/-- A key bound by what `concat` puts beside the rest is not the rest's. -/
theorem right_none {b R m : Utxo.SortProcCellMap} (h : MapHook.concat b R = some m) {k}
    (hb : MapHook.lookup b k ≠ none) : MapHook.lookup R k = none := by
  cases e : MapHook.lookup R k with
  | none => rfl
  | some w => exact absurd (MapHook.lookup_left_none_of_concat h (by rw [e]; simp)) hb

/-- The keys of a map of two bindings. -/
theorem pair_key {r : Utxo.SortProcCellMap} {x y v w k}
    (h : MapHook.concat (MapHook.element x v) (MapHook.element y w) = some r)
    (hk : MapHook.lookup r k ≠ none) : k = x ∨ k = y := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hk
  have := ((MapHook.binds_pair h) k u).1 hu
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
  rcases this with ⟨e, -⟩ | ⟨e, -⟩
  · exact Or.inl e
  · exact Or.inr e

theorem hand.join.key.create.create : join.key.create.create.statement := by
  intro c c₁ c₂ ch₁ ch₂ s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Change.KCompat] at hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, L, G0, D2, P, N, Q, V, D3, r, r3, hm, hr, hr4, e, e'⟩ := Inst.of s₁
  obtain ⟨m', L', G0', D2', P', N', Q', V', D3', r', r3', hm', hr', hr4', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  obtain ⟨p₁, a₁⟩ := ledger_step o₁ rfl rfl
  obtain ⟨p₂, a₂⟩ := ledger_step o₂ rfl rfl
  rw [MCh.insert_of p₁ a₁ k₁ hr4, MCh.insert_of p₂ a₂ k₂ hr4'] at hk
  by_cases eo : Utxo.SortKItem.inj_Oid (Utxo.SortOid.«oid(_,_)» P N) =
      Utxo.SortKItem.inj_Oid (Utxo.SortOid.«oid(_,_)» P' N')
  · cases eo
    k2l_det
    all_goals exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  · refine (hk (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl,
      Or.inl ⟨fun _ => Or.inl MapHook.lookup_unit, fun j => ?_⟩⟩))).elim
    by_cases ej : j = Utxo.SortKItem.inj_Oid (Utxo.SortOid.«oid(_,_)» P N)
    · subst ej; exact Or.inr (MapHook.lookup_element_ne eo)
    · exact Or.inl (MapHook.lookup_element_ne ej)

theorem hand.join.key.spend.spend : join.key.spend.spend.statement := by
  intro c c₁ c₂ ch₁ ch₂ s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Change.KCompat] at hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, m2, G0, D2, P, D3, I, D4, D5, g0, r, hm, hm6, hr, e, e'⟩ := Inst.of s₁
  obtain ⟨m', m2', G0', D2', P', D3', I', D4', D5', g0', r', hm', hm6', hr', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  obtain ⟨p₁, a₁⟩ := ledger_step o₁ rfl rfl
  obtain ⟨p₂, a₂⟩ := ledger_step o₂ rfl rfl
  rw [MCh.remove_of p₁ a₁ k₁ hm6, MCh.remove_of p₂ a₂ k₂ hm6'] at hk
  by_cases eo : Utxo.SortKItem.inj_Oid I = Utxo.SortKItem.inj_Oid I'
  · cases eo
    k2l_det
    all_goals exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
  · refine (hk (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl,
      Or.inl ⟨fun j => ?_, fun _ => Or.inl MapHook.lookup_unit⟩⟩))).elim
    by_cases ej : j = Utxo.SortKItem.inj_Oid I
    · subst ej; exact Or.inr (MapHook.lookup_element_ne eo)
    · exact Or.inl (MapHook.lookup_element_ne ej)

theorem hand.join.key.create.spend : join.key.create.spend.statement := by
  intro c c₁ c₂ ch₁ ch₂ s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Change.KCompat] at hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, L, G0, D2, P, N, Q, V, D3, r, r3, hm, hr, hr4, e, e'⟩ := Inst.of s₁
  obtain ⟨m', m2', G0', D2', P', D3', I', D4', D5', g0', r', hm', hm6', hr', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  obtain ⟨p₁, a₁⟩ := ledger_step o₁ rfl rfl
  obtain ⟨p₂, a₂⟩ := ledger_step o₂ rfl rfl
  rw [MCh.insert_of p₁ a₁ k₁ hr4, MCh.remove_of p₂ a₂ k₂ hm6'] at hk
  exact (hk (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl,
    Or.inl ⟨fun _ => Or.inl MapHook.lookup_unit, fun _ => Or.inr MapHook.lookup_unit⟩⟩))).elim

theorem hand.join.key.spend.create : join.key.spend.create.statement := by
  intro c c₁ c₂ ch₁ ch₂ s₁ s₂ ⟨o₁, k₁, i₁⟩ ⟨o₂, k₂, i₂⟩ hk
  simp only [Change.KCompat] at hk
  simp only [Rule.cls, InClass] at i₁ i₂
  obtain ⟨m, m2, G0, D2, P, D3, I, D4, D5, g0, r, hm, hm6, hr, e, e'⟩ := Inst.of s₁
  obtain ⟨m', L', G0', D2', P', N', Q', V', D3', r', r3', hm', hr', hr4', f, f'⟩ := Inst.of s₂
  subst e e'; cases f; subst f'
  obtain ⟨p₁, a₁⟩ := ledger_step o₁ rfl rfl
  obtain ⟨p₂, a₂⟩ := ledger_step o₂ rfl rfl
  rw [MCh.remove_of p₁ a₁ k₁ hm6, MCh.insert_of p₂ a₂ k₂ hr4'] at hk
  exact (hk (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl,
    Or.inl ⟨fun _ => Or.inr MapHook.lookup_unit, fun _ => Or.inl MapHook.lookup_unit⟩⟩))).elim

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
      exact right_none hr4 (by
        rw [((MapHook.binds_pair hr) _ _).2 (List.mem_cons_of_mem _ List.mem_cons_self)]; simp)
    have new₂ : MapHook.lookup m (Utxo.SortPidCell.«<pid>» (Utxo.SortPid.«child(_,_)» P' N')) = none := by
      rw [MapHook.lookup_concat_right hm' (MapHook.lookup_element_ne (by k2l_ne))]
      exact right_none hr4' (by
        rw [((MapHook.binds_pair hr') _ _).2 (List.mem_cons_of_mem _ List.mem_cons_self)]; simp)
    obtain ⟨R₁₂, R₂₁, m₀, e₁, e₂, e₃, e₄⟩ := MapHook.concat_frame_b hm hr4 hm' hr4'
      (fun k => by
        by_cases ek : k = Utxo.SortPidCell.«<pid>» P
        · subst ek; exact Or.inr (MapHook.lookup_element_ne eP)
        · exact Or.inl (MapHook.lookup_element_ne ek))
      (fun k => by
        by_cases h₁ : MapHook.lookup r k = none
        · exact Or.inl h₁
        refine Or.inr (Classical.byContradiction fun h₂ => ?_)
        rcases pair_key hr h₁ with rfl | rfl <;> rcases pair_key hr' h₂ with e | e
        · exact eP e
        · rw [e] at old₁; exact old₁ new₂
        · rw [e] at new₁; exact old₂ new₁
        · cases e; exact eP rfl)
    exact ⟨_, _, Or.inr (Utxo.Step.spawn _ _ _ _ _ _ _ _ _ _ e₁ hr' e₂),
      Or.inr (Utxo.Step.spawn _ _ _ _ _ _ _ _ _ _ e₃ hr e₄), rfl⟩

end UtxoConf
