import RangeIncRefine.RefineDefs

/-! The parts of `inc` (`open.txt`), which checks that the stored value is nonnegative in `KRangeInc`
and not in `KRangeIncOpt`. Forward, `KRangeIncOpt`'s step needs less; backward, `KRangeInc`'s check
holds under the invariant that every stored value is a nonnegative integer
(`KRangeInc.Invariant`, `storeNat`). -/

set_option maxHeartbeats 0

namespace RangeIncRefine

open KPrelude

/-- Under the invariant, a value bound in the store is nonnegative. -/
theorem nonneg_of_inv {k : KRangeInc.SortKCell} {n : KRangeInc.SortNextCell} {m d : KRangeInc.SortMap}
    {G : KRangeInc.SortGeneratedCounterCell} {L V : Int}
    (h : KRangeInc.Invariant (.«<generatedTop>» k n (.«<store>» m) G))
    (hm : MapHook.concat (MapHook.element (KRangeInc.SortKItem.inj_Int L) (KRangeInc.SortKItem.inj_Int V)) d = some m) :
    IntHook.ge V 0 = true := by
  simp only [KRangeInc.Invariant, KRangeInc.Invariant.storeNat, KRangeInc.Invariant.cell_store,
    KRangeInc.Invariant.content_store, KRangeInc.Eqn.«storeNat(_)_RANGE_Bool_Map_1»,
    Option.bind_fun_some, KRangeInc.Invariant.natVals_iff, ListHook.elemsOn_values_iff] at h
  have h := MapHook.entriesOn_of_concat_left hm h
  have h := h _ (by unfold MapHook.element; rw [ListIso.toList_ofList, List.mem_singleton])
  simpa [KRangeInc.Eqn.«isNat(_)_RANGE_Bool_KItem_1»] using h

theorem fwd_tr.inc : fwd_tr.inc.statement := by
  intro L K N m G D V r hm hreq hr hinv
  refine Or.inl ⟨_, .single ?_, Or.inl rfl⟩
  simp only [k2l_tr]
  refine KRangeIncOpt.Step.inc L (tr_SortK K) (tr_SortNextCell N) (tr_SortMap m)
    (tr_SortGeneratedCounterCell G) (tr_SortMap D) V (tr_SortMap r) ?_ ?_
  all_goals simp only [k2l_rel, *, Option.map_some]

/-- `KRangeInc`'s check holds where the invariant does: the value is nonnegative. -/
theorem bwd_tr.inc : bwd_tr.inc.statement := by
  intro L K N m G D V r hm hr c hinv hd
  k2l_inv
  obtain ⟨k, v, d, hk, hv, rfl, hm'⟩ := map_bwd_SortMap hm
  k2l_inv
  simp only [k2l_rel] at hr
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hr
  exact Or.inl ⟨_, .single (KRangeInc.Step.inc _ _ _ _ _ _ _ _ hm' (nonneg_of_inv hinv hm') hr'),
    Or.inl rfl⟩

end RangeIncRefine
