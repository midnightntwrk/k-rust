import ContractObsNI.Stack
import Contract.Determinism

/-! Hand-written: `demos/ContractNI`'s `Store.lean` for the relation without a disclosure cell
(the observation, the ledger, the transcript and the disclosed values, unchanged by the store's
cases), at the checker that releases nothing.

What the relation needs about the fixture's store and labelling beyond the
generated `Spec.lean`: the level of an identifier is its label (`lev_id`, the checker's equation with
a map pattern), a high identifier is not low, a value passes the store's test (`storeOk`'s) and a
binding that passes it is typed low and quiet, the initial store, and the five per-rule cases that
read or write the store (`CONTRACT.var` in `CQ`, `SQ`, `SameQ`; `CONTRACT.assign` in `CQ`,
`SameQ`). -/

namespace ContractObsNI

open KPrelude

variable {G : Lab}

/-- The level of an identifier: its label. -/
def levId (G : Lab) (X : Contract.SortId) : Option Lvl :=
  if MapHook.wfb G = true then
    match MapHook.lookup G (ContractSecNR.SortKItem.inj_Id (tr_SortId X)) with
    | some (ContractSecNR.SortKItem.inj_Level L) => some L
    | _ => none
  else none

theorem lev_id (G : Lab) (X : Contract.SortId) : lev G (.inj_Id X) = levId G X := by
  simp only [lev, levId, k2l_tr]
  rw [ContractSecNR.K.«lev(_,_)_CONTRACTSEC_Level_Expr_Map».eq_def]
  simp only []
  by_cases hw : MapHook.wfb G = true
  · simp only [hw, dite_true, ite_true]
    split <;> rename_i hl <;> split at hl <;> rename_i hlk <;> (try split at hl) <;> simp_all
  · simp [hw]

theorem not_low_of_lev {G : Lab} {X : Contract.SortId} (h : lev G (.inj_Id X) = some .hi) : ¬ Low G X := by
  intro hl; unfold Low at hl; unfold lev at h; rw [hl] at h; cases h

/-- What the store's test unfolds to: the sort predicates of `storeOk`'s test. -/
local macro "k2l_test" : tactic => `(tactic| simp_all [Contract.Invariant.storeOk_test, BoolHook.or,
  BoolHook.not, Contract.K.isId, Contract.K.isId.rule1, Contract.K.isValue, Contract.K.isValue.rule1,
  Contract.proj_KItem_Value, lev.inj_Int, lev.inj_Bool, quiet.inj_Int, quiet.inj_Bool])

/-- A value passes the store's test. -/
theorem test_inj_Value (X : Contract.SortId) (V : Contract.SortValue) :
    Contract.Invariant.storeOk_test (.inj_Id X) (Contract.inj_Value_KItem V) := by
  k2l_cases V <;> rfl

theorem citem0_of_test (G : Lab) {X : Contract.SortId} {v : Contract.SortKItem}
    (h : Contract.Invariant.storeOk_test (.inj_Id X) v) : citem0 G v = some true := by
  k2l_cases v <;> k2l_test

theorem litem0_of_test (G : Lab) {X : Contract.SortId} {v : Contract.SortKItem}
    (h : Contract.Invariant.storeOk_test (.inj_Id X) v) : litem0 G v = some true := by
  k2l_cases v <;> k2l_test

theorem lev_hi_of_conf_assign {G : Lab} {X : Contract.SortId} {y : Contract.SortExpr}
    (h : conf G (.«_=_;» X y) = some true) : lev G (.inj_Id X) = some .hi := by
  rw [conf.«_=_;»] at h
  split at h
  · rename_i l q hl hq
    k2l_cases l <;> simp_all
  · simp at h

/-- The initial store: empty. -/
theorem good_init (P : Contract.SortStmt) (L : Contract.SortMap) (W : Contract.SortList) :
    Good (storeOf (Contract.init P L W)) := good_unit

/-! ## The per-rule cases that read or write the store -/

/-- `CONTRACT.var`, by hand: the looked-up value is a value, since the store is one. -/
theorem cq.«CONTRACT.var» (G : Lab) : Contract.Step.Rel.«CONTRACT.var» (CQ G) := by
  intro X D l w t d g m v D2 hm K hck hne hgood
  simp only [kOf, storeOf, CK_kseq, citem_false, citem0_inj_Id, quiet.inj_Id] at hck hne hgood ⊢
  have hv := hgood.lookup (MapHook.lookup_of_concat_element hm)
  refine ⟨Or.inr ?_, hiOnly_refl hgood, rfl⟩
  simp only [citem0_of_test G hv]
  simp_all
/-- `CONTRACT.assign`, by hand: a confined assignment writes a high identifier. -/
theorem cq.«CONTRACT.assign» (G : Lab) : Contract.Step.Rel.«CONTRACT.assign» (CQ G) := by
  intro X y D E l w t d g V hp K hck hne hgood
  simp only [kOf, storeOf, CK_kseq, citem_false, citem0_inj_Stmt] at hck hne hgood ⊢
  simp only [hne, false_or, and_false] at hck
  split at hck
  · rename_i o ho
    split at ho
    · rename_i hc
      cases ho
      exact ⟨hck, hiOnly_update hgood (not_low_of_lev (lev_hi_of_conf_assign hc)) (test_inj_Value X V), rfl⟩
    · cases ho
  · exact hck.elim
/-- `CONTRACT.var`, by hand: the looked-up value is a value. -/
theorem sq.«CONTRACT.var» (G : Lab) : Contract.Step.Rel.«CONTRACT.var» (SQ G) := by
  intro X D l w t d g m v D2 hm hlk hgood
  simp only [kOf, storeOf, lk_kseq, litem_false, litem0_inj_Id] at hlk hgood ⊢
  have hv := hgood.lookup (MapHook.lookup_of_concat_element hm)
  apply sq_base
  split at hlk
  · rename_i o ho
    split at ho
    · cases ho; simp [litem0_of_test G hv, hlk]
    · cases ho
  · cases hlk
/-- `CONTRACT.var`, by hand: a low identifier holds the same value in both stores. -/
theorem same.«CONTRACT.var» (G : Lab) : Contract.Step.Rel.«CONTRACT.var» (SameQ G) := by
  intro X D l w t d g m v D2 hm c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow, hpub⟩ := hS
  k2l_cases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, l₂, w₂, t₂, d₂, g₂⟩
  simp only [kOf, storeOf, pubOf, Prod.mk.injEq] at hk hlow hlk hpub ⊢
  obtain ⟨hl, ht, hd'⟩ := hpub
  subst hk hl ht hd'
  simp only [lk_kseq, litem_false, litem0_inj_Id] at hlk
  have hX : lev G (.inj_Id X) = some .lo :=
    Classical.byContradiction fun hn => by simp [hn] at hlk
  have hl₂ : MapHook.lookup E₂ (Contract.SortKItem.inj_Id X) = some v := by
    rw [← lowEq_lookup hlow (X := X) hX]; exact MapHook.lookup_of_concat_element hm
  have hd := Contract.Step.deterministic h₂
    (Contract.Step.«CONTRACT.var» X D _ w₂ _ _ g₂ E₂ v _ (MapHook.concat_element_remove hlow.2.1.wf hl₂))
  subst hd
  exact ⟨rfl, hlow, rfl⟩
/-- `CONTRACT.assign`, by hand: both runs assign the same value. -/
theorem same.«CONTRACT.assign» (G : Lab) : Contract.Step.Rel.«CONTRACT.assign» (SameQ G) := by
  intro X y D E l w t d g V hp c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow, hpub⟩ := hS
  k2l_cases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, l₂, w₂, t₂, d₂, g₂⟩
  simp only [kOf, storeOf, pubOf, Prod.mk.injEq] at hk hlow hpub ⊢
  obtain ⟨hl, ht, hd'⟩ := hpub
  subst hk hl ht hd'
  have hd := Contract.Step.deterministic h₂ (Contract.Step.«CONTRACT.assign» X y D E₂ _ w₂ _ _ g₂ V hp)
  subst hd
  exact ⟨rfl, lowEq_update hlow X (test_inj_Value X V), rfl⟩

end ContractObsNI
