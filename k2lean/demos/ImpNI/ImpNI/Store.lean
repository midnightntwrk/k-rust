import ImpNI.Stack
import KImpNI.Determinism

/-! Hand-written. What the generated relation (`Stack.lean`, `Proof.lean`) needs about kimp's store
and the labelling beyond the generated `Spec.lean`: the level of an identifier is its label (`lev_id`,
the checker's equation with a map pattern, which gets no generated inversion lemma), a high
identifier is not low, a value passes the store's test (`storeOk`'s) and a binding that passes it is
typed low and confined, and the five per-rule cases that read or write the store (`CALC.var` in `CQ`,
`SQ`, `SameQ`; `CALC.assign` in `CQ`, `SameQ`). -/

namespace ImpNI

open KPrelude

variable {G : Lab}

/-- The level of an identifier: its label. -/
def levId (G : Lab) (X : KImpNI.SortId) : Option Lvl :=
  if MapHook.wfb G = true then
    match MapHook.lookup G (KImpSec.SortKItem.inj_Id (tr_SortId X)) with
    | some (KImpSec.SortKItem.inj_Level L) => some L
    | _ => none
  else none

theorem lev_id (G : Lab) (X : KImpNI.SortId) : lev G (.inj_Id X) = levId G X := by
  simp only [lev, levId, k2l_tr]
  rw [KImpSec.K.«lev(_,_)_IMP-SEC_Level_Expr_Map».eq_def]
  simp only []
  by_cases hw : MapHook.wfb G = true
  · simp only [hw, dite_true, ite_true]
    split <;> rename_i hl <;> split at hl <;> rename_i hlk <;> (try split at hl) <;> simp_all
  · simp [hw]

theorem not_low_of_lev {G : Lab} {X : KImpNI.SortId} (h : lev G (.inj_Id X) = some .hi) : ¬ Low G X := by
  intro hl; unfold Low at hl; unfold lev at h; rw [hl] at h; cases h

/-- What the store's test unfolds to: the sort predicates of `storeOk`'s test. -/
local macro "k2l_test" : tactic => `(tactic| simp_all [KImpNI.Invariant.storeOk_test, BoolHook.or,
  BoolHook.not, KImpNI.K.isId, KImpNI.K.isId.rule1, KImpNI.K.isValue, KImpNI.K.isValue.rule1,
  KImpNI.proj_KItem_Value, lev.inj_Int, lev.inj_Bool])

/-- A value passes the store's test. -/
theorem test_inj_Value (X : KImpNI.SortId) (V : KImpNI.SortValue) :
    KImpNI.Invariant.storeOk_test (.inj_Id X) (KImpNI.inj_Value_KItem V) := by
  k2l_cases V <;> rfl

theorem citem0_of_test (G : Lab) {X : KImpNI.SortId} {v : KImpNI.SortKItem}
    (h : KImpNI.Invariant.storeOk_test (.inj_Id X) v) : citem0 G v = some true := by
  k2l_cases v <;> k2l_test

theorem litem0_of_test (G : Lab) {X : KImpNI.SortId} {v : KImpNI.SortKItem}
    (h : KImpNI.Invariant.storeOk_test (.inj_Id X) v) : litem0 G v = some true := by
  k2l_cases v <;> k2l_test

theorem lev_hi_of_conf_assign {G : Lab} {X : KImpNI.SortId} {y : KImpNI.SortExpr}
    (h : conf G (.«_=_;» X y) = some true) : lev G (.inj_Id X) = some .hi := by
  rw [conf.«_=_;»] at h
  split at h
  · rename_i l hl
    k2l_cases l <;> simp_all
  · simp at h


/-! ## The per-rule cases that read or write the store -/

/-- `CALC.var`, by hand: the looked-up value is a value, since the store is one. -/
theorem cq.«CALC.var» (G : Lab) : KImpNI.Step.Rel.«CALC.var» (CQ G) := by
  intro X D g m v D2 hm K hck hne hgood
  simp only [kOf, storeOf, CK_kseq, citem_false, citem0_inj_Id] at hck hne hgood ⊢
  have hv := hgood.lookup (MapHook.lookup_of_concat_element hm)
  refine ⟨Or.inr ?_, hiOnly_refl hgood⟩
  simp only [citem0_of_test G hv]
  simp_all
/-- `CALC.assign`, by hand: a confined assignment writes a high identifier. -/
theorem cq.«CALC.assign» (G : Lab) : KImpNI.Step.Rel.«CALC.assign» (CQ G) := by
  intro X y D E g V hp K hck hne hgood
  simp only [kOf, storeOf, CK_kseq, citem_false, citem0_inj_Stmt] at hck hne hgood ⊢
  simp only [hne, false_or, and_false] at hck
  split at hck
  · rename_i o ho
    split at ho
    · rename_i hc
      cases ho
      exact ⟨hck, hiOnly_update hgood (not_low_of_lev (lev_hi_of_conf_assign hc)) (test_inj_Value X V)⟩
    · cases ho
  · exact hck.elim
theorem sq.«CALC.var» (G : Lab) : KImpNI.Step.Rel.«CALC.var» (SQ G) := by
  intro X D g m v D2 hm hlk hgood
  simp only [kOf, storeOf, lk_kseq, litem_false, litem0_inj_Id] at hlk hgood ⊢
  have hv := hgood.lookup (MapHook.lookup_of_concat_element hm)
  apply sq_base
  split at hlk
  · rename_i o ho
    split at ho
    · cases ho; simp [litem0_of_test G hv, hlk]
    · cases ho
  · cases hlk
/-- `CALC.var`, by hand: a low identifier holds the same value in both stores. -/
theorem same.«CALC.var» (G : Lab) : KImpNI.Step.Rel.«CALC.var» (SameQ G) := by
  intro X D g m v D2 hm c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow⟩ := hS
  k2l_cases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, g₂⟩
  simp only [kOf, storeOf] at hk hlow hlk ⊢
  subst hk
  simp only [lk_kseq, litem_false, litem0_inj_Id] at hlk
  have hX : lev G (.inj_Id X) = some .lo :=
    Classical.byContradiction fun hn => by simp [hn] at hlk
  have hl₂ : MapHook.lookup E₂ (KImpNI.SortKItem.inj_Id X) = some v := by
    rw [← lowEq_lookup hlow (X := X) hX]; exact MapHook.lookup_of_concat_element hm
  have hd := KImpNI.Step.deterministic h₂
    (KImpNI.Step.«CALC.var» X D g₂ E₂ v _ (MapHook.concat_element_remove hlow.2.1.wf hl₂))
  subst hd
  exact ⟨rfl, hlow⟩
/-- `CALC.assign`, by hand: both runs assign the same value. -/
theorem same.«CALC.assign» (G : Lab) : KImpNI.Step.Rel.«CALC.assign» (SameQ G) := by
  intro X y D E g V hp c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow⟩ := hS
  k2l_cases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, g₂⟩
  simp only [kOf, storeOf] at hk hlow ⊢
  subst hk
  have hd := KImpNI.Step.deterministic h₂ (KImpNI.Step.«CALC.assign» X y D E₂ g₂ V hp)
  subst hd
  exact ⟨rfl, lowEq_update hlow X (test_inj_Value X V)⟩

end ImpNI
