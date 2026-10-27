import ImpNI.Stack
import KImp.Determinism

/-! Hand-written. What the generated relation (`Stack.lean`, `Proof.lean`) needs about kimp's store
and the labelling: the level of an identifier is its label (`lev_id`, the checker's equation with a
map pattern, which gets no generated inversion lemma), how stores and `lowEq` change under an update,
`hiOnly_refl`, `lowEq_symm`, `lowEq_hiOnly`, and the five per-rule cases that read or write the store
(`CALC.var` in `CQ`, `SQ`, `SameQ`; `CALC.assign` in `CQ`, `SameQ`). -/

namespace ImpNI

open KPrelude

variable {G : Lab}

/-- The level of an identifier: its label. -/
def levId (G : Lab) (X : KImp.SortId) : Option Lvl :=
  if MapHook.wfb G = true then
    match MapHook.lookup G (KImpSec.SortKItem.inj_Id (tr_SortId X)) with
    | some (KImpSec.SortKItem.inj_Level L) => some L
    | _ => none
  else none

theorem lev_id (G : Lab) (X : KImp.SortId) : lev G (.inj_Id X) = levId G X := by
  simp only [lev, levId, k2l_tr]
  rw [KImpSec.K.«lev(_,_)_IMP-SEC_Level_Expr_Map».eq_def]
  simp only []
  by_cases hw : MapHook.wfb G = true
  · simp only [hw, dite_true, ite_true]
    split <;> rename_i hl <;> split at hl <;> rename_i hlk <;> (try split at hl) <;> simp_all
  · simp [hw]

theorem low_of_lev {G : Lab} {X : KImp.SortId} (h : lev G (.inj_Id X) = some .lo) : Low G X := by
  rw [lev_id, levId] at h
  unfold Low
  split at h
  · split at h <;> simp_all
  · simp at h

theorem not_low_of_lev {G : Lab} {X : KImp.SortId} (h : lev G (.inj_Id X) = some .hi) : ¬ Low G X := by
  rw [lev_id, levId] at h
  unfold Low
  intro hl
  split at h
  · simp [hl] at h
  · simp at h

theorem isVal_inj_Value (V : KImp.SortValue) : isVal (KImp.inj_Value_KItem V) = true := by
  k2l_cases V <;> rfl

theorem citem0_of_isVal (G : Lab) {v : KImp.SortKItem} (h : isVal v = true) : citem0 G v = some true := by
  k2l_cases v <;> simp_all [isVal]

theorem litem0_of_isVal (G : Lab) {v : KImp.SortKItem} (h : isVal v = true) : litem0 G v = some true := by
  k2l_cases v <;> simp_all [isVal, lev.inj_Int, lev.inj_Bool]

theorem Good.lookup {E : KImp.SortMap} (hE : Good E) {X : KImp.SortId} {v : KImp.SortKItem}
    (h : MapHook.lookup E (KImp.SortKItem.inj_Id X) = some v) : isVal v = true := hE.2 X v h

theorem Good.update {E : KImp.SortMap} (hE : Good E) (X : KImp.SortId) (V : KImp.SortValue) :
    Good (MapHook.update E (KImp.SortKItem.inj_Id X) (KImp.inj_Value_KItem V)) := by
  refine ⟨MapHook.wf_update hE.1, fun X' v h => ?_⟩
  by_cases hx : X' = X
  · subst hx
    rw [MapHook.lookup_update_self] at h
    cases h; exact isVal_inj_Value V
  · rw [MapHook.lookup_update_ne _ _ (fun h => hx (by cases h; rfl))] at h
    exact hE.2 X' v h

theorem hiOnly_refl {G : Lab} {E : KImp.SortMap} (hE : Good E) : HiOnly G E E := ⟨hE, fun _ _ => rfl⟩

theorem hiOnly_update {G : Lab} {E : KImp.SortMap} (hE : Good E) {X : KImp.SortId} (V : KImp.SortValue)
    (hX : lev G (.inj_Id X) = some .hi) :
    HiOnly G E (MapHook.update E (KImp.SortKItem.inj_Id X) (KImp.inj_Value_KItem V)) := by
  refine ⟨hE.update X V, fun X' hl => ?_⟩
  have hne : X' ≠ X := fun h => not_low_of_lev hX (h ▸ hl)
  rw [MapHook.lookup_update_ne _ _ (fun h => hne (by cases h; rfl))]

theorem lev_hi_of_conf_assign {G : Lab} {X : KImp.SortId} {y : KImp.SortExpr}
    (h : conf G (.«_=_;» X y) = some true) : lev G (.inj_Id X) = some .hi := by
  rw [conf.«_=_;»] at h
  split at h
  · rename_i l hl
    k2l_cases l <;> simp_all
  · simp at h

theorem lowEq_update {G : Lab} {E₁ E₂ : KImp.SortMap} (h : lowEq G E₁ E₂) (X : KImp.SortId) (V : KImp.SortValue) :
    lowEq G (MapHook.update E₁ (KImp.SortKItem.inj_Id X) (KImp.inj_Value_KItem V))
      (MapHook.update E₂ (KImp.SortKItem.inj_Id X) (KImp.inj_Value_KItem V)) := by
  refine ⟨h.1.update X V, h.2.1.update X V, fun X' hl => ?_⟩
  by_cases hx : X' = X
  · subst hx; rw [MapHook.lookup_update_self, MapHook.lookup_update_self]
  · have hne : KImp.SortKItem.inj_Id X' ≠ KImp.SortKItem.inj_Id X := fun h => hx (by cases h; rfl)
    rw [MapHook.lookup_update_ne _ _ hne, MapHook.lookup_update_ne _ _ hne]
    exact h.2.2 X' hl

theorem lowEq_lookup {G : Lab} {E₁ E₂ : KImp.SortMap} (h : lowEq G E₁ E₂) {X : KImp.SortId}
    (hX : lev G (.inj_Id X) = some .lo) :
    MapHook.lookup E₁ (KImp.SortKItem.inj_Id X) = MapHook.lookup E₂ (KImp.SortKItem.inj_Id X) :=
  h.2.2 X (low_of_lev hX)

theorem lowEq_symm {E₁ E₂ : KImp.SortMap} (h : lowEq G E₁ E₂) : lowEq G E₂ E₁ :=
  ⟨h.2.1, h.1, fun X hX => (h.2.2 X hX).symm⟩

theorem lowEq_hiOnly {E₁ E₁' E₂ : KImp.SortMap} (h : lowEq G E₁ E₂) (h' : HiOnly G E₁ E₁') :
    lowEq G E₁' E₂ :=
  ⟨h'.1, h.2.1, fun X hX => (h'.2 X hX).symm.trans (h.2.2 X hX)⟩


/-! ## The per-rule cases that read or write the store -/

/-- `CALC.var`, by hand: the looked-up value is a value, since the store is one. -/
theorem cq.«CALC.var» (G : Lab) : KImp.Step.Rel.«CALC.var» (CQ G) := by
  intro X D g m v D2 hm K hck hne hgood
  simp only [kOf, storeOf, CK_kseq, citem_false, citem0_inj_Id] at hck hne hgood ⊢
  have hv := hgood.lookup (MapHook.lookup_of_concat_element hm)
  refine ⟨Or.inr ?_, hiOnly_refl hgood⟩
  simp only [citem0_of_isVal G hv]
  simp_all
/-- `CALC.assign`, by hand: a confined assignment writes a high identifier. -/
theorem cq.«CALC.assign» (G : Lab) : KImp.Step.Rel.«CALC.assign» (CQ G) := by
  intro X y D E g V hp K hck hne hgood
  simp only [kOf, storeOf, CK_kseq, citem_false, citem0_inj_Stmt] at hck hne hgood ⊢
  simp only [hne, false_or, and_false] at hck
  split at hck
  · rename_i o ho
    split at ho
    · rename_i hc
      cases ho
      exact ⟨hck, hiOnly_update hgood V (lev_hi_of_conf_assign hc)⟩
    · cases ho
  · exact hck.elim
theorem sq.«CALC.var» (G : Lab) : KImp.Step.Rel.«CALC.var» (SQ G) := by
  intro X D g m v D2 hm hlk hgood
  simp only [kOf, storeOf, lk_kseq, litem_false, litem0_inj_Id] at hlk hgood ⊢
  have hv := hgood.lookup (MapHook.lookup_of_concat_element hm)
  apply sq_base
  split at hlk
  · rename_i o ho
    split at ho
    · cases ho; simp [litem0_of_isVal G hv, hlk]
    · cases ho
  · cases hlk
/-- `CALC.var`, by hand: a low identifier holds the same value in both stores. -/
theorem same.«CALC.var» (G : Lab) : KImp.Step.Rel.«CALC.var» (SameQ G) := by
  intro X D g m v D2 hm c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow⟩ := hS
  k2l_cases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, g₂⟩
  simp only [kOf, storeOf] at hk hlow hlk ⊢
  subst hk
  simp only [lk_kseq, litem_false, litem0_inj_Id] at hlk
  have hX : lev G (.inj_Id X) = some .lo :=
    Classical.byContradiction fun hn => by simp [hn] at hlk
  have hl₂ : MapHook.lookup E₂ (KImp.SortKItem.inj_Id X) = some v := by
    rw [← lowEq_lookup hlow hX]; exact MapHook.lookup_of_concat_element hm
  have hd := KImp.Step.deterministic h₂
    (KImp.Step.«CALC.var» X D g₂ E₂ v _ (MapHook.concat_element_remove hlow.2.1.1 hl₂))
  subst hd
  exact ⟨rfl, hlow⟩
/-- `CALC.assign`, by hand: both runs assign the same value. -/
theorem same.«CALC.assign» (G : Lab) : KImp.Step.Rel.«CALC.assign» (SameQ G) := by
  intro X y D E g V hp c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow⟩ := hS
  k2l_cases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, g₂⟩
  simp only [kOf, storeOf] at hk hlow ⊢
  subst hk
  have hd := KImp.Step.deterministic h₂ (KImp.Step.«CALC.assign» X y D E₂ g₂ V hp)
  subst hd
  exact ⟨rfl, lowEq_update hlow X V⟩

end ImpNI
