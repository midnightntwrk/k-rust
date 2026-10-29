import ContractNI.Stack
import Contract.Determinism

/-! Hand-written. What the relation needs about the fixture's store and labelling, and the
lists of the disclosure cell: the level of an identifier is its label (`lev_id`, the checker's
equation with a map pattern), how stores and `lowEq` change under an update, `hiOnly_refl`,
`lowEq_symm`, `lowEq_hiOnly`, and appending to a list. -/

namespace ContractNI

open KPrelude

variable {G : Lab}

/-- The level of an identifier: its label. -/
def levId (G : Lab) (X : Contract.SortId) : Option Lvl :=
  if MapHook.wfb G = true then
    match MapHook.lookup G (ContractSec.SortKItem.inj_Id (tr_SortId X)) with
    | some (ContractSec.SortKItem.inj_Level L) => some L
    | _ => none
  else none

theorem lev_id (G : Lab) (X : Contract.SortId) : lev G (.inj_Id X) = levId G X := by
  simp only [lev, levId, k2l_tr]
  rw [ContractSec.K.«lev(_,_)_CONTRACTSEC_Level_Expr_Map».eq_def]
  simp only []
  by_cases hw : MapHook.wfb G = true
  · simp only [hw, dite_true, ite_true]
    split <;> rename_i hl <;> split at hl <;> rename_i hlk <;> (try split at hl) <;> simp_all
  · simp [hw]

theorem low_of_lev {G : Lab} {X : Contract.SortId} (h : lev G (.inj_Id X) = some .lo) : Low G X := by
  rw [lev_id, levId] at h
  unfold Low
  split at h
  · split at h <;> simp_all
  · simp at h

theorem not_low_of_lev {G : Lab} {X : Contract.SortId} (h : lev G (.inj_Id X) = some .hi) : ¬ Low G X := by
  rw [lev_id, levId] at h
  unfold Low
  intro hl
  split at h
  · simp [hl] at h
  · simp at h

theorem isVal_inj_Value (V : Contract.SortValue) : isVal (Contract.inj_Value_KItem V) = true := by
  k2l_cases V <;> rfl








theorem citem0_of_isVal (G : Lab) {v : Contract.SortKItem} (h : isVal v = true) : citem0 G v = some true := by
  k2l_cases v <;> simp_all [isVal, quiet.inj_Int, quiet.inj_Bool]

theorem litem0_of_isVal (G : Lab) {v : Contract.SortKItem} (h : isVal v = true) : litem0 G v = some true := by
  k2l_cases v <;> simp_all [isVal, lev.inj_Int, lev.inj_Bool]

theorem Good.lookup {E : Contract.SortMap} (hE : Good E) {X : Contract.SortId} {v : Contract.SortKItem}
    (h : MapHook.lookup E (Contract.SortKItem.inj_Id X) = some v) : isVal v = true := hE.2 X v h

theorem Good.update {E : Contract.SortMap} (hE : Good E) (X : Contract.SortId) (V : Contract.SortValue) :
    Good (MapHook.update E (Contract.SortKItem.inj_Id X) (Contract.inj_Value_KItem V)) := by
  refine ⟨MapHook.wf_update hE.1, fun X' v h => ?_⟩
  by_cases hx : X' = X
  · subst hx
    rw [MapHook.lookup_update_self] at h
    cases h; exact isVal_inj_Value V
  · rw [MapHook.lookup_update_ne _ _ (fun h => hx (by cases h; rfl))] at h
    exact hE.2 X' v h

theorem good_unit : Good (MapHook.unit : Contract.SortMap) :=
  ⟨MapHook.wf_unit, fun X v h => by simp [MapHook.lookup_unit] at h⟩

theorem hiOnly_refl {G : Lab} {E : Contract.SortMap} (hE : Good E) : HiOnly G E E := ⟨hE, fun _ _ => rfl⟩

theorem hiOnly_update {G : Lab} {E : Contract.SortMap} (hE : Good E) {X : Contract.SortId} (V : Contract.SortValue)
    (hX : lev G (.inj_Id X) = some .hi) :
    HiOnly G E (MapHook.update E (Contract.SortKItem.inj_Id X) (Contract.inj_Value_KItem V)) := by
  refine ⟨hE.update X V, fun X' hl => ?_⟩
  have hne : X' ≠ X := fun h => not_low_of_lev hX (h ▸ hl)
  rw [MapHook.lookup_update_ne _ _ (fun h => hne (by cases h; rfl))]

theorem lev_hi_of_conf_assign {G : Lab} {X : Contract.SortId} {y : Contract.SortExpr}
    (h : conf G (.«_=_;» X y) = some true) : lev G (.inj_Id X) = some .hi := by
  rw [conf.«_=_;»] at h
  split at h
  · rename_i l q hl hq
    k2l_cases l <;> simp_all
  · simp at h

theorem lowEq_update {G : Lab} {E₁ E₂ : Contract.SortMap} (h : lowEq G E₁ E₂) (X : Contract.SortId) (V : Contract.SortValue) :
    lowEq G (MapHook.update E₁ (Contract.SortKItem.inj_Id X) (Contract.inj_Value_KItem V))
      (MapHook.update E₂ (Contract.SortKItem.inj_Id X) (Contract.inj_Value_KItem V)) := by
  refine ⟨h.1.update X V, h.2.1.update X V, fun X' hl => ?_⟩
  by_cases hx : X' = X
  · subst hx; rw [MapHook.lookup_update_self, MapHook.lookup_update_self]
  · have hne : Contract.SortKItem.inj_Id X' ≠ Contract.SortKItem.inj_Id X := fun h => hx (by cases h; rfl)
    rw [MapHook.lookup_update_ne _ _ hne, MapHook.lookup_update_ne _ _ hne]
    exact h.2.2 X' hl

theorem lowEq_lookup {G : Lab} {E₁ E₂ : Contract.SortMap} (h : lowEq G E₁ E₂) {X : Contract.SortId}
    (hX : lev G (.inj_Id X) = some .lo) :
    MapHook.lookup E₁ (Contract.SortKItem.inj_Id X) = MapHook.lookup E₂ (Contract.SortKItem.inj_Id X) :=
  h.2.2 X (low_of_lev hX)

theorem lowEq_symm {E₁ E₂ : Contract.SortMap} (h : lowEq G E₁ E₂) : lowEq G E₂ E₁ :=
  ⟨h.2.1, h.1, fun X hX => (h.2.2 X hX).symm⟩

theorem lowEq_hiOnly {E₁ E₁' E₂ : Contract.SortMap} (h : lowEq G E₁ E₂) (h' : HiOnly G E₁ E₁') :
    lowEq G E₁' E₂ :=
  ⟨h'.1, h.2.1, fun X hX => (h'.2 X hX).symm.trans (h.2.2 X hX)⟩


theorem lowEq_refl {E : Contract.SortMap} (h : Good E) : lowEq G E E := ⟨h, h, fun _ _ => rfl⟩

/-- The initial store: empty. -/
theorem good_init (P : Contract.SortStmt) (L : Contract.SortMap) (W : Contract.SortList) :
    Good (storeOf (Contract.init P L W)) := good_unit

/-! ## The per-rule cases that read or write the store -/

/-- `CONTRACT.var`, by hand: the looked-up value is a value, since the store is one. -/
theorem cq.«CONTRACT.var» (G : Lab) : Contract.Step.Rel.«CONTRACT.var» (CQ G) := by
  intro X D l w t d g m v D2 hm K b₀ hck hne hgood
  k2l_cases_cells
  simp only [kOf, storeOf, pubOf, discOf, CK_kseq, citem_false, citem0_inj_Id, quiet.inj_Id] at hck hne hgood ⊢
  have hv := hgood.lookup (MapHook.lookup_of_concat_element hm)
  refine ⟨Or.inr ?_, hiOnly_refl hgood, trivial, trivial⟩
  simp only [citem0_of_isVal G hv]
  cases b₀ <;> simp_all
/-- `CONTRACT.assign`, by hand: a confined assignment writes a high identifier. -/
theorem cq.«CONTRACT.assign» (G : Lab) : Contract.Step.Rel.«CONTRACT.assign» (CQ G) := by
  intro X y D E l w t d g V hp K b₀ hck hne hgood
  k2l_cases_cells
  simp only [kOf, storeOf, pubOf, discOf, CK_kseq, citem_false, citem0_inj_Stmt] at hck hne hgood ⊢
  have hck' := hck.resolve_left (fun ⟨h1, h2⟩ => by cases b₀ <;> simp_all)
  split at hck'
  · rename_i o ho
    split at ho
    · rename_i hc
      cases ho
      exact ⟨hck', hiOnly_update hgood V (lev_hi_of_conf_assign hc), trivial, trivial⟩
    · cases ho
  · exact hck'.elim
/-- `CONTRACT.var`, by hand: the looked-up value is a value. -/
theorem sq.«CONTRACT.var» (G : Lab) : Contract.Step.Rel.«CONTRACT.var» (SQ G) := by
  intro X D l w t d g m v D2 hm hlk hgood
  simp only [kOf, storeOf, lk_kseq, litem_false, litem0_inj_Id] at hlk hgood ⊢
  have hv := hgood.lookup (MapHook.lookup_of_concat_element hm)
  apply sq_base
  split at hlk
  · rename_i o ho
    split at ho
    · cases ho; simp [litem0_of_isVal G hv, hlk]
    · cases ho
  · cases hlk
/-- `CONTRACT.var`, by hand: a low identifier holds the same value in both stores. -/
theorem same.«CONTRACT.var» (G : Lab) : Contract.Step.Rel.«CONTRACT.var» (SameQ G) := by
  intro X D l w t d g m v D2 hm c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow, hpub, hdisc⟩ := hS
  k2l_cases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, l₂, w₂, t₂, d₂, g₂⟩
  k2l_cases_cells
  simp only [kOf, storeOf, pubOf, discOf, Prod.mk.injEq] at hk hlow hlk hpub hdisc ⊢
  obtain ⟨hl, ht⟩ := hpub
  subst hk hl ht hdisc
  simp only [lk_kseq, litem_false, litem0_inj_Id] at hlk
  have hX : lev G (.inj_Id X) = some .lo :=
    Classical.byContradiction fun hn => by simp [hn] at hlk
  have hl₂ : MapHook.lookup E₂ (Contract.SortKItem.inj_Id X) = some v := by
    rw [← lowEq_lookup hlow hX]; exact MapHook.lookup_of_concat_element hm
  have hd := Contract.Step.deterministic h₂
    (Contract.Step.«CONTRACT.var» X D _ w₂ _ _ g₂ E₂ v _ (MapHook.concat_element_remove hlow.2.1.1 hl₂))
  subst hd
  exact ⟨rfl, hlow, rfl, rfl⟩
/-- `CONTRACT.assign`, by hand: both runs assign the same value. -/
theorem same.«CONTRACT.assign» (G : Lab) : Contract.Step.Rel.«CONTRACT.assign» (SameQ G) := by
  intro X y D E l w t d g V hp c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow, hpub, hdisc⟩ := hS
  k2l_cases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, l₂, w₂, t₂, d₂, g₂⟩
  k2l_cases_cells
  simp only [kOf, storeOf, pubOf, discOf, Prod.mk.injEq] at hk hlow hpub hdisc ⊢
  obtain ⟨hl, ht⟩ := hpub
  subst hk hl ht hdisc
  have hd := Contract.Step.deterministic h₂ (Contract.Step.«CONTRACT.assign» X y D E₂ _ w₂ _ _ g₂ V hp)
  subst hd
  exact ⟨rfl, lowEq_update hlow X V, rfl, rfl⟩

end ContractNI
