import ContractOwiseNI.Stack
import ContractOw.Determinism

/-! Hand-written: `demos/ContractNI`'s `Store.lean` over contractow (the fixture contract with
`owise` rules), unchanged but for the namespaces.

What the relation needs about the fixture's store and labelling beyond the generated `Spec.lean`: a
high identifier is not low (an identifier's level is its label, `lev_id`, generated in
`Levels.lean`), a value passes the store's test (`storeOk`'s) and a binding that passes it is typed
low and quiet, the initial store, and the five per-rule cases that read or write the store
(`CONTRACT.var` in `CQ`, `SQ`, `SameQ`; `CONTRACT.assign` in `CQ`, `SameQ`). -/

namespace ContractOwiseNI

open KPrelude

variable {G : Lab}

theorem not_low_of_lev {G : Lab} {X : ContractOw.SortId} (h : lev G (.inj_Id X) = some .hi) : ¬ Low G X := by
  intro hl; unfold Low at hl; unfold lev at h; rw [hl] at h; cases h

/-- What the store's test unfolds to: the sort predicates of `storeOk`'s test. -/
local macro "k2l_test" : tactic => `(tactic| simp_all [ContractOw.Invariant.storeOk_test, BoolHook.or,
  BoolHook.not, ContractOw.K.isId, ContractOw.K.isId.rule1, ContractOw.K.isValue, ContractOw.K.isValue.rule1,
  ContractOw.proj_KItem_Value, lev.inj_Int, lev.inj_Bool, quiet.inj_Int, quiet.inj_Bool])

/-- A value passes the store's test. -/
theorem test_inj_Value (X : ContractOw.SortId) (V : ContractOw.SortValue) :
    ContractOw.Invariant.storeOk_test (.inj_Id X) (ContractOw.inj_Value_KItem V) := by
  k2l_cases V <;> rfl

theorem citem0_of_test (G : Lab) {X : ContractOw.SortId} {v : ContractOw.SortKItem}
    (h : ContractOw.Invariant.storeOk_test (.inj_Id X) v) : citem0 G v = some true := by
  k2l_cases v <;> k2l_test

theorem litem0_of_test (G : Lab) {X : ContractOw.SortId} {v : ContractOw.SortKItem}
    (h : ContractOw.Invariant.storeOk_test (.inj_Id X) v) : litem0 G v = some true := by
  k2l_cases v <;> k2l_test

theorem lev_hi_of_conf_assign {G : Lab} {X : ContractOw.SortId} {y : ContractOw.SortExpr}
    (h : conf G (.«_=_;» X y) = some true) : lev G (.inj_Id X) = some .hi := by
  rw [conf.«_=_;»] at h
  split at h
  · rename_i l q hl hq
    k2l_cases l <;> simp_all
  · simp at h

/-- The initial store: empty. -/
theorem good_init (P : ContractOw.SortStmt) (L : ContractOw.SortMap) (W : ContractOw.SortList) :
    Good (storeOf (ContractOw.init P L W)) := good_unit

/-! ## The per-rule cases that read or write the store -/

/-- `CONTRACT.var`, by hand: the looked-up value is a value, since the store is one. -/
theorem cq.«CONTRACT.var» (G : Lab) : ContractOw.Step.Rel.«CONTRACT.var» (CQ G) := by
  intro X D l w t d g m v D2 hm K b₀ hck hne hgood
  k2l_cases_cells
  simp only [kOf, storeOf, pubOf, discOf, CK_kseq, citem_false, citem0_inj_Id, quiet.inj_Id] at hck hne hgood ⊢
  have hv := hgood.lookup (MapHook.lookup_of_concat_element hm)
  refine ⟨Or.inr ?_, hiOnly_refl hgood, trivial, trivial⟩
  simp only [citem0_of_test G hv]
  cases b₀ <;> simp_all
/-- `CONTRACT.assign`, by hand: a confined assignment writes a high identifier. -/
theorem cq.«CONTRACT.assign» (G : Lab) : ContractOw.Step.Rel.«CONTRACT.assign» (CQ G) := by
  intro X y D E l w t d g V hp K b₀ hck hne hgood
  k2l_cases_cells
  simp only [kOf, storeOf, pubOf, discOf, CK_kseq, citem_false, citem0_inj_Stmt] at hck hne hgood ⊢
  have hck' := hck.resolve_left (fun ⟨h1, h2⟩ => by cases b₀ <;> simp_all)
  split at hck'
  · rename_i o ho
    split at ho
    · rename_i hc
      cases ho
      exact ⟨hck', hiOnly_update hgood (not_low_of_lev (lev_hi_of_conf_assign hc)) (test_inj_Value X V), trivial, trivial⟩
    · cases ho
  · exact hck'.elim
/-- `CONTRACT.var`, by hand: the looked-up value is a value. -/
theorem sq.«CONTRACT.var» (G : Lab) : ContractOw.Step.Rel.«CONTRACT.var» (SQ G) := by
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
theorem same.«CONTRACT.var» (G : Lab) : ContractOw.Step.Rel.«CONTRACT.var» (SameQ G) := by
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
  have hl₂ : MapHook.lookup E₂ (ContractOw.SortKItem.inj_Id X) = some v := by
    rw [← lowEq_lookup hlow (X := X) hX]; exact MapHook.lookup_of_concat_element hm
  have hd := ContractOw.Step.deterministic h₂
    (ContractOw.Step.«CONTRACT.var» X D _ w₂ _ _ g₂ E₂ v _ (MapHook.concat_element_remove hlow.2.1.wf hl₂))
  subst hd
  exact ⟨rfl, hlow, rfl, rfl⟩
/-- `CONTRACT.assign`, by hand: both runs assign the same value. -/
theorem same.«CONTRACT.assign» (G : Lab) : ContractOw.Step.Rel.«CONTRACT.assign» (SameQ G) := by
  intro X y D E l w t d g V hp c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow, hpub, hdisc⟩ := hS
  k2l_cases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, l₂, w₂, t₂, d₂, g₂⟩
  k2l_cases_cells
  simp only [kOf, storeOf, pubOf, discOf, Prod.mk.injEq] at hk hlow hpub hdisc ⊢
  obtain ⟨hl, ht⟩ := hpub
  subst hk hl ht hdisc
  have hd := ContractOw.Step.deterministic h₂ (ContractOw.Step.«CONTRACT.assign» X y D E₂ _ w₂ _ _ g₂ V hp)
  subst hd
  exact ⟨rfl, lowEq_update hlow X (test_inj_Value X V), rfl, rfl⟩

end ContractOwiseNI
