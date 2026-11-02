import ImpOutNI.Stack
import KImpOutNI.Determinism

/-! Hand-written: `demos/ImpNI`'s `Store.lean` over kimpoutni (kimp with `print` to a plain
`<output>` cell), with the output, observed, unchanged by the store's cases.

What the generated relation (`Stack.lean`, `Proof.lean`) needs about kimp's store and the labelling
beyond the generated `Spec.lean`: a high identifier is not low (an identifier's level is its label,
`lev_id`, generated in `Levels.lean`), a value passes the store's test (`storeOk`'s) and a binding
that passes it is typed low and confined, and the five per-rule cases that read or write the store
(`CALC.var` in `CQ`, `SQ`, `SameQ`; `CALC.assign` in `CQ`, `SameQ`). -/

namespace ImpOutNI

open KPrelude

variable {G : Lab}

theorem not_low_of_lev {G : Lab} {X : KImpOutNI.SortId} (h : lev G (.inj_Id X) = some .hi) : ¬ Low G X := by
  intro hl; unfold Low at hl; unfold lev at h; rw [hl] at h; cases h

/-- What the store's test unfolds to: the sort predicates of `storeOk`'s test. -/
local macro "k2l_test" : tactic => `(tactic| simp_all [KImpOutNI.Invariant.storeOk_test, BoolHook.or,
  BoolHook.not, KImpOutNI.K.isId, KImpOutNI.K.isId.rule1, KImpOutNI.K.isValue, KImpOutNI.K.isValue.rule1,
  KImpOutNI.proj_KItem_Value, lev.inj_Int, lev.inj_Bool])

/-- A value passes the store's test. -/
theorem test_inj_Value (X : KImpOutNI.SortId) (V : KImpOutNI.SortValue) :
    KImpOutNI.Invariant.storeOk_test (.inj_Id X) (KImpOutNI.inj_Value_KItem V) := by
  k2l_cases V <;> rfl

theorem citem0_of_test (G : Lab) {X : KImpOutNI.SortId} {v : KImpOutNI.SortKItem}
    (h : KImpOutNI.Invariant.storeOk_test (.inj_Id X) v) : citem0 G v = some true := by
  k2l_cases v <;> k2l_test

theorem litem0_of_test (G : Lab) {X : KImpOutNI.SortId} {v : KImpOutNI.SortKItem}
    (h : KImpOutNI.Invariant.storeOk_test (.inj_Id X) v) : litem0 G v = some true := by
  k2l_cases v <;> k2l_test

theorem lev_hi_of_conf_assign {G : Lab} {X : KImpOutNI.SortId} {y : KImpOutNI.SortExpr}
    (h : conf G (.«_=_;» X y) = some true) : lev G (.inj_Id X) = some .hi := by
  rw [conf.«_=_;»] at h
  split at h
  · rename_i l hl
    k2l_cases l <;> simp_all
  · simp at h


/-! ## The per-rule cases that read or write the store -/

/-- `CALC.var`, by hand: the looked-up value is a value, since the store is one. -/
theorem cq.«CALC.var» (G : Lab) : KImpOutNI.Step.Rel.«CALC.var» (CQ G) := by
  intro X D o g m v D2 hm K hck hne hgood
  simp only [kOf, storeOf, CK_kseq, citem_false, citem0_inj_Id] at hck hne hgood ⊢
  have hv := hgood.lookup (MapHook.lookup_of_concat_element hm)
  refine ⟨Or.inr ?_, hiOnly_refl hgood, rfl⟩
  simp only [citem0_of_test G hv]
  simp_all
/-- `CALC.assign`, by hand: a confined assignment writes a high identifier. -/
theorem cq.«CALC.assign» (G : Lab) : KImpOutNI.Step.Rel.«CALC.assign» (CQ G) := by
  intro X y D E o g V hp K hck hne hgood
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
theorem sq.«CALC.var» (G : Lab) : KImpOutNI.Step.Rel.«CALC.var» (SQ G) := by
  intro X D o g m v D2 hm hlk hgood
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
theorem same.«CALC.var» (G : Lab) : KImpOutNI.Step.Rel.«CALC.var» (SameQ G) := by
  intro X D o g m v D2 hm c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow, hpub⟩ := hS
  k2l_cases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, o₂, g₂⟩
  simp only [kOf, storeOf, pubOf] at hk hlow hlk hpub ⊢
  subst hk hpub
  simp only [lk_kseq, litem_false, litem0_inj_Id] at hlk
  have hX : lev G (.inj_Id X) = some .lo :=
    Classical.byContradiction fun hn => by simp [hn] at hlk
  have hl₂ : MapHook.lookup E₂ (KImpOutNI.SortKItem.inj_Id X) = some v := by
    rw [← lowEq_lookup hlow (X := X) hX]; exact MapHook.lookup_of_concat_element hm
  have hd := KImpOutNI.Step.deterministic h₂
    (KImpOutNI.Step.«CALC.var» X D o g₂ E₂ v _ (MapHook.concat_element_remove hlow.2.1.wf hl₂))
  subst hd
  exact ⟨rfl, hlow, rfl⟩
/-- `CALC.assign`, by hand: both runs assign the same value. -/
theorem same.«CALC.assign» (G : Lab) : KImpOutNI.Step.Rel.«CALC.assign» (SameQ G) := by
  intro X y D E o g V hp c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow, hpub⟩ := hS
  k2l_cases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, o₂, g₂⟩
  simp only [kOf, storeOf, pubOf] at hk hlow hpub ⊢
  subst hk hpub
  have hd := KImpOutNI.Step.deterministic h₂ (KImpOutNI.Step.«CALC.assign» X y D E₂ o g₂ V hp)
  subst hd
  exact ⟨rfl, lowEq_update hlow X (test_inj_Value X V), rfl⟩

end ImpOutNI
