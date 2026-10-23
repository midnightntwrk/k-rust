import ImpTypes.Soundness
import KPrelude.InvTactic
import KPrelude.InvColl

/-! Hand-written. `preservation` of `Soundness.lean` (the runtime typing `WTc G` of kimp
configurations, for the K type checker `imp-typing.k`), re-proved with the invariant core
(`KPrelude.Invariant`) and `k2l_preserve` only: no `pres_auto`, `ty_cases` or `ty_simp`.

The unfolding set is the runtime typing's definitions and characterization lemmas (sections 1–3
of `Soundness.lean`, imported): it says how `WTc` computes. `split [tyOf, wtS]` names the two
typing functions whose values the computation cases on. The two store rules are the residual
goals `«CALC.var»` and `«CALC.assign»`; their proofs are `Soundness.lean`'s hand proofs,
unchanged. -/

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace ImpTypesPres

open KPrelude ImpTypes

theorem wtc_preserved (G : TEnv) : Preserved KImp.Step (WTc G) := by
  k2l_preserve [kOf, envOf, kty_dotk, kty_kseq, item_none, item_frz, item0_int, item0_bool,
    item0_id, item0_expr, item0_stmt, item0_frz, plug, dflt, bin, una, same,
    KImp.proj_inj_KItem_Expr, KImp.proj_inj_KItem_Id, KImp.proj_inj_KItem_Stmt, item0_inj_Expr,
    item0_inj_Stmt, tyOf_dflt, tyOf_int, tyOf_bool, tyOf_neg, tyOf_not, tyOf_add, tyOf_sub,
    tyOf_mul, tyOf_div, tyOf_ge, tyOf_gt, tyOf_le, tyOf_lt, tyOf_eq, tyOf_ne, tyOf_and, tyOf_or,
    wtS_skip, wtS_block, wtS_assign, wtS_seq, wtS_ife, wtS_if, wtS_while] split [tyOf, wtS]
  -- HAND-WRITTEN (from `Soundness.lean`): the two rules that read or write the store
  case «CALC.var» X K g m v D hm =>
    rintro ⟨hk, he⟩
    simp only [WTc, kOf, envOf, envTyC] at hk he ⊢
    refine ⟨?_, he⟩
    simp only [kty_kseq, item_none, item0_id] at hk ⊢
    cases ht : tyOf G (.inj_Id X) with
    | none => simp [ht] at hk
    | some t =>
      simp only [ht, Option.map_some] at hk
      obtain ⟨v', hl, hv⟩ := he.2 X t ht
      rw [MapHook.lookup_of_concat_element hm] at hl
      obtain rfl := Option.some.inj hl
      cases v <;> simp_all [valTy, item_none, item0_int, item0_bool]
  case «CALC.assign» X y K E g V hp =>
    rintro ⟨hk, he⟩
    simp only [WTc, kOf, envOf, envTyC] at hk he ⊢
    rw [KImp.proj_eq_some_Expr_Value] at hp
    subst hp
    simp only [kty_kseq, item_none, item0_stmt, wtS_assign] at hk
    by_cases hw : ∃ t, tyOf G (.inj_Id X) = some t ∧ tyOf G (KImp.inj_Value_Expr V) = some t
    · simp only [hw, decide_true, ite_true] at hk
      refine ⟨hk, MapHook.wf_update he.1, ?_⟩
      intro x t hx
      obtain ⟨t₀, h₁, h₂⟩ := hw
      by_cases hxX : x = X
      · subst hxX
        refine ⟨KImp.inj_Value_KItem V, ?_, ?_⟩
        · rw [MapHook.lookup_def, MapHook.update_def, ListIso.toList_ofList]; exact SAL.lookup_insert_self _ _ _
        · rw [← tyOf_value, h₂, ← h₁, hx]
      · obtain ⟨v, hl, hv⟩ := he.2 x t hx
        refine ⟨v, ?_, hv⟩
        rw [MapHook.lookup_def, MapHook.update_def, ListIso.toList_ofList, SAL_lookup_insert_ne]
        · rwa [← MapHook.lookup_def]
        · intro h; exact hxX (by cases h; rfl)
    · simp [hw] at hk

/-- The statement of `ImpTypes.preservation`. -/
theorem preservation {G : TEnv} {c c' : KImp.SortGeneratedTopCell} (h : KImp.Step c c') :
    WTc G c → WTc G c' :=
  fun hw => wtc_preserved G c c' hw h

#k2l_assert_axioms wtc_preserved preservation

end ImpTypesPres
