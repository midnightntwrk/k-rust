import ImpTypes.Soundness
import KImp.Preserves
import KImp.Init
import KPrelude.InvTactic
import KPrelude.InvColl

/-! Hand-written. `preservation` of `Soundness.lean` through the generated per-rule principle
`KImp.Step.preserves_of` (`KImp/Preserves.lean`), and the generated initial configuration
`KImp.init` (`KImp/Init.lean`) against `Soundness.lean`'s hand-written `init`.

`wtc_preserved_of` takes the two store rules as hypotheses of `Step.preserves_of`'s types,
`KImp.Step.Case.«CALC.var» (WTc G)` and `KImp.Step.Case.«CALC.assign» (WTc G)`, and proves the
other 77 rules with `k2l_preserve` (the unfolding set of `Preserve.lean`). The goal that
`k2l_preserve` leaves for a rule is that rule's `Step.Case` with the rule's variables and side
conditions introduced, so each residual case is closed by applying its hypothesis.
`case_var` and `case_assign` are `Soundness.lean`'s hand proofs of the two cases, unchanged apart
from the `intro` that names the rule's variables. -/

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace ImpTypesPreservesOf

open KPrelude ImpTypes

/-- `CALC.var` keeps the runtime typing (the hand proof of `Soundness.lean`). -/
theorem case_var (G : TEnv) : KImp.Step.Case.«CALC.var» (WTc G) := by
  intro X K g m v D hm
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

/-- `CALC.assign` keeps the runtime typing (the hand proof of `Soundness.lean`). -/
theorem case_assign (G : TEnv) : KImp.Step.Case.«CALC.assign» (WTc G) := by
  intro X y K E g V hp
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

/-- The runtime typing is preserved by every rule, given the two store rules' cases of
`Step.preserves_of`; the other 77 rules by `k2l_preserve`. -/
theorem wtc_preserved_of (G : TEnv)
    («CALC.var» : KImp.Step.Case.«CALC.var» (WTc G))
    («CALC.assign» : KImp.Step.Case.«CALC.assign» (WTc G)) :
    Preserved KImp.Step (WTc G) := by
  k2l_preserve [kOf, envOf, kty_dotk, kty_kseq, item_none, item_frz, item0_int, item0_bool,
    item0_id, item0_expr, item0_stmt, item0_frz, plug, dflt, bin, una, same,
    KImp.proj_inj_KItem_Expr, KImp.proj_inj_KItem_Id, KImp.proj_inj_KItem_Stmt, item0_inj_Expr,
    item0_inj_Stmt, tyOf_dflt, tyOf_int, tyOf_bool, tyOf_neg, tyOf_not, tyOf_add, tyOf_sub,
    tyOf_mul, tyOf_div, tyOf_ge, tyOf_gt, tyOf_le, tyOf_lt, tyOf_eq, tyOf_ne, tyOf_and, tyOf_or,
    wtS_skip, wtS_block, wtS_assign, wtS_seq, wtS_ife, wtS_if, wtS_while] split [tyOf, wtS]
  case «CALC.var» X K g m v D hm => exact «CALC.var» X K g m v D hm
  case «CALC.assign» X y K E g V hp => exact «CALC.assign» X y K E g V hp

theorem wtc_preserved (G : TEnv) : Preserved KImp.Step (WTc G) :=
  wtc_preserved_of G (case_var G) (case_assign G)

/-- The direct form: `apply Step.preserves_of` leaves one goal `Step.Case.r (WTc G)` per rule,
`k2l_preserve` in its per-case mode closes 77 of them, and the two store rules remain as goals
tagged by their rules, with the rules' variables introduced. -/
theorem wtc_preserved_direct (G : TEnv) : Preserved KImp.Step (WTc G) := by
  apply KImp.Step.preserves_of
  all_goals k2l_preserve [kOf, envOf, kty_dotk, kty_kseq, item_none, item_frz, item0_int, item0_bool,
    item0_id, item0_expr, item0_stmt, item0_frz, plug, dflt, bin, una, same,
    KImp.proj_inj_KItem_Expr, KImp.proj_inj_KItem_Id, KImp.proj_inj_KItem_Stmt, item0_inj_Expr,
    item0_inj_Stmt, tyOf_dflt, tyOf_int, tyOf_bool, tyOf_neg, tyOf_not, tyOf_add, tyOf_sub,
    tyOf_mul, tyOf_div, tyOf_ge, tyOf_gt, tyOf_le, tyOf_lt, tyOf_eq, tyOf_ne, tyOf_and, tyOf_or,
    wtS_skip, wtS_block, wtS_assign, wtS_seq, wtS_ife, wtS_if, wtS_while] split [tyOf, wtS]
  case «CALC.var» => exact case_var G _ _ _ _ _ _ ‹_›
  case «CALC.assign» => exact case_assign G _ _ _ _ _ _ ‹_›

/-- The statement of `ImpTypes.preservation`. -/
theorem preservation {G : TEnv} {c c' : KImp.SortGeneratedTopCell} (h : KImp.Step c c') :
    WTc G c → WTc G c' :=
  fun hw => wtc_preserved G c c' hw h

/-! ## The generated initial configuration

`KImp.init P E` is the configuration `krun` starts from for `$PGM = P` and `$ENV = E`, with the
`<generatedCounter>` cell at its declared default `0`. `Soundness.lean`'s `init` leaves that cell
a parameter `g`, so the two agree at `g = <generatedCounter> 0`, and `soundness` holds from the
generated initial configuration. -/

theorem init_eq (P : KImp.SortStmt) (E : KImp.SortMap) :
    KImp.init P E = ImpTypes.init P E (.«<generatedCounter>» 0) := rfl

/-- **Type soundness** from the generated initial configuration. -/
theorem soundness_init {G : TEnv} {P : KImp.SortStmt} {E : KImp.SortMap}
    (hP : KImpTypes.K.«wt(_,_)_IMP-TYPING_Bool_Stmt_Map» (tr_SortStmt P) G = some true) (hE : envTy G E)
    {n : Nat} {c : KImp.SortGeneratedTopCell} (h : StepsN KImp.Step n (KImp.init P E) c) :
    Final c ∨ KImp.App c :=
  soundness hP hE (init_eq P E ▸ h)

#k2l_assert_axioms KImp.Step.preserves_of case_var case_assign wtc_preserved_of wtc_preserved preservation
#k2l_assert_axioms wtc_preserved_direct
#k2l_assert_axioms init_eq soundness_init

end ImpTypesPreservesOf
