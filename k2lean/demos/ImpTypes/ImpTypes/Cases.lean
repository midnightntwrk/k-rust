import ImpTypes.Invariant
import KImp.Preserves
import KPrelude.InvTactic
import KPrelude.InvColl

/-!
# Every rule of kimp keeps the runtime typing `WTc G` (kind 2 layout: `Cases.lean`)

HAND-WRITTEN. `preserved` applies the generated per-rule principle `KImp.Step.preserves_of`
(`KImp/Preserves.lean`) through `k2l_preserve … hand ImpTypes.hand`: the case of rule `r` is the
theorem `ImpTypes.hand.r` below when it exists, and is closed by `k2l_preserve`'s closers
otherwise (77 of kimp's 79 rules). Each hand case is stated as the generated
`KImp.Step.Case.r (WTc G)`, by reference, so an edit of rule `r` in kimp changes what its hand
case must prove and no other statement here.

Hand cases (the rules that read or write the store, whose typing needs the store typing):
- `CALC.var` (calc.k): a variable is looked up;
- `CALC.assign` (calc.k): a value is assigned.
-/

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace ImpTypes

open KPrelude

namespace hand

/-! ## HAND CASE `CALC.var`: `<k> X:Id => V ...</k> <env> X |-> V ...</env>`

The looked-up value `v` is the store's value at `X`, and the store typing says that it has the
type of `X`, which is the type the continuation expects. -/

theorem «CALC.var» (G : TEnv) : KImp.Step.Case.«CALC.var» (WTc G) := by
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

/-! ## HAND CASE `CALC.assign`: `<k> X = V:Value ; => .K ...</k> <env> E => E [ X <- V ] </env>`

A well-typed assignment stores a value of `X`'s type at `X`, so the updated store is typed; the
other keys keep their values. -/

theorem «CALC.assign» (G : TEnv) : KImp.Step.Case.«CALC.assign» (WTc G) := by
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

-- k2lean new-invariant --from-log: new hand cases go above this line
end hand

/-! ## Every rule

The unfolding set is how `WTc` computes (`Invariant.lean`); `split [tyOf, wtS]` names the two
typing functions whose values the computation cases on. -/

/-- The runtime typing is preserved by every rule of kimp. -/
theorem preserved (G : TEnv) : Preserved KImp.Step (WTc G) := by
  k2l_preserve [kOf, envOf, kty_dotk, kty_kseq, item_none, item_frz, item0_int, item0_bool,
    item0_id, item0_expr, item0_stmt, item0_frz, plug, dflt, bin, una, same,
    KImp.proj_inj_KItem_Expr, KImp.proj_inj_KItem_Id, KImp.proj_inj_KItem_Stmt, item0_inj_Expr,
    item0_inj_Stmt, tyOf_dflt, tyOf_int, tyOf_bool, tyOf_neg, tyOf_not, tyOf_add, tyOf_sub,
    tyOf_mul, tyOf_div, tyOf_ge, tyOf_gt, tyOf_le, tyOf_lt, tyOf_eq, tyOf_ne, tyOf_and, tyOf_or,
    wtS_skip, wtS_block, wtS_assign, wtS_seq, wtS_ife, wtS_if, wtS_while] split [tyOf, wtS]
    hand ImpTypes.hand

end ImpTypes
