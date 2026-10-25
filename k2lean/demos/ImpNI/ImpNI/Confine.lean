import ImpNI.Stack
import ImpNI.NI

namespace ImpNI

open KPrelude

/-- A step of a run inside a confined stack keeps it a confined stack over the same continuation,
and changes the store only at high identifiers. -/
def CQ (G : Lab) (c c' : KImp.SortGeneratedTopCell) : Prop :=
  ∀ K, CK G K false (kOf c) → kOf c ≠ K → Good (storeOf c) →
    CK G K false (kOf c') ∧ HiOnly G (storeOf c) (storeOf c')

/-- The generic case of `CQ`. -/
macro "k2l_cq" : tactic => `(tactic| (
  intros
  k2l_cases_env
  unfold CQ
  intro K hck hne hgood
  simp only [kOf, storeOf, CK_kseq] at hck hne hgood ⊢
  refine ⟨?_, ?_⟩
  all_goals first
    | exact ⟨hgood, fun _ _ => rfl⟩
    | (try simp only [KImp.proj_eq_some_KItem_Expr] at *
       try subst_vars
       try k2l_ni_comp)))

theorem cq.«- X» (G : Lab) : KImp.Step.Rel.«- X» (CQ G) := by
  unfold KImp.Step.Rel.«- X»
  k2l_cq
theorem cq.«! B» (G : Lab) : KImp.Step.Rel.«! B» (CQ G) := by
  unfold KImp.Step.Rel.«! B»
  k2l_cq
theorem cq.«X + Y» (G : Lab) : KImp.Step.Rel.«X + Y» (CQ G) := by
  unfold KImp.Step.Rel.«X + Y»
  k2l_cq
theorem cq.«X - Y» (G : Lab) : KImp.Step.Rel.«X - Y» (CQ G) := by
  unfold KImp.Step.Rel.«X - Y»
  k2l_cq
theorem cq.«X * Y» (G : Lab) : KImp.Step.Rel.«X * Y» (CQ G) := by
  unfold KImp.Step.Rel.«X * Y»
  k2l_cq
theorem cq.«X / Y» (G : Lab) : KImp.Step.Rel.«X / Y» (CQ G) := by
  unfold KImp.Step.Rel.«X / Y»
  k2l_cq
theorem cq.«I1 >= I2» (G : Lab) : KImp.Step.Rel.«I1 >= I2» (CQ G) := by
  unfold KImp.Step.Rel.«I1 >= I2»
  k2l_cq
theorem cq.«I1 > I2» (G : Lab) : KImp.Step.Rel.«I1 > I2» (CQ G) := by
  unfold KImp.Step.Rel.«I1 > I2»
  k2l_cq
theorem cq.«I1 <= I2» (G : Lab) : KImp.Step.Rel.«I1 <= I2» (CQ G) := by
  unfold KImp.Step.Rel.«I1 <= I2»
  k2l_cq
theorem cq.«I1 < I2» (G : Lab) : KImp.Step.Rel.«I1 < I2» (CQ G) := by
  unfold KImp.Step.Rel.«I1 < I2»
  k2l_cq
theorem cq.«B1 == B2» (G : Lab) : KImp.Step.Rel.«B1 == B2» (CQ G) := by
  unfold KImp.Step.Rel.«B1 == B2»
  k2l_cq
theorem cq.«I1 == I2» (G : Lab) : KImp.Step.Rel.«I1 == I2» (CQ G) := by
  unfold KImp.Step.Rel.«I1 == I2»
  k2l_cq
theorem cq.«B1 != B2» (G : Lab) : KImp.Step.Rel.«B1 != B2» (CQ G) := by
  unfold KImp.Step.Rel.«B1 != B2»
  k2l_cq
theorem cq.«I1 != I2» (G : Lab) : KImp.Step.Rel.«I1 != I2» (CQ G) := by
  unfold KImp.Step.Rel.«I1 != I2»
  k2l_cq
theorem cq.«true && B» (G : Lab) : KImp.Step.Rel.«true && B» (CQ G) := by
  unfold KImp.Step.Rel.«true && B»
  k2l_cq
theorem cq.«false && _» (G : Lab) : KImp.Step.Rel.«false && _» (CQ G) := by
  unfold KImp.Step.Rel.«false && _»
  k2l_cq
theorem cq.«true || _» (G : Lab) : KImp.Step.Rel.«true || _» (CQ G) := by
  unfold KImp.Step.Rel.«true || _»
  k2l_cq
theorem cq.«false || B» (G : Lab) : KImp.Step.Rel.«false || B» (CQ G) := by
  unfold KImp.Step.Rel.«false || B»
  k2l_cq
theorem cq.«CALC.step» (G : Lab) : KImp.Step.Rel.«CALC.step» (CQ G) := by
  unfold KImp.Step.Rel.«CALC.step»
  k2l_cq
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
theorem cq.«IMP.if-true» (G : Lab) : KImp.Step.Rel.«IMP.if-true» (CQ G) := by
  unfold KImp.Step.Rel.«IMP.if-true»
  k2l_cq
theorem cq.«IMP.if-false» (G : Lab) : KImp.Step.Rel.«IMP.if-false» (CQ G) := by
  unfold KImp.Step.Rel.«IMP.if-false»
  k2l_cq
theorem cq.«IMP.if-else» (G : Lab) : KImp.Step.Rel.«IMP.if-else» (CQ G) := by
  unfold KImp.Step.Rel.«IMP.if-else»
  k2l_cq
theorem cq.«IMP.while» (G : Lab) : KImp.Step.Rel.«IMP.while» (CQ G) := by
  unfold KImp.Step.Rel.«IMP.while»
  k2l_cq
theorem cq.«IMP.block» (G : Lab) : KImp.Step.Rel.«IMP.block» (CQ G) := by
  unfold KImp.Step.Rel.«IMP.block»
  k2l_cq
theorem cq.«IMP.done» (G : Lab) : KImp.Step.Rel.«IMP.done» (CQ G) := by
  unfold KImp.Step.Rel.«IMP.done»
  k2l_cq
theorem cq.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_cq
theorem cq.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_cq
theorem cq.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_cq
theorem cq.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» (G : Lab) : KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» (CQ G) := by
  unfold KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat»
  k2l_cq
theorem cq.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» (G : Lab) : KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» (CQ G) := by
  unfold KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool»
  k2l_cq
theorem cq.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» (G : Lab) : KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» (CQ G) := by
  unfold KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat»
  k2l_cq
theorem cq.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» (G : Lab) : KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» (CQ G) := by
  unfold KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool»
  k2l_cq

/-- Every step keeps a confined stack confined (`CQ`). -/
theorem cq_step (G : Lab) {c c' : KImp.SortGeneratedTopCell} (h : KImp.Step c c') : CQ G c c' :=
  KImp.Step.rel_of (cq.«- X» G) (cq.«! B» G) (cq.«X + Y» G) (cq.«X - Y» G) (cq.«X * Y» G) (cq.«X / Y» G) (cq.«I1 >= I2» G) (cq.«I1 > I2» G) (cq.«I1 <= I2» G) (cq.«I1 < I2» G) (cq.«B1 == B2» G) (cq.«I1 == I2» G) (cq.«B1 != B2» G) (cq.«I1 != I2» G) (cq.«true && B» G) (cq.«false && _» G) (cq.«true || _» G) (cq.«false || B» G) (cq.«CALC.step» G) (cq.«CALC.var» G) (cq.«CALC.assign» G) (cq.«IMP.if-true» G) (cq.«IMP.if-false» G) (cq.«IMP.if-else» G) (cq.«IMP.while» G) (cq.«IMP.block» G) (cq.«IMP.done» G) (cq.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (cq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (cq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (cq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (cq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (cq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (cq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (cq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (cq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (cq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (cq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (cq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (cq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (cq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (cq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (cq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (cq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (cq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (cq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (cq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (cq.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (cq.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (cq.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (cq.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» G) (cq.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» G) (cq.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» G) (cq.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» G) h

end ImpNI
