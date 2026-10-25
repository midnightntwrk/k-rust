import ImpNI.Confine

namespace ImpNI

open KPrelude

/-- The first `n` items of `<k>` dropped. -/
def dropK : Nat → KImp.SortK → KImp.SortK
  | 0, k => k
  | _ + 1, .dotk => .dotk
  | n + 1, .kseq _ k => dropK n k

/-- A step from a low stack leads to a confined stack over a low stack (the confined part is empty
unless the step enters a high assignment or a branch on a high condition). -/
def SQ (G : Lab) (c c' : KImp.SortGeneratedTopCell) : Prop :=
  lk G false (kOf c) = true → Good (storeOf c) → ∃ K, CK G K false (kOf c') ∧ lk G false K = true

theorem sq_base {G : Lab} {k : KImp.SortK} (h : lk G false k = true) :
    ∃ K, CK G K false k ∧ lk G false K = true := ⟨k, CK_base G k, h⟩

theorem sq_drop2 {G : Lab} {k : KImp.SortK} (h₁ : CK G (dropK 2 k) false k)
    (h₂ : lk G false (dropK 2 k) = true) : ∃ K, CK G K false k ∧ lk G false K = true :=
  ⟨_, h₁, h₂⟩

macro "k2l_sq" : tactic => `(tactic| (
  intros
  k2l_cases_env
  unfold SQ
  intro hlk hgood
  simp only [kOf, storeOf] at hlk hgood ⊢
  try simp only [KImp.proj_eq_some_KItem_Expr] at *
  try subst_vars
  try k2l_ni_simp
  try k2l_ni_split
  all_goals (try k2l_ni_simp)
  all_goals first
    | (apply sq_base; k2l_ni_comp; done)
    | (apply sq_drop2 <;> simp only [dropK, CK_kseq] <;> k2l_ni_comp <;> done)
    | skip))

theorem sq.«- X» (G : Lab) : KImp.Step.Rel.«- X» (SQ G) := by
  unfold KImp.Step.Rel.«- X»
  k2l_sq
theorem sq.«! B» (G : Lab) : KImp.Step.Rel.«! B» (SQ G) := by
  unfold KImp.Step.Rel.«! B»
  k2l_sq
theorem sq.«X + Y» (G : Lab) : KImp.Step.Rel.«X + Y» (SQ G) := by
  unfold KImp.Step.Rel.«X + Y»
  k2l_sq
theorem sq.«X - Y» (G : Lab) : KImp.Step.Rel.«X - Y» (SQ G) := by
  unfold KImp.Step.Rel.«X - Y»
  k2l_sq
theorem sq.«X * Y» (G : Lab) : KImp.Step.Rel.«X * Y» (SQ G) := by
  unfold KImp.Step.Rel.«X * Y»
  k2l_sq
theorem sq.«X / Y» (G : Lab) : KImp.Step.Rel.«X / Y» (SQ G) := by
  unfold KImp.Step.Rel.«X / Y»
  k2l_sq
theorem sq.«I1 >= I2» (G : Lab) : KImp.Step.Rel.«I1 >= I2» (SQ G) := by
  unfold KImp.Step.Rel.«I1 >= I2»
  k2l_sq
theorem sq.«I1 > I2» (G : Lab) : KImp.Step.Rel.«I1 > I2» (SQ G) := by
  unfold KImp.Step.Rel.«I1 > I2»
  k2l_sq
theorem sq.«I1 <= I2» (G : Lab) : KImp.Step.Rel.«I1 <= I2» (SQ G) := by
  unfold KImp.Step.Rel.«I1 <= I2»
  k2l_sq
theorem sq.«I1 < I2» (G : Lab) : KImp.Step.Rel.«I1 < I2» (SQ G) := by
  unfold KImp.Step.Rel.«I1 < I2»
  k2l_sq
theorem sq.«B1 == B2» (G : Lab) : KImp.Step.Rel.«B1 == B2» (SQ G) := by
  unfold KImp.Step.Rel.«B1 == B2»
  k2l_sq
theorem sq.«I1 == I2» (G : Lab) : KImp.Step.Rel.«I1 == I2» (SQ G) := by
  unfold KImp.Step.Rel.«I1 == I2»
  k2l_sq
theorem sq.«B1 != B2» (G : Lab) : KImp.Step.Rel.«B1 != B2» (SQ G) := by
  unfold KImp.Step.Rel.«B1 != B2»
  k2l_sq
theorem sq.«I1 != I2» (G : Lab) : KImp.Step.Rel.«I1 != I2» (SQ G) := by
  unfold KImp.Step.Rel.«I1 != I2»
  k2l_sq
theorem sq.«true && B» (G : Lab) : KImp.Step.Rel.«true && B» (SQ G) := by
  unfold KImp.Step.Rel.«true && B»
  k2l_sq
theorem sq.«false && _» (G : Lab) : KImp.Step.Rel.«false && _» (SQ G) := by
  unfold KImp.Step.Rel.«false && _»
  k2l_sq
theorem sq.«true || _» (G : Lab) : KImp.Step.Rel.«true || _» (SQ G) := by
  unfold KImp.Step.Rel.«true || _»
  k2l_sq
theorem sq.«false || B» (G : Lab) : KImp.Step.Rel.«false || B» (SQ G) := by
  unfold KImp.Step.Rel.«false || B»
  k2l_sq
theorem sq.«CALC.step» (G : Lab) : KImp.Step.Rel.«CALC.step» (SQ G) := by
  unfold KImp.Step.Rel.«CALC.step»
  k2l_sq
/-- `CALC.var`, by hand: the looked-up value is a value, since the store is one. -/
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
theorem sq.«CALC.assign» (G : Lab) : KImp.Step.Rel.«CALC.assign» (SQ G) := by
  unfold KImp.Step.Rel.«CALC.assign»
  k2l_sq
theorem sq.«IMP.if-true» (G : Lab) : KImp.Step.Rel.«IMP.if-true» (SQ G) := by
  unfold KImp.Step.Rel.«IMP.if-true»
  k2l_sq
theorem sq.«IMP.if-false» (G : Lab) : KImp.Step.Rel.«IMP.if-false» (SQ G) := by
  unfold KImp.Step.Rel.«IMP.if-false»
  k2l_sq
theorem sq.«IMP.if-else» (G : Lab) : KImp.Step.Rel.«IMP.if-else» (SQ G) := by
  unfold KImp.Step.Rel.«IMP.if-else»
  k2l_sq
theorem sq.«IMP.while» (G : Lab) : KImp.Step.Rel.«IMP.while» (SQ G) := by
  unfold KImp.Step.Rel.«IMP.while»
  k2l_sq
theorem sq.«IMP.block» (G : Lab) : KImp.Step.Rel.«IMP.block» (SQ G) := by
  unfold KImp.Step.Rel.«IMP.block»
  k2l_sq
theorem sq.«IMP.done» (G : Lab) : KImp.Step.Rel.«IMP.done» (SQ G) := by
  unfold KImp.Step.Rel.«IMP.done»
  k2l_sq
theorem sq.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_sq
theorem sq.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_sq
theorem sq.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_sq
theorem sq.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» (G : Lab) : KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» (SQ G) := by
  unfold KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat»
  k2l_sq
theorem sq.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» (G : Lab) : KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» (SQ G) := by
  unfold KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool»
  k2l_sq
theorem sq.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» (G : Lab) : KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» (SQ G) := by
  unfold KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat»
  k2l_sq
theorem sq.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» (G : Lab) : KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» (SQ G) := by
  unfold KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool»
  k2l_sq

/-- A step from a low stack (`SQ`). -/
theorem sq_step (G : Lab) {c c' : KImp.SortGeneratedTopCell} (h : KImp.Step c c') : SQ G c c' :=
  KImp.Step.rel_of (sq.«- X» G) (sq.«! B» G) (sq.«X + Y» G) (sq.«X - Y» G) (sq.«X * Y» G) (sq.«X / Y» G) (sq.«I1 >= I2» G) (sq.«I1 > I2» G) (sq.«I1 <= I2» G) (sq.«I1 < I2» G) (sq.«B1 == B2» G) (sq.«I1 == I2» G) (sq.«B1 != B2» G) (sq.«I1 != I2» G) (sq.«true && B» G) (sq.«false && _» G) (sq.«true || _» G) (sq.«false || B» G) (sq.«CALC.step» G) (sq.«CALC.var» G) (sq.«CALC.assign» G) (sq.«IMP.if-true» G) (sq.«IMP.if-false» G) (sq.«IMP.if-else» G) (sq.«IMP.while» G) (sq.«IMP.block» G) (sq.«IMP.done» G) (sq.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (sq.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (sq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (sq.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (sq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (sq.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (sq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (sq.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (sq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (sq.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (sq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (sq.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (sq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (sq.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (sq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (sq.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (sq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (sq.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (sq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (sq.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (sq.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (sq.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (sq.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (sq.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» G) (sq.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» G) (sq.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» G) (sq.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» G) h

end ImpNI
