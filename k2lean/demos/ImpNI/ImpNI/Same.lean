import ImpNI.Sync
import KImp.Determinism

namespace ImpNI

open KPrelude

/-- Both runs at the same low stack, with low-equal stores. -/
def Sync (G : Lab) (c₁ c₂ : KImp.SortGeneratedTopCell) : Prop :=
  kOf c₁ = kOf c₂ ∧ lk G false (kOf c₁) = true ∧ lowEq G (storeOf c₁) (storeOf c₂)

/-- From the same low stack, the other run steps to the same stack, with low-equal stores. -/
def SameQ (G : Lab) (c₁ c₁' : KImp.SortGeneratedTopCell) : Prop :=
  ∀ c₂ c₂', Sync G c₁ c₂ → KImp.Step c₂ c₂' → kOf c₁' = kOf c₂' ∧ lowEq G (storeOf c₁') (storeOf c₂')

/-- The generic case of `SameQ` for the rule whose `Step` constructor is `c`: the other run takes
the same rule (`Step.deterministic`), which reads and writes no store. -/
macro "k2l_same " c:ident : tactic => `(tactic| (
  intros
  unfold SameQ
  intro c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow⟩ := hS
  rcases c₂ with ⟨⟨k₂⟩, e₂, g₂⟩
  simp only [kOf] at hk
  subst hk
  have hd := KImp.Step.deterministic h₂ (by apply $c <;> assumption)
  subst hd
  k2l_cases_env
  simp only [kOf, storeOf] at hlow ⊢
  first
    | (simp only [true_and]; assumption)
    | exact ⟨rfl, by assumption⟩))

theorem same.«- X» (G : Lab) : KImp.Step.Rel.«- X» (SameQ G) := by
  unfold KImp.Step.Rel.«- X»
  k2l_same KImp.Step.«- X»
theorem same.«! B» (G : Lab) : KImp.Step.Rel.«! B» (SameQ G) := by
  unfold KImp.Step.Rel.«! B»
  k2l_same KImp.Step.«! B»
theorem same.«X + Y» (G : Lab) : KImp.Step.Rel.«X + Y» (SameQ G) := by
  unfold KImp.Step.Rel.«X + Y»
  k2l_same KImp.Step.«X + Y»
theorem same.«X - Y» (G : Lab) : KImp.Step.Rel.«X - Y» (SameQ G) := by
  unfold KImp.Step.Rel.«X - Y»
  k2l_same KImp.Step.«X - Y»
theorem same.«X * Y» (G : Lab) : KImp.Step.Rel.«X * Y» (SameQ G) := by
  unfold KImp.Step.Rel.«X * Y»
  k2l_same KImp.Step.«X * Y»
theorem same.«X / Y» (G : Lab) : KImp.Step.Rel.«X / Y» (SameQ G) := by
  unfold KImp.Step.Rel.«X / Y»
  k2l_same KImp.Step.«X / Y»
theorem same.«I1 >= I2» (G : Lab) : KImp.Step.Rel.«I1 >= I2» (SameQ G) := by
  unfold KImp.Step.Rel.«I1 >= I2»
  k2l_same KImp.Step.«I1 >= I2»
theorem same.«I1 > I2» (G : Lab) : KImp.Step.Rel.«I1 > I2» (SameQ G) := by
  unfold KImp.Step.Rel.«I1 > I2»
  k2l_same KImp.Step.«I1 > I2»
theorem same.«I1 <= I2» (G : Lab) : KImp.Step.Rel.«I1 <= I2» (SameQ G) := by
  unfold KImp.Step.Rel.«I1 <= I2»
  k2l_same KImp.Step.«I1 <= I2»
theorem same.«I1 < I2» (G : Lab) : KImp.Step.Rel.«I1 < I2» (SameQ G) := by
  unfold KImp.Step.Rel.«I1 < I2»
  k2l_same KImp.Step.«I1 < I2»
theorem same.«B1 == B2» (G : Lab) : KImp.Step.Rel.«B1 == B2» (SameQ G) := by
  unfold KImp.Step.Rel.«B1 == B2»
  k2l_same KImp.Step.«B1 == B2»
theorem same.«I1 == I2» (G : Lab) : KImp.Step.Rel.«I1 == I2» (SameQ G) := by
  unfold KImp.Step.Rel.«I1 == I2»
  k2l_same KImp.Step.«I1 == I2»
theorem same.«B1 != B2» (G : Lab) : KImp.Step.Rel.«B1 != B2» (SameQ G) := by
  unfold KImp.Step.Rel.«B1 != B2»
  k2l_same KImp.Step.«B1 != B2»
theorem same.«I1 != I2» (G : Lab) : KImp.Step.Rel.«I1 != I2» (SameQ G) := by
  unfold KImp.Step.Rel.«I1 != I2»
  k2l_same KImp.Step.«I1 != I2»
theorem same.«true && B» (G : Lab) : KImp.Step.Rel.«true && B» (SameQ G) := by
  unfold KImp.Step.Rel.«true && B»
  k2l_same KImp.Step.«true && B»
theorem same.«false && _» (G : Lab) : KImp.Step.Rel.«false && _» (SameQ G) := by
  unfold KImp.Step.Rel.«false && _»
  k2l_same KImp.Step.«false && _»
theorem same.«true || _» (G : Lab) : KImp.Step.Rel.«true || _» (SameQ G) := by
  unfold KImp.Step.Rel.«true || _»
  k2l_same KImp.Step.«true || _»
theorem same.«false || B» (G : Lab) : KImp.Step.Rel.«false || B» (SameQ G) := by
  unfold KImp.Step.Rel.«false || B»
  k2l_same KImp.Step.«false || B»
theorem same.«CALC.step» (G : Lab) : KImp.Step.Rel.«CALC.step» (SameQ G) := by
  unfold KImp.Step.Rel.«CALC.step»
  k2l_same KImp.Step.«CALC.step»
/-- `CALC.var`, by hand: a low identifier holds the same value in both stores. -/
theorem same.«CALC.var» (G : Lab) : KImp.Step.Rel.«CALC.var» (SameQ G) := by
  intro X D g m v D2 hm c₂ c₂' hS h₂
  obtain ⟨hk, hlk, hlow⟩ := hS
  rcases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, g₂⟩
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
  rcases c₂ with ⟨⟨k₂⟩, ⟨E₂⟩, g₂⟩
  simp only [kOf, storeOf] at hk hlow ⊢
  subst hk
  have hd := KImp.Step.deterministic h₂ (KImp.Step.«CALC.assign» X y D E₂ g₂ V hp)
  subst hd
  exact ⟨rfl, lowEq_update hlow X V⟩
theorem same.«IMP.if-true» (G : Lab) : KImp.Step.Rel.«IMP.if-true» (SameQ G) := by
  unfold KImp.Step.Rel.«IMP.if-true»
  k2l_same KImp.Step.«IMP.if-true»
theorem same.«IMP.if-false» (G : Lab) : KImp.Step.Rel.«IMP.if-false» (SameQ G) := by
  unfold KImp.Step.Rel.«IMP.if-false»
  k2l_same KImp.Step.«IMP.if-false»
theorem same.«IMP.if-else» (G : Lab) : KImp.Step.Rel.«IMP.if-else» (SameQ G) := by
  unfold KImp.Step.Rel.«IMP.if-else»
  k2l_same KImp.Step.«IMP.if-else»
theorem same.«IMP.while» (G : Lab) : KImp.Step.Rel.«IMP.while» (SameQ G) := by
  unfold KImp.Step.Rel.«IMP.while»
  k2l_same KImp.Step.«IMP.while»
theorem same.«IMP.block» (G : Lab) : KImp.Step.Rel.«IMP.block» (SameQ G) := by
  unfold KImp.Step.Rel.«IMP.block»
  k2l_same KImp.Step.«IMP.block»
theorem same.«IMP.done» (G : Lab) : KImp.Step.Rel.«IMP.done» (SameQ G) := by
  unfold KImp.Step.Rel.«IMP.done»
  k2l_same KImp.Step.«IMP.done»
theorem same.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
theorem same.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
theorem same.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
theorem same.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
theorem same.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
theorem same.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
theorem same.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
theorem same.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
theorem same.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
theorem same.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
theorem same.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
theorem same.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
theorem same.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
theorem same.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
theorem same.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
theorem same.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
theorem same.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
theorem same.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
theorem same.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat»
theorem same.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool»
theorem same.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
theorem same.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
  k2l_same KImp.Step.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat»
theorem same.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (G : Lab) : KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
  k2l_same KImp.Step.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool»
theorem same.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» (G : Lab) : KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat»
  k2l_same KImp.Step.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat»
theorem same.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» (G : Lab) : KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool»
  k2l_same KImp.Step.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool»
theorem same.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» (G : Lab) : KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» (SameQ G) := by
  unfold KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat»
  k2l_same KImp.Step.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat»
theorem same.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» (G : Lab) : KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» (SameQ G) := by
  unfold KImp.Step.Rel.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool»
  k2l_same KImp.Step.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool»

/-- From the same low stack, both runs step to the same stack (`SameQ`). -/
theorem same_step (G : Lab) {c c' : KImp.SortGeneratedTopCell} (h : KImp.Step c c') : SameQ G c c' :=
  KImp.Step.rel_of (same.«- X» G) (same.«! B» G) (same.«X + Y» G) (same.«X - Y» G) (same.«X * Y» G) (same.«X / Y» G) (same.«I1 >= I2» G) (same.«I1 > I2» G) (same.«I1 <= I2» G) (same.«I1 < I2» G) (same.«B1 == B2» G) (same.«I1 == I2» G) (same.«B1 != B2» G) (same.«I1 != I2» G) (same.«true && B» G) (same.«false && _» G) (same.«true || _» G) (same.«false || B» G) (same.«CALC.step» G) (same.«CALC.var» G) (same.«CALC.assign» G) (same.«IMP.if-true» G) (same.«IMP.if-false» G) (same.«IMP.if-else» G) (same.«IMP.while» G) (same.«IMP.block» G) (same.«IMP.done» G) (same.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX.-__EXPR-SYNTAX_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX.!__EXPR-SYNTAX_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (same.«EXPR-SYNTAX._*__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (same.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (same.«EXPR-SYNTAX._/__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (same.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (same.«EXPR-SYNTAX._+__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (same.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (same.«EXPR-SYNTAX._-__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (same.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (same.«EXPR-SYNTAX._>=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (same.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (same.«EXPR-SYNTAX._>__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (same.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (same.«EXPR-SYNTAX._<=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (same.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (same.«EXPR-SYNTAX._<__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (same.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (same.«EXPR-SYNTAX._==__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (same.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-heat» G) (same.«EXPR-SYNTAX._!=__EXPR-SYNTAX_Expr_Expr_Expr2-cool» G) (same.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX._&&__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (same.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-heat» G) (same.«EXPR-SYNTAX._||__EXPR-SYNTAX_Expr_Expr_Expr1-cool» G) (same.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-heat» G) (same.«CALC-SYNTAX._=_;_CALC-SYNTAX_Stmt_Id_Expr2-cool» G) (same.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-heat» G) (same.«IMP-SYNTAX.if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt1-cool» G) h

end ImpNI
