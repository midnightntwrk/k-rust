import ImpMut.Tr
import KImp.Rules
import KMut.Rules

/-!
# A mutant of kimp diverges from kimp

HAND-WRITTEN. `KMut` is generated from `k/kimp-mutant`, kimp with
`rule X - Y => X -Int Y` replaced by `X +Int Y`; `k2lean relate` (`ImpMut.Tr`, generated) matches
every symbol and 78 of 79 rules and reports kimp's `X - Y` (`expr.k:45:3`) as the one rule without a
counterpart.
The theorem below is what kink's "killed" verdict becomes: a configuration where kimp's step and
every step of the mutant from its translation disagree. A template would take the configuration
from kink's killing program and prove the rest the same way (both steps are computed).
-/

namespace ImpMut

open KPrelude

/-- `<k> 1 - 1 ~> .K </k> <env> .Map </env>`. -/
def c₀ : KImp.SortGeneratedTopCell :=
  .«<generatedTop>» (.«<k>» (.kseq (.inj_Expr (.«_-_» (.inj_Int 1) (.inj_Int 1))) .dotk)) (.«<env>» (KImp.Term.coll_SortMap [])) (.«<generatedCounter>» 0)

theorem kimp_step : KImp.Step c₀ (.«<generatedTop>» (.«<k>» (.kseq (.inj_Int 0) .dotk)) (.«<env>» (KImp.Term.coll_SortMap [])) (.«<generatedCounter>» 0)) :=
  KImp.Step.«X - Y» 1 1 .dotk _ _

/-- Every step the mutant takes from the translated configuration differs from the translation
of kimp's step. -/
theorem diverge : ∀ d, KMut.Step (tr_SortGeneratedTopCell c₀) d →
    d ≠ tr_SortGeneratedTopCell (.«<generatedTop>» (.«<k>» (.kseq (.inj_Int 0) .dotk)) (.«<env>» (KImp.Term.coll_SortMap [])) (.«<generatedCounter>» 0)) := by
  intro d h
  simp only [c₀, tr_SortGeneratedTopCell] at h ⊢
  cases h <;> first
    | decide
    | (simp_all [KMut.K.isKResult, KMut.K.isKResult.rule1, KMut.proj_KItem_KResult, KMut.inj_Expr_KItem, BoolHook.and, BoolHook.not]; done)

#k2l_assert_axioms kimp_step diverge

end ImpMut
