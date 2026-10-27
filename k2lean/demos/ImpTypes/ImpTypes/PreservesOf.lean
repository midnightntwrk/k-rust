import ImpTypes.Soundness
import KImp.Preserves
import KImp.Init
import KPrelude.InvTactic
import KPrelude.InvColl

/-! Hand-written. `preservation` of `Soundness.lean` through the generated per-rule principle
`KImp.Step.preserves_of` (`KImp/Preserves.lean`), and the generated initial configuration
`KImp.init` (`KImp/Init.lean`) against the generated `ImpTypes.init` of `Typing.lean`.

`wtc_preserved_of` takes the two store rules as hypotheses of `Step.preserves_of`'s types,
`KImp.Step.Case.«CALC.var» (WTc envTy G)` and `KImp.Step.Case.«CALC.assign» (WTc envTy G)`, and
proves the other 77 rules with `k2l_preserve`. The goal that `k2l_preserve` leaves for a rule is
that rule's `Step.Case` with the rule's variables and side conditions introduced, so each
residual case is closed by applying its hypothesis.

The two proofs by `k2l_preserve` cover 79 rules, and their elaboration after the tactic counts
every rule's heartbeats, so they have no bound of their own (`maxHeartbeats 0`) and bound each
rule by `k2l.preserve.maxHeartbeats` (`KPrelude.InvTactic`, *Heartbeats*). -/

namespace ImpTypesPreservesOf

open KPrelude ImpTypes

set_option maxHeartbeats 0 in
set_option k2l.preserve.maxHeartbeats 200000 in
/-- The runtime typing is preserved by every rule, given the two store rules' cases of
`Step.preserves_of`; the other 77 rules by `k2l_preserve`. -/
theorem wtc_preserved_of (G : TEnv)
    («CALC.var» : KImp.Step.Case.«CALC.var» (WTc envTy G))
    («CALC.assign» : KImp.Step.Case.«CALC.assign» (WTc envTy G)) :
    Preserved KImp.Step (WTc envTy G) := by
  k2l_preserve split [typeOf, wt]
  case «CALC.var» X K g m v D hm => exact «CALC.var» X K g m v D hm
  case «CALC.assign» X y K E g V hp => exact «CALC.assign» X y K E g V hp

theorem wtc_preserved (G : TEnv) : Preserved KImp.Step (WTc envTy G) :=
  wtc_preserved_of G (hand.«CALC.var» G) (hand.«CALC.assign» G)

set_option maxHeartbeats 0 in
set_option k2l.preserve.maxHeartbeats 200000 in
/-- The direct form: `apply Step.preserves_of` leaves one goal `Step.Case.r (WTc envTy G)` per
rule, `k2l_preserve` in its per-case mode closes 77 of them, and the two store rules remain as
goals tagged by their rules, with the rules' variables introduced. -/
theorem wtc_preserved_direct (G : TEnv) : Preserved KImp.Step (WTc envTy G) := by
  apply KImp.Step.preserves_of
  all_goals k2l_preserve split [typeOf, wt]
  case «CALC.var» => exact hand.«CALC.var» G _ _ _ _ _ _ ‹_›
  case «CALC.assign» => exact hand.«CALC.assign» G _ _ _ _ _ _ ‹_›

/-- The statement of `ImpTypes.preservation`. -/
theorem preservation {G : TEnv} {c c' : KImp.SortGeneratedTopCell} (h : KImp.Step c c') :
    WTc envTy G c → WTc envTy G c' :=
  fun hw => wtc_preserved G c c' hw h

/-! ## The generated initial configuration

`KImp.init P E` is the configuration `krun` starts from for `$PGM = P` and `$ENV = E`, with the
`<generatedCounter>` cell at its declared default `0`. `ImpTypes.init` leaves that cell a
parameter `g`, so the two agree at `g = <generatedCounter> 0`, and `soundness` holds from the
generated initial configuration. -/

theorem init_eq (P : KImp.SortStmt) (E : KImp.SortMap) :
    KImp.init P E = ImpTypes.init P E (.«<generatedCounter>» 0) := rfl

/-- **Type soundness** from the generated initial configuration. -/
theorem soundness_init {G : TEnv} {P : KImp.SortStmt} {E : KImp.SortMap}
    (hP : KImpTypes.K.«wt(_,_)_IMP-TYPING_Bool_Stmt_Map» (tr_SortStmt P) G = some true) (hE : envTy G E)
    {n : Nat} {c : KImp.SortGeneratedTopCell} (h : StepsN KImp.Step n (KImp.init P E) c) :
    Final c ∨ KImp.App c :=
  soundness hP hE (init_eq P E ▸ h)

#k2l_assert_axioms KImp.Step.preserves_of wtc_preserved_of wtc_preserved preservation
#k2l_assert_axioms wtc_preserved_direct
#k2l_assert_axioms init_eq soundness_init

end ImpTypesPreservesOf
