import ImpTypes.Typed
import KPrelude.InvTactic
import KPrelude.InvColl

/-! Hand-written. `preservation` of `Typed.lean` (the runtime typing `WTc envTy G` of kimp
configurations, for the K type checker `imp-typing.k`), re-proved with the invariant core
(`KPrelude.Invariant`) and `k2l_preserve` in its `Preserved` mode, without `hand`.

The unfolding set is the generated `@[k2l_pres]` lemmas of `Typing.lean`: they say how `WTc`
computes. `split [typeOf, wt]` names the two typing functions whose values the computation cases
on. The two store rules are the residual goals `«CALC.var»` and `«CALC.assign»`, closed by the
hand cases of `Store.lean`.

The proof covers 79 rules, and its elaboration after the tactic counts every rule's heartbeats,
so it has no bound of its own (`maxHeartbeats 0`) and bounds each rule by
`k2l.preserve.maxHeartbeats` (`KPrelude.InvTactic`, *Heartbeats*). -/

namespace ImpTypesPres

open KPrelude ImpTypes

set_option maxHeartbeats 0 in
set_option k2l.preserve.maxHeartbeats 200000 in
theorem wtc_preserved (G : TEnv) : Preserved KImp.Step (WTc envTy G) := by
  k2l_preserve split [typeOf, wt]
  case «CALC.var» X K g m v D hm => exact hand.«CALC.var» G X K g m v D hm
  case «CALC.assign» X y K E g V hp => exact hand.«CALC.assign» G X y K E g V hp

/-- The statement of `ImpTypes.preservation`. -/
theorem preservation {G : TEnv} {c c' : KImp.SortGeneratedTopCell} (h : KImp.Step c c') :
    WTc envTy G c → WTc envTy G c' :=
  fun hw => wtc_preserved G c c' hw h

#k2l_assert_axioms wtc_preserved preservation

end ImpTypesPres
