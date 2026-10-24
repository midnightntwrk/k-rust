import KImpKeys.InvariantDefs

/-! Hand-written proofs of the cases of `Invariant` listed in `open-invariant-cases.txt`.

This library is the gate's fixture of the kind 1 hand path (`k2lean/tests/gate.sh`, `kimpkeys-hand`):
`k2l_preserve` proves `CALC.assign` in the library `kimpkeys`, and here the case is listed in
`open-invariant-cases.txt`, so `Invariants.lean` takes it from this module. -/

namespace KImpKeys

open KPrelude

/-- Rule `CALC.assign` (calc.k:32:3): the updated store's keys are the old keys and `X`, an `Id`. -/
theorem Invariant.hand.«CALC.assign» : Step.Case.«CALC.assign» Invariant := by
  intro X y DotVar1 E DotVar0 V hp h
  simp only [Invariant, Invariant.envKeysOk, Invariant.cell_env, Invariant.content_env,
    Eqn.«envKeysOk(_)_IMP-KEYS_Bool_Map_1», Invariant.allIds_iff, Option.bind_fun_some,
    ListHook.elemsOn_keysList_iff] at h ⊢
  exact MapHook.entriesOn_update h (Eqn.isId_1 X)

end KImpKeys
