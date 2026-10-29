import KVm.InvariantDefs
import KVm.Init

/-! Hand-written proofs of the cases of `Invariant` listed in `open-invariant-cases.txt`.

`k2lean gen` wrote this file once, because it did not exist, and never changes it. Prove each case
below as the theorem it names (uncomment and complete it); `Invariants.lean` uses them by name. The
generated proofs use `k2l_preserve [Invariant.kOk, Invariant.cell_T, Invariant.cell_k, Invariant.content_k, Eqn.«itemOk(_)_VM_Bool_KItem_1», Eqn.«itemOk(_)_VM_Bool_KItem_2», Eqn.«itemOk(_)_VM_Bool_KItem_3», Eqn.«itemOk(_)_VM_Bool_KItem_4», Eqn.«kOk(_)_VM_Bool_K_1», Eqn.«kOk(_)_VM_Bool_K_2», KPrelude.bind_bool_eq_some_true, KPrelude.BoolHook.and, KPrelude.BoolHook.or, KPrelude.BoolHook.not, KPrelude.BoolHook.implies, Option.some.injEq, Bool.false_eq_true, and_false, false_and, or_false, false_or, Option.bind_fun_some]`. -/

namespace KVm

open KPrelude

/-- The program is a `Pgm`, so `<k>` holds one program item: `kOk` computes to `true`. -/
theorem Invariant.hand.init (pgm : SortPgm) : Invariant (init pgm) := by
  simp only [Invariant, Invariant.kOk, KVm.init, Invariant.cell_T, Invariant.cell_k, Invariant.content_k]
  rw [Eqn.«kOk(_)_VM_Bool_K_2», Eqn.«kOk(_)_VM_Bool_K_1», Eqn.«itemOk(_)_VM_Bool_KItem_2»]
  rfl

end KVm
