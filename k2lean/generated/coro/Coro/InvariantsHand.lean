import Coro.InvariantDefs
import Coro.Init

/-! Hand-written proofs of the cases of `Invariant` listed in `open-invariant-cases.txt`.

`k2lean gen` wrote this file once, because it did not exist, and never changes it. Prove each case
below as the theorem it names (uncomment and complete it); `Invariants.lean` uses them by name. The
generated proofs use `k2l_preserve [Invariant.kOk, Invariant.cell_T, Invariant.cell_procs, Invariant.content_procs, Invariant.cell_k, Invariant.content_k, Invariant.kOk_elem, Eqn.«itemOk(_)_CORO_Bool_KItem_1», Eqn.«itemOk(_)_CORO_Bool_KItem_2», Eqn.«itemOk(_)_CORO_Bool_KItem_3», Eqn.«itemOk(_)_CORO_Bool_KItem_4», Eqn.«itemOk(_)_CORO_Bool_KItem_5», Eqn.«kOk(_)_CORO_Bool_K_1», Eqn.«kOk(_)_CORO_Bool_K_2», KPrelude.bind_bool_eq_some_true, KPrelude.BoolHook.and, KPrelude.BoolHook.or, KPrelude.BoolHook.not, KPrelude.BoolHook.implies, Option.some.injEq, Bool.false_eq_true, and_false, false_and, or_false, false_or, Option.bind_fun_some]`. -/

namespace Coro

open KPrelude

theorem Invariant.hand.init (pgm : SortPgm) : Invariant (init pgm) := by
  simp only [Invariant, Invariant.kOk, Coro.init, Invariant.cell_T, Invariant.cell_procs, Invariant.content_procs]
  apply MapHook.entriesOn_element
  simp only [Invariant.kOk_elem, Invariant.cell_k, Invariant.content_k]
  rw [Eqn.«kOk(_)_CORO_Bool_K_2», Eqn.«kOk(_)_CORO_Bool_K_1», Eqn.«itemOk(_)_CORO_Bool_KItem_2»]
  rfl

end Coro
