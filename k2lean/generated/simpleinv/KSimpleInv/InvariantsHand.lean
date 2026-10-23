import KSimpleInv.InvariantDefs

/-! Hand-written proofs of the cases of `Invariant` listed in `open-invariant-cases.txt`.

`k2lean gen` wrote this file once, because it did not exist, and never changes it. Prove each case
below as the theorem it names (uncomment and complete it); `Invariants.lean` uses them by name. The
generated proofs use `k2l_preserve [Invariant.holdsOk, Invariant.cell_T, Invariant.cell_threads, Invariant.content_threads, Invariant.cell_holds, Invariant.content_holds, Invariant.holdsOk_elem, Eqn.«holdsOk(_)_SIMPLE-INV_Bool_Map_1», Eqn.«isCount(_)_SIMPLE-INV_Bool_KItem_1», Invariant.allCounts_iff, Option.bind_fun_some]`.

The two cases are the rules that change a lock count, `N => N +Int 1` and `N => N -Int 1` (under
`N >Int 0`). `k2l_preserve` reduces each to the count's test, `isCount(N +Int 1)` from
`isCount(N)`, and `isCount(N -Int 1)` from `N >Int 0`, which is linear arithmetic (`omega`); its
closers do not run arithmetic decision procedures. Everything else in the two proofs is the
collection reasoning the closers do: the thread is the element `k |-> T` of the `<thread>` map,
its `<holds>` map has the element `V |-> N`, and both are rebuilt by `concat` with the other
elements unchanged. -/

namespace KSimpleInv

open KPrelude

/-- The thread's lock count test, `N ≥ 0`. -/
theorem Invariant.isCount_int (n : SortInt) :
    K.«isCount(_)_SIMPLE-INV_Bool_KItem» (SortKItem.inj_Int n) = true ↔ 0 ≤ n := by
  simp [Eqn.«isCount(_)_SIMPLE-INV_Bool_KItem_1», IntHook.ge]

/-- The `<holds>` map of a thread satisfies `holdsOk` exactly when every count in it is an `Int`
that is at least 0. -/
theorem Invariant.holdsOk_iff (H : SortMap) :
    K.«holdsOk(_)_SIMPLE-INV_Bool_Map» H = some true ↔
      MapHook.EntriesOn (fun p => K.«isCount(_)_SIMPLE-INV_Bool_KItem» p.2 = true) H := by
  simp only [Eqn.«holdsOk(_)_SIMPLE-INV_Bool_Map_1», Option.bind_fun_some, Invariant.allCounts_iff,
    ListHook.elemsOn_values_iff]

/-- Rule `acquire V:Val; #59f263` (simple-untyped.md:1009:3): a re-acquired lock's count goes from
`N` to `N +Int 1`. -/
theorem Invariant.hand.«acquire V:Val; #59f263» : Step.Case.«acquire V:Val; #59f263» Invariant := by
  intro m Gen7 Gen11 Gen6 Gen12 Gen8 Gen10 Gen9 DotVar0 k DotVar2 y_2 DotVar4 Gen13 Gen14 m_3 V DotVar5 N r r_8 hm hp hm_6 hr hr_9 hpri h
  simp only [Invariant, Invariant.holdsOk, Invariant.cell_T, Invariant.cell_threads,
    Invariant.content_threads] at h ⊢
  have ht := MapHook.entry_of_concat_element hm h
  simp only [Invariant.holdsOk_elem, Invariant.cell_holds, Invariant.content_holds,
    Invariant.holdsOk_iff] at ht
  refine MapHook.entriesOn_concat hr_9 (MapHook.entriesOn_element ?_) (MapHook.entriesOn_of_concat_right hm h)
  simp only [Invariant.holdsOk_elem, Invariant.cell_holds, Invariant.content_holds, Invariant.holdsOk_iff]
  refine MapHook.entriesOn_concat hr (MapHook.entriesOn_element ?_) (MapHook.entriesOn_of_concat_right hm_6 ht)
  have hN := MapHook.entry_of_concat_element hm_6 ht
  simp only [Invariant.isCount_int, IntHook.add] at hN ⊢
  -- `SortInt` is `Int`; `omega` reads `Int` syntactically
  have hN' : (0 : Int) ≤ (N : Int) := hN
  show (0 : Int) ≤ (N : Int) + 1
  omega

/-- Rule `release V:Val; #489dca` (simple-untyped.md:1023:3): a lock's count goes from `N` to
`N -Int 1` when `N >Int 0`. -/
theorem Invariant.hand.«release V:Val; #489dca» : Step.Case.«release V:Val; #489dca» Invariant := by
  intro m Gen7 Gen11 Gen6 Gen12 Gen8 Gen10 Gen9 DotVar0 k DotVar2 y_2 DotVar4 Gen13 Gen14 m_3 V DotVar5 N r r_8 hm hp hm_6 hreq hr hr_9 hpri h
  simp only [Invariant, Invariant.holdsOk, Invariant.cell_T, Invariant.cell_threads,
    Invariant.content_threads] at h ⊢
  have ht := MapHook.entry_of_concat_element hm h
  simp only [Invariant.holdsOk_elem, Invariant.cell_holds, Invariant.content_holds,
    Invariant.holdsOk_iff] at ht
  refine MapHook.entriesOn_concat hr_9 (MapHook.entriesOn_element ?_) (MapHook.entriesOn_of_concat_right hm h)
  simp only [Invariant.holdsOk_elem, Invariant.cell_holds, Invariant.content_holds, Invariant.holdsOk_iff]
  refine MapHook.entriesOn_concat hr (MapHook.entriesOn_element ?_) (MapHook.entriesOn_of_concat_right hm_6 ht)
  simp only [Invariant.isCount_int, IntHook.sub]
  simp only [IntHook.gt, decide_eq_true_eq] at hreq
  have hN' : (0 : Int) < (N : Int) := hreq
  show (0 : Int) ≤ (N : Int) - 1
  omega

end KSimpleInv
