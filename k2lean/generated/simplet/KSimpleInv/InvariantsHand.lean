import KSimpleInv.InvariantDefs

/-! Hand-written proofs of the cases of `Invariant` listed in `open-invariant-cases.txt`.

`k2lean gen` wrote this file once, because it did not exist, and never changes it. Prove each case
below as the theorem it names; `Invariants.lean` uses them by name.

The one case is the array declaration `var X[N];`, which binds `N` fresh locations to
`undefined` through the recursive function `N ... M |-> K` of `simple-untyped.md`, and the array's
location to an `array(…)` value. `k2l_preserve` has no fact about the bindings of that function's
result; `Invariant.range_entries` proves, by induction on the number of keys, that it binds its
value at every key. The rest is the collection reasoning the closers do. -/

namespace KSimpleInv

open KPrelude

/-- The map `N ... M |-> K` of SIMPLE's array allocation binds `K` at every key: by induction on
the number of keys, from its two K equations. -/
theorem Invariant.range_entries (b : SortInt) (v : SortKItem) :
    ∀ (n : Nat) (a : SortInt) (r : SortMap), (b + 1 - a).toNat = n →
      K.«_..._|->__SIMPLE-UNTYPED_Map_Int_Int_K» a b (SortK.kseq v SortK.dotk) = some r →
      MapHook.EntriesOn (fun p => p.2 = v) r := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a r hn h
    by_cases hab : IntHook.gt a b = true
    · rw [Eqn.«_..._|->__SIMPLE-UNTYPED_Map_Int_Int_K_1» _ _ _ hab] at h
      obtain rfl := Option.some.inj h
      exact MapHook.entriesOn_unit
    · have hle : IntHook.le a b = true := by
        simp only [IntHook.gt, IntHook.le, decide_eq_true_eq] at hab ⊢
        omega
      rw [Eqn.«_..._|->__SIMPLE-UNTYPED_Map_Int_Int_K_2» _ _ _ hle] at h
      cases hrest : K.«_..._|->__SIMPLE-UNTYPED_Map_Int_Int_K» (IntHook.add a (1 : Int)) b
          (SortK.kseq v SortK.dotk) with
      | none => simp [hrest] at h
      | some r' =>
        simp only [hrest, Option.bind_some, Option.bind_fun_some] at h
        refine MapHook.entriesOn_concat h (MapHook.entriesOn_element rfl) ?_
        have hlt : (b + 1 - IntHook.add a 1).toNat < n := by
          simp only [IntHook.le, decide_eq_true_eq] at hle
          simp only [IntHook.add]
          omega
        exact ih _ hlt _ _ rfl hrest

/-- `undefined`, the value of an array element before its first assignment, passes the store
test. -/
theorem Invariant.undefined_ok :
    KPrelude.BoolHook.or (K.isVal (SortK.kseq (SortKItem.inj_KItem SortKItem.Own.undefined) SortK.dotk))
      (KPrelude.KEqHook.eq (SortK.kseq (SortKItem.inj_KItem SortKItem.Own.undefined) SortK.dotk)
        (SortK.kseq (SortKItem.inj_KItem SortKItem.Own.undefined) SortK.dotk)) = true := by
  simp [KPrelude.BoolHook.or, KPrelude.KEqHook.eq]

/-- Rule `var X[N];` (simple-untyped.md:471:3): the store gains the array's location and `N`
locations bound to `undefined`. -/
theorem Invariant.hand.«var X[N];» : Step.Case.«var X[N];» Invariant := by
  intro m Gen7 DotVar2 Gen6 Gen10 Gen8 Gen9 L DotVar0 k DotVar3 X N DotVar5 Gen11 Env Gen12 r r_2 r_4 r_6 hm hreq hr hr_3 hr_5 hr_7 hpri h
  simp only [Invariant, Invariant.tStoreOk, Invariant.tStoreOk_cells, Invariant.cell_T, Invariant.cell_store, Invariant.content_store, Option.bind_fun_some, Invariant.allVals_iff, ListHook.elemsOn_values_iff] at h ⊢
  refine MapHook.entriesOn_concat hr_7 (MapHook.entriesOn_concat hr_5 (MapHook.entriesOn_element ?_) ?_) h
  · have hv : K.isVal (SortK.kseq (SortKItem.inj_Val (SortVal.Own.«array(_,_)» (IntHook.add L 1) N)) SortK.dotk) = true :=
      Eqn.isVal_1 (SortVal.inj_Val (SortVal.Own.«array(_,_)» (IntHook.add L 1) N))
    simp [KPrelude.BoolHook.or, hv]
  · intro p hp
    have hu := Invariant.range_entries _ _ _ _ _ rfl hr_3 p hp
    simp only at hu ⊢
    rw [hu]
    exact Invariant.undefined_ok

end KSimpleInv
