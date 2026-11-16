/-
  `rangeMapHook_sorted_read` and `rangeMapHook_sorted_build` (KcoreSpec/RangeMapSorted.lean)
  applied at one semantics, once per symbol: the hypotheses are computed by the kernel (`decide +kernel`, `rfl`), and the conclusion
  is the sort of the hook's value (`Collections.lean`'s `DecidableEq GroundTerm` decides the
  values that `rmCanon` computes). The semantics `c1` has the Range constructor with Range and Int
  below KItem; its collection at RangeMap is `builtinColls`' fourth row, as in every semantics
  (`hco` by `rfl`). Then the fourteen together (`rangeMapHook_sorted`, no hypothesis on the
  semantics), `hook_sorted` at a range-map symbol, and the collection's three symbols at values
  (`rmM_elem`, `rmM_concat`), at `c1` and at a semantics without the Range constructor. Run from
  the package root: `lake env lean -j1 test/RangeMapSorted.lean`.
-/
import KcoreSpec.RangeMapSorted
import KcoreSpec.Collections
import KcoreSpec.SubjectReduction

set_option autoImplicit false

open KCore

namespace RangeMapSortedTest

def lib1 : Lib := { sortsBelowKItem := [Srt.int, Srt.range], ctors := [⟨rangeCtor, [Srt.kitem, Srt.kitem], Srt.range⟩] }

def c1 : Semantics where
  lib := lib1
  sortNames := []
  symNames := []
  userSorts := []
  ctors := []
  fns := []
  userSubsorts := []
  pgmSort := Srt.k
  rules := []

theorem hco : c1.collOf Srt.rangeMap = some (builtinColl .rangeMap) := rfl

theorem mem (i : Nat) (h : i < rangeMapHooks.length) :
    (rangeMapHooks[i].1, rangeMapHooks[i].2) ∈ rangeMapHooks := List.getElem_mem h

/-- `([0,3) r|-> 7) ([5,7) r|-> 8)`. -/
def M : GroundTerm := rmV [(rangeT 0 3, kint 7), (rangeT 5 7, kint 8)]

example : c1.sortOf (rmV []) = some Srt.rangeMap :=
  rangeMapHook_sorted_read (ws := []) (k := rangeMapSigs[0]) (v := rmV [])
    hco (mem 0 (by decide)) (by decide) (by decide) (by decide +kernel) rfl

example : c1.sortOf (rmV [(rangeT 0 3, kint 7)]) = some Srt.rangeMap :=
  rangeMapHook_sorted_read (ws := [rangeT 0 3, kint 7]) (k := rangeMapSigs[1]) (v := rmV [(rangeT 0 3, kint 7)])
    hco (mem 1 (by decide)) (by decide) (by decide) (by decide +kernel) rfl

example : c1.sortOf (kint 7) = some Srt.kitem :=
  rangeMapHook_sorted_read (ws := [M, kint 1]) (k := rangeMapSigs[3]) (v := kint 7)
    hco (mem 3 (by decide)) (by decide) (by decide) (by decide +kernel) rfl

example : c1.sortOf (kint 9) = some Srt.kitem :=
  rangeMapHook_sorted_read (ws := [M, kint 4, kint 9]) (k := rangeMapSigs[4]) (v := kint 9)
    hco (mem 4 (by decide)) (by decide) (by decide) (by decide +kernel) rfl

example : c1.sortOf (rangeT 5 7) = some Srt.range :=
  rangeMapHook_sorted_read (ws := [M, kint 6]) (k := rangeMapSigs[5]) (v := rangeT 5 7)
    hco (mem 5 (by decide)) (by decide) (by decide) (by decide +kernel) rfl

example : c1.sortOf (bool true) = some Srt.bool :=
  rangeMapHook_sorted_read (ws := [kint 2, M]) (k := rangeMapSigs[11]) (v := bool true)
    hco (mem 11 (by decide)) (by decide) (by decide) (by decide +kernel) rfl

example : c1.sortOf (int 2) = some Srt.int :=
  rangeMapHook_sorted_read (ws := [M]) (k := rangeMapSigs[12]) (v := int 2)
    hco (mem 12 (by decide)) (by decide) (by decide) (by decide +kernel) rfl

example : c1.sortOf (bool true) = some Srt.bool :=
  rangeMapHook_sorted_read (ws := [M, M]) (k := rangeMapSigs[13]) (v := bool true)
    hco (mem 13 (by decide)) (by decide) (by decide) (by decide +kernel) rfl

/-- `[0,10) r|-> 7`. -/
def M10 : GroundTerm := rmV [(rangeT 0 10, kint 7)]

example : c1.sortOf (rmV [(rangeT 0 5, kint 7)]) = some Srt.rangeMap :=
  rangeMapHook_sorted_build (ws := [rmV [(rangeT 0 3, kint 7)], rmV [(rangeT 3 5, kint 7)]]) (k := rangeMapSigs[2])
    (v := rmV [(rangeT 0 5, kint 7)])
    hco (mem 2 (by decide)) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

example : c1.sortOf (rmV [(rangeT 0 3, kint 7), (rangeT 3 5, kint 8), (rangeT 5 10, kint 7)]) = some Srt.rangeMap :=
  rangeMapHook_sorted_build (ws := [M10, rangeT 3 5, kint 8]) (k := rangeMapSigs[6])
    (v := rmV [(rangeT 0 3, kint 7), (rangeT 3 5, kint 8), (rangeT 5 10, kint 7)])
    hco (mem 6 (by decide)) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

example : c1.sortOf (rmV [(rangeT 0 3, kint 7), (rangeT 5 10, kint 7)]) = some Srt.rangeMap :=
  rangeMapHook_sorted_build (ws := [M10, rangeT 3 5]) (k := rangeMapSigs[7])
    (v := rmV [(rangeT 0 3, kint 7), (rangeT 5 10, kint 7)])
    hco (mem 7 (by decide)) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

example : c1.sortOf (rmV [(rangeT 0 3, kint 7), (rangeT 5 10, kint 7)]) = some Srt.rangeMap :=
  rangeMapHook_sorted_build (ws := [M10, rmV [(rangeT 3 5, kint 7)]]) (k := rangeMapSigs[8])
    (v := rmV [(rangeT 0 3, kint 7), (rangeT 5 10, kint 7)])
    hco (mem 8 (by decide)) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

example : c1.sortOf (rmV [(rangeT 0 3, kint 7), (rangeT 3 5, kint 8), (rangeT 5 10, kint 7)]) = some Srt.rangeMap :=
  rangeMapHook_sorted_build (ws := [M10, rmV [(rangeT 3 5, kint 8)]]) (k := rangeMapSigs[9])
    (v := rmV [(rangeT 0 3, kint 7), (rangeT 3 5, kint 8), (rangeT 5 10, kint 7)])
    hco (mem 9 (by decide)) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

example : c1.sortOf (rmV [(rangeT 0 3, kint 7), (rangeT 5 10, kint 7)]) = some Srt.rangeMap :=
  rangeMapHook_sorted_build (ws := [M10, .set Srt.set [.inj Srt.range Srt.kitem (rangeT 3 5)]]) (k := rangeMapSigs[10])
    (v := rmV [(rangeT 0 3, kint 7), (rangeT 5 10, kint 7)])
    hco (mem 10 (by decide)) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

/-! ## The fourteen together, and `hook_sorted` -/

/-- A semantics with no Range constructor: its only range map value is the empty one. -/
def c0 : Semantics where
  lib := {}
  sortNames := []
  symNames := []
  userSorts := []
  ctors := []
  fns := []
  userSubsorts := []
  pgmSort := Srt.k
  rules := []

example : c0.sortOf (rmV []) = some Srt.rangeMap :=
  rangeMapHook_sorted (ws := []) (k := rangeMapSigs[0]) (v := rmV []) (mem 0 (by decide)) (by decide +kernel)
    (by decide) rfl

example : c1.sortOf (rmV [(rangeT 0 5, kint 7)]) = some Srt.rangeMap :=
  rangeMapHook_sorted (ws := [rmV [(rangeT 0 3, kint 7)], rmV [(rangeT 3 5, kint 7)]]) (k := rangeMapSigs[2])
    (v := rmV [(rangeT 0 5, kint 7)]) (mem 2 (by decide)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : c1.sortOf (int 2) = some Srt.int :=
  hook_sorted (f := rmSize) (k := ⟨rmSize, [Srt.rangeMap], Srt.int⟩) (ws := [M]) (fun he => absurd he (by decide)) (by decide +kernel) (by decide +kernel) rfl

example : c0.sortOf (rmV []) = some Srt.rangeMap :=
  hook_sorted (f := rmUnit) (k := ⟨rmUnit, [], Srt.rangeMap⟩) (ws := []) (fun he => absurd he (by decide)) (by decide +kernel) rfl rmM_unit

example : c1.collOf Srt.rangeMap = some (builtinColl .rangeMap) := collOf_rangeMap
example : builtinColl .rangeMap ∈ c0.allColls := rmM_mem

/-! ## The collection's symbols at values -/

example : hook rmElem [rangeT 0 5, kint 7] = some (some (rmV [(rangeT 0 5, kint 7)])) := rmM_elem rfl
example : hook rmConcat [rmV [(rangeT 0 5, kint 7)], rmV [(rangeT 5 7, kint 8)]] =
    some (some (rmV [(rangeT 0 5, kint 7), (rangeT 5 7, kint 8)])) := rmM_concat (by decide +kernel)
example : rangesOK [(rangeT 5 7, kint 8)] = true := rmM_tail (x := (rangeT 0 5, kint 7)) (by decide +kernel)

end RangeMapSortedTest
