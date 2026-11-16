/-
  A definition's own collection of kind `.rangeMap`, built by three parameters implemented by
  RANGEMAP's unit, element and concatenation. Run from the package root:
  `lake env lean -j1 test/RangeMapOwn.lean`. Kernel-checked (`decide +kernel`).

  - With Int keys and values (no Range constructor; its one value of the own sort is the empty
    map) `coreOK` holds, at kind `.rangeMap` as at `.map`.
  - With Range keys, KItem values and the Range constructor (`cO`), `coreOK` holds; a two-entry
    map of the own sort denotes itself (`den_val`, `den_rmEntriesK`, `den_rmEntryK`), the
    concatenation reads maps of the own sort (`rmM_concat_sortK`), no junk at the own sort
    (`sat_collNoJunk`), and the element parameter at `[5, 3)` has the interpretation's value (none
    under `HookParams.none`, the map an interpretation gives otherwise); at `[0, 3)` the one-entry
    map of the own sort.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.RangeMapOwnTest

open KCore ML Faithful Faithful.Model

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- The Range constructor, with Int and Range below KItem. -/
def libR : Lib := { sortsBelowKItem := [Srt.int, Srt.range], ctors := [⟨rangeCtor, [Srt.kitem, Srt.kitem], Srt.range⟩] }

def e2 : List (GroundTerm × GroundTerm) := [(rangeT 0 3, kint 7), (rangeT 5 7, kint 8)]

def ownCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def S : Srt := nRegSorts + 2
def uS : Sym := nRegSyms + 5
def eS : Sym := nRegSyms + 6
def cS : Sym := nRegSyms + 7

/-- The cells and one collection sort `S` of the definition's own, of kind `K`, from `key` to `val`,
built by three parameters implemented by the library's symbols of that kind, over the library `l`. -/
def w (l : Lib) (K : CollKind) (key val : Srt) : Semantics where
  lib := l
  sortNames := ["KCell", "KCellOpt", "S"]
  symNames := ["LblisKCell", "LblisKCellOpt", "LblisS", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lbl'Stop'S", "LblSItem",
    "Lbl'Unds'S'Unds'"]
  userSorts := cellSorts ++ [S]
  ctors := ownCtors
  fns := []
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []
  params := [{ sig := ⟨uS, [], S⟩, impl := some (builtinColl K).unit },
    { sig := ⟨eS, [key, val], S⟩, impl := some (builtinColl K).elem },
    { sig := ⟨cS, [S, S], S⟩, impl := some (builtinColl K).concat }]
  colls := [⟨S, K, key, some val, uS, eS, cS⟩]

def lInt : Lib := { sortsBelowKItem := [Srt.int, Srt.bool] }

/-- Int keys and values, no Range constructor: `coreOK` holds at kind `.rangeMap` as at `.map`.
Its one value of `S` is the empty map. -/
theorem wInt_coreOK : (w lInt .rangeMap Srt.int Srt.int).coreOK = true := by decide +kernel
theorem wInt_map_coreOK : (w lInt .map Srt.int Srt.int).coreOK = true := by decide +kernel

example : (w lInt .rangeMap Srt.int Srt.int).sortOf (.map S []) = some S ∧
    (w lInt .rangeMap Srt.int Srt.int).paramVal uS [] = some (.map S []) := by decide +kernel

/-- Range keys and KItem values, with the Range constructor. -/
def cO : Semantics := w libR .rangeMap Srt.range Srt.kitem

def kO : CollSig := ⟨S, .rangeMap, Srt.range, some Srt.kitem, uS, eS, cS⟩

theorem kO_mem : kO ∈ cO.allColls := List.mem_append_right _ (List.mem_singleton_self _)

instance : OvlOK cO := .of_nil rfl (by decide +kernel)

theorem cO_sortedOK : cO.sortedOK = true := by decide +kernel

theorem cO_coreOK : cO.coreOK = true := by decide +kernel

theorem cO_fnHyp : FnHyp cO :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_sortedOK cO_sortedOK⟩

theorem hypO : HypModelCore cO := hypModel_of_fnHyp cO_coreOK cO_fnHyp

/-- `[0,3) ↦ 7, [5,7) ↦ 8` at the own sort is a value of it, and denotes itself (`den_val`'s
range-map case at an own collection). -/
example (e : Valuation Elem) : Sing cO e (den cO (.map S e2)) (.val (.map S e2)) :=
  den_val hypO _ (s := S) (by decide +kernel) e

/-- The same by the entries (`den_rmEntriesK`, its `x :: y :: es` case) and by one entry. -/
example (e : Valuation Elem) :
    Sing cO e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries cO kO e2)) (.val (.map S e2)) :=
  den_rmEntriesK hypO kO kO_mem (by decide +kernel) rfl rfl e2 (by decide +kernel) (by decide +kernel) e

example (e : Valuation Elem) :
    Sing cO e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntry cO kO (rangeT 0 3, kint 7)))
      (.val (.map S [(rangeT 0 3, kint 7)])) :=
  den_rmEntryK hypO kO kO_mem (by decide +kernel) rfl rfl (rangeT 0 3, kint 7) rfl (by decide +kernel) e

/-- The concatenation at maps of the own sort. -/
example : hook rmConcat [.map S [(rangeT 0 3, kint 7)], .map S [(rangeT 5 7, kint 8)]] = some (some (rmV e2)) :=
  rmM_concat_sortK (by decide +kernel)

/-- No junk at the own sort. -/
example : stdI cO ⊧ᴵ collNoJunk cO kO := sat_collNoJunk hypO kO_mem

/-- The element parameter at `[5, 3)`: the interpretation's value (`paramVal` through `hookRes`),
none under `HookParams.none` and the map an interpretation gives there otherwise; at `[0, 3)` the
one-entry map of the own sort. -/
def hE : HookParams := ⟨fun f _ => if f == rmElem then some (rmV []) else none⟩

example : (cO.withHooks HookParams.none).paramVal eS [rangeT 5 3, kint 7] = none ∧
    (cO.withHooks hE).paramVal eS [rangeT 5 3, kint 7] = some (.map S []) ∧
    cO.paramVal eS [rangeT 0 3, kint 7] = some (.map S [(rangeT 0 3, kint 7)]) := by
  decide +kernel

end KCore.RangeMapOwnTest
