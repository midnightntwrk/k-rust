/-
  RANGEMAP's interpreted symbols (KcoreSpec/RangeMapHooks.lean) at the values of the fixture
  test/constructs/fixtures/e6-rangemap, with `M := ([0,3) r|-> a) ([5,7) r|-> b)`. Each expectation
  is from domains.md's prose (line numbers of K 7.1.337), not from a run. Run from the package root:
  `lake env lean test/RangeMap.lean`. Kernel-checked (`decide +kernel`).

  The statements are about the table `rangeMapHooks` (`rmHook`), which with `rangeMapKeysHooks`
  is the last part of `hookTable`, so `hook` gives the same at these symbols (the first example
  below); `keys` is the one entry of `rangeMapKeysHooks`, `hook` gives `rmKeysHook` at it, and its
  value is a Set value (`rmKeysHook_sorted`, `hook_sorted`) at a semantics with the Range
  constructor (sections `KeysSorted`, `KeysHook`).

  The library's row of sort RangeMap is in every semantics, so `coreOK` leaves the semantics in
  which sort 29 has another role, and, by the fourteen entries, those in which a range-map symbol
  is a constructor (section `RowWitnesses`): sort 29 a library token sort (`collSortsOK`), a library
  constructor sort (`genWf`), the sort of an own Map collection (`collsOK`), and the unit `rmUnit`
  a library constructor of KItem (`kindsApart`); a library of RANGEMAP's shape keeps `coreOK`.
-/
import KcoreSpec.RangeMapHooks
import KcoreSpec.RangeMapLaws
import KcoreSpec.FaithOK
import KcoreSpec.RangeMapKeys
import KcoreSpec.LazySound
import KcoreSpec.Statements
import KcoreSpec.CoreDecide

set_option autoImplicit false

open KCore

/-- Three KItem values. -/
def a : GroundTerm := .ctor 900 []
def b : GroundTerm := .ctor 901 []
def c : GroundTerm := .ctor 902 []

/-- Results compared by `GroundTerm.cmp`. -/
def same : Option (Option GroundTerm) → Option (Option GroundTerm) → Bool
  | some (some v), some (some w) => GroundTerm.cmp v w == .eq
  | some none, some none => true
  | none, none => true
  | _, _ => false

def val (v : GroundTerm) : Option (Option GroundTerm) := some (some v)

def elem (x y : Int) (v : GroundTerm) : GroundTerm := rmV [(rangeT x y, v)]
def cat (m n : GroundTerm) : Option (Option GroundTerm) := rmHook rmConcat [m, n]

/-- `M`, the canonical value of `([0,3) r|-> a) ([5,7) r|-> b)`. -/
def M : GroundTerm := rmV [(rangeT 0 3, a), (rangeT 5 7, b)]
/-- `([0,3) r|-> a) ([3,5) r|-> a)`, merged (499-500). -/
def M2 : GroundTerm := rmV [(rangeT 0 5, a)]
def M10 : GroundTerm := elem 0 10 a

/-- `hook`, by `hookTable`, is `rmHook` at RANGEMAP's symbols. -/
example : hook rmSize [M] = rmHook rmSize [M] ∧ hook rmConcat [elem 0 3 a, elem 5 7 b] = cat (elem 0 3 a) (elem 5 7 b) ∧
    hook rmKeys [M] = some (rmKeysHook [M]) := ⟨rfl, rfl, rfl⟩

/-- The concatenations, and what is computed from them. -/
example : same (cat (elem 0 3 a) (elem 5 7 b)) (val M) = true ∧
    rangesOK [(rangeT 0 3, a), (rangeT 5 7, b)] = true ∧
    -- size 2 (657)
    same (rmHook rmSize [M]) (val (int 2)) = true ∧
    -- inclusive below, exclusive above (498-499)
    same (rmHook rmLookup [M, kint 1]) (val a) = true ∧
    same (rmHook rmLookupOrDefault [M, kint 3, c]) (val c) = true ∧
    same (rmHook rmInKeys [kint 2, M]) (val (bool true)) = true ∧
    same (rmHook rmInKeys [kint 3, M]) (val (bool false)) = true ∧
    -- merged (499-500)
    same (cat (elem 0 3 a) (elem 3 5 a)) (val M2) = true ∧
    same (rmHook rmSize [M2]) (val (int 1)) = true ∧
    same (rmHook rmFindRange [M2, kint 4]) (val (rangeT 0 5)) = true ∧
    -- overlapping ranges: no value of the hook, and a silent point (503-504, 600-602)
    same (cat (elem 0 3 a) (elem 2 5 b)) (some none) = true ∧
    silent rmConcat [elem 0 3 a, elem 2 5 b] = true := by decide +kernel

/-- Update, removal, difference (564-566, 574-576, 584-588). -/
example : same (rmHook rmUpdate [M10, rangeT 3 5, b]) (val (rmV [(rangeT 0 3, a), (rangeT 3 5, b), (rangeT 5 10, a)])) = true ∧
    same (rmHook rmSize [rmV [(rangeT 0 3, a), (rangeT 3 5, b), (rangeT 5 10, a)]]) (val (int 3)) = true ∧
    same (rmHook rmRemove [M10, rangeT 3 5]) (val (rmV [(rangeT 0 3, a), (rangeT 5 10, a)])) = true ∧
    same (rmHook rmDifference [M10, elem 3 5 a]) (val (rmV [(rangeT 0 3, a), (rangeT 5 10, a)])) = true ∧
    same (rmHook rmDifference [M10, elem 3 5 b]) (val M10) = true ∧
    -- a part of every range of the Set present; the empty Set (611-613)
    same (rmHook rmRemoveAll [M10, .set Srt.set [.inj Srt.range Srt.kitem (rangeT 3 5)]])
      (val (rmV [(rangeT 0 3, a), (rangeT 5 10, a)])) = true ∧
    same (rmHook rmRemoveAll [M, .set Srt.set []]) (val M) = true := by decide +kernel

/-- Where the text gives no value: `M[9]` (534-535: a run's exception), a range with a bound that
is no Int or that is empty (476-477), `[_ <- undef]` and `removeAll` at a proper range no part of
which is in the map (575-576, 611-613: "all or any part … present"; 579, 616: not `total`): no
value and silent, so the interpretation's. `choice` is a
parameter: no entry. `<=RangeMap` at two equal maps is `true` (663-671, as `<=Set`). -/
example : same (rmHook rmLookup [M, kint 9]) (some none) = true ∧
    same (rmHook rmElem [.ctor rangeCtor [a, kint 5], b]) (some none) = true ∧
    same (rmHook rmElem [rangeT 3 3, b]) (some none) = true ∧
    same (rmHook rmRemove [M, rangeT 3 5]) (some none) = true ∧
    same (rmHook rmRemove [M, rangeT 10 12]) (some none) = true ∧
    same (rmHook rmRemoveAll [M, .set Srt.set [.inj Srt.range Srt.kitem (rangeT 0 3),
      .inj Srt.range Srt.kitem (rangeT 10 12)]]) (some none) = true ∧
    (rangeMapSilent.map (·.1)) =
      [rmElem, rmConcat, rmLookup, rmFindRange, rmUpdate, rmRemove, rmRemoveAll] ∧
    (rmHook rmChoice [M]).isNone = true ∧ (rmHook rmKeysList [M]).isNone = true ∧
    (rmHook rmValues [M]).isNone = true ∧
    same (rmHook rmInclusion [M, M]) (val (bool true)) = true ∧
    same (rmHook rmInclusion [elem 0 3 a, M10]) (val (bool true)) = true ∧
    same (rmHook rmInclusion [M10, elem 0 3 a]) (val (bool false)) = true := by decide +kernel

/-- `keys` is no entry of `rangeMapHooks`; `hook` gives `rmKeysHook` at it, a canonical Set of the
ranges injected into KItem. -/
example : (rmHook rmKeys [M]).isNone = true ∧
    same (hook rmKeys [M])
      (val (.set Srt.set [.inj Srt.range Srt.kitem (rangeT 0 3), .inj Srt.range Srt.kitem (rangeT 5 7)])) = true := by
  decide +kernel

/-! `rmKeysHook_sorted` at a semantics with the Range constructor and Range and Int below KItem
(the range-map collection is `builtinColls`' fourth row): `genWf` holds, and `keys` of a map of two
entries is a Set value. -/
namespace KeysSorted

def lib1 : Lib := { sortsBelowKItem := [Srt.int, Srt.range], ctors := [⟨rangeCtor, [Srt.kitem, Srt.kitem], Srt.range⟩] }

def cK : Semantics where
  lib := lib1
  sortNames := []
  symNames := []
  userSorts := []
  ctors := []
  fns := []
  userSubsorts := []
  pgmSort := Srt.k
  rules := []

instance : OvlOK cK := .of_nil rfl (by decide +kernel)

def MK : GroundTerm := rmV [(rangeT 0 3, kint 7), (rangeT 5 7, kint 8)]

example : cK.sortOf (.set Srt.set [.inj Srt.range Srt.kitem (rangeT 0 3), .inj Srt.range Srt.kitem (rangeT 5 7)]) =
    some Srt.set :=
  rmKeysHook_sorted (ws := [MK]) (by decide +kernel) rfl (by decide +kernel) rfl

/-- Range is below KItem in `cK`, from a Range value under `genWf`, and the subsort form of the lemma. -/
example : (Srt.range, Srt.kitem) ∈ cK.subsorts := rmK_range_below (a := 0) (b := 3) (by decide +kernel) (by decide +kernel)

example : cK.sortOf (.set Srt.set [.inj Srt.range Srt.kitem (rangeT 0 3), .inj Srt.range Srt.kitem (rangeT 5 7)]) =
    some Srt.set :=
  rmKeysHook_sorted_of_sub (ws := [MK]) rfl (by decide +kernel) (by decide +kernel) rfl

end KeysSorted

/-- The mutation the fixture kills: canonical form without the merge conjunct admits the unmerged
description, whose size is 2 where the text's (merged) value has size 1. -/
def rangesOKNoMerge : Entries → Bool
  | [] => true
  | [(k, _)] => (asRange k).isSome
  | (k, _) :: (k', v') :: es => (match asRange k, asRange k' with
      | some (_, b), some (a', _) => decide (b ≤ a')
      | _, _ => false) && rangesOKNoMerge ((k', v') :: es)

example : rangesOK [(rangeT 0 3, a), (rangeT 3 5, a)] = false ∧
    rangesOKNoMerge [(rangeT 0 3, a), (rangeT 3 5, a)] = true ∧
    same (rmHook rmSize [rmV [(rangeT 0 3, a), (rangeT 3 5, a)]]) (val (int 2)) = true ∧
    same (rmHook rmSize [M2]) (val (int 1)) = true := by decide +kernel

/-- Concatenation after a result: undefined stays undefined. -/
def catR : Option (Option GroundTerm) → GroundTerm → Option (Option GroundTerm)
  | some (some m), n => cat m n
  | r, _ => r
def catL (m : GroundTerm) : Option (Option GroundTerm) → Option (Option GroundTerm)
  | some (some n) => cat m n
  | r => r

/-- The text's associativity and unit sentences of `_RangeMap_` (domains.md 508: `assoc`,
`unit(.RangeMap)`; kompiled as equalities of patterns, so an undefined side forces the other), at
values: defined and merged, and overlapping. They read no interpretation: `_RangeMap_` and
`.RangeMap` have no silent point. -/
example : same (catR (cat (elem 0 3 a) (elem 3 5 a)) (elem 5 7 b)) (catL (elem 0 3 a) (cat (elem 3 5 a) (elem 5 7 b))) = true ∧
    same (catR (cat (elem 0 3 a) (elem 2 5 b)) (elem 5 7 b)) (catL (elem 0 3 a) (cat (elem 2 5 b) (elem 5 7 b))) = true ∧
    same (catR (cat (elem 0 3 a) (elem 5 7 b)) (elem 6 9 c)) (catL (elem 0 3 a) (cat (elem 5 7 b) (elem 6 9 c))) = true ∧
    same (cat M (rmV [])) (val M) = true ∧ same (cat (rmV []) M) (val M) = true ∧
    same (rmHook rmUnit []) (val (rmV [])) = true := by decide +kernel

/-- The same laws as lemmas for every range-map value (`rmConcat_unit`, `rmConcat_assoc`), at the
fixture's maps: merged, overlapping (both groupings undefined) and disjoint. -/
example : rmHook rmConcat [rmV [], M] = some (some M) ∧ rmHook rmConcat [M, rmV []] = some (some M) :=
  (rmConcat_unit (es := [(rangeT 0 3, a), (rangeT 5 7, b)]) (by decide +kernel)).2
example := rmConcat_assoc (es := [(rangeT 0 3, a)]) (fs := [(rangeT 3 5, a)]) (gs := [(rangeT 5 7, b)])
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
example := rmConcat_assoc (es := [(rangeT 0 3, a)]) (fs := [(rangeT 2 5, b)]) (gs := [(rangeT 5 7, b)])
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
example := rmConcat_assoc (es := [(rangeT 0 3, a), (rangeT 5 7, b)]) (fs := [(rangeT 3 5, c)])
  (gs := [(rangeT 7 10, a)]) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## The carrier's lemmas, at instances -/

/-- A range's sort at two pairs of bounds, in a semantics where `RangeMap:Range` is a constructor. -/
def cr : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.range], ctors := [⟨rangeCtor, [Srt.kitem, Srt.kitem], Srt.range⟩] }
  sortNames := []
  symNames := []
  userSorts := []
  ctors := []
  fns := []
  userSubsorts := []
  pgmSort := Srt.k
  rules := []

example : cr.sortOf (rangeT 0 1) = some Srt.range ∧ cr.sortOf (rangeT 5 3) = some Srt.range := by decide +kernel
example : cr.sortOf (rangeT 0 1) = cr.sortOf (rangeT 7 9) := sortOf_rangeT cr 0 1 7 9

/-- Three pairwise disjoint intervals out of order, two of them touching with one value: merged. -/
example : same (val (rmV (rmCanon [(5, 7, b), (0, 3, a), (3, 5, a)]))) (val (rmV [(rangeT 0 5, a), (rangeT 5 7, b)])) = true := by
  decide +kernel
example : rangesOK (rmCanon [(5, 7, b), (0, 3, a), (3, 5, a)]) = true :=
  rangesOK_rmCanon (by decide) (by decide)
example : (rmTriples [(rangeT 0 5, a), (rangeT 5 7, b)]).isSome = true := rmTriples_of_rangesOK (by decide +kernel)

/-- `collSortOK` reads the sort and not the kind of a definition's own collection: of kind
`.rangeMap` or `.map`, it passes at its sort. -/
def crm (k : CollKind) : Semantics := { cr with userSorts := [nRegSorts], colls := [⟨nRegSorts, k, Srt.int, some Srt.int, 400, 401, 402⟩] }
example : Faithful.collSortOK (crm .rangeMap) nRegSorts = true ∧ Faithful.collSortOK (crm .map) nRegSorts = true := by
  decide +kernel

/-! The semantics `coreOK` leaves by the library's row of sort RangeMap and its entries, and a
control of RANGEMAP's shape that it keeps. Each has a `<k>` cell and the generated counter. -/
namespace RowWitnesses

open Faithful Faithful.Model

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- The cells with the library `l` and nothing else of its own. -/
def fr (l : Lib) : Semantics where
  lib := l
  sortNames := ["KCell", "KCellOpt"]
  symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
  userSorts := cellSorts
  ctors := [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
  fns := []
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

def S : Srt := nRegSorts + 2
def uS : Sym := nRegSyms + 5
def eS : Sym := nRegSyms + 6
def cS : Sym := nRegSyms + 7

/-- An own collection of kind `K` from Int to Int at the sort `s` (not among the own sorts). -/
def wAt (s : Srt) (K : CollKind) : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
  sortNames := ["KCell", "KCellOpt", "S"]
  symNames := ["LblisKCell", "LblisKCellOpt", "LblisS", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lbl'Stop'S", "LblSItem", "Lbl'Unds'S'Unds'"]
  userSorts := cellSorts ++ [S]
  ctors := cellCtors
  fns := []
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []
  params := [{ sig := ⟨uS, [], s⟩, impl := some (builtinColl K).unit },
    { sig := ⟨eS, [Srt.int, Srt.int], s⟩, impl := some (builtinColl K).elem },
    { sig := ⟨cS, [s, s], s⟩, impl := some (builtinColl K).concat }]
  colls := [⟨s, K, Srt.int, some Srt.int, uS, eS, cS⟩]

def bI : List Srt := [Srt.int, Srt.bool]
/-- Sort 29 a token sort of the library. -/
def kTok := fr { sortsBelowKItem := bI, tokenSorts := [Srt.rangeMap] }
/-- Sort 29 a library constructor sort. -/
def kCons := fr { sortsBelowKItem := bI ++ [Srt.rangeMap], ctors := [⟨rangeCtor, [], Srt.rangeMap⟩] }
/-- `rmUnit` a library constructor of KItem. -/
def kCtor (f : Sym) := fr { sortsBelowKItem := bI, ctors := [⟨f, [], Srt.kitem⟩] }
/-- RANGEMAP's shape: Range and RangeMap below KItem, the Range constructor. -/
def kBelow := fr { sortsBelowKItem := bI ++ [Srt.range, Srt.rangeMap], ctors := [⟨rangeCtor, [Srt.kitem, Srt.kitem], Srt.range⟩] }

example : kTok.coreOK = false ∧ collSortsOK kTok = false := by decide_cheap
example : kCons.coreOK = false ∧ genWf kCons = false := by decide_cheap
example : (wAt Srt.rangeMap .map).coreOK = false ∧ collsOK (wAt Srt.rangeMap .map) = false ∧
    (wAt S .map).coreOK = true := by decide_cheap
example : (kCtor rmUnit).coreOK = false ∧ kindsApart (kCtor rmUnit) = false ∧
    (fr { sortsBelowKItem := bI }).coreOK = true := by
  decide_cheap
example : kBelow.coreOK = true := by decide_cheap

end RowWitnesses

/-! The sort predicates of Range and RangeMap: the registry numbers `isRange` and `isRangeMap` after
RANGEMAP's symbols (`predOf`), as every other library sort below KItem has its predicate, so the
text's sentences of them are read and none is listed unread (`noSortPredicate`); nor are `isK`,
`isKItem` (registry symbols), `isInt` (a predicate) and a user sort's `isX`. -/
example : predOf Srt.range = some 375 ∧ predOf Srt.rangeMap = some 377 ∧
    regSymNames[375]? = some "LblisRange" ∧ regSymNames[377]? = some "LblisRangeMap" := by
  decide +kernel
example : KCore.Parse.isNoPredName "LblisRange" = false ∧ KCore.Parse.isNoPredName "LblisRangeMap" = false ∧
    KCore.Parse.isNoPredName "LblisK" = false ∧ KCore.Parse.isNoPredName "LblisKItem" = false ∧
    KCore.Parse.isNoPredName "LblisInt" = false ∧ KCore.Parse.isNoPredName "LblisExp" = false := by
  decide +kernel

/-! `keys` interpreted, at `KeysSorted.cK` (the Range constructor, Range below KItem): `hook_sorted`
at `keys`, its `RangeBelow` from `srReady`'s conjunct `rangeKeysOK`, gives the Set of the two ranges
of a map of two entries sort Set; `hook_total`'s case of `keys` (`rmKeysHook_total`, from
`shapesOK`) gives a value at it; `keys` is no parameter of a semantics that holds none, and the
value is the same under every interpretation of the parameters. -/
namespace KeysHook

def keysMK : GroundTerm :=
  .set Srt.set [.inj Srt.range Srt.kitem (rangeT 0 3), .inj Srt.range Srt.kitem (rangeT 5 7)]

theorem hook_keysMK : hook rmKeys [KeysSorted.MK] = some (some keysMK) := rfl

example : KeysSorted.cK.sortOf keysMK = some Srt.set :=
  hook_sorted (fun _ => rangeBelow_of_keysOK (by decide +kernel)) lookupSig_hookSigs_rmKeys
    (by decide +kernel) hook_keysMK

example : ∃ v, hook rmKeys [KeysSorted.MK] = some (some v) :=
  rmKeysHook_total (c := KeysSorted.cK) (by decide +kernel) (by decide +kernel)

example (H : HookParams) : (KeysSorted.cK.withHooks H).hookRes rmKeys [KeysSorted.MK] = some (some keysMK) :=
  Semantics.hookRes_of_value hook_keysMK

/-- The discharges of `hook_sorted`'s hypothesis at a symbol that is no `keys`: by its signature,
and at an interpreted collection pattern symbol. -/
example : rmInclusion ≠ rmKeys :=
  ne_rmKeys_of_sig (k := ⟨rmInclusion, [Srt.rangeMap, Srt.rangeMap], Srt.bool⟩) (by decide +kernel) (by decide)
example : setConcat ≠ rmKeys :=
  isCollPat_hook_ne_rmKeys (c := KeysSorted.cK) (by decide +kernel) (by decide +kernel)

end KeysHook
