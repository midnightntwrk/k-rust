/-
  The interpreted hook rows of RANGEMAP: the sort row `RANGEMAP.RangeMap` and the fifteen
  operations whose `hook` attribute is among `regHookNames` (`rmRows`: `RANGEMAP.unit`,
  `elementRng`, `concat`, `lookup`, `lookupOrDefault`, `find_range`, `updateRng`, `removeRng`,
  `difference`, `updateAll`, `removeAll`, `in_keys`, `size`, `inclusion`, `keys`), the rows the
  RangeMap carrier (c1) interprets. Each has its three statements (DONE-0 C2, evidence row
  "supported hook (E6)"). The expectation is the builtin file's prose, cited by line: DOM is
  K 7.1.337's `k-distribution/include/kframework/builtin/domains.md`. No expected value below is
  taken from a run or from `hook`'s text: each value of `vals` is derived by hand from the cited
  sentence (the derivation is written at the point), and at every argument list an operation is
  stated by the function of its result. Run from the package root:
  `lake env lean test/HooksRangeMap.lean`. Kernel-checked.

  A range map is a partial function from Int to KItem (DOM 471-472: "range maps from `Int` to
  `KItem`"), written by its maximal intervals in order (DOM 498-500: "a map whose keys are stored
  as ranges, bounded inclusively below and exclusively above. Contiguous or overlapping ranges
  that map to the same value are merged into a single range"). `rmV (rmEntries ts)` is the value
  of the triples `ts` (`(a, b, v)`: every key `a ≤ k < b` has the value `v`), `RmOK ts` says they
  are maximal and in order, and `RmCov ts k x` that the key `k` has the value `x`; two values with
  the same function are one value (`rm_ext`). The points use injected integers as KItems
  (`kint n`) and need a semantics with the Range constructor, Int below KItem and Range below
  KItem (`RangeIn`; `cU_rangeIn` is one, with `coreOK`): a range is a value of sort Range only
  where the constructor is, and a member of a Set of ranges (the result of `keys`, the argument of
  `removeAll`) is the range injected into KItem.

  1. One in-domain value per operation (`vals`, most operations three or more): `hook`'s value
     there is the hand-derived one (`vals_hook`), it is the result under every interpretation
     (`vals_hookRes`; so also for the six keys of `silentTable`), and Γ states it under every
     interpretation (`vals_gamma`, `vals_gamma_H`).
  2. The regions the prose excludes or leaves unstated. Seven of the fifteen are not declared
     `total` (`partials`: DOM 508, 525, 538, 559, 569, 579, 616), and of none does the prose write
     a `#False`.
     - `M[K]` and `find_range(M, K)`: "This will yield an exception during concrete execution if
       the key is not in the range map" (DOM 534-535, 555-556). That is said of a run and names no
       value (MAP's lookup writes "The value is `#False`" beside the same words, DOM 267-268): a
       key in no range of the map is unstated (DOM 14-16: "some functions in the K prelude
       functions are not total … When you invoke such a function on an undefined input, the
       behavior is undefined").
     - `R r|-> V`, `M[R <- V]`, `M[R <- undef]`, `removeAll(M, S)` at a range that is no proper
       Int range (`[a, b)` with Int bounds and `a < b`), for `removeAll` at a member of the Set
       that is none: the prose describes ranges of Int keys "bounded inclusively below and
       exclusively above" (DOM 471-477, 488, 498-499) and says nothing of another; unstated. The
       reading that `[5, 3)` or `[3, 3)` is the range of no key (and its element the empty map) is
       excluded by the text: `r|->` is declared `injective` (DOM 525), and `[3, 3) r|-> V` and
       `[4, 4) r|-> W` would then be one value; one notion of range serves the four operations.
       `elem_injective` is the attribute at the proper ranges.
     At a point of each region the `param_undetermined` shape holds: over all interpretations H, Γ
     entails neither ⊥ nor a value (`undetermined`, the schema of test/SilentPoints.lean;
     `silent_undetermined` at every semantics with `coreOK` and every argument list where a key of
     `silentTable` has no value of `hook`; the points `opens` in the semantics `cU`,
     `opens_undetermined`; `elem_nonInt_undetermined` at a range whose bound is no Int).
     The seventh, `_RangeMap_`, is the first finding below.
  3. The silent predicate. Eight rows are declared `total` (`totals`: DOM 516, 549, 591, 605, 625,
     643, 660, 671), are no key of `silentTable` (`rm_silentKey`, `total_not_silent`) and have a
     value at every argument list of their signature (`covered_total`; under `shapesOK` a value of
     sort RangeMap is the value of maximal triples, `rm_only`). Six are keys with the predicate
     `fun _ => true` (`silents`, `silents_silent`), read only where `hook` gives no value
     (`Semantics.hookRes`), so the silent region of each is where `hook` gives none; at every
     argument list of the signature that is the region of statement 2 (`covered_elem`,
     `covered_lookup`, `covered_find`, `covered_update`, `covered_remove`, `covered_removeAll`),
     where the result is the interpretation's (`off_hookRes`). `_RangeMap_`: `covered_concat`.

  Two rows where the text does not say one thing; both are reported with the ticket (findings).
  The statements below prove what the library gives and name the other reading.
  - `_RangeMap_` at two maps with a key in common. The prose: "If the RangeMaps have overlapping
    ranges an exception will be thrown during concrete execution" (DOM 503-504), no `#False`, the
    production not declared `total` (DOM 508); and of `updateRangeMap`: "This function is total,
    which is distinct from range map concatenation, a partial function only defined on range maps
    with non overlapping ranges" (DOM 600-602). Reading A (the library's: `rmConcat` is no key of
    `silentTable`, `hook` gives no value there, and Γ states ⊥): "only defined on" says that there
    is no value off the non-overlapping maps, as MAP says of `_Map_` in the same words (DOM
    320-321), where however the prose also writes "The result is `#False`" (DOM 227-228). Reading
    B: the exception is of a run and names no value (the reading taken for `lookup` and
    `find_range` above, and for `memsetBytes` in `silentTable`), "partial … only defined on" says
    the function is not total, and an input a non-total function is not defined on has undefined
    behaviour (DOM 14-16); `silentTable` itself reads "only defined on valid indices" (DOM
    1753-1755) as a silent region for `substrString` (which is declared `total`, DOM 1758). Under
    B the overlap is unstated, `silentTable` lacks the row `(rmConcat, fun _ => true)`, and the
    `param_undetermined` shape, which fails today (`overlaps_entails`: Γ entails ⊥ for every H),
    would hold. The points are `overlaps`, kept apart; test/RangeMapGamma.lean's
    `gamma_overlaps` is the same at the fixture e6-rangemap.
    Within it, a second reading: two overlapping ranges of one value (`[0, 3) ↦ 7` with
    `[2, 5) ↦ 7`). DOM 499-500 says overlapping ranges of the same value "are merged into a single
    range" (then the result would be `[0, 5) ↦ 7`); DOM 503-504 and 600-602 speak of overlapping
    ranges whatever the values. The library takes the second (no value); `overlaps` holds such a
    point and `vals` none.
  - `M[R <- undef]` and `removeAll(M, S)` at a proper range no part of which is in the map.
    Neither is declared `total` (DOM 579, 616). The prose: "If all or any part of the range is
    present in the range map, it will be removed" (DOM 575-576); "For every range in the set, all
    or any part of it that is present in the range map will be removed" (DOM 611-613). Reading A
    (the library's: `hook` gives the map unchanged, `remove_absent`, `absents`): the sentence says
    which keys go, those of the range that the map holds, whatever part of the range that is,
    none included; the operation is not `total` because of the ranges that are no proper range.
    Reading B: the sentence covers a range of which all or a part is present; for an operation
    not declared `total` an input the sentence does not cover is unstated (as `range` of LIST at
    more elements than the list has, test/HooksList.lean), and then `hook` gives a value on an
    unstated region: it should give none there and the point be silent. `vals` holds for these two
    operations only points where a part of every range is present (and `removeAll` at the empty
    Set, where no range is named); the others are `absents`, kept apart.

  Readings taken, none leaving a value open:
  - `M[R <- V]` at a range meeting ranges of the map: "Any ranges adjacent to or overlapping with
    the range to be inserted will be updated accordingly" (DOM 565-566). Read as: the inserted
    pair holds on the range, the map elsewhere (`update_at`), which is what DOM 598-600 says in
    full of `updateRangeMap` ("the value from the second range map overwrites the value in the
    first for the parts where ranges are overlapping").
  - `<=RangeMap` at two equal maps: the prose says "strict subset" (DOM 665), the symbol is
    `<=RangeMap` and the hook `RANGEMAP.inclusion` (DOM 671), under the heading "Range map
    inclusion" (DOM 663). Taken: inclusion (`incl_at`, `incl_refl`), the reading taken for `<=Set`
    (test/HooksSet.lean). `vals` holds no point where the two differ.
  - A key that is no Int at the `total` operations `orDefault` and `in_keys`: keys are Ints (DOM
    471-477), so such a key is not present; the default (DOM 543-545), `false` (DOM 639).
  - `size`: "the number of range/value pairs" (DOM 657) of the map as it is stored, contiguous
    ranges of one value merged (DOM 499-500): the number of maximal intervals.

  The sort row `RANGEMAP.RangeMap` (DOM 471-472, 493, 498-500): `rm_value`, `rm_ext`, `rm_inj`,
  `rm_only`; a sort has no argument list, so no key of `silentTable` is about it. RANGEMAP's other
  hooks, `choice` (DOM 682), `keys_list` (634) and `values` (652), are parameters
  (`params_not_interpreted`): the prose leaves the chosen key and the order of the list open.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.HooksRangeMapTest

open KCore ML Faithful

/-! ## Γ at an interpreted symbol's application (as test/HooksList.lean writes it) -/

/-- The interpreted symbol `k` applied to the values `vs`, as Γ writes it. -/
abbrev appP (c : Semantics) (k : CtorSig) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))

/-- Where `hook` gives a value, Γ states it, in every semantics. -/
theorem gamma_val (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) {v : GroundTerm} (hh : hook k.name vs = some (some v)) :
    Γ c (appP c k vs ≡ den c v) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, some v, hk, hvs, hh, (fun h => nomatch h), rfl⟩)))))

/-- Off the silent points, Γ states ⊥ where `hook` gives no value, in every semantics. -/
theorem gamma_bot (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = false) :
    Γ c (appP c k vs ≡ ⊥) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, none, hk, hvs, hh, fun _ => hs, rfl⟩)))))

/-- The interpretation that gives `v` everywhere. -/
def constH (v : GroundTerm) : HookParams := ⟨fun _ _ => some v⟩

/-- At a silent point, `Γ (c.withHooks H)` holds the fallback's graph. -/
theorem gamma_fallback (c : Semantics) (H : HookParams) {k : CtorSig}
    (hks : lookupSig hookSigs k.name = some k) {vs : List GroundTerm}
    (hvs : (c.withHooks H).sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = true) :
    Γ (c.withHooks H) (appP (c.withHooks H) k vs ≡ (match (c.withHooks H).fallback k.name vs with
      | some v => den (c.withHooks H) v
      | none => ⊥)) :=
  Or.inr (Or.inl ⟨k, vs, (lookupSig_spec hks).1, hvs, hh, hs, rfl⟩)

theorem fallback_none (c : Semantics) (k : CtorSig) (vs : List GroundTerm) :
    (c.withHooks HookParams.none).fallback k.name vs = none := by
  unfold Semantics.fallback; split <;> rfl

theorem fallback_const (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) {k : CtorSig}
    (hks : lookupSig hookSigs k.name = some k) (vs : List GroundTerm) {v : GroundTerm}
    (hv : c.sortOf v = some k.result) : (c.withHooks (constH v)).fallback k.name vs = some v := by
  unfold Semantics.fallback; rw [hks, Semantics.sortOf_withHooks c _ hr]
  simp [Semantics.withHooks, constH, Option.filter, hv]

/-- **The `param_undetermined` shape at a silent point** (the schema `undetermined` of
test/SilentPoints.lean). Over all interpretations, Γ entails neither that the application has no
value nor that it is `v`: under `HookParams.none` it is ⊥ in every model, under `constH v` it is `v`
in every model, and both theories have models (`sound_hyp`). -/
theorem undetermined (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {k : CtorSig}
    (hks : lookupSig hookSigs k.name = some k) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = true)
    {v : GroundTerm} (hv : c.sortOf v = some k.result)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constH v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) k vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) k vs ≡ den (c.withHooks H) v)) := by
  constructor
  · -- under `constH v` the application is `v`'s element, so not ⊥
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks (constH v)) ((Semantics.coreOK_withHooks c _).trans hok) hfnv).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks (constH v)) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hfb := hIΓ _ (gamma_fallback c (constH v) hks (by rw [Semantics.sortsOf_withHooks c _ hr]; exact hvs) hh hs)
    rw [fallback_const c hr hks vs hv] at hfb
    have hbot := hall (constH v) hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks (constH v))
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hfb KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hbot KoreAML.val0 default) a
    exact absurd ((h2.mp (h1.mpr ((ha a).mpr rfl)))) (by simp [Pattern.interpret])
  · -- under `HookParams.none` the application is ⊥, so not `v`
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks HookParams.none) ((Semantics.coreOK_withHooks c _).trans hok) hfn₀).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks HookParams.none) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hfb := hIΓ _ (gamma_fallback c HookParams.none hks (by rw [Semantics.sortsOf_withHooks c _ hr]; exact hvs) hh hs)
    rw [fallback_none c k vs] at hfb
    have hval := hall HookParams.none hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks HookParams.none)
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hfb KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hval KoreAML.val0 default) a
    exact absurd (h1.mp (h2.mpr ((ha a).mpr rfl))) (by simp [Pattern.interpret])

/-- The signature of an interpreted symbol. -/
def sig (f : Sym) : CtorSig := (lookupSig hookSigs f).getD default

/-! ## The rows -/

/-- The fifteen interpreted operation rows of RANGEMAP: the symbol and its `hook` attribute in the
prose's productions (DOM 516 `RANGEMAP.unit`, 525 `elementRng`, 508 `concat`, 538 `lookup`,
549 `lookupOrDefault`, 559 `find_range`, 569 `updateRng`, 579 `removeRng`, 591 `difference`,
605 `updateAll`, 616 `removeAll`, 643 `in_keys`, 660 `size`, 671 `inclusion`, 625 `keys`). The
sixteenth row is the sort (`RANGEMAP.RangeMap`, DOM 493). -/
def rmRows : List (Sym × String) :=
  [(rmUnit, "RANGEMAP.unit"), (rmElem, "RANGEMAP.elementRng"), (rmConcat, "RANGEMAP.concat"),
   (rmLookup, "RANGEMAP.lookup"), (rmLookupOrDefault, "RANGEMAP.lookupOrDefault"),
   (rmFindRange, "RANGEMAP.find_range"), (rmUpdate, "RANGEMAP.updateRng"),
   (rmRemove, "RANGEMAP.removeRng"), (rmDifference, "RANGEMAP.difference"),
   (rmUpdateAll, "RANGEMAP.updateAll"), (rmRemoveAll, "RANGEMAP.removeAll"),
   (rmInKeys, "RANGEMAP.in_keys"), (rmSize, "RANGEMAP.size"), (rmInclusion, "RANGEMAP.inclusion"),
   (rmKeys, "RANGEMAP.keys")]

/-- The seven the prose does not declare `total` (DOM 525, 508, 538, 559, 569, 579, 616). -/
def partials : List Sym := [rmElem, rmConcat, rmLookup, rmFindRange, rmUpdate, rmRemove, rmRemoveAll]

/-- The eight the prose declares `total` (DOM 516, 549, 591, 605, 643, 660, 671, 625). -/
def totals : List Sym :=
  [rmUnit, rmLookupOrDefault, rmDifference, rmUpdateAll, rmInKeys, rmSize, rmInclusion, rmKeys]

/-- The six with a region the prose leaves unstated under every reading of the header. -/
def silents : List Sym := [rmElem, rmLookup, rmFindRange, rmUpdate, rmRemove, rmRemoveAll]

/-- The rows are the registry's entries with a `RANGEMAP.` hook, each with its hook name. -/
theorem rmRows_registry :
    regHookNames.filter (fun e => e.2.toList.take 9 == "RANGEMAP.".toList) = rmRows := by
  decide +kernel

/-- The signatures, as the prose's productions give them (the lines of `rmRows`). -/
def rmSigs : List (Sym × List Srt × Srt) :=
  [(rmUnit, [], Srt.rangeMap), (rmElem, [Srt.range, Srt.kitem], Srt.rangeMap),
   (rmConcat, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap),
   (rmLookup, [Srt.rangeMap, Srt.kitem], Srt.kitem),
   (rmLookupOrDefault, [Srt.rangeMap, Srt.kitem, Srt.kitem], Srt.kitem),
   (rmFindRange, [Srt.rangeMap, Srt.kitem], Srt.range),
   (rmUpdate, [Srt.rangeMap, Srt.range, Srt.kitem], Srt.rangeMap),
   (rmRemove, [Srt.rangeMap, Srt.range], Srt.rangeMap),
   (rmDifference, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap),
   (rmUpdateAll, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap),
   (rmRemoveAll, [Srt.rangeMap, Srt.set], Srt.rangeMap),
   (rmInKeys, [Srt.kitem, Srt.rangeMap], Srt.bool), (rmSize, [Srt.rangeMap], Srt.int),
   (rmInclusion, [Srt.rangeMap, Srt.rangeMap], Srt.bool), (rmKeys, [Srt.rangeMap], Srt.set)]

/-- Each row's symbol has that signature among `hookSigs`. -/
theorem rmRows_sig : (rmRows.map (·.1) == rmSigs.map (·.1) &&
    rmSigs.all (fun r => decide (sig r.1 ∈ hookSigs) && (sig r.1).name == r.1 &&
      lookupSig hookSigs r.1 == some (sig r.1) &&
      (sig r.1).args == r.2.1 && (sig r.1).result == r.2.2)) = true := by
  decide +kernel

/-- `partialHooks` (the interpreted symbols the totality deciders do not count as total) holds of
these rows exactly the seven the prose does not declare `total`; the rows are those seven and the
eight. -/
theorem rmRows_partial : (rmRows.all (fun r => partialHooks.contains r.1 == partials.contains r.1) &&
    rmRows.all (fun r => partials.contains r.1 != totals.contains r.1)) = true := by
  decide +kernel

/-- **The keys of `silentTable` among the rows are exactly the six of `silents`**: the seven the
prose does not declare `total`, less `_RangeMap_` (the header's first finding). -/
theorem rm_silentKey : (rmRows.all (fun r => silentKey r.1 == silents.contains r.1) &&
    partials.all (fun f => silents.contains f != (f == rmConcat))) = true := by
  decide +kernel

/-- `choice`, `keys_list` and `values` are not interpreted: no entry of `hookTable`, none of the
registry. -/
theorem params_not_interpreted : [rmChoice, rmKeysList, rmValues].all (fun f =>
    (hook f []).isNone && !regHookNames.any (·.1 == f)) = true := by
  decide +kernel

/-! ## Values -/

/-- The Range constructor is in `c` and Int and Range are below KItem: a range `[a, b)` is a value
of sort Range, an injected integer and an injected range are KItems. -/
structure RangeIn (c : Semantics) : Prop where
  int : (Srt.int, Srt.kitem) ∈ c.subsorts
  rng : (Srt.range, Srt.kitem) ∈ c.subsorts
  ctor : c.sortOf (rangeT 0 1) = some Srt.range

theorem RangeIn.withHooks {c : Semantics} (h : RangeIn c) (hr : ∀ k ∈ c.params, k.raw = false)
    (H : HookParams) : RangeIn (c.withHooks H) :=
  ⟨h.int, h.rng, by rw [Semantics.sortOf_withHooks c H hr]; exact h.ctor⟩

/-- A range injected into KItem (a member of a Set of ranges). -/
def kr (a b : Int) : GroundTerm := .inj Srt.range Srt.kitem (rangeT a b)

theorem int_value (c : Semantics) (i : Int) : c.sortOf (int i) = some Srt.int := by
  simp [int, Semantics.sortOf, dvOK]

theorem bool_value (c : Semantics) (b : Bool) : c.sortOf (bool b) = some Srt.bool := by
  simp [bool, Semantics.sortOf, dvOK]

theorem ki_value {c : Semantics} (h : RangeIn c) (n : Int) : c.sortOf (kint n) = some Srt.kitem :=
  sortOf_inj.mpr ⟨h.int, rfl, int_value c n, rfl⟩

theorem range_value {c : Semantics} (h : RangeIn c) (a b : Int) : c.sortOf (rangeT a b) = some Srt.range :=
  (sortOf_rangeT c a b 0 1).trans h.ctor

theorem kr_value {c : Semantics} (h : RangeIn c) (a b : Int) : c.sortOf (kr a b) = some Srt.kitem :=
  sortOf_inj.mpr ⟨h.rng, rfl, range_value h a b, rfl⟩

theorem asKInt_kint (i : Int) : asKInt (kint i) = some i := by
  simp [asKInt, kint, asInt, int]

/-- A range term is a proper range exactly when it is `[a, b)` with Int bounds and `a < b`. -/
theorem asRange_iff {r : GroundTerm} {a b : Int} : asRange r = some (a, b) ↔ r = rangeT a b ∧ a < b :=
  ⟨asRange_some, by rintro ⟨rfl, h⟩; exact asRange_rangeT h⟩

theorem asKRange_kr (r : GroundTerm) : asKRange (.inj Srt.range Srt.kitem r) = asRange r := by
  simp [asKRange]

/-! ## The sort row `RANGEMAP.RangeMap` -/

/-- Maximal triples whose ranges are of sort Range and whose values are KItems are a value of sort
RangeMap, in every semantics: "range maps from `Int` to `KItem`" (DOM 471-472), the sort declared
at DOM 493, its keys "stored as ranges" (DOM 498). -/
theorem rm_value {c : Semantics} {ts : List RmTriple} (hok : RmOK ts) (hs : RmSorted c ts) :
    c.sortOf (rmV (rmEntries ts)) = some Srt.rangeMap :=
  (rmS_sortOf_map collOf_rangeMap).mpr ⟨rfl, rangesOK_of_rmOK hok, fun e he => by
    obtain ⟨⟨a, b, v⟩, ht, rfl⟩ := List.mem_map.mp he
    exact ⟨(hs _ ht).2.1, (hs _ ht).2.2⟩⟩

/-- "Contiguous or overlapping ranges that map to the same value are merged into a single range"
(DOM 499-500): a range map is its function; two maximal descriptions of one function are one
value. -/
theorem rm_ext {ts us : List RmTriple} (ht : RmOK ts) (hu : RmOK us)
    (h : ∀ k x, RmCov ts k x ↔ RmCov us k x) : rmV (rmEntries ts) = rmV (rmEntries us) := by
  rw [rmOK_unique ht hu h]

/-- Two values of proper triples are the same value only when the triples are the same. -/
theorem rm_inj {ts us : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (hq : ∀ u ∈ us, u.1 < u.2.1)
    (h : rmV (rmEntries ts) = rmV (rmEntries us)) : ts = us := by
  have h' := congrArg rmTriples (GroundTerm.map.inj h).2
  rw [rmTriples_rmEntries hp, rmTriples_rmEntries hq] at h'
  exact Option.some.inj h'

/-- Nothing else is a value of sort RangeMap (where the sorts the interpreted symbols read have
their shapes, `shapesOK`): the value of maximal triples, ranges of sort Range, values KItems. -/
theorem rm_only {c : Semantics} (hs : c.shapesOK = true) {v : GroundTerm}
    (h : c.sortOf v = some Srt.rangeMap) :
    ∃ ts, v = rmV (rmEntries ts) ∧ RmOK ts ∧ RmSorted c ts := by
  obtain ⟨es, _, rfl, -⟩ := shape_rangeMap hs h
  obtain ⟨-, hr, -⟩ := (rmS_sortOf_map collOf_rangeMap).mp h
  obtain ⟨ts, hts, rfl, hok⟩ := rmOK_of_value hr
  exact ⟨ts, rfl, hok, (rmS_arg collOf_rangeMap h hts).1⟩

/-! ## The function of a range map -/

/-- Two intervals of pairwise disjoint triples that hold one key are one triple. -/
theorem dj_unique {i : Int} : ∀ {ts : List RmTriple}, ts.Pairwise rmDj → ∀ {t u : RmTriple},
    t ∈ ts → u ∈ ts → t.1 ≤ i → i < t.2.1 → u.1 ≤ i → i < u.2.1 → t = u
  | [], _, _, _, ht, _, _, _, _, _ => nomatch ht
  | a :: l, hd, t, u, ht, hu, h1, h2, h3, h4 => by
    have hda : ∀ x ∈ l, a.2.1 ≤ x.1 ∨ x.2.1 ≤ a.1 := fun x hx => List.rel_of_pairwise_cons hd hx
    rcases List.mem_cons.mp ht with ht | ht <;> rcases List.mem_cons.mp hu with hu | hu
    · rw [ht, hu]
    · have := hda u hu; rw [ht] at h1 h2; omega
    · have := hda t ht; rw [hu] at h3 h4; omega
    · exact dj_unique hd.of_cons ht hu h1 h2 h3 h4

/-- A range map is a function: a key has at most one value. -/
theorem cov_fun {ts : List RmTriple} (hd : ts.Pairwise rmDj) {k : Int} {x y : GroundTerm}
    (hx : RmCov ts k x) (hy : RmCov ts k y) : x = y := by
  obtain ⟨t, ht, h1, h2, rfl⟩ := hx
  obtain ⟨u, hu, h3, h4, rfl⟩ := hy
  rw [dj_unique hd ht hu h1 h2 h3 h4]

theorem find_in {i : Int} {ts : List RmTriple} {t : RmTriple} (h : rmFind i ts = some t) :
    t ∈ ts ∧ t.1 ≤ i ∧ i < t.2.1 := by
  unfold rmFind at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  obtain ⟨a, b, v⟩ := t
  simp at hp
  exact ⟨hm, hp.1, hp.2⟩

theorem find_cov {ts : List RmTriple} (hd : ts.Pairwise rmDj) {i : Int} {t : RmTriple} (ht : t ∈ ts)
    (h1 : t.1 ≤ i) (h2 : i < t.2.1) : rmFind i ts = some t := by
  cases hf : rmFind i ts with
  | none =>
    unfold rmFind at hf
    obtain ⟨a, b, v⟩ := t
    have h1' : a ≤ i := h1
    have h2' : i < b := h2
    have hn : ¬ ((decide (a ≤ i) && decide (i < b)) = true) := List.find?_eq_none.mp hf (a, b, v) ht
    exact absurd (by simp [h1', h2']) hn
  | some u =>
    obtain ⟨hu, h3, h4⟩ := find_in hf
    rw [dj_unique hd hu ht h3 h4 h1 h2]

theorem find_none {ts : List RmTriple} {i : Int} (h : ∀ x, ¬ RmCov ts i x) : rmFind i ts = none := by
  cases hf : rmFind i ts with
  | none => rfl
  | some t =>
    obtain ⟨ht, h1, h2⟩ := find_in hf
    exact absurd ⟨t, ht, h1, h2, rfl⟩ (h t.2.2)

/-- The KItem `k` is a key of the map with the value `x`: an Int (DOM 471-477) that a range of the
map holds. -/
def Holds (ts : List RmTriple) (k x : GroundTerm) : Prop := ∃ i, asKInt k = some i ∧ RmCov ts i x

theorem holds_kint {ts : List RmTriple} {i : Int} {x : GroundTerm} : Holds ts (kint i) x ↔ RmCov ts i x :=
  ⟨fun ⟨j, hj, h⟩ => by rw [asKInt_kint] at hj; cases hj; exact h, fun h => ⟨i, asKInt_kint i, h⟩⟩

/-- One interval less a range: its keys outside the range, with their value. -/
theorem cutOne_cov {a b k : Int} {t : RmTriple} {x : GroundTerm} :
    RmCov (rmCutOne a b t) k x ↔ (t.1 ≤ k ∧ k < t.2.1 ∧ t.2.2 = x) ∧ (k < a ∨ b ≤ k) := by
  constructor
  · rintro ⟨y, hy, h1, h2, h3⟩
    obtain ⟨-, g1, g2, g3, g4⟩ := rmS_cutOne_mem hy
    exact ⟨⟨by omega, by omega, g3.symm.trans h3⟩, by omega⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    obtain ⟨p, q, w⟩ := t
    have h1' : p ≤ k := h1
    have h2' : k < q := h2
    rcases h4 with h4 | h4
    · have hlt : p < min q a := by omega
      refine ⟨(p, min q a, w), ?_, h1, ?_, h3⟩
      · show _ ∈ (if p < min q a then [(p, min q a, w)] else []) ++
          (if max p b < q then [(max p b, q, w)] else [])
        simp only [hlt, ↓reduceIte]; exact List.mem_append_left _ (List.mem_singleton_self _)
      · show k < min q a
        omega
    · have hlt : max p b < q := by omega
      refine ⟨(max p b, q, w), ?_, ?_, h2, h3⟩
      · show _ ∈ (if p < min q a then [(p, min q a, w)] else []) ++
          (if max p b < q then [(max p b, q, w)] else [])
        simp only [hlt, ↓reduceIte]; exact List.mem_append_right _ (List.mem_singleton_self _)
      · show max p b ≤ k
        omega

/-- The intervals less a range: the map's keys outside the range. -/
theorem cut_cov {a b k : Int} {ts : List RmTriple} {x : GroundTerm} :
    RmCov (rmCut a b ts) k x ↔ RmCov ts k x ∧ (k < a ∨ b ≤ k) := by
  constructor
  · rintro ⟨y, hy, hc⟩
    obtain ⟨t, ht, hyt⟩ := List.mem_flatMap.mp hy
    obtain ⟨h, h'⟩ := cutOne_cov.mp ⟨y, hyt, hc⟩
    exact ⟨⟨t, ht, h⟩, h'⟩
  · rintro ⟨⟨t, ht, h⟩, h'⟩
    obtain ⟨y, hy, hc⟩ := cutOne_cov.mpr ⟨h, h'⟩
    exact ⟨y, List.mem_flatMap.mpr ⟨t, ht, hy⟩, hc⟩

/-- Sorted, pairwise disjoint triples have a maximal description of the same function, a value of
sort RangeMap (`rmCanonT_spec`, `rmS_canon_sorted`). -/
theorem canon_at {c : Semantics} {ts : List RmTriple} (hs : RmSorted c ts) (hd : ts.Pairwise rmDj) :
    RmOK (rmCanonT ts) ∧ (∀ k x, RmCov (rmCanonT ts) k x ↔ RmCov ts k x) ∧
      c.sortOf (rmV (rmEntries (rmCanonT ts))) = some Srt.rangeMap :=
  have h := rmCanonT_spec (fun t ht => (hs t ht).1) hd
  ⟨h.1, h.2, rmS_canon_sorted collOf_rangeMap hs hd⟩

theorem out_iff {us : List RmTriple} {k : Int} :
    (∀ u ∈ us, k < u.1 ∨ u.2.1 ≤ k) ↔ ∀ y, ¬ RmCov us k y := by
  constructor
  · rintro h y ⟨u, hu, h1, h2, -⟩
    have := h u hu
    omega
  · intro h u hu
    by_cases h1 : u.1 ≤ k
    · by_cases h2 : k < u.2.1
      · exact absurd ⟨u, hu, h1, h2, rfl⟩ (h u.2.2)
      · exact .inr (by omega)
    · exact .inl (by omega)

/-! ## `hook` at every argument list, by the function of the result -/

/-- "The `RangeMap` with zero elements is represented by `.RangeMap`" (DOM 513), `total` (DOM 516):
no key. -/
theorem unit_at : hook rmUnit [] = some (some (rmV (rmEntries []))) := rfl

theorem elem_raw (r v : GroundTerm) :
    hook rmElem [r, v] = some ((asRange r).map fun (a, b) => rmV [(rangeT a b, v)]) := rfl

/-- "An element of a `RangeMap` is constructed via the `r|->` operator. The range of keys is on the
left, and the value is on the right" (DOM 521-522): at a proper range, the map of that one range
(its keys `a ≤ k < b`, "bounded inclusively below and exclusively above", DOM 488) with the value. -/
theorem elem_at {a b : Int} (h : a < b) (v : GroundTerm) :
    hook rmElem [rangeT a b, v] = some (some (rmV (rmEntries [(a, b, v)]))) :=
  (elem_raw _ _).trans (by rw [asRange_rangeT h] <;> rfl)

/-- At a range that is no proper Int range `hook` gives no value (and the prose says nothing). -/
theorem elem_off {r : GroundTerm} (h : asRange r = none) (v : GroundTerm) : hook rmElem [r, v] = some none :=
  (elem_raw _ _).trans (by rw [h] <;> rfl)

/-- `injective` (DOM 525), at the proper ranges: the element determines its range and its value. -/
theorem elem_injective {a b a' b' : Int} {v v' : GroundTerm} (h : a < b) (h' : a' < b')
    (he : rmV (rmEntries [(a, b, v)]) = rmV (rmEntries [(a', b', v')])) : a = a' ∧ b = b' ∧ v = v' := by
  have e := rm_inj (ts := [(a, b, v)]) (us := [(a', b', v')])
    (fun t ht => by rw [List.mem_singleton.mp ht]; exact h)
    (fun t ht => by rw [List.mem_singleton.mp ht]; exact h') he
  injection e with e1 _
  injection e1 with ea e2
  injection e2 with eb ev
  exact ⟨ea, eb, ev⟩

theorem join_some_eq {α : Type} {o : Option (Option α)} {y x : Option α} (h1 : o = some y)
    (h2 : o.join = x) : o = some x := by
  subst h1; exact congrArg some h2

/-- "You can construct a new `RangeMap` consisting of range/value pairs of two RangeMaps" (DOM
502-503): where no key is in both, the map with the keys of both, each with its value. -/
theorem concat_at {ts us : List RmTriple} (ht : RmOK ts) (hu : RmOK us) (h : RmApart ts us) :
    ∃ zs, RmOK zs ∧ (∀ k x, RmCov zs k x ↔ RmCov ts k x ∨ RmCov us k x) ∧
      hook rmConcat [rmV (rmEntries ts), rmV (rmEntries us)] = some (some (rmV (rmEntries zs))) := by
  have hd : rmDisjoint ts us = true := (rmDisjoint_iff (rmOK_proper ht) (rmOK_proper hu)).mpr h
  have hc : rmCatT ts us = some (rmCanonT (ts ++ us)) := by simp [rmCatT, hd]
  obtain ⟨-, hok, hcov⟩ := (rmCatT_some ht hu).mp hc
  exact ⟨_, hok, hcov, join_some_eq (rmHook_rmConcat Srt.rangeMap Srt.rangeMap _ _)
    ((rmConcat_value ht hu).trans (by rw [hc] <;> rfl))⟩

/-- Where a key is in both, `hook` gives no value (the header's first finding). -/
theorem concat_off {ts us : List RmTriple} (ht : RmOK ts) (hu : RmOK us) (h : ¬ RmApart ts us) :
    hook rmConcat [rmV (rmEntries ts), rmV (rmEntries us)] = some none := by
  have hd : rmDisjoint ts us = false := by
    cases h' : rmDisjoint ts us with
    | false => rfl
    | true => exact absurd ((rmDisjoint_iff (rmOK_proper ht) (rmOK_proper hu)).mp h') h
  have hc : rmCatT ts us = none := by simp [rmCatT, hd]
  exact join_some_eq (rmHook_rmConcat Srt.rangeMap Srt.rangeMap _ _)
    ((rmConcat_value ht hu).trans (by rw [hc] <;> rfl))

/-- `comm` (DOM 508): either order gives the same (one value, or none). `assoc` and
`unit(.RangeMap)` are the library's `rmConcat_assoc` and `rmConcat_unit`. -/
theorem concat_comm {ts us : List RmTriple} (ht : RmOK ts) (hu : RmOK us) :
    hook rmConcat [rmV (rmEntries ts), rmV (rmEntries us)] =
      hook rmConcat [rmV (rmEntries us), rmV (rmEntries ts)] := by
  by_cases h : RmApart ts us
  · obtain ⟨zs, hz, hcz, hhz⟩ := concat_at ht hu h
    obtain ⟨ws, hw, hcw, hhw⟩ := concat_at hu ht (rmApart_symm h)
    rw [hhz, hhw, rmOK_unique hz hw fun k x => (hcz k x).trans (Or.comm.trans (hcw k x).symm)]
  · rw [concat_off ht hu h, concat_off hu ht fun h' => h (rmApart_symm h')]

theorem lookup_raw (s : Srt) (m : Entries) (k : GroundTerm) : hook rmLookup [.map s m, k] =
    some ((rmTriples m).bind fun ts => (asKInt k).bind fun i => (rmFind i ts).map (·.2.2)) := rfl

theorem lookup_eq {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (k : GroundTerm) :
    hook rmLookup [rmV (rmEntries ts), k] = some ((asKInt k).bind fun i => (rmFind i ts).map (·.2.2)) :=
  (lookup_raw _ _ _).trans (by rw [rmTriples_rmEntries hp] <;> rfl)

/-- "You can look up the value associated with a key of a `RangeMap`" (DOM 533): at a key of the
map, its value. -/
theorem lookup_at {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (hd : ts.Pairwise rmDj)
    {k x : GroundTerm} (h : Holds ts k x) : hook rmLookup [rmV (rmEntries ts), k] = some (some x) := by
  obtain ⟨i, hk, t, ht, h1, h2, rfl⟩ := h
  rw [lookup_eq hp, hk]
  show some ((rmFind i ts).map (·.2.2)) = _
  rw [find_cov hd ht h1 h2] <;> rfl

/-- At a key that is not in the map `hook` gives no value (DOM 534-535 names a run's exception and
no value). -/
theorem lookup_off {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) {k : GroundTerm}
    (h : ∀ x, ¬ Holds ts k x) : hook rmLookup [rmV (rmEntries ts), k] = some none := by
  rw [lookup_eq hp]
  cases hk : asKInt k with
  | none => rfl
  | some i =>
    show some ((rmFind i ts).map (·.2.2)) = _
    rw [find_none fun x hx => h x ⟨i, hk, hx⟩] <;> rfl

theorem ord_raw (s : Srt) (m : Entries) (k d : GroundTerm) : hook rmLookupOrDefault [.map s m, k, d] =
    some ((rmTriples m).map fun ts => (((asKInt k).bind fun i => rmFind i ts).map (·.2.2)).getD d) := rfl

theorem ord_eq {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (k d : GroundTerm) :
    hook rmLookupOrDefault [rmV (rmEntries ts), k, d] =
      some (some ((((asKInt k).bind fun i => rmFind i ts).map (·.2.2)).getD d)) :=
  (ord_raw _ _ _ _).trans (by rw [rmTriples_rmEntries hp] <;> rfl)

/-- "look up the value associated with a key of a `RangeMap` using a total function that assigns a
specific default value if the key is not present" (DOM 543-545), `total` (DOM 549): at a key of the
map, its value. -/
theorem ord_at {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (hd : ts.Pairwise rmDj)
    {k x : GroundTerm} (h : Holds ts k x) (d : GroundTerm) :
    hook rmLookupOrDefault [rmV (rmEntries ts), k, d] = some (some x) := by
  obtain ⟨i, hk, t, ht, h1, h2, rfl⟩ := h
  rw [ord_eq hp, hk]
  show some (some (((rmFind i ts).map (·.2.2)).getD d)) = _
  rw [find_cov hd ht h1 h2] <;> rfl

/-- At a key that is not in the map, the default. -/
theorem ord_off {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) {k : GroundTerm}
    (h : ∀ x, ¬ Holds ts k x) (d : GroundTerm) :
    hook rmLookupOrDefault [rmV (rmEntries ts), k, d] = some (some d) := by
  rw [ord_eq hp]
  cases hk : asKInt k with
  | none => rfl
  | some i =>
    show some (some (((rmFind i ts).map (·.2.2)).getD d)) = _
    rw [find_none fun x hx => h x ⟨i, hk, hx⟩] <;> rfl

theorem findr_raw (s : Srt) (m : Entries) (k : GroundTerm) : hook rmFindRange [.map s m, k] =
    some ((rmTriples m).bind fun ts => (asKInt k).bind fun i =>
      (rmFind i ts).map fun (a, b, _) => rangeT a b) := rfl

theorem findr_eq {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (k : GroundTerm) :
    hook rmFindRange [rmV (rmEntries ts), k] =
      some ((asKInt k).bind fun i => (rmFind i ts).map fun (a, b, _) => rangeT a b) :=
  (findr_raw _ _ _).trans (by rw [rmTriples_rmEntries hp] <;> rfl)

/-- "the range that a key of a `RangeMap` is stored in" (DOM 554): at an Int key that the range
`[a, b)` of the map holds, that range. -/
theorem findr_at {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (hd : ts.Pairwise rmDj)
    {k : GroundTerm} {i a b : Int} {v : GroundTerm} (hk : asKInt k = some i) (ht : (a, b, v) ∈ ts)
    (h1 : a ≤ i) (h2 : i < b) : hook rmFindRange [rmV (rmEntries ts), k] = some (some (rangeT a b)) := by
  rw [findr_eq hp, hk]
  show some ((rmFind i ts).map fun (a, b, _) => rangeT a b) = _
  rw [find_cov hd ht h1 h2] <;> rfl

/-- At a key that is not in the map `hook` gives no value (DOM 555-556 names a run's exception and
no value). -/
theorem findr_off {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) {k : GroundTerm}
    (h : ∀ x, ¬ Holds ts k x) : hook rmFindRange [rmV (rmEntries ts), k] = some none := by
  rw [findr_eq hp]
  cases hk : asKInt k with
  | none => rfl
  | some i =>
    show some ((rmFind i ts).map fun (a, b, _) => rangeT a b) = _
    rw [find_none fun x hx => h x ⟨i, hk, hx⟩] <;> rfl

theorem update_raw (s : Srt) (m : Entries) (r v : GroundTerm) : hook rmUpdate [.map s m, r, v] =
    some ((rmTriples m).bind fun ts => (asRange r).map fun (a, b) =>
      rmV (rmCanon (rmCut a b ts ++ [(a, b, v)]))) := rfl

/-- "You can insert a range/value pair into a `RangeMap` … Any ranges adjacent to or overlapping
with the range to be inserted will be updated accordingly" (DOM 564-566): at a proper range, the
map that holds the inserted pair on the range and the map's own keys outside it. -/
theorem update_at {c : Semantics} {ts : List RmTriple} (hs : RmSorted c ts) (hd : ts.Pairwise rmDj)
    {a b : Int} (hab : a < b) (hr : c.sortOf (rangeT a b) = some Srt.range) {v : GroundTerm}
    (hv : c.sortOf v = some Srt.kitem) :
    ∃ zs, RmOK zs ∧
      (∀ k x, RmCov zs k x ↔ (a ≤ k ∧ k < b ∧ v = x) ∨ (RmCov ts k x ∧ (k < a ∨ b ≤ k))) ∧
      c.sortOf (rmV (rmEntries zs)) = some Srt.rangeMap ∧
      hook rmUpdate [rmV (rmEntries ts), rangeT a b, v] = some (some (rmV (rmEntries zs))) := by
  obtain ⟨h1, h2⟩ := rmS_over hab hr hv hs hd
  obtain ⟨hok, hcov, hsort⟩ := canon_at h1 h2
  refine ⟨_, hok, fun k x => ?_, hsort, ?_⟩
  · rw [hcov, rmCov_append, cut_cov, rmCov_cons]
    constructor
    · rintro (h | h | h)
      · exact .inr h
      · exact .inl h
      · exact absurd h (rmCov_nil k x)
    · rintro (h | h)
      · exact .inr (.inl h)
      · exact .inl h
  · exact (update_raw _ _ _ _).trans
      (by rw [rmTriples_rmEntries fun t ht => (hs t ht).1, asRange_rangeT hab] <;> rfl)

/-- At a range that is no proper Int range `hook` gives no value (and the prose says nothing). -/
theorem update_off {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) {r : GroundTerm}
    (hr : asRange r = none) (v : GroundTerm) : hook rmUpdate [rmV (rmEntries ts), r, v] = some none :=
  (update_raw _ _ _ _).trans (by rw [rmTriples_rmEntries hp, hr] <;> rfl)

theorem remove_raw (s : Srt) (m : Entries) (r : GroundTerm) : hook rmRemove [.map s m, r] =
    some ((rmTriples m).bind fun ts => (asRange r).map fun (a, b) => rmV (rmCanon (rmCut a b ts))) := rfl

/-- "If all or any part of the range is present in the range map, it will be removed" (DOM
575-576): at a proper range, the map's keys outside the range. -/
theorem remove_at {c : Semantics} {ts : List RmTriple} (hs : RmSorted c ts) (hd : ts.Pairwise rmDj)
    {a b : Int} (hab : a < b) :
    ∃ zs, RmOK zs ∧ (∀ k x, RmCov zs k x ↔ RmCov ts k x ∧ (k < a ∨ b ≤ k)) ∧
      c.sortOf (rmV (rmEntries zs)) = some Srt.rangeMap ∧
      hook rmRemove [rmV (rmEntries ts), rangeT a b] = some (some (rmV (rmEntries zs))) := by
  obtain ⟨h1, h2, -⟩ := rmS_cut (Int.le_of_lt hab) hs hd
  obtain ⟨hok, hcov, hsort⟩ := canon_at h1 h2
  exact ⟨_, hok, fun k x => by rw [hcov, cut_cov], hsort, (remove_raw _ _ _).trans
    (by rw [rmTriples_rmEntries fun t ht => (hs t ht).1, asRange_rangeT hab] <;> rfl)⟩

/-- At a proper range no key of which is in the map, `hook` gives the map (reading A of the header's
second finding; under reading B the point is unstated). -/
theorem remove_absent {c : Semantics} {ts : List RmTriple} (hs : RmSorted c ts) (hok : RmOK ts)
    {a b : Int} (hab : a < b) (hno : ∀ k x, RmCov ts k x → k < a ∨ b ≤ k) :
    hook rmRemove [rmV (rmEntries ts), rangeT a b] = some (some (rmV (rmEntries ts))) := by
  obtain ⟨zs, hz, hcov, -, hh⟩ := remove_at hs (rmOK_pairwise hok) hab
  have e : zs = ts := rmOK_unique hz hok fun k x => (hcov k x).trans ⟨fun h => h.1, fun h => ⟨h, hno k x h⟩⟩
  rw [hh, e]

theorem remove_off {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) {r : GroundTerm}
    (hr : asRange r = none) : hook rmRemove [rmV (rmEntries ts), r] = some none :=
  (remove_raw _ _ _).trans (by rw [rmTriples_rmEntries hp, hr] <;> rfl)

theorem removeAll_raw (s : Srt) (m : Entries) (s' : Srt) (rs : List GroundTerm) :
    hook rmRemoveAll [.map s m, .set s' rs] =
      some ((rmTriples m).bind fun ts => (rs.mapM asKRange).map fun ps =>
        rmV (rmCanon (ps.foldl (fun acc (a, b) => rmCut a b acc) ts))) := rfl

theorem cuts_cov {k : Int} {x : GroundTerm} : ∀ (ps : List (Int × Int)) (ts : List RmTriple),
    RmCov (ps.foldl (fun acc (a, b) => rmCut a b acc) ts) k x ↔
      RmCov ts k x ∧ ∀ p ∈ ps, k < p.1 ∨ p.2 ≤ k
  | [], ts => by simp
  | (a, b) :: ps, ts => by
    show RmCov (ps.foldl (fun acc (a, b) => rmCut a b acc) (rmCut a b ts)) k x ↔ _
    rw [cuts_cov ps, cut_cov]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with hp | hp
      · rw [hp]; exact h2
      · exact h3 p hp
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2 (a, b) (List.mem_cons_self ..)⟩, fun p hp => h2 p (List.mem_cons_of_mem _ hp)⟩

/-- The members of a Set that are proper ranges injected into KItem read as their bounds. -/
theorem mapM_ranges : ∀ ps : List (Int × Int), (∀ p ∈ ps, p.1 < p.2) →
    (ps.map fun p => kr p.1 p.2).mapM asKRange = some ps
  | [], _ => rfl
  | (a, b) :: ps, h => by
    have hab : a < b := h (a, b) (List.mem_cons_self ..)
    have ih := mapM_ranges ps fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [List.map_cons, List.mapM_cons]
    show (asKRange (.inj Srt.range Srt.kitem (rangeT a b))).bind (fun x =>
      ((ps.map fun p => kr p.1 p.2).mapM asKRange).bind fun xs => some (x :: xs)) = _
    rw [asKRange_kr, asRange_rangeT hab, ih] <;> rfl

/-- A Set with a member that is no proper range injected into KItem does not read. -/
theorem mapM_bad : ∀ {rs : List GroundTerm} {r : GroundTerm}, r ∈ rs → asKRange r = none →
    rs.mapM asKRange = none
  | r' :: rs, r, hr, h => by
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hr with hr | hr
    · rw [← hr, h]; rfl
    · rw [mapM_bad hr h]; cases asKRange r' <;> rfl

/-- "For every range in the set, all or any part of it that is present in the range map will be
removed" (DOM 611-613): at a Set of proper ranges, the map's keys outside every range of the Set. -/
theorem removeAll_at {c : Semantics} {ts : List RmTriple} (hs : RmSorted c ts) (hd : ts.Pairwise rmDj)
    {rs : List GroundTerm} {ps : List (Int × Int)} (hm : rs.mapM asKRange = some ps) (s' : Srt) :
    ∃ zs, RmOK zs ∧ (∀ k x, RmCov zs k x ↔ RmCov ts k x ∧ ∀ p ∈ ps, k < p.1 ∨ p.2 ≤ k) ∧
      c.sortOf (rmV (rmEntries zs)) = some Srt.rangeMap ∧
      hook rmRemoveAll [rmV (rmEntries ts), .set s' rs] = some (some (rmV (rmEntries zs))) := by
  obtain ⟨h1, h2⟩ := rmS_cuts (rmS_mapM_asKRange hm) hs hd
  obtain ⟨hok, hcov, hsort⟩ := canon_at h1 h2
  exact ⟨_, hok, fun k x => by rw [hcov, cuts_cov], hsort, (removeAll_raw _ _ _ _).trans
    (by rw [rmTriples_rmEntries fun t ht => (hs t ht).1, hm] <;> rfl)⟩

theorem removeAll_off {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) {rs : List GroundTerm}
    (hm : rs.mapM asKRange = none) (s' : Srt) :
    hook rmRemoveAll [rmV (rmEntries ts), .set s' rs] = some none :=
  (removeAll_raw _ _ _ _).trans (by rw [rmTriples_rmEntries hp, hm] <;> rfl)

theorem diff_raw (s s' : Srt) (m n : Entries) : hook rmDifference [.map s m, .map s' n] =
    some ((rmTriples m).bind fun ts => (rmTriples n).map fun us => rmV (rmCanon (rmDiffT ts us))) := rfl

theorem diffStep_cov {a b k : Int} {w x : GroundTerm} {ts : List RmTriple} :
    RmCov (ts.flatMap fun t => if GroundTerm.cmp t.2.2 w == .eq then rmCutOne a b t else [t]) k x ↔
      RmCov ts k x ∧ ¬ (a ≤ k ∧ k < b ∧ w = x) := by
  constructor
  · rintro ⟨y, hy, hc⟩
    obtain ⟨t, ht, hyt⟩ := List.mem_flatMap.mp hy
    have hyt : y ∈ (if GroundTerm.cmp t.2.2 w == .eq then rmCutOne a b t else [t]) := hyt
    by_cases hw : GroundTerm.cmp t.2.2 w = .eq
    · have hb : (GroundTerm.cmp t.2.2 w == .eq) = true := by simpa using hw
      simp only [hb, ↓reduceIte] at hyt
      obtain ⟨h, h'⟩ := cutOne_cov.mp ⟨y, hyt, hc⟩
      exact ⟨⟨t, ht, h⟩, fun ⟨g1, g2, _⟩ => by omega⟩
    · have hb : ¬ (GroundTerm.cmp t.2.2 w == .eq) = true := by simpa using hw
      simp only [hb] at hyt
      rw [List.mem_singleton.mp hyt] at hc
      exact ⟨⟨t, ht, hc⟩, fun ⟨_, _, g3⟩ => hw (cmp_eq_iff.mpr (hc.2.2.trans g3.symm))⟩
  · rintro ⟨⟨t, ht, h⟩, hn⟩
    by_cases hw : GroundTerm.cmp t.2.2 w = .eq
    · have hb : (GroundTerm.cmp t.2.2 w == .eq) = true := by simpa using hw
      have hkx : k < a ∨ b ≤ k := by
        have e : w = x := (cmp_eq_iff.mp hw).symm.trans h.2.2
        by_cases h1 : a ≤ k
        · by_cases h2 : k < b
          · exact absurd ⟨h1, h2, e⟩ hn
          · exact .inr (by omega)
        · exact .inl (by omega)
      obtain ⟨y, hy, hc⟩ := cutOne_cov.mpr ⟨h, hkx⟩
      refine ⟨y, List.mem_flatMap.mpr ⟨t, ht, ?_⟩, hc⟩
      show y ∈ (if GroundTerm.cmp t.2.2 w == .eq then rmCutOne a b t else [t])
      simp only [hb, ↓reduceIte]; exact hy
    · have hb : ¬ (GroundTerm.cmp t.2.2 w == .eq) = true := by simpa using hw
      refine ⟨t, List.mem_flatMap.mpr ⟨t, ht, ?_⟩, h⟩
      show t ∈ (if GroundTerm.cmp t.2.2 w == .eq then rmCutOne a b t else [t])
      simp only [hb]; exact List.mem_singleton_self _

theorem diff_cov {k : Int} {x : GroundTerm} : ∀ (us ts : List RmTriple),
    RmCov (rmDiffT ts us) k x ↔ RmCov ts k x ∧ ¬ RmCov us k x
  | [], ts => by simp [rmDiffT, rmCov_nil]
  | (a, b, w) :: us, ts => by
    show RmCov (rmDiffT (ts.flatMap fun t =>
      if GroundTerm.cmp t.2.2 w == .eq then rmCutOne a b t else [t]) us) k x ↔ _
    rw [diff_cov us, diffStep_cov, rmCov_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, fun h => h.elim (fun g => h2 g) h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun g => h2 (.inl g)⟩, fun g => h2 (.inr g)⟩

/-- "You can remove the range/value pairs in a `RangeMap` that are also present in another
`RangeMap` … only the parts of overlapping ranges whose value is the same in both range maps will
be removed" (DOM 584-588), `total` (DOM 591): the first map's keys with their values, less the keys
the second map holds with the same value. -/
theorem diff_at {c : Semantics} {ts us : List RmTriple} (hs : RmSorted c ts) (hd : ts.Pairwise rmDj)
    (hu : ∀ u ∈ us, u.1 < u.2.1) :
    ∃ zs, RmOK zs ∧ (∀ k x, RmCov zs k x ↔ RmCov ts k x ∧ ¬ RmCov us k x) ∧
      c.sortOf (rmV (rmEntries zs)) = some Srt.rangeMap ∧
      hook rmDifference [rmV (rmEntries ts), rmV (rmEntries us)] = some (some (rmV (rmEntries zs))) := by
  obtain ⟨h1, h2⟩ := rmS_diffT hu hs hd
  obtain ⟨hok, hcov, hsort⟩ := canon_at h1 h2
  exact ⟨_, hok, fun k x => by rw [hcov, diff_cov], hsort, (diff_raw _ _ _ _).trans
    (by rw [rmTriples_rmEntries fun t ht => (hs t ht).1, rmTriples_rmEntries hu] <;> rfl)⟩

theorem over_raw (s s' : Srt) (m n : Entries) : hook rmUpdateAll [.map s m, .map s' n] =
    some ((rmTriples m).bind fun ts => (rmTriples n).map fun us => rmV (rmCanon (rmOverT ts us))) := rfl

theorem over_cov {k : Int} {x : GroundTerm} : ∀ (us ts : List RmTriple), us.Pairwise rmDj →
    (RmCov (rmOverT ts us) k x ↔ RmCov us k x ∨ (RmCov ts k x ∧ ∀ u ∈ us, k < u.1 ∨ u.2.1 ≤ k))
  | [], ts, _ => by simp [rmOverT, rmCov_nil]
  | (a, b, w) :: us, ts, hd => by
    have hda : ∀ u ∈ us, b ≤ u.1 ∨ u.2.1 ≤ a := fun u hu => List.rel_of_pairwise_cons hd hu
    show RmCov (rmOverT (rmCut a b ts ++ [(a, b, w)]) us) k x ↔ _
    rw [over_cov us _ hd.of_cons, rmCov_append, cut_cov]
    constructor
    · rintro (h | ⟨(⟨h1, h2⟩ | h), h3⟩)
      · exact .inl (rmCov_cons.mpr (.inr h))
      · refine .inr ⟨h1, fun u hu => ?_⟩
        rcases List.mem_cons.mp hu with hu | hu
        · rw [hu]; exact h2
        · exact h3 u hu
      · rcases rmCov_cons.mp h with h | h
        · exact .inl (rmCov_cons.mpr (.inl h))
        · exact absurd h (rmCov_nil k x)
    · rintro (h | ⟨h1, h2⟩)
      · rcases rmCov_cons.mp h with h | h
        · refine .inr ⟨.inr (rmCov_cons.mpr (.inl h)), fun u hu => ?_⟩
          have g := hda u hu
          have g1 : a ≤ k := h.1
          have g2 : k < b := h.2.1
          omega
        · exact .inl h
      · exact .inr ⟨.inl ⟨h1, h2 (a, b, w) (List.mem_cons_self ..)⟩,
          fun u hu => h2 u (List.mem_cons_of_mem _ hu)⟩

/-- "You can update a `RangeMap` by adding all the range/value pairs in the second `RangeMap` … If
any ranges are overlapping, the value from the second range map overwrites the value in the first
for the parts where ranges are overlapping. This function is total" (DOM 596-600; 605): the second
map's keys with its values, and the first map's keys that the second does not hold. -/
theorem over_at {c : Semantics} {ts us : List RmTriple} (hs : RmSorted c ts) (hd : ts.Pairwise rmDj)
    (hus : RmSorted c us) (hud : us.Pairwise rmDj) :
    ∃ zs, RmOK zs ∧ (∀ k x, RmCov zs k x ↔ RmCov us k x ∨ (RmCov ts k x ∧ ∀ y, ¬ RmCov us k y)) ∧
      c.sortOf (rmV (rmEntries zs)) = some Srt.rangeMap ∧
      hook rmUpdateAll [rmV (rmEntries ts), rmV (rmEntries us)] = some (some (rmV (rmEntries zs))) := by
  obtain ⟨h1, h2⟩ := rmS_overT hus hs hd
  obtain ⟨hok, hcov, hsort⟩ := canon_at h1 h2
  exact ⟨_, hok, fun k x => by rw [hcov, over_cov us ts hud, out_iff], hsort, (over_raw _ _ _ _).trans
    (by rw [rmTriples_rmEntries fun t ht => (hs t ht).1, rmTriples_rmEntries fun t ht => (hus t ht).1] <;> rfl)⟩

theorem inkeys_raw (k : GroundTerm) (s : Srt) (m : Entries) : hook rmInKeys [k, .map s m] =
    some ((rmTriples m).map fun ts => bool (((asKInt k).bind fun i => rmFind i ts).isSome)) := rfl

theorem inkeys_eq {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (k : GroundTerm) :
    hook rmInKeys [k, rmV (rmEntries ts)] =
      some (some (bool (((asKInt k).bind fun i => rmFind i ts).isSome))) :=
  (inkeys_raw _ _ _).trans (by rw [rmTriples_rmEntries hp] <;> rfl)

/-- "You can check whether a key is present in a `RangeMap`" (DOM 639), `total` (DOM 643). -/
theorem inkeys_at {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (hd : ts.Pairwise rmDj)
    {k x : GroundTerm} (h : Holds ts k x) : hook rmInKeys [k, rmV (rmEntries ts)] = some (some (bool true)) := by
  obtain ⟨i, hk, t, ht, h1, h2, rfl⟩ := h
  rw [inkeys_eq hp, hk]
  show some (some (bool ((rmFind i ts).isSome))) = _
  rw [find_cov hd ht h1 h2] <;> rfl

theorem inkeys_off {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) {k : GroundTerm}
    (h : ∀ x, ¬ Holds ts k x) : hook rmInKeys [k, rmV (rmEntries ts)] = some (some (bool false)) := by
  rw [inkeys_eq hp]
  cases hk : asKInt k with
  | none => rfl
  | some i =>
    show some (some (bool ((rmFind i ts).isSome))) = _
    rw [find_none fun x hx => h x ⟨i, hk, hx⟩] <;> rfl

/-- "You can get the number of range/value pairs in a `RangeMap`" (DOM 657), `total` (DOM 660): the
number of maximal intervals (contiguous ranges of one value are one, DOM 499-500). -/
theorem size_at (ts : List RmTriple) : hook rmSize [rmV (rmEntries ts)] = some (some (int ts.length)) := by
  show some (some (int (rmEntries ts).length)) = _
  rw [rmEntries, List.length_map]

theorem keys_raw (s : Srt) (m : Entries) : hook rmKeys [.map s m] =
    some (some (.set Srt.set (m.foldr (fun (k, _) s => insertS (.inj Srt.range Srt.kitem k) s) []))) := rfl

/-- "You can get a `Set` of all the ranges in a `RangeMap`" (DOM 621), `total` (DOM 625): the
members of the result are the map's ranges, each injected into KItem. -/
theorem keys_at (ts : List RmTriple) : ∃ ms, hook rmKeys [rmV (rmEntries ts)] = some (some (.set Srt.set ms)) ∧
    ∀ e, e ∈ ms ↔ ∃ t ∈ ts, e = kr t.1 t.2.1 := by
  refine ⟨_, keys_raw _ _, fun e => ?_⟩
  have hm : ∀ (es : Entries), e ∈ es.foldr (fun (k, _) s => insertS (.inj Srt.range Srt.kitem k) s) [] ↔
      ∃ p ∈ es, e = .inj Srt.range Srt.kitem p.1 := by
    intro es
    induction es with
    | nil =>
      show e ∈ ([] : List GroundTerm) ↔ _
      constructor
      · intro h; cases h
      · rintro ⟨_, hp, _⟩; cases hp
    | cons p es ih =>
      obtain ⟨k, v⟩ := p
      show e ∈ insertS (.inj Srt.range Srt.kitem k) _ ↔ _
      rw [KCore.Set.mem_insert, ih]
      constructor
      · rintro (h | ⟨p, hp, h⟩)
        · exact ⟨(k, v), List.mem_cons_self .., h⟩
        · exact ⟨p, List.mem_cons_of_mem _ hp, h⟩
      · rintro ⟨p, hp, h⟩
        rcases List.mem_cons.mp hp with hp | hp
        · exact .inl (by rw [h, hp])
        · exact .inr ⟨p, hp, h⟩
  rw [hm]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨⟨a, b, v⟩, ht, rfl⟩ := List.mem_map.mp hp
    exact ⟨(a, b, v), ht, rfl⟩
  · rintro ⟨⟨a, b, v⟩, ht, rfl⟩
    exact ⟨(rangeT a b, v), List.mem_map.mpr ⟨(a, b, v), ht, rfl⟩, rfl⟩

theorem incl_raw (s s' : Srt) (m n : Entries) : hook rmInclusion [.map s m, .map s' n] =
    some ((rmTriples m).bind fun ts => (rmTriples n).map fun us => bool (rmIncluded ts us)) := rfl

theorem incl_eq {ts us : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (hq : ∀ u ∈ us, u.1 < u.2.1) :
    hook rmInclusion [rmV (rmEntries ts), rmV (rmEntries us)] = some (some (bool (rmIncluded ts us))) :=
  (incl_raw _ _ _ _).trans (by rw [rmTriples_rmEntries hp, rmTriples_rmEntries hq] <;> rfl)

theorem cutsT_cov {k : Int} {x : GroundTerm} : ∀ (us acc : List RmTriple),
    RmCov (us.foldl (fun acc u => rmCut u.1 u.2.1 acc) acc) k x ↔
      RmCov acc k x ∧ ∀ u ∈ us, k < u.1 ∨ u.2.1 ≤ k
  | [], acc => by simp
  | u :: us, acc => by
    show RmCov (us.foldl (fun acc u => rmCut u.1 u.2.1 acc) (rmCut u.1 u.2.1 acc)) k x ↔ _
    rw [cutsT_cov us, cut_cov]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun v hv => ?_⟩
      rcases List.mem_cons.mp hv with hv | hv
      · rw [hv]; exact h2
      · exact h3 v hv
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2 u (List.mem_cons_self ..)⟩, fun v hv => h2 v (List.mem_cons_of_mem _ hv)⟩

theorem cutsT_proper : ∀ (us acc : List RmTriple), (∀ t ∈ acc, t.1 < t.2.1) →
    ∀ t ∈ us.foldl (fun acc u => rmCut u.1 u.2.1 acc) acc, t.1 < t.2.1
  | [], _, h => h
  | u :: us, acc, _ => cutsT_proper us (rmCut u.1 u.2.1 acc) fun t ht => by
      obtain ⟨s, -, hts⟩ := List.mem_flatMap.mp ht
      exact (rmS_cutOne_mem hts).1

theorem empty_iff {l : List RmTriple} (hp : ∀ t ∈ l, t.1 < t.2.1) :
    l.isEmpty = true ↔ ∀ k x, ¬ RmCov l k x := by
  cases l with
  | nil => exact ⟨fun _ k x => rmCov_nil k x, fun _ => rfl⟩
  | cons t l =>
    refine ⟨fun h => by simp at h, fun h => ?_⟩
    exact absurd ⟨t, List.mem_cons_self .., Int.le_refl _, hp t (List.mem_cons_self ..), rfl⟩ (h t.1 t.2.2)

/-- `rmIncluded` is the inclusion of the functions: every key of the first with its value is a key
of the second with that value. -/
theorem incl_iff {ts us : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) :
    rmIncluded ts us = true ↔ ∀ k x, RmCov ts k x → RmCov us k x := by
  unfold rmIncluded
  rw [List.all_eq_true]
  have hpp : ∀ t ∈ ts, ∀ s ∈ (us.filter fun u => GroundTerm.cmp u.2.2 t.2.2 == .eq).foldl
      (fun acc u => rmCut u.1 u.2.1 acc) [t], s.1 < s.2.1 := fun t ht =>
    cutsT_proper _ [t] fun s hs => by rw [List.mem_singleton.mp hs]; exact hp t ht
  constructor
  · rintro h k x ⟨t, ht, h1, h2, rfl⟩
    have he := (empty_iff (hpp t ht)).mp (h t ht) k t.2.2
    rw [cutsT_cov] at he
    by_cases hex : ∃ u ∈ us, u.2.2 = t.2.2 ∧ u.1 ≤ k ∧ k < u.2.1
    · obtain ⟨u, hu, g1, g2, g3⟩ := hex
      exact ⟨u, hu, g2, g3, g1⟩
    · exfalso
      apply he
      refine ⟨⟨t, List.mem_singleton_self _, h1, h2, rfl⟩, fun u hu => ?_⟩
      obtain ⟨hu1, hu2⟩ := List.mem_filter.mp hu
      have hv : u.2.2 = t.2.2 := cmp_eq_iff.mp (by simpa using hu2)
      by_cases g1 : u.1 ≤ k
      · by_cases g2 : k < u.2.1
        · exact absurd ⟨u, hu1, hv, g1, g2⟩ hex
        · exact .inr (by omega)
      · exact .inl (by omega)
  · intro h t ht
    refine (empty_iff (hpp t ht)).mpr fun k x hc => ?_
    rw [cutsT_cov] at hc
    obtain ⟨⟨s, hs, h1, h2, h3⟩, hout⟩ := hc
    rw [List.mem_singleton.mp hs] at h1 h2 h3
    obtain ⟨u, hu, g1, g2, g3⟩ := h k x ⟨t, ht, h1, h2, h3⟩
    have hf : u ∈ us.filter fun u => GroundTerm.cmp u.2.2 t.2.2 == .eq :=
      List.mem_filter.mpr ⟨hu, by simpa using cmp_eq_iff.mpr (g3.trans h3.symm)⟩
    have := hout u hf
    omega

/-- "Only keys within equal or overlapping ranges that are bound to the same value are considered
equal" (DOM 667-668), `total` (DOM 671): `true` where every key of the first map is a key of the
second with the same value (the header's reading at two equal maps). -/
theorem incl_at {ts us : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (hq : ∀ u ∈ us, u.1 < u.2.1)
    (h : ∀ k x, RmCov ts k x → RmCov us k x) :
    hook rmInclusion [rmV (rmEntries ts), rmV (rmEntries us)] = some (some (bool true)) := by
  rw [incl_eq hp hq, (incl_iff hp).mpr h]

theorem incl_off {ts us : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) (hq : ∀ u ∈ us, u.1 < u.2.1)
    (h : ¬ ∀ k x, RmCov ts k x → RmCov us k x) :
    hook rmInclusion [rmV (rmEntries ts), rmV (rmEntries us)] = some (some (bool false)) := by
  rw [incl_eq hp hq]
  cases hb : rmIncluded ts us with
  | false => rfl
  | true => exact absurd ((incl_iff hp).mp hb) h

/-- A map is included in itself: the reading taken at two equal maps ("strict subset", DOM 665,
would give `false`). -/
theorem incl_refl {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1) :
    hook rmInclusion [rmV (rmEntries ts), rmV (rmEntries ts)] = some (some (bool true)) :=
  incl_at hp hp fun _ _ h => h

/-! ## Statement 1: in-domain values, derived from the prose -/

/-- An argument or a result of a point: a KItem that is an Int (`kint n`), an Int, a Bool, a range
`[a, b)`, a range injected into KItem, a range map by its entries `(a, b, n)` (the range `[a, b)`
with the value `kint n`), a Set of injected ranges, a Set of injected integers. -/
inductive A where
  | k (n : Int)
  | i (n : Int)
  | b (x : Bool)
  | r (a b : Int)
  | kr (a b : Int)
  | rm (l : List (Int × Int × Int))
  | sr (l : List (Int × Int))
  | sk (l : List Int)

def A.val : A → GroundTerm
  | .k n => kint n
  | .i n => int n
  | .b x => bool x
  | .r x y => rangeT x y
  | .kr x y => HooksRangeMapTest.kr x y
  | .rm l => rmV (l.map fun e => (rangeT e.1 e.2.1, kint e.2.2))
  | .sr l => .set Srt.set (l.map fun p => HooksRangeMapTest.kr p.1 p.2)
  | .sk l => .set Srt.set (l.map kint)

def A.srt : A → Srt
  | .k _ => Srt.kitem
  | .i _ => Srt.int
  | .b _ => Srt.bool
  | .r _ _ => Srt.range
  | .kr _ _ => Srt.kitem
  | .rm _ => Srt.rangeMap
  | .sr _ => Srt.set
  | .sk _ => Srt.set

/-- A range map is written by its maximal intervals in order, a Set with its members increasing,
as a value has them. -/
def A.ok : A → Bool
  | .rm l => rangesOK (l.map fun e => (rangeT e.1 e.2.1, kint e.2.2))
  | .sr l => elemsSorted (l.map fun p => HooksRangeMapTest.kr p.1 p.2)
  | .sk l => elemsSorted (l.map kint)
  | _ => true

/-- Such a term is a value of its sort, in every semantics with `RangeIn`. -/
theorem A.sorted {c : Semantics} (hI : RangeIn c) : ∀ a : A, a.ok = true → c.sortOf a.val = some a.srt
  | .k n, _ => ki_value hI n
  | .i n, _ => int_value c n
  | .b x, _ => bool_value c x
  | .r x y, _ => range_value hI x y
  | .kr x y, _ => kr_value hI x y
  | .rm l, h => (rmS_sortOf_map collOf_rangeMap).mpr ⟨rfl, h, fun e he => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
      exact ⟨range_value hI _ _, ki_value hI _⟩⟩
  | .sr l, h => sortOf_setS.mpr ⟨_, collOf_set, rfl, h, fun e he => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
      exact kr_value hI _ _, rfl⟩
  | .sk l, h => sortOf_setS.mpr ⟨_, collOf_set, rfl, h, fun e he => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
      exact ki_value hI x, rfl⟩

theorem A.sortsOf {c : Semantics} (hI : RangeIn c) : ∀ xs : List A, xs.all A.ok = true →
    c.sortsOf (xs.map A.val) = some (xs.map A.srt)
  | [], _ => by simp [Semantics.sortsOf]
  | a :: xs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [Semantics.sortsOf, A.sorted hI a h.1, A.sortsOf hI xs h.2]

/-- A point: the operation, its hook name, its arguments and a value (the expected one, or at a
point of statement 2 a value of the result sort). -/
structure Pt where
  f : Sym
  name : String
  xs : List A
  v : A

/-- The expected values, each derived by hand from the cited sentence. `n` is the KItem `kint n`;
`{[0,3) ↦ 7, [5,7) ↦ 8}` is the map whose keys 0, 1, 2 have the value 7 and 5, 6 the value 8
("bounded inclusively below and exclusively above", DOM 488, 498-499), called `M` here.
- `.RangeMap`: "The `RangeMap` with zero elements" (DOM 513): no range.
- `[0,3) r|-> 7`: "The range of keys is on the left, and the value is on the right" (DOM 521-522):
  `{[0,3) ↦ 7}`.
- `_RangeMap_`: "a new `RangeMap` consisting of range/value pairs of two RangeMaps" (DOM 502-503):
  of `{[0,3) ↦ 7}` and `{[5,7) ↦ 8}`, `M`, in either order (`comm`, DOM 508); of `{[0,3) ↦ 7}` and
  `{[3,5) ↦ 7}`, `{[0,5) ↦ 7}` (no key in both, 3 being outside the first; "Contiguous … ranges
  that map to the same value are merged into a single range", DOM 499-500); of `{[0,3) ↦ 7}` and
  `{[3,5) ↦ 8}`, the two ranges (different values are not merged); of `.RangeMap` and `M`, `M`
  (`unit(.RangeMap)`, DOM 508).
- lookup (DOM 533): `M[0]` is 7 (0 is in `[0,3)`, inclusive below); `M[2]` is 7; `M[5]` is 8;
  `M[6]` is 8.
- lookup with default (DOM 543-545): `M[1] orDefault 9` is 7; `M[3] orDefault 9` is 9 (3 is outside
  `[0,3)`, exclusive above, and below 5); `M[4] orDefault 9` is 9; `M[ [0,3) ] orDefault 9` is 9
  (the KItem `[0,3)` is no Int, so no key: DOM 471-477).
- `find_range` (DOM 554): `find_range(M, 1)` is `[0,3)`; `find_range(M, 5)` is `[5,7)`;
  `find_range({[0,5) ↦ 7}, 4)` is `[0,5)`.
- update (DOM 564-566, the header's reading): `{[0,10) ↦ 7}[ [3,5) <- 8 ]` is
  `{[0,3) ↦ 7, [3,5) ↦ 8, [5,10) ↦ 7}`; `M[ [3,5) <- 7 ]` is `{[0,5) ↦ 7, [5,7) ↦ 8}` (the inserted
  range is contiguous with `[0,3)` of the same value: merged, DOM 499-500);
  `.RangeMap[ [1,2) <- 3 ]` is `{[1,2) ↦ 3}`; `M[ [0,7) <- 9 ]` is `{[0,7) ↦ 9}`.
- delete, a part of the range present (DOM 575-576): `{[0,10) ↦ 7}[ [3,5) <- undef ]` is
  `{[0,3) ↦ 7, [5,10) ↦ 7}`; `M[ [0,3) <- undef ]` is `{[5,7) ↦ 8}`; `M[ [2,6) <- undef ]` is
  `{[0,2) ↦ 7, [6,7) ↦ 8}` (the parts `[2,3)` and `[5,6)` are present and go).
- difference (DOM 584-588): `{[0,10) ↦ 7} -RangeMap {[3,5) ↦ 7}` is `{[0,3) ↦ 7, [5,10) ↦ 7}`;
  `{[0,10) ↦ 7} -RangeMap {[3,5) ↦ 8}` is `{[0,10) ↦ 7}` ("only the parts of overlapping ranges
  whose value is the same in both range maps will be removed"); `M -RangeMap M` is `.RangeMap`;
  `M -RangeMap .RangeMap` is `M`.
- `updateRangeMap` (DOM 596-600): of `{[0,10) ↦ 7}` and `{[3,5) ↦ 8}`,
  `{[0,3) ↦ 7, [3,5) ↦ 8, [5,10) ↦ 7}`; of `M` and `{[2,6) ↦ 9}`,
  `{[0,2) ↦ 7, [2,6) ↦ 9, [6,7) ↦ 8}`; of `.RangeMap` and `M`, `M`.
- `removeAll` (DOM 610-613): `removeAll({[0,10) ↦ 7}, {[1,2), [3,5)})` is
  `{[0,1) ↦ 7, [2,3) ↦ 7, [5,10) ↦ 7}`; `removeAll(M, .Set)` is `M` (no range is named).
- `keys` (DOM 621): of `M`, the Set of `[0,3)` and `[5,7)`; of `.RangeMap`, `.Set`.
- `in_keys` (DOM 639): 2 in `M`, true; 3 in `M`, false (exclusive above); 5 in `M`, true; the KItem
  `[0,3)` in `M`, false (no Int, DOM 471-477).
- `size` (DOM 657): of `M`, 2; of `.RangeMap`, 0; of `{[0,5) ↦ 7}`, 1.
- `<=RangeMap` (DOM 665-668), at two different maps only: `{[0,2) ↦ 7} <=RangeMap M` is true (the
  keys 0, 1 are keys of `M` with the value 7, "within … overlapping ranges that are bound to the
  same value"); `{[0,4) ↦ 7} <=RangeMap M` is false (3 is no key of `M`);
  `{[0,2) ↦ 8} <=RangeMap M` is false (another value); `.RangeMap <=RangeMap M` is true;
  `M <=RangeMap {[0,2) ↦ 7}` is false. -/
def vals : List Pt :=
  [⟨rmUnit, "RANGEMAP.unit", [], .rm []⟩,
   ⟨rmElem, "RANGEMAP.elementRng", [.r 0 3, .k 7], .rm [(0, 3, 7)]⟩,
   ⟨rmConcat, "RANGEMAP.concat", [.rm [(0, 3, 7)], .rm [(5, 7, 8)]], .rm [(0, 3, 7), (5, 7, 8)]⟩,
   ⟨rmConcat, "RANGEMAP.concat", [.rm [(5, 7, 8)], .rm [(0, 3, 7)]], .rm [(0, 3, 7), (5, 7, 8)]⟩,
   ⟨rmConcat, "RANGEMAP.concat", [.rm [(0, 3, 7)], .rm [(3, 5, 7)]], .rm [(0, 5, 7)]⟩,
   ⟨rmConcat, "RANGEMAP.concat", [.rm [(0, 3, 7)], .rm [(3, 5, 8)]], .rm [(0, 3, 7), (3, 5, 8)]⟩,
   ⟨rmConcat, "RANGEMAP.concat", [.rm [], .rm [(0, 3, 7), (5, 7, 8)]], .rm [(0, 3, 7), (5, 7, 8)]⟩,
   ⟨rmLookup, "RANGEMAP.lookup", [.rm [(0, 3, 7), (5, 7, 8)], .k 0], .k 7⟩,
   ⟨rmLookup, "RANGEMAP.lookup", [.rm [(0, 3, 7), (5, 7, 8)], .k 2], .k 7⟩,
   ⟨rmLookup, "RANGEMAP.lookup", [.rm [(0, 3, 7), (5, 7, 8)], .k 5], .k 8⟩,
   ⟨rmLookup, "RANGEMAP.lookup", [.rm [(0, 3, 7), (5, 7, 8)], .k 6], .k 8⟩,
   ⟨rmLookupOrDefault, "RANGEMAP.lookupOrDefault", [.rm [(0, 3, 7), (5, 7, 8)], .k 1, .k 9], .k 7⟩,
   ⟨rmLookupOrDefault, "RANGEMAP.lookupOrDefault", [.rm [(0, 3, 7), (5, 7, 8)], .k 3, .k 9], .k 9⟩,
   ⟨rmLookupOrDefault, "RANGEMAP.lookupOrDefault", [.rm [(0, 3, 7), (5, 7, 8)], .k 4, .k 9], .k 9⟩,
   ⟨rmLookupOrDefault, "RANGEMAP.lookupOrDefault", [.rm [(0, 3, 7), (5, 7, 8)], .kr 0 3, .k 9], .k 9⟩,
   ⟨rmFindRange, "RANGEMAP.find_range", [.rm [(0, 3, 7), (5, 7, 8)], .k 1], .r 0 3⟩,
   ⟨rmFindRange, "RANGEMAP.find_range", [.rm [(0, 3, 7), (5, 7, 8)], .k 5], .r 5 7⟩,
   ⟨rmFindRange, "RANGEMAP.find_range", [.rm [(0, 5, 7)], .k 4], .r 0 5⟩,
   ⟨rmUpdate, "RANGEMAP.updateRng", [.rm [(0, 10, 7)], .r 3 5, .k 8], .rm [(0, 3, 7), (3, 5, 8), (5, 10, 7)]⟩,
   ⟨rmUpdate, "RANGEMAP.updateRng", [.rm [(0, 3, 7), (5, 7, 8)], .r 3 5, .k 7], .rm [(0, 5, 7), (5, 7, 8)]⟩,
   ⟨rmUpdate, "RANGEMAP.updateRng", [.rm [], .r 1 2, .k 3], .rm [(1, 2, 3)]⟩,
   ⟨rmUpdate, "RANGEMAP.updateRng", [.rm [(0, 3, 7), (5, 7, 8)], .r 0 7, .k 9], .rm [(0, 7, 9)]⟩,
   ⟨rmRemove, "RANGEMAP.removeRng", [.rm [(0, 10, 7)], .r 3 5], .rm [(0, 3, 7), (5, 10, 7)]⟩,
   ⟨rmRemove, "RANGEMAP.removeRng", [.rm [(0, 3, 7), (5, 7, 8)], .r 0 3], .rm [(5, 7, 8)]⟩,
   ⟨rmRemove, "RANGEMAP.removeRng", [.rm [(0, 3, 7), (5, 7, 8)], .r 2 6], .rm [(0, 2, 7), (6, 7, 8)]⟩,
   ⟨rmDifference, "RANGEMAP.difference", [.rm [(0, 10, 7)], .rm [(3, 5, 7)]], .rm [(0, 3, 7), (5, 10, 7)]⟩,
   ⟨rmDifference, "RANGEMAP.difference", [.rm [(0, 10, 7)], .rm [(3, 5, 8)]], .rm [(0, 10, 7)]⟩,
   ⟨rmDifference, "RANGEMAP.difference", [.rm [(0, 3, 7), (5, 7, 8)], .rm [(0, 3, 7), (5, 7, 8)]], .rm []⟩,
   ⟨rmDifference, "RANGEMAP.difference", [.rm [(0, 3, 7), (5, 7, 8)], .rm []], .rm [(0, 3, 7), (5, 7, 8)]⟩,
   ⟨rmUpdateAll, "RANGEMAP.updateAll", [.rm [(0, 10, 7)], .rm [(3, 5, 8)]], .rm [(0, 3, 7), (3, 5, 8), (5, 10, 7)]⟩,
   ⟨rmUpdateAll, "RANGEMAP.updateAll", [.rm [(0, 3, 7), (5, 7, 8)], .rm [(2, 6, 9)]],
     .rm [(0, 2, 7), (2, 6, 9), (6, 7, 8)]⟩,
   ⟨rmUpdateAll, "RANGEMAP.updateAll", [.rm [], .rm [(0, 3, 7), (5, 7, 8)]], .rm [(0, 3, 7), (5, 7, 8)]⟩,
   ⟨rmRemoveAll, "RANGEMAP.removeAll", [.rm [(0, 10, 7)], .sr [(1, 2), (3, 5)]],
     .rm [(0, 1, 7), (2, 3, 7), (5, 10, 7)]⟩,
   ⟨rmRemoveAll, "RANGEMAP.removeAll", [.rm [(0, 3, 7), (5, 7, 8)], .sr []], .rm [(0, 3, 7), (5, 7, 8)]⟩,
   ⟨rmKeys, "RANGEMAP.keys", [.rm [(0, 3, 7), (5, 7, 8)]], .sr [(0, 3), (5, 7)]⟩,
   ⟨rmKeys, "RANGEMAP.keys", [.rm []], .sr []⟩,
   ⟨rmInKeys, "RANGEMAP.in_keys", [.k 2, .rm [(0, 3, 7), (5, 7, 8)]], .b true⟩,
   ⟨rmInKeys, "RANGEMAP.in_keys", [.k 3, .rm [(0, 3, 7), (5, 7, 8)]], .b false⟩,
   ⟨rmInKeys, "RANGEMAP.in_keys", [.k 5, .rm [(0, 3, 7), (5, 7, 8)]], .b true⟩,
   ⟨rmInKeys, "RANGEMAP.in_keys", [.kr 0 3, .rm [(0, 3, 7), (5, 7, 8)]], .b false⟩,
   ⟨rmSize, "RANGEMAP.size", [.rm [(0, 3, 7), (5, 7, 8)]], .i 2⟩,
   ⟨rmSize, "RANGEMAP.size", [.rm []], .i 0⟩,
   ⟨rmSize, "RANGEMAP.size", [.rm [(0, 5, 7)]], .i 1⟩,
   ⟨rmInclusion, "RANGEMAP.inclusion", [.rm [(0, 2, 7)], .rm [(0, 3, 7), (5, 7, 8)]], .b true⟩,
   ⟨rmInclusion, "RANGEMAP.inclusion", [.rm [(0, 4, 7)], .rm [(0, 3, 7), (5, 7, 8)]], .b false⟩,
   ⟨rmInclusion, "RANGEMAP.inclusion", [.rm [(0, 2, 8)], .rm [(0, 3, 7), (5, 7, 8)]], .b false⟩,
   ⟨rmInclusion, "RANGEMAP.inclusion", [.rm [], .rm [(0, 3, 7), (5, 7, 8)]], .b true⟩,
   ⟨rmInclusion, "RANGEMAP.inclusion", [.rm [(0, 3, 7), (5, 7, 8)], .rm [(0, 2, 7)]], .b false⟩]

/-- Points of the header's second finding, kept apart from `vals`: a proper range no part of which
is in the map. Reading A (the library's): the map. `M[ [10,12) <- undef ]`,
`M[ [3,5) <- undef ]` (the gap between the two ranges), `.RangeMap[ [0,1) <- undef ]`,
`removeAll(M, {[10,12)})`, `removeAll(M, {[3,5), [10,12)})`. -/
def absents : List Pt :=
  [⟨rmRemove, "RANGEMAP.removeRng", [.rm [(0, 3, 7), (5, 7, 8)], .r 10 12], .rm [(0, 3, 7), (5, 7, 8)]⟩,
   ⟨rmRemove, "RANGEMAP.removeRng", [.rm [(0, 3, 7), (5, 7, 8)], .r 3 5], .rm [(0, 3, 7), (5, 7, 8)]⟩,
   ⟨rmRemove, "RANGEMAP.removeRng", [.rm [], .r 0 1], .rm []⟩,
   ⟨rmRemoveAll, "RANGEMAP.removeAll", [.rm [(0, 3, 7), (5, 7, 8)], .sr [(10, 12)]], .rm [(0, 3, 7), (5, 7, 8)]⟩,
   ⟨rmRemoveAll, "RANGEMAP.removeAll", [.rm [(0, 3, 7), (5, 7, 8)], .sr [(3, 5), (10, 12)]],
     .rm [(0, 3, 7), (5, 7, 8)]⟩]

/-- `hook`'s value at each point of a list is the point's. -/
def hookOK (ps : List Pt) : Bool := ps.all fun p => hook p.f (p.xs.map A.val) == some (some p.v.val)

/-- The arguments of each point are written as values of the signature's argument sorts, and the
expected value as one of its result sort; the point is of a row. -/
def sigOK (ps : List Pt) : Bool := ps.all fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
  (sig p.f).args == p.xs.map A.srt && p.xs.all A.ok && p.v.ok && (sig p.f).result == p.v.srt &&
  rmRows.contains (p.f, p.name)

/-- Every row has a point. -/
theorem vals_rows : rmRows.all (fun r => vals.any fun p => p.f == r.1 && p.name == r.2) = true := by
  decide +kernel

/-- **`hook`'s value at each point is the one derived from the prose.** -/
theorem vals_hook : hookOK vals = true := by decide +kernel

theorem vals_sig : sigOK vals = true := by decide +kernel

/-- The points of `absents`: `hook` gives the map unchanged (reading A of the second finding). -/
theorem absents_hook : hookOK absents = true := by decide +kernel

theorem absents_sig : sigOK absents = true := by decide +kernel

/-- No part of the range (of any range of the Set) is in the map, at each point of `absents`; a
part of every range is, at each point of `vals` of the two operations (the empty Set aside). -/
theorem absents_regions :
    (absents.all (fun p => match p.xs with
      | [.rm l, .r a b] => p.f == rmRemove && decide (a < b) &&
          l.all (fun e => decide (e.2.1 ≤ a) || decide (b ≤ e.1))
      | [.rm l, .sr rs] => p.f == rmRemoveAll && rs.any (fun q => decide (q.1 < q.2) &&
          l.all (fun e => decide (e.2.1 ≤ q.1) || decide (q.2 ≤ e.1)))
      | _ => false) &&
    vals.all (fun p => match p.xs with
      | [.rm l, .r a b] => p.f != rmRemove || (decide (a < b) &&
          l.any (fun e => decide (a < e.2.1) && decide (e.1 < b)))
      | [.rm l, .sr rs] => p.f != rmRemoveAll || rs.all (fun q => decide (q.1 < q.2) &&
          l.any (fun e => decide (q.1 < e.2.1) && decide (e.1 < q.2)))
      | _ => true)) = true := by
  decide +kernel

/-- At each point of such a list the result is the point's value, under every interpretation, in
every semantics. -/
theorem pts_hookRes {ps : List Pt} (h : hookOK ps = true) : ∀ p ∈ ps, ∀ (c : Semantics) (H : HookParams),
    (c.withHooks H).hookRes p.f (p.xs.map A.val) = some (some p.v.val) :=
  fun p hp _ _ => Semantics.hookRes_of_value (by simpa using List.all_eq_true.mp h p hp)

/-- At each point of such a list Γ states the point's value, in every semantics with `RangeIn`:
there the arguments are values of the signature's sorts and the value one of the result sort. -/
theorem pts_gamma {ps : List Pt} (h1 : hookOK ps = true) (h2 : sigOK ps = true) : ∀ p ∈ ps,
    ∀ (c : Semantics), RangeIn c →
    c.sortsOf (p.xs.map A.val) = some (sig p.f).args ∧ c.sortOf p.v.val = some (sig p.f).result ∧
    Γ c (appP c (sig p.f) (p.xs.map A.val) ≡ den c p.v.val) := by
  intro p hp c hI
  have h := List.all_eq_true.mp h2 p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hk, hname⟩, hargs⟩, hok⟩, hvok⟩, hres⟩, -⟩ := h
  have hh : hook p.f (p.xs.map A.val) = some (some p.v.val) := by
    simpa using List.all_eq_true.mp h1 p hp
  have hvs : c.sortsOf (p.xs.map A.val) = some (sig p.f).args := by
    rw [hargs]; exact A.sortsOf hI _ hok
  exact ⟨hvs, by rw [hres]; exact A.sorted hI _ hvok, gamma_val _ hk hvs (by rw [hname]; exact hh)⟩

/-- **At each point the result is that value, under every interpretation, in every semantics**
(also at the points of the six keys of `silentTable`: the interpretation is read only where `hook`
gives no value). -/
theorem vals_hookRes : ∀ p ∈ vals, ∀ (c : Semantics) (H : HookParams),
    (c.withHooks H).hookRes p.f (p.xs.map A.val) = some (some p.v.val) := pts_hookRes vals_hook

/-- **At each point Γ states that value**, in every semantics with `RangeIn`. -/
theorem vals_gamma : ∀ p ∈ vals, ∀ (c : Semantics), RangeIn c →
    c.sortsOf (p.xs.map A.val) = some (sig p.f).args ∧ c.sortOf p.v.val = some (sig p.f).result ∧
    Γ c (appP c (sig p.f) (p.xs.map A.val) ≡ den c p.v.val) := pts_gamma vals_hook vals_sig

/-- **… under every interpretation** (`c.withHooks H` is a semantics with `RangeIn` where `c` is
one whose parameters are not raw). -/
theorem vals_gamma_H : ∀ p ∈ vals, ∀ (c : Semantics), RangeIn c → (∀ k ∈ c.params, k.raw = false) →
    ∀ H : HookParams,
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map A.val) ≡ den (c.withHooks H) p.v.val) :=
  fun p hp _ hI hr H => (vals_gamma p hp _ (hI.withHooks hr H)).2.2

/-- The same at the points of `absents` (reading A of the second finding): under every
interpretation the result is the map, and Γ states it. -/
theorem absents_hookRes : ∀ p ∈ absents, ∀ (c : Semantics) (H : HookParams),
    (c.withHooks H).hookRes p.f (p.xs.map A.val) = some (some p.v.val) := pts_hookRes absents_hook

theorem absents_gamma_H : ∀ p ∈ absents, ∀ (c : Semantics), RangeIn c → (∀ k ∈ c.params, k.raw = false) →
    ∀ H : HookParams,
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map A.val) ≡ den (c.withHooks H) p.v.val) :=
  fun p hp _ hI hr H => (pts_gamma absents_hook absents_sig p hp _ (hI.withHooks hr H)).2.2

/-! ## `_RangeMap_` at two maps with a key in common (the header's first finding) -/

/-- `_RangeMap_` is no key of `silentTable`: no point of it is silent. -/
theorem concat_not_silent (vs : List GroundTerm) : silent rmConcat vs = false :=
  silent_of_not_silentKey (by decide +kernel) vs

/-- **Γ of every semantics states ⊥ at two range maps with a key in common** (reading A; DOM
600-602, "a partial function only defined on range maps with non overlapping ranges"). -/
theorem concat_common_gamma (c : Semantics) {ts us : List RmTriple} (ht : RmOK ts) (hu : RmOK us)
    (hvs : c.sortsOf [rmV (rmEntries ts), rmV (rmEntries us)] = some [Srt.rangeMap, Srt.rangeMap])
    (h : ¬ RmApart ts us) :
    Γ c (appP c ⟨rmConcat, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩
      [rmV (rmEntries ts), rmV (rmEntries us)] ≡ ⊥) :=
  gamma_bot c (k := ⟨rmConcat, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩) (by decide +kernel) hvs
    (concat_off ht hu h) (concat_not_silent _)

/-- Points of that region (the value is unused): `{[0,3) ↦ 7} {[2,5) ↦ 8}` (the key 2 in both),
`{[0,3) ↦ 7} {[2,5) ↦ 7}` (the same with one value: the second reading of the finding), `M M`,
`M {[6,9) ↦ 7}`. -/
def overlaps : List Pt :=
  [⟨rmConcat, "RANGEMAP.concat", [.rm [(0, 3, 7)], .rm [(2, 5, 8)]], .rm []⟩,
   ⟨rmConcat, "RANGEMAP.concat", [.rm [(0, 3, 7)], .rm [(2, 5, 7)]], .rm []⟩,
   ⟨rmConcat, "RANGEMAP.concat", [.rm [(0, 3, 7), (5, 7, 8)], .rm [(0, 3, 7), (5, 7, 8)]], .rm []⟩,
   ⟨rmConcat, "RANGEMAP.concat", [.rm [(0, 3, 7), (5, 7, 8)], .rm [(6, 9, 7)]], .rm []⟩]

theorem overlaps_ok : overlaps.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.xs.map A.srt && p.xs.all A.ok && partials.contains p.f &&
    hook p.f (p.xs.map A.val) == some none && !silent p.f (p.xs.map A.val)) = true := by
  decide +kernel

/-- Each point holds a key of both maps. -/
theorem overlaps_regions : overlaps.all (fun p => match p.xs with
    | [.rm l, .rm l'] => l.any fun e => l'.any fun e' => decide (e.1 < e'.2.1) && decide (e'.1 < e.2.1)
    | _ => false) = true := by
  decide +kernel

/-- **At each, Γ states ⊥**, in every semantics with `RangeIn`. -/
theorem overlaps_gamma : ∀ p ∈ overlaps, ∀ (c : Semantics), RangeIn c →
    Γ c (appP c (sig p.f) (p.xs.map A.val) ≡ ⊥) := by
  intro p hp c hI
  have h := List.all_eq_true.mp overlaps_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hk, hname⟩, hargs⟩, hok⟩, -⟩, hh⟩, hsl⟩ := h
  exact gamma_bot _ hk (by rw [hargs]; exact A.sortsOf hI _ hok)
    (by rw [hname]; exact hh) (by rw [hname]; exact hsl)

/-- **So today no interpretation gives these points a value**: over all H, Γ entails ⊥ there, the
negation of the first half of the `param_undetermined` shape. Under reading B of the finding
(`rmConcat` a key of `silentTable`) this would not hold. -/
theorem overlaps_entails : ∀ p ∈ overlaps, ∀ (c : Semantics), RangeIn c → (∀ k ∈ c.params, k.raw = false) →
    ∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig p.f) (p.xs.map A.val) ≡ ⊥) := by
  intro p hp c hI hr H M _ I hI'
  exact hI' _ (overlaps_gamma p hp _ (hI.withHooks hr H))

/-! ## Statement 3: the silent predicate against the prose's regions -/

/-- **The eight `total` rows are no key of `silentTable`: no point of theirs is silent.** -/
theorem total_not_silent : ∀ f ∈ totals, ∀ vs : List GroundTerm, silent f vs = false :=
  fun f hf vs => silent_of_not_silentKey
    ((by decide +kernel : ∀ f ∈ totals, silentKey f = false) f hf) vs

/-- The predicate of the six keys is `fun _ => true`: it is `hook` giving no value that makes a
point one where the interpretation is read. -/
theorem silents_silent : ∀ f ∈ silents, ∀ vs : List GroundTerm, silent f vs = true := by
  intro f hf vs
  simp only [silents, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Where `hook` gives no value at a silent point, the result is the interpretation's. -/
theorem off_hookRes (c : Semantics) (H : HookParams) {f : Sym} {vs : List GroundTerm}
    (he : hook f vs = some none) (hs : silent f vs = true) :
    (c.withHooks H).hookRes f vs = some ((c.withHooks H).fallback f vs) :=
  Semantics.hookRes_of_silent he hs

/-- **The eight operations declared `total` have a value at every argument list of their
signature** (the library's `hook_total`), the one `*_at` describes. -/
theorem covered_total {c : Semantics} (hs : c.shapesOK = true) : ∀ f ∈ totals,
    ∀ vs : List GroundTerm, c.sortsOf vs = some (sig f).args → ∃ v, hook f vs = some (some v) := by
  intro f hf vs hvs
  have h := (by decide +kernel : ∀ f ∈ totals, sig f ∈ hookSigs ∧ (sig f).name = f ∧
    partialHooks.contains (sig f).name = false) f hf
  obtain ⟨v, hv⟩ := hook_total hs (sig f) h.1 h.2.2 vs hvs
  rw [h.2.1] at hv
  exact ⟨v, hv⟩

/-- **`r|->` at every argument list of its signature**: at a proper Int range the one-range map,
and everywhere else `hook` gives none and the point is silent: the silent region is the region the
prose does not speak of. -/
theorem covered_elem {c : Semantics} {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.range, Srt.kitem]) :
    ∃ r v, vs = [r, v] ∧
      (∀ a b, r = rangeT a b → a < b → hook rmElem vs = some (some (rmV (rmEntries [(a, b, v)])))) ∧
      ((¬ ∃ a b, r = rangeT a b ∧ a < b) → hook rmElem vs = some none ∧ silent rmElem vs = true) := by
  obtain ⟨r, v, rfl, -, -⟩ := sortsOf_two hvs
  refine ⟨r, v, rfl, fun a b hr hab => by subst hr; exact elem_at hab v, fun h => ⟨elem_off ?_ v, rfl⟩⟩
  cases hr : asRange r with
  | none => rfl
  | some p =>
    obtain ⟨a, b⟩ := p
    exact absurd ⟨a, b, asRange_some hr⟩ h

/-- **`M[K]` at every argument list of its signature**: at a key of the map its value, and
everywhere else (a key in no range of the map; a KItem that is no Int) `hook` gives none and the
point is silent. -/
theorem covered_lookup {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.rangeMap, Srt.kitem]) :
    ∃ ts k, vs = [rmV (rmEntries ts), k] ∧ RmOK ts ∧
      (∀ x, Holds ts k x → hook rmLookup vs = some (some x)) ∧
      ((∀ x, ¬ Holds ts k x) → hook rmLookup vs = some none ∧ silent rmLookup vs = true) := by
  obtain ⟨w, k, rfl, h₁, -⟩ := sortsOf_two hvs
  obtain ⟨ts, rfl, hok, -⟩ := rm_only hs h₁
  exact ⟨ts, k, rfl, hok, fun x h => lookup_at (rmOK_proper hok) (rmOK_pairwise hok) h,
    fun h => ⟨lookup_off (rmOK_proper hok) h, rfl⟩⟩

/-- **`find_range(M, K)` at every argument list of its signature**: at an Int key that a range of
the map holds, that range, and everywhere else `hook` gives none and the point is silent. -/
theorem covered_find {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.rangeMap, Srt.kitem]) :
    ∃ ts k, vs = [rmV (rmEntries ts), k] ∧ RmOK ts ∧
      (∀ i a b v, asKInt k = some i → (a, b, v) ∈ ts → a ≤ i → i < b →
        hook rmFindRange vs = some (some (rangeT a b))) ∧
      ((∀ x, ¬ Holds ts k x) → hook rmFindRange vs = some none ∧ silent rmFindRange vs = true) := by
  obtain ⟨w, k, rfl, h₁, -⟩ := sortsOf_two hvs
  obtain ⟨ts, rfl, hok, -⟩ := rm_only hs h₁
  exact ⟨ts, k, rfl, hok,
    fun i a b v hk ht h1 h2 => findr_at (rmOK_proper hok) (rmOK_pairwise hok) hk ht h1 h2,
    fun h => ⟨findr_off (rmOK_proper hok) h, rfl⟩⟩

/-- **`M[R <- V]` at every argument list of its signature**: at a proper Int range the map with
the inserted pair over it, a value of sort RangeMap, and everywhere else `hook` gives none and the
point is silent. -/
theorem covered_update {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.rangeMap, Srt.range, Srt.kitem]) :
    ∃ ts r v, vs = [rmV (rmEntries ts), r, v] ∧ RmOK ts ∧
      (∀ a b, r = rangeT a b → a < b → ∃ zs, RmOK zs ∧
        (∀ k x, RmCov zs k x ↔ (a ≤ k ∧ k < b ∧ v = x) ∨ (RmCov ts k x ∧ (k < a ∨ b ≤ k))) ∧
        c.sortOf (rmV (rmEntries zs)) = some Srt.rangeMap ∧
        hook rmUpdate vs = some (some (rmV (rmEntries zs)))) ∧
      ((¬ ∃ a b, r = rangeT a b ∧ a < b) → hook rmUpdate vs = some none ∧ silent rmUpdate vs = true) := by
  obtain ⟨w, r, v, rfl, h₁, h₂, h₃⟩ := sortsOf_three hvs
  obtain ⟨ts, rfl, hok, hst⟩ := rm_only hs h₁
  refine ⟨ts, r, v, rfl, hok, fun a b hr hab => by subst hr; exact update_at hst (rmOK_pairwise hok) hab h₂ h₃,
    fun h => ⟨update_off (rmOK_proper hok) ?_ v, rfl⟩⟩
  cases hr : asRange r with
  | none => rfl
  | some p =>
    obtain ⟨a, b⟩ := p
    exact absurd ⟨a, b, asRange_some hr⟩ h

/-- **`M[R <- undef]` at every argument list of its signature**: at a proper Int range the map's
keys outside the range (at one no key of which is in the map, the map: reading A of the second
finding; reading B has that part unstated), and at every other range `hook` gives none and the
point is silent. -/
theorem covered_remove {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.rangeMap, Srt.range]) :
    ∃ ts r, vs = [rmV (rmEntries ts), r] ∧ RmOK ts ∧
      (∀ a b, r = rangeT a b → a < b → ∃ zs, RmOK zs ∧
        (∀ k x, RmCov zs k x ↔ RmCov ts k x ∧ (k < a ∨ b ≤ k)) ∧
        c.sortOf (rmV (rmEntries zs)) = some Srt.rangeMap ∧
        hook rmRemove vs = some (some (rmV (rmEntries zs)))) ∧
      (∀ a b, r = rangeT a b → a < b → (∀ k x, RmCov ts k x → k < a ∨ b ≤ k) →
        hook rmRemove vs = some (some (rmV (rmEntries ts)))) ∧
      ((¬ ∃ a b, r = rangeT a b ∧ a < b) → hook rmRemove vs = some none ∧ silent rmRemove vs = true) := by
  obtain ⟨w, r, rfl, h₁, -⟩ := sortsOf_two hvs
  obtain ⟨ts, rfl, hok, hst⟩ := rm_only hs h₁
  refine ⟨ts, r, rfl, hok, fun a b hr hab => by subst hr; exact remove_at hst (rmOK_pairwise hok) hab,
    fun a b hr hab hno => by subst hr; exact remove_absent hst hok hab hno,
    fun h => ⟨remove_off (rmOK_proper hok) ?_, rfl⟩⟩
  cases hr : asRange r with
  | none => rfl
  | some p =>
    obtain ⟨a, b⟩ := p
    exact absurd ⟨a, b, asRange_some hr⟩ h

/-- **`removeAll(M, S)` at every argument list of its signature**: where every member of the Set
is a proper Int range injected into KItem (`mapM_ranges`), the map's keys outside every range of
the Set, and where a member is none (`mapM_bad`) `hook` gives none and the point is silent. -/
theorem covered_removeAll {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.rangeMap, Srt.set]) :
    ∃ ts rs, vs = [rmV (rmEntries ts), .set Srt.set rs] ∧ RmOK ts ∧
      (∀ ps, rs.mapM asKRange = some ps → ∃ zs, RmOK zs ∧
        (∀ k x, RmCov zs k x ↔ RmCov ts k x ∧ ∀ p ∈ ps, k < p.1 ∨ p.2 ≤ k) ∧
        c.sortOf (rmV (rmEntries zs)) = some Srt.rangeMap ∧
        hook rmRemoveAll vs = some (some (rmV (rmEntries zs)))) ∧
      (rs.mapM asKRange = none → hook rmRemoveAll vs = some none ∧ silent rmRemoveAll vs = true) := by
  obtain ⟨w, s, rfl, h₁, h₂⟩ := sortsOf_two hvs
  obtain ⟨ts, rfl, hok, hst⟩ := rm_only hs h₁
  obtain ⟨rs, rfl⟩ := shape_set hs h₂
  exact ⟨ts, rs, rfl, hok, fun ps hm => removeAll_at hst (rmOK_pairwise hok) hm _,
    fun hm => ⟨removeAll_off (rmOK_proper hok) hm _, rfl⟩⟩

/-- **`_RangeMap_` at every argument list of its signature**: where no key is in both maps, the map
of the keys of both, and where one is, `hook` gives none and the point is not silent (so Γ states
⊥, `concat_common_gamma`; the header's first finding). -/
theorem covered_concat {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.rangeMap, Srt.rangeMap]) :
    ∃ ts us, vs = [rmV (rmEntries ts), rmV (rmEntries us)] ∧ RmOK ts ∧ RmOK us ∧
      (RmApart ts us → ∃ zs, RmOK zs ∧ (∀ k x, RmCov zs k x ↔ RmCov ts k x ∨ RmCov us k x) ∧
        hook rmConcat vs = some (some (rmV (rmEntries zs)))) ∧
      (¬ RmApart ts us → hook rmConcat vs = some none ∧ silent rmConcat vs = false) := by
  obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := sortsOf_two hvs
  obtain ⟨ts, rfl, hok, -⟩ := rm_only hs h₁
  obtain ⟨us, rfl, hok', -⟩ := rm_only hs h₂
  exact ⟨ts, us, rfl, hok, hok', concat_at hok hok', fun h => ⟨concat_off hok hok' h, concat_not_silent _⟩⟩

/-! ## Statement 2: the `param_undetermined` shape at the regions the prose leaves unstated -/

/-- **Wherever one of the six keys has no value of `hook`, the point has the `param_undetermined`
shape**, in every semantics with `coreOK`: over all interpretations Γ entails neither ⊥ nor the
value `v` of the result sort. By `covered_elem` … `covered_removeAll` those argument lists are the
regions the prose leaves unstated. -/
theorem silent_undetermined (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {f : Sym} (hf : f ∈ silents) {vs : List GroundTerm} (hvs : c.sortsOf vs = some (sig f).args)
    (hh : hook f vs = some none) {v : GroundTerm} (hv : c.sortOf v = some (sig f).result)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constH v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig f) vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig f) vs ≡ den (c.withHooks H) v)) := by
  have h := (by decide +kernel : ∀ f ∈ silents, lookupSig hookSigs f = some (sig f)) f hf
  have hname : (sig f).name = f := (lookupSig_spec h).2
  exact undetermined c hok hr (by rw [hname]; exact h) hvs (by rw [hname]; exact hh)
    (by rw [hname]; exact silents_silent f hf vs) hv hfn₀ hfnv

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors and
subsorts (as test/RangeMapModel.lean's `cR`). -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- A semantics with `coreOK` and `RangeIn`: the Range constructor, Int and Range below KItem, the
`k` cell with the counter, and no function. -/
def cU : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int, Srt.range], ctors := [⟨rangeCtor, [Srt.kitem, Srt.kitem], Srt.range⟩] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK cU := .of_nil rfl (by decide +kernel)

theorem cU_coreOK : cU.coreOK = true := by decide +kernel

theorem cU_rangeIn : RangeIn cU := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem cU_noRaw : ∀ k ∈ cU.params, k.raw = false := by decide +kernel

theorem fnHypU (H : HookParams) : FnHyp (cU.withHooks H) := by
  have h : (cU.withHooks H).fns = [] := rfl
  have hrc : (cU.withHooks H).readsConfined = false :=
    (Semantics.readsConfined_withHooks cU H).trans (by decide +kernel)
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrc, openLaws_of_plain (c := cU.withHooks H) cU_noRaw⟩ <;> intro fn hfn <;> rw [h] at hfn <;>
    exact absurd hfn List.not_mem_nil

/-- Points the prose leaves unstated under every reading of the header; `v` is a value of the
result sort (`.RangeMap`, the KItem 0, the range `[0, 1)`). With `M = {[0,3) ↦ 7, [5,7) ↦ 8}`:
`[5,3) r|-> 7`, `[3,3) r|-> 7` (no proper range); `M[9]`, `M[3]` (3 is outside `[0,3)`), `M[4]`,
`.RangeMap[0]`, `M[ [0,3) ]` (a KItem that is no Int); `find_range` at the same four keys;
`M[ [5,3) <- 7 ]`, `M[ [2,2) <- 7 ]`; `M[ [5,3) <- undef ]`, `.RangeMap[ [1,1) <- undef ]`;
`removeAll(M, {1})` (a member that is no range), `removeAll(M, {[5,3)})`,
`removeAll(M, {[0,3), [9,9)})` (one member a proper range, one not). -/
def opens : List Pt :=
  [⟨rmElem, "RANGEMAP.elementRng", [.r 5 3, .k 7], .rm []⟩,
   ⟨rmElem, "RANGEMAP.elementRng", [.r 3 3, .k 7], .rm []⟩,
   ⟨rmLookup, "RANGEMAP.lookup", [.rm [(0, 3, 7), (5, 7, 8)], .k 9], .k 0⟩,
   ⟨rmLookup, "RANGEMAP.lookup", [.rm [(0, 3, 7), (5, 7, 8)], .k 3], .k 0⟩,
   ⟨rmLookup, "RANGEMAP.lookup", [.rm [(0, 3, 7), (5, 7, 8)], .k 4], .k 0⟩,
   ⟨rmLookup, "RANGEMAP.lookup", [.rm [], .k 0], .k 0⟩,
   ⟨rmLookup, "RANGEMAP.lookup", [.rm [(0, 3, 7), (5, 7, 8)], .kr 0 3], .k 0⟩,
   ⟨rmFindRange, "RANGEMAP.find_range", [.rm [(0, 3, 7), (5, 7, 8)], .k 9], .r 0 1⟩,
   ⟨rmFindRange, "RANGEMAP.find_range", [.rm [(0, 3, 7), (5, 7, 8)], .k 3], .r 0 1⟩,
   ⟨rmFindRange, "RANGEMAP.find_range", [.rm [], .k 0], .r 0 1⟩,
   ⟨rmFindRange, "RANGEMAP.find_range", [.rm [(0, 3, 7), (5, 7, 8)], .kr 0 3], .r 0 1⟩,
   ⟨rmUpdate, "RANGEMAP.updateRng", [.rm [(0, 3, 7), (5, 7, 8)], .r 5 3, .k 7], .rm []⟩,
   ⟨rmUpdate, "RANGEMAP.updateRng", [.rm [(0, 3, 7), (5, 7, 8)], .r 2 2, .k 7], .rm []⟩,
   ⟨rmRemove, "RANGEMAP.removeRng", [.rm [(0, 3, 7), (5, 7, 8)], .r 5 3], .rm []⟩,
   ⟨rmRemove, "RANGEMAP.removeRng", [.rm [], .r 1 1], .rm []⟩,
   ⟨rmRemoveAll, "RANGEMAP.removeAll", [.rm [(0, 3, 7), (5, 7, 8)], .sk [1]], .rm []⟩,
   ⟨rmRemoveAll, "RANGEMAP.removeAll", [.rm [(0, 3, 7), (5, 7, 8)], .sr [(5, 3)]], .rm []⟩,
   ⟨rmRemoveAll, "RANGEMAP.removeAll", [.rm [(0, 3, 7), (5, 7, 8)], .sr [(0, 3), (9, 9)]], .rm []⟩]

/-- At every point: a key of `silentTable` among the rows, its arguments written as values of the
argument sorts, no value of `hook`, a silent point, `v` of the result sort. -/
theorem opens_ok : opens.all (fun p => silents.contains p.f && rmRows.contains (p.f, p.name) &&
    (sig p.f).args == p.xs.map A.srt && p.xs.all A.ok && hook p.f (p.xs.map A.val) == some none &&
    silent p.f (p.xs.map A.val) && p.v.ok && (sig p.f).result == p.v.srt) = true := by
  decide +kernel

/-- Every one of the six keys has a point. -/
theorem opens_rows : silents.all (fun f => opens.any fun p => p.f == f) = true := by decide +kernel

/-- The points lie in the regions the header names: a range `[a, b)` with `b ≤ a`; a key that no
range of the map holds, or a KItem that is no Int; a Set with a member that is an Int or a range
that is no proper range. -/
theorem opens_regions : opens.all (fun p => match p.xs with
    | [.r a b, .k _] => p.f == rmElem && decide (b ≤ a)
    | [.rm l, .k n] => (p.f == rmLookup || p.f == rmFindRange) &&
        l.all (fun e => decide (n < e.1) || decide (e.2.1 ≤ n))
    | [.rm _, .kr _ _] => p.f == rmLookup || p.f == rmFindRange
    | [.rm _, .r a b, .k _] => p.f == rmUpdate && decide (b ≤ a)
    | [.rm _, .r a b] => p.f == rmRemove && decide (b ≤ a)
    | [.rm _, .sk l] => p.f == rmRemoveAll && !l.isEmpty
    | [.rm _, .sr l] => p.f == rmRemoveAll && l.any (fun q => decide (q.2 ≤ q.1))
    | _ => false) = true := by
  decide +kernel

/-- **Γ determines none of the points**: over all interpretations it entails neither that the
application has no value nor that it is the point's `v`. -/
theorem opens_undetermined : ∀ p ∈ opens,
    ¬ (∀ H : HookParams, Γ (cU.withHooks H) ⊧ (appP (cU.withHooks H) (sig p.f) (p.xs.map A.val) ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (cU.withHooks H) ⊧
      (appP (cU.withHooks H) (sig p.f) (p.xs.map A.val) ≡ den (cU.withHooks H) p.v.val)) := by
  intro p hp
  have h := List.all_eq_true.mp opens_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hf, -⟩, hargs⟩, hok⟩, hh⟩, -⟩, hvok⟩, hres⟩ := h
  exact silent_undetermined cU cU_coreOK cU_noRaw hf
    (by rw [hargs]; exact A.sortsOf cU_rangeIn _ hok) hh
    (by rw [hres]; exact A.sorted cU_rangeIn _ hvok) (fnHypU _) (fnHypU _)

/-- A range one bound of which is no Int (`[ [0,1), 3 )`, its lower bound a range injected into
KItem) is a value of sort Range in `cU`, and `r|->` at it has the `param_undetermined` shape: the
prose describes ranges of Int keys only (DOM 471-477). -/
theorem elem_nonInt_undetermined :
    cU.sortOf (.ctor rangeCtor [kr 0 1, kint 3]) = some Srt.range ∧
    ¬ (∀ H : HookParams, Γ (cU.withHooks H) ⊧
      (appP (cU.withHooks H) (sig rmElem) [.ctor rangeCtor [kr 0 1, kint 3], kint 7] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (cU.withHooks H) ⊧
      (appP (cU.withHooks H) (sig rmElem) [.ctor rangeCtor [kr 0 1, kint 3], kint 7] ≡
        den (cU.withHooks H) (rmV []))) :=
  ⟨by decide +kernel, silent_undetermined cU cU_coreOK cU_noRaw (f := rmElem) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (fnHypU _) (fnHypU _)⟩

/-! ## Axioms -/

/-- info: 'KCore.HooksRangeMapTest.vals_gamma_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vals_gamma_H

/-- info: 'KCore.HooksRangeMapTest.vals_hookRes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vals_hookRes

/-- info: 'KCore.HooksRangeMapTest.absents_gamma_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms absents_gamma_H

/-- info: 'KCore.HooksRangeMapTest.overlaps_entails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overlaps_entails

/-- info: 'KCore.HooksRangeMapTest.opens_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms opens_undetermined

/-- info: 'KCore.HooksRangeMapTest.elem_nonInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms elem_nonInt_undetermined

/-- info: 'KCore.HooksRangeMapTest.silent_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms silent_undetermined

/-- info: 'KCore.HooksRangeMapTest.covered_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_total

/-- info: 'KCore.HooksRangeMapTest.covered_elem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_elem

/-- info: 'KCore.HooksRangeMapTest.covered_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_lookup

/-- info: 'KCore.HooksRangeMapTest.covered_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_find

/-- info: 'KCore.HooksRangeMapTest.covered_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_update

/-- info: 'KCore.HooksRangeMapTest.covered_remove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_remove

/-- info: 'KCore.HooksRangeMapTest.covered_removeAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_removeAll

/-- info: 'KCore.HooksRangeMapTest.covered_concat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_concat

/-- info: 'KCore.HooksRangeMapTest.diff_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms diff_at

/-- info: 'KCore.HooksRangeMapTest.over_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms over_at

/-- info: 'KCore.HooksRangeMapTest.incl_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms incl_iff

/-- info: 'KCore.HooksRangeMapTest.keys_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms keys_at

/-- info: 'KCore.HooksRangeMapTest.rm_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rm_only

end KCore.HooksRangeMapTest
