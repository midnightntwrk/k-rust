/-
  The supported hook rows of MAP (test/constructs/rows.toml, `hook:MAP.*` with status `supported`):
  the sort row `MAP.Map` and the eleven operations `MAP.unit`, `element`, `concat`, `update`,
  `remove`, `lookup`, `lookupOrDefault`, `in_keys`, `size`, `removeAll`, `keys` (`mapRows`). Each has
  its three statements (DONE-0 C2, evidence row "supported hook (E6)"). The expectation is the
  builtin file's prose, cited by line: DOM is K 7.1.337's
  `k-distribution/include/kframework/builtin/domains.md`. No expected value below is taken from a
  run or from `hook`'s text: each value of `vals` is derived by hand from the cited sentence (the
  derivation is written at the point), and at every argument list an operation is stated by the
  bindings of its result (which bindings a map holds is what the prose speaks of), the result being
  the one map with those bindings (`map_ext`). Run from the package root:
  `lake env lean test/HooksMap.lean`. Kernel-checked.

  A map value is `mp es`: `es` its bindings (key, value), the keys strictly increasing. A key or a
  value is a KItem; the points below use injected integers (`ki n`), which are KItems in the
  semantics where Int is below KItem (`IntBelow`; every statement at a point is for every such
  semantics and every interpretation H, `sem_intBelow` is one).

  1. One in-domain value per operation (`vals`, most operations two): `hook`'s value there is the
     hand-derived one (`vals_hook`), it is the result under every interpretation (`vals_hookRes`),
     and Γ states it under every interpretation (`vals_gamma`).
  2. The regions the prose excludes or leaves unstated. Two of the eleven are not declared `total`
     (DOM 240, 271), and of each the prose states the value off its domain: "The result is `#False`
     if the maps have keys in common" (DOM 227-228; "a partial function only defined on maps with
     disjoint keys", DOM 320-321) and "The value is `#False` if the key is not in the map" (DOM
     267-268). `#False` is a statement of the value (none), so these regions are stated, not left
     open: Γ states ⊥ at every point of them (`concat_common_gamma`, `lookup_off_gamma`), under
     every interpretation (`bots_entails`), which is the negation of the first half of the
     `param_undetermined` shape (over all H, Γ entails neither ⊥ nor a value). The other nine are
     declared `total`. No point of these rows has the `param_undetermined` shape. Both sentences go
     on "(in particular, this will yield an exception during concrete execution)": that is said of a
     run, beside the `#False`, and takes nothing from it.
  3. The silent predicate: none of the eleven is a key of `silentTable` (`map_not_silentKey`), so
     its silent region is empty (`map_not_silent`), and the prose covers every argument list: under
     `shapesOK` a value of sort Map is a map with strictly increasing keys (`map_only`), the nine
     `total` operations have a value at every argument list of their signature (`covered_total`),
     `_Map_` has one where the keys are disjoint and none where one is common (`covered_concat`),
     and the lookup one where the key is bound and none where it is not (`covered_lookup`).

  Three readings, written here because the sentence of the operation does not by itself name the
  case; each is derived from the prose, and the rules of MAP-KORE-SYMBOLIC that agree are proved
  below (DOM 398-401 says of them: "They do not affect the semantics of maps, merely describing
  additional rules that the backend can use to simplify terms", so they are consequences the file
  states, not definitions).
  - Update at a key the map binds. "You can insert a key/value pair into a map" (DOM 286-287),
    declared `total` (DOM 290): a result exists at a bound key too; it holds the inserted pair;
    "Multiple bindings for the same key are not allowed" (DOM 225), so it does not hold the map's
    former binding of that key; the other bindings are the map's. Agreeing rules: DOM 434-435
    (`rule_434`, `rule_435`), 445, 447 (`rule_445`, `rule_447`).
  - Removal at a key the map does not bind. "You can remove a key/value pair from a map via its
    key" (DOM 295-296), declared `total` (DOM 299): a result exists; there is no pair of that key to
    remove, so every binding stays. Agreeing rules: DOM 426 (`rule_426`), 444 (`rule_444`).
  - `removeAll` at a set holding a key the map does not bind. "You can remove a `Set` of keys from a
    map" (DOM 329-330), declared `total` (DOM 333), and DOM 307-308 uses it at such a set ("To
    remove all the keys in one map from another map, you can say `removeAll(M1, keys(M2))`"): the
    bindings whose key is in the set go, the others stay.
  None of the three leaves the value open, so none is a finding against `silentTable`.

  The sort row `MAP.Map` (DOM 205-206, 218, 223-225): `map_value`, `map_of_bindings`,
  `map_functional`, `map_ext`, `map_only`; a sort has no argument list, so no key of `silentTable`
  is about it.
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.HooksMapTest

open KCore ML Faithful

/-! ## Γ at an interpreted symbol's application (as test/HooksInt.lean writes it) -/

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

/-- The signature of an interpreted symbol. -/
def sig (f : Sym) : CtorSig := (lookupSig hookSigs f).getD default

/-! ## The rows -/

/-- The eleven supported operation rows of MAP: the symbol and its `hook` attribute in the prose's
productions (DOM 248 `MAP.unit`, 257 `MAP.element`, 240 `MAP.concat`, 290 `MAP.update`,
299 `MAP.remove`, 271 `MAP.lookup`, 281 `MAP.lookupOrDefault`, 357 `MAP.in_keys`, 373 `MAP.size`,
333 `MAP.removeAll`, 341 `MAP.keys`). The twelfth row is the sort (`MAP.Map`, DOM 218). MAP's
other hooks (`difference` DOM 311, `updateAll` 324, `keys_list` 349, `values` 365, `inclusion` 383,
`choice` 393) are parameters in rows.toml, not supported rows. -/
def mapRows : List (Sym × String) :=
  [(mapUnit, "MAP.unit"), (mapElem, "MAP.element"), (mapConcat, "MAP.concat"),
   (mapUpdate, "MAP.update"), (mapRemove, "MAP.remove"), (mapLookup, "MAP.lookup"),
   (mapLookupOrDefault, "MAP.lookupOrDefault"), (mapInKeys, "MAP.in_keys"), (mapSize, "MAP.size"),
   (mapRemoveAll, "MAP.removeAll"), (mapKeys, "MAP.keys")]

/-- The two the prose does not declare `total` (DOM 240, 271), each with its `#False` sentence
(DOM 227-228, 267-268). -/
def partials : List Sym := [mapConcat, mapLookup]

/-- The nine the prose declares `total` (DOM 248, 257, 290, 299, 281, 357, 373, 333, 341). -/
def totals : List Sym :=
  [mapUnit, mapElem, mapUpdate, mapRemove, mapLookupOrDefault, mapInKeys, mapSize, mapRemoveAll, mapKeys]

/-- The rows are the registry's entries with a `MAP.` hook, each with its hook name. -/
theorem mapRows_registry :
    regHookNames.filter (fun e => e.2.toList.take 4 == "MAP.".toList) = mapRows := by
  decide +kernel

/-- The signatures, as the prose's productions give them (the lines of `mapRows`). -/
def mapSigs : List (Sym × List Srt × Srt) :=
  [(mapUnit, [], Srt.map), (mapElem, [Srt.kitem, Srt.kitem], Srt.map),
   (mapConcat, [Srt.map, Srt.map], Srt.map), (mapUpdate, [Srt.map, Srt.kitem, Srt.kitem], Srt.map),
   (mapRemove, [Srt.map, Srt.kitem], Srt.map), (mapLookup, [Srt.map, Srt.kitem], Srt.kitem),
   (mapLookupOrDefault, [Srt.map, Srt.kitem, Srt.kitem], Srt.kitem),
   (mapInKeys, [Srt.kitem, Srt.map], Srt.bool), (mapSize, [Srt.map], Srt.int),
   (mapRemoveAll, [Srt.map, Srt.set], Srt.map), (mapKeys, [Srt.map], Srt.set)]

/-- Each row's symbol has that signature among `hookSigs`. -/
theorem mapRows_sig : (mapRows.map (·.1) == mapSigs.map (·.1) &&
    mapSigs.all (fun r => decide (sig r.1 ∈ hookSigs) && (sig r.1).name == r.1 &&
      (sig r.1).args == r.2.1 && (sig r.1).result == r.2.2)) = true := by
  decide +kernel

/-- `partialHooks` (the interpreted symbols the totality deciders do not count as total) holds of
these rows exactly the two the prose does not declare `total`; the rows are those two and the nine. -/
theorem mapRows_partial : (mapRows.all (fun r => partialHooks.contains r.1 == partials.contains r.1) &&
    mapRows.all (fun r => partials.contains r.1 != totals.contains r.1)) = true := by
  decide +kernel

/-! ## Values -/

/-- An integer as a KItem. -/
def ki (n : Int) : GroundTerm := .inj Srt.int Srt.kitem (int n)
/-- A map of the library's sort, by its bindings. -/
abbrev mp (es : Entries) : GroundTerm := .map Srt.map es
/-- A set of the library's sort, by its members. -/
abbrev st (es : List GroundTerm) : GroundTerm := .set Srt.set es

/-- Int is below KItem in `c`, so that an injected integer is a KItem. -/
def IntBelow (c : Semantics) : Prop := (Srt.int, Srt.kitem) ∈ c.subsorts

theorem IntBelow.withHooks {c : Semantics} (h : IntBelow c) (H : HookParams) : IntBelow (c.withHooks H) := h

/-- A semantics with Int below KItem (no sentence of its own). -/
def sem : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.string, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := []
  ctors := []
  fns := []
  userSubsorts := []
  pgmSort := Srt.k
  rules := []

theorem sem_intBelow : IntBelow sem := by unfold IntBelow; decide +kernel

theorem int_value (c : Semantics) (i : Int) : c.sortOf (int i) = some Srt.int := by
  simp [int, Semantics.sortOf, dvOK]

theorem bool_value (c : Semantics) (b : Bool) : c.sortOf (bool b) = some Srt.bool := by
  simp [bool, Semantics.sortOf, dvOK]

theorem ki_value {c : Semantics} (h : IntBelow c) (n : Int) : c.sortOf (ki n) = some Srt.kitem :=
  sortOf_inj.mpr ⟨h, rfl, int_value c n, rfl⟩

/-! ## The sort row `MAP.Map` -/

/-- `k` has a binding in `m`. -/
def Bound (m : Entries) (k : GroundTerm) : Prop := ∃ v, (k, v) ∈ m

/-- No key of `a` is a key of `b`. -/
def Apart (a b : Entries) : Prop := ∀ e ∈ a, ∀ e' ∈ b, e.1 ≠ e'.1

/-- Bindings of KItems to KItems with strictly increasing keys are a value of sort Map, in every
semantics: "maps from `KItem` to `KItem`" (DOM 205-206), the sort declared at DOM 218. -/
theorem map_value (c : Semantics) {es : Entries} (hs : keysSorted es = true)
    (he : ∀ e ∈ es, c.sortOf e.1 = some Srt.kitem ∧ c.sortOf e.2 = some Srt.kitem) :
    c.sortOf (mp es) = some Srt.map := by
  rw [Map.sortOf_map, hs, entriesOK_iff.mpr he]; rfl

/-- Every finite list of bindings with distinct keys is the bindings of one such list with
strictly increasing keys: every finite function from keys to values is represented. -/
theorem map_of_bindings {L : Entries} (h : L.Pairwise fun e e' => e.1 ≠ e'.1) :
    ∃ es, keysSorted es = true ∧ ∀ e, e ∈ es ↔ e ∈ L :=
  ⟨sortE L, sortE_spec (h.imp fun hne hc => hne (cmp_eq_iff.mp hc))⟩

/-- "Each key can be paired with an arbitrary value … Multiple bindings for the same key are not
allowed" (DOM 223-225): a map binds a key to one value. -/
theorem map_functional {m : Entries} (hm : keysSorted m = true) {k v v' : GroundTerm}
    (h : (k, v) ∈ m) (h' : (k, v') ∈ m) : v = v' :=
  Option.some.inj ((Map.find_of_mem hm h).symm.trans (Map.find_of_mem hm h'))

/-- "associative, commutative maps" (DOM 205-206): a map is its bindings, in no order; two maps
with the same bindings are the same value. -/
theorem map_ext {a b : Entries} (ha : keysSorted a = true) (hb : keysSorted b = true)
    (h : ∀ e, e ∈ a ↔ e ∈ b) : mp a = mp b := by
  rw [entries_canon ha hb h]

/-- Nothing else is a value of sort Map (where the sorts the interpreted symbols read have their
shapes, `shapesOK`): bindings of KItems to KItems, the keys strictly increasing. -/
theorem map_only {c : Semantics} (hs : c.shapesOK = true) {v : GroundTerm}
    (h : c.sortOf v = some Srt.map) : ∃ es, v = mp es ∧ keysSorted es = true ∧
      ∀ e ∈ es, c.sortOf e.1 = some Srt.kitem ∧ c.sortOf e.2 = some Srt.kitem := by
  obtain ⟨es, rfl⟩ := shape_map hs h
  rw [Map.sortOf_map] at h
  by_cases hb : (keysSorted es && c.entriesOK Srt.kitem Srt.kitem es) = true
  · simp only [Bool.and_eq_true] at hb
    exact ⟨es, rfl, hb.1, entriesOK_iff.mp hb.2⟩
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-! ## `hook` at every argument list, by the bindings of the result -/

theorem find_unbound {m : Entries} {k : GroundTerm} (h : ¬ Bound m k) : Map.find m k = none := by
  cases hf : Map.find m k with
  | none => rfl
  | some v => exact absurd ⟨v, Map.mem_of_find hf⟩ h

theorem apart_cmp {a b : Entries} :
    Apart a b ↔ ∀ e ∈ a, ∀ e' ∈ b, GroundTerm.cmp e.1 e'.1 ≠ .eq :=
  ⟨fun h e he e' he' hc => h e he e' he' (cmp_eq_iff.mp hc),
   fun h e he e' he' hc => h e he e' he' (cmp_eq_iff.mpr hc)⟩

theorem Apart.symm {a b : Entries} (h : Apart a b) : Apart b a :=
  fun e he e' he' hk => h e' he' e he hk.symm

/-- "The map with zero elements is represented by `.Map`" (DOM 245): no binding. -/
theorem unit_at : hook mapUnit [] = some (some (mp [])) := rfl

/-- "An element of a `Map` is constructed via the `|->` operator. The key is on the left and the
value is on the right" (DOM 253-254): the one binding of `k` to `v`. -/
theorem elem_at (k v : GroundTerm) : hook mapElem [k, v] = some (some (mp [(k, v)])) := rfl

/-- "You can construct a new Map consisting of key/value pairs of two Maps" (DOM 227), where the
maps have no key in common: the map whose bindings are those of the one and of the other. -/
theorem concat_at {a b : Entries} (ha : keysSorted a = true) (hb : keysSorted b = true)
    (h : Apart a b) : ∃ m, hook mapConcat [mp a, mp b] = some (some (mp m)) ∧
      keysSorted m = true ∧ ∀ e, e ∈ m ↔ e ∈ a ∨ e ∈ b := by
  obtain ⟨m, hu, hm⟩ := union_exists (sorted_apart ha) (apart_cmp.mp h)
  exact ⟨m, by rw [hook_mapConcat, hu]; rfl, union_sorted hb hu, hm⟩

/-- "The result is `#False` if the maps have keys in common" (DOM 227-228): no value. -/
theorem concat_common {a b : Entries} (h : ¬ Apart a b) : hook mapConcat [mp a, mp b] = some none := by
  rw [hook_mapConcat]
  cases hu : union a b with
  | none => rfl
  | some m => exact absurd (apart_cmp.mpr (union_spec hu).2.2.2) h

/-- The same at a common key named. -/
theorem concat_common_key {a b : Entries} {e e' : GroundTerm × GroundTerm} (he : e ∈ a) (he' : e' ∈ b)
    (hk : e.1 = e'.1) : hook mapConcat [mp a, mp b] = some none :=
  concat_common fun h => h e he e' he' hk

/-- `comm` (DOM 240; "commutative", DOM 205-206): the two orders give the same result, a value or
none. -/
theorem concat_comm {a b : Entries} (ha : keysSorted a = true) (hb : keysSorted b = true) :
    hook mapConcat [mp a, mp b] = hook mapConcat [mp b, mp a] := by
  by_cases h : Apart a b
  · obtain ⟨m, h1, s1, m1⟩ := concat_at ha hb h
    obtain ⟨m', h2, s2, m2⟩ := concat_at hb ha h.symm
    have hm : m = m' := entries_canon s1 s2 fun e => by rw [m1, m2, or_comm]
    rw [h1, h2, hm]
  · rw [concat_common h, concat_common fun h' => h h'.symm]

/-- `unit(.Map)` (DOM 240): `.Map` on either side gives the other map. -/
theorem concat_unit_left (b : Entries) : hook mapConcat [mp [], mp b] = some (some (mp b)) := rfl

theorem concat_unit_right {a : Entries} (ha : keysSorted a = true) :
    hook mapConcat [mp a, mp []] = some (some (mp a)) := by
  rw [concat_comm ha rfl]; rfl

theorem concat_inv {a b m : Entries} (h : hook mapConcat [mp a, mp b] = some (some (mp m))) :
    union a b = some m := by
  rw [hook_mapConcat] at h
  cases hu : union a b with
  | none => rw [hu] at h; cases h
  | some m' =>
    rw [hu] at h
    simp only [Option.map_some, Option.some.injEq, GroundTerm.map.injEq, true_and] at h
    rw [h]

/-- `assoc` (DOM 240; "associative", DOM 205-206): where `(a b) d` has the value `r`, so has
`a (b d)`. (The other direction is this one through `concat_comm`.) -/
theorem concat_assoc {a b d ab r : Entries} (ha : keysSorted a = true) (hb : keysSorted b = true)
    (hd : keysSorted d = true) (h1 : hook mapConcat [mp a, mp b] = some (some (mp ab)))
    (h2 : hook mapConcat [mp ab, mp d] = some (some (mp r))) :
    ∃ bd, hook mapConcat [mp b, mp d] = some (some (mp bd)) ∧
      hook mapConcat [mp a, mp bd] = some (some (mp r)) := by
  have u1 := concat_inv h1
  have u2 := concat_inv h2
  obtain ⟨m1, -, -, d1⟩ := union_spec u1
  obtain ⟨m2, -, -, d2⟩ := union_spec u2
  have a1 : Apart a b := apart_cmp.mpr d1
  have a2 : Apart ab d := apart_cmp.mpr d2
  obtain ⟨bd, hbd, sbd, mbd⟩ := concat_at hb hd fun e he => a2 e ((m1 e).mpr (Or.inr he))
  have a3 : Apart a bd := fun e he e' he' => by
    rcases (mbd e').mp he' with h | h
    · exact a1 e he e' h
    · exact a2 e ((m1 e).mpr (Or.inl he)) e' h
  obtain ⟨r', hr', sr', mr'⟩ := concat_at ha sbd a3
  have hr : r' = r := entries_canon sr' (union_sorted hd u2) fun e => by
    rw [mr', m2, m1, mbd, or_assoc]
  exact ⟨bd, hbd, by rw [hr', hr]⟩

/-- "You can look up the value associated with the key of a map" (DOM 265): where `m` binds `k` to
`v`, `v`. -/
theorem lookup_at {m : Entries} (hm : keysSorted m = true) {k v : GroundTerm} (h : (k, v) ∈ m) :
    hook mapLookup [mp m, k] = some (some v) := by
  rw [hook_mapLookup, Map.find_of_mem hm h]

/-- "The value is `#False` if the key is not in the map" (DOM 267-268): no value. -/
theorem lookup_off {m : Entries} {k : GroundTerm} (h : ¬ Bound m k) :
    hook mapLookup [mp m, k] = some none := by
  rw [hook_mapLookup, find_unbound h]

theorem hook_lookupOrDefault (m : Entries) (k d : GroundTerm) :
    hook mapLookupOrDefault [mp m, k, d] = some (some ((Map.find m k).getD d)) := rfl

/-- "look up the value associated with the key of a map using a total function that assigns a
specific default value if the key is not present in the map" (DOM 276-278): the bound value, or
the default. -/
theorem lookupOrDefault_at {m : Entries} (hm : keysSorted m = true) {k v : GroundTerm} (d : GroundTerm)
    (h : (k, v) ∈ m) : hook mapLookupOrDefault [mp m, k, d] = some (some v) := by
  rw [hook_lookupOrDefault, Map.find_of_mem hm h]; rfl

theorem lookupOrDefault_off {m : Entries} {k : GroundTerm} (d : GroundTerm) (h : ¬ Bound m k) :
    hook mapLookupOrDefault [mp m, k, d] = some (some d) := by
  rw [hook_lookupOrDefault, find_unbound h]; rfl

/-- "You can insert a key/value pair into a map" (DOM 286-287), `total` (DOM 290): the map whose
bindings are the pair and the map's bindings of the other keys (at a key the map binds, its former
binding is not kept: DOM 225; the reading is in the file's header). -/
theorem update_at {m : Entries} (hm : keysSorted m = true) (k v : GroundTerm) :
    ∃ m', hook mapUpdate [mp m, k, v] = some (some (mp m')) ∧ keysSorted m' = true ∧
      ∀ e, e ∈ m' ↔ e = (k, v) ∨ (e ∈ m ∧ e.1 ≠ k) := by
  refine ⟨insertE k v m, rfl, insertE_sorted hm, fun ⟨k', v'⟩ => ?_⟩
  rw [← Map.find_iff_mem (Map.insert_canon hm), Map.find_insert]
  by_cases hk : k' = k
  · subst hk; simp [eq_comm]
  · simp [hk, Map.find_iff_mem hm]

/-- "You can remove a key/value pair from a map via its key" (DOM 295-296), `total` (DOM 299): the
map's bindings of the other keys (all of them where the map does not bind the key). -/
theorem remove_at {m : Entries} (hm : keysSorted m = true) (k : GroundTerm) :
    ∃ m', hook mapRemove [mp m, k] = some (some (mp m')) ∧ keysSorted m' = true ∧
      ∀ e, e ∈ m' ↔ e ∈ m ∧ e.1 ≠ k := by
  refine ⟨eraseK k m, rfl, eraseK_sorted hm, fun ⟨k', v'⟩ => ?_⟩
  rw [← Map.find_iff_mem (Map.erase_canon hm), Map.find_erase hm]
  by_cases hk : k' = k
  · subst hk; simp
  · simp [hk, Map.find_iff_mem hm]

/-- "You can remove a `Set` of keys from a map" (DOM 329-330), `total` (DOM 333): the map's
bindings of the keys that are no member of the set. -/
theorem removeAll_at {m : Entries} (hm : keysSorted m = true) (ks : List GroundTerm) :
    ∃ m', hook mapRemoveAll [mp m, st ks] = some (some (mp m')) ∧ keysSorted m' = true ∧
      ∀ e, e ∈ m' ↔ e ∈ m ∧ e.1 ∉ ks := by
  refine ⟨m.filter fun e => !memS e.1 ks, rfl, sorted_sublist List.filter_sublist hm, fun e => ?_⟩
  rw [List.mem_filter, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Set.memS_iff]

/-- "You can get a `Set` of all the keys in a Map" (DOM 338): the set whose members are the keys
the map binds. -/
theorem keys_at {m : Entries} (hm : keysSorted m = true) :
    ∃ ks, hook mapKeys [mp m] = some (some (st ks)) ∧ elemsSorted ks = true ∧
      ∀ x, x ∈ ks ↔ Bound m x := by
  refine ⟨keysOf m, rfl, Map.keys_canon hm, fun x => ?_⟩
  unfold keysOf
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨k, v⟩, h, rfl⟩; exact ⟨v, h⟩
  · rintro ⟨v, h⟩; exact ⟨(x, v), h, rfl⟩

/-- "You can check whether a key is present in a map" (DOM 354). -/
theorem inKeys_at {m : Entries} (hm : keysSorted m = true) {k : GroundTerm} (h : Bound m k) :
    hook mapInKeys [k, mp m] = some (some (bool true)) := by
  obtain ⟨v, h⟩ := h
  rw [hook_mapInKeys, Map.find_of_mem hm h]; rfl

theorem inKeys_off {m : Entries} {k : GroundTerm} (h : ¬ Bound m k) :
    hook mapInKeys [k, mp m] = some (some (bool false)) := by
  rw [hook_mapInKeys, find_unbound h]; rfl

/-- "You can get the number of key/value pairs in a map" (DOM 370): the number of bindings. -/
theorem size_at (m : Entries) : hook mapSize [mp m] = some (some (int m.length)) := rfl

/-! ## The rules of MAP-KORE-SYMBOLIC that fix the three readings (DOM 398-401 on their status) -/

theorem update_val {m : Entries} {k v u : GroundTerm} (h : hook mapUpdate [mp m, k, v] = some (some u)) :
    u = mp (insertE k v m) := (Option.some.inj (Option.some.inj h)).symm

theorem remove_val {m : Entries} {k u : GroundTerm} (h : hook mapRemove [mp m, k] = some (some u)) :
    u = mp (eraseK k m) := (Option.some.inj (Option.some.inj h)).symm

/-- `(_MAP:Map [ K <- V1 ]) [ K ] => V1` (DOM 434): also where `_MAP` binds `K`. -/
theorem rule_434 {m : Entries} {k v u : GroundTerm} (h : hook mapUpdate [mp m, k, v] = some (some u)) :
    hook mapLookup [u, k] = some (some v) := by
  rw [update_val h, hook_mapLookup, Map.find_insert_self]

/-- `( MAP:Map [ K1 <- _V1 ]) [ K2 ] => MAP [ K2 ] requires K1 =/=K K2` (DOM 435). -/
theorem rule_435 {m : Entries} {k₁ k₂ v u : GroundTerm} (hk : k₁ ≠ k₂)
    (h : hook mapUpdate [mp m, k₁, v] = some (some u)) :
    hook mapLookup [u, k₂] = hook mapLookup [mp m, k₂] := by
  rw [update_val h, hook_mapLookup, hook_mapLookup, Map.find_insert_ne v (Ne.symm hk)]

/-- `K in_keys(_M [ K <- _ ]) => true` (DOM 445). -/
theorem rule_445 {m : Entries} {k v u : GroundTerm} (h : hook mapUpdate [mp m, k, v] = some (some u)) :
    hook mapInKeys [k, u] = some (some (bool true)) := by
  rw [update_val h, hook_mapInKeys, Map.find_insert_self]; rfl

/-- `K1 in_keys(M [ K2 <- _ ]) => K1 in_keys(M) requires K1 =/=K K2` (DOM 447). -/
theorem rule_447 {m : Entries} {k₁ k₂ v u : GroundTerm} (hk : k₁ ≠ k₂)
    (h : hook mapUpdate [mp m, k₂, v] = some (some u)) :
    hook mapInKeys [k₁, u] = hook mapInKeys [k₁, mp m] := by
  rw [update_val h, hook_mapInKeys, hook_mapInKeys, Map.find_insert_ne v hk]

/-- `M:Map [ K <- undef ] => M requires notBool (K in_keys(M))` (DOM 426). -/
theorem rule_426 {m : Entries} (hm : keysSorted m = true) {k : GroundTerm} (h : ¬ Bound m k) :
    hook mapRemove [mp m, k] = some (some (mp m)) := by
  obtain ⟨m', h1, s1, m1⟩ := remove_at hm k
  have : m' = m := entries_canon s1 hm fun e => by
    rw [m1]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', fun hk => h ⟨e.2, by rw [← hk]; exact h'⟩⟩⟩
  rw [h1, this]

/-- `K in_keys(_M [ K <- undef ]) => false` (DOM 444). -/
theorem rule_444 {m : Entries} (hm : keysSorted m = true) {k u : GroundTerm}
    (h : hook mapRemove [mp m, k] = some (some u)) :
    hook mapInKeys [k, u] = some (some (bool false)) := by
  rw [remove_val h, hook_mapInKeys, Map.find_erase_self k hm]; rfl

/-- `.Map [ _ ] orDefault D => D` (DOM 441). -/
theorem rule_441 (k d : GroundTerm) : hook mapLookupOrDefault [mp [], k, d] = some (some d) := rfl

/-! ## Statement 1: in-domain values, derived from the prose -/

/-- An argument or a result of a point: a KItem `ki n`, an Int, a Bool, a map of integers to
integers (its bindings, as written) or a set of integers. -/
inductive A where
  | k (n : Int)
  | i (n : Int)
  | b (x : Bool)
  | m (l : List (Int × Int))
  | s (l : List Int)

def A.val : A → GroundTerm
  | .k n => ki n
  | .i n => int n
  | .b x => bool x
  | .m l => mp (l.map fun e => (ki e.1, ki e.2))
  | .s l => st (l.map ki)

def A.srt : A → Srt
  | .k _ => Srt.kitem
  | .i _ => Srt.int
  | .b _ => Srt.bool
  | .m _ => Srt.map
  | .s _ => Srt.set

/-- The bindings (members) are written with strictly increasing keys, as a value has them. -/
def A.ok : A → Bool
  | .m l => keysSorted (l.map fun e => (ki e.1, ki e.2))
  | .s l => elemsSorted (l.map ki)
  | _ => true

/-- Such a term is a value of its sort, in every semantics with Int below KItem. -/
theorem A.sorted {c : Semantics} (hI : IntBelow c) : ∀ a : A, a.ok = true → c.sortOf a.val = some a.srt
  | .k n, _ => ki_value hI n
  | .i n, _ => int_value c n
  | .b x, _ => bool_value c x
  | .m l, h => map_value c h fun e he => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
      exact ⟨ki_value hI _, ki_value hI _⟩
  | .s l, h => sortOf_setS.mpr ⟨_, collOf_set, rfl, h, fun e he => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
      exact ki_value hI x, rfl⟩

theorem A.sortsOf {c : Semantics} (hI : IntBelow c) : ∀ xs : List A, xs.all A.ok = true →
    c.sortsOf (xs.map A.val) = some (xs.map A.srt)
  | [], _ => by simp [Semantics.sortsOf]
  | a :: xs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [Semantics.sortsOf, A.sorted hI a h.1, A.sortsOf hI xs h.2]

/-- A point: the operation, its hook name, its arguments and the expected value. -/
structure Pt where
  f : Sym
  name : String
  xs : List A
  v : A

/-- The expected values, each derived by hand from the cited sentence (`n` is the KItem `ki n`,
`{1 ↦ 2, 3 ↦ 4}` the map binding 1 to 2 and 3 to 4).
- `.Map`: "The map with zero elements" (DOM 245): no binding.
- `1 |-> 2`: "The key is on the left and the value is on the right" (DOM 253-254): `{1 ↦ 2}`.
- `_Map_`: "a new Map consisting of key/value pairs of two Maps" (DOM 227): of `{1 ↦ 2}` and
  `{3 ↦ 4}`, `{1 ↦ 2, 3 ↦ 4}`, in either order; of `.Map` and `{1 ↦ 2}`, `{1 ↦ 2}`.
- lookup: "the value associated with the key" (DOM 265): `{1 ↦ 2, 3 ↦ 4}[3]` is 4 (2 is the value
  of the other key).
- lookup with default: "a specific default value if the key is not present" (DOM 276-278):
  `{1 ↦ 2}[1] orDefault 9` is 2; `{1 ↦ 2}[5] orDefault 9` is 9; `{1 ↦ 2}[2] orDefault 9` is 9 (2 is
  a value of the map, no key).
- update: "insert a key/value pair into a map" (DOM 286-287): `{1 ↦ 2}[3 <- 4]` is
  `{1 ↦ 2, 3 ↦ 4}`; at a bound key (the header's first reading) `{1 ↦ 2, 3 ↦ 4}[1 <- 7]` is
  `{1 ↦ 7, 3 ↦ 4}`.
- delete: "remove a key/value pair from a map via its key" (DOM 295-296):
  `{1 ↦ 2, 3 ↦ 4}[1 <- undef]` is `{3 ↦ 4}`; at an unbound key (second reading)
  `{1 ↦ 2}[5 <- undef]` is `{1 ↦ 2}`.
- `removeAll`: "remove a `Set` of keys from a map" (DOM 329-330):
  `removeAll({1 ↦ 2, 3 ↦ 4, 5 ↦ 6}, {1, 5})` is `{3 ↦ 4}`; with a member that is no key (third
  reading) `removeAll({1 ↦ 2}, {1, 7})` is `.Map`.
- `keys`: "a `Set` of all the keys" (DOM 338): of `{1 ↦ 2, 3 ↦ 4}`, `{1, 3}`; of `.Map`, `.Set`.
- `in_keys`: "whether a key is present" (DOM 354): 3 in `{1 ↦ 2, 3 ↦ 4}`, true; 2 in `{1 ↦ 2}`,
  false (a value, no key).
- `size`: "the number of key/value pairs" (DOM 370): of `{1 ↦ 2, 3 ↦ 4}`, 2; of `.Map`, 0. -/
def vals : List Pt :=
  [⟨mapUnit, "MAP.unit", [], .m []⟩,
   ⟨mapElem, "MAP.element", [.k 1, .k 2], .m [(1, 2)]⟩,
   ⟨mapConcat, "MAP.concat", [.m [(1, 2)], .m [(3, 4)]], .m [(1, 2), (3, 4)]⟩,
   ⟨mapConcat, "MAP.concat", [.m [(3, 4)], .m [(1, 2)]], .m [(1, 2), (3, 4)]⟩,
   ⟨mapConcat, "MAP.concat", [.m [], .m [(1, 2)]], .m [(1, 2)]⟩,
   ⟨mapLookup, "MAP.lookup", [.m [(1, 2), (3, 4)], .k 3], .k 4⟩,
   ⟨mapLookupOrDefault, "MAP.lookupOrDefault", [.m [(1, 2)], .k 1, .k 9], .k 2⟩,
   ⟨mapLookupOrDefault, "MAP.lookupOrDefault", [.m [(1, 2)], .k 5, .k 9], .k 9⟩,
   ⟨mapLookupOrDefault, "MAP.lookupOrDefault", [.m [(1, 2)], .k 2, .k 9], .k 9⟩,
   ⟨mapUpdate, "MAP.update", [.m [(1, 2)], .k 3, .k 4], .m [(1, 2), (3, 4)]⟩,
   ⟨mapUpdate, "MAP.update", [.m [(1, 2), (3, 4)], .k 1, .k 7], .m [(1, 7), (3, 4)]⟩,
   ⟨mapRemove, "MAP.remove", [.m [(1, 2), (3, 4)], .k 1], .m [(3, 4)]⟩,
   ⟨mapRemove, "MAP.remove", [.m [(1, 2)], .k 5], .m [(1, 2)]⟩,
   ⟨mapRemoveAll, "MAP.removeAll", [.m [(1, 2), (3, 4), (5, 6)], .s [1, 5]], .m [(3, 4)]⟩,
   ⟨mapRemoveAll, "MAP.removeAll", [.m [(1, 2)], .s [1, 7]], .m []⟩,
   ⟨mapKeys, "MAP.keys", [.m [(1, 2), (3, 4)]], .s [1, 3]⟩,
   ⟨mapKeys, "MAP.keys", [.m []], .s []⟩,
   ⟨mapInKeys, "MAP.in_keys", [.k 3, .m [(1, 2), (3, 4)]], .b true⟩,
   ⟨mapInKeys, "MAP.in_keys", [.k 2, .m [(1, 2)]], .b false⟩,
   ⟨mapSize, "MAP.size", [.m [(1, 2), (3, 4)]], .i 2⟩,
   ⟨mapSize, "MAP.size", [.m []], .i 0⟩]

/-- Every row has a point, and every point is of a row. -/
theorem vals_rows : (mapRows.all (fun r => vals.any fun p => p.f == r.1 && p.name == r.2) &&
    vals.all (fun p => mapRows.contains (p.f, p.name))) = true := by
  decide +kernel

/-- **`hook`'s value at each point is the one derived from the prose.** -/
theorem vals_hook : vals.all (fun p => hook p.f (p.xs.map A.val) == some (some p.v.val)) = true := by
  decide +kernel

/-- The arguments of each point are written as values (increasing keys) of the signature's
argument sorts, and the expected value as one of its result sort. -/
theorem vals_sig : vals.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.xs.map A.srt && p.xs.all A.ok && p.v.ok && (sig p.f).result == p.v.srt) = true := by
  decide +kernel

/-- **At each point the result is that value, under every interpretation, in every semantics.** -/
theorem vals_hookRes : ∀ p ∈ vals, ∀ (c : Semantics) (H : HookParams),
    (c.withHooks H).hookRes p.f (p.xs.map A.val) = some (some p.v.val) :=
  fun p hp _ _ => Semantics.hookRes_of_value (by simpa using List.all_eq_true.mp vals_hook p hp)

/-- **At each point Γ states that value, under every interpretation**, in every semantics with Int
below KItem: there the arguments are values of the signature's sorts and the expected value one of
the result sort. -/
theorem vals_gamma : ∀ p ∈ vals, ∀ (c : Semantics), IntBelow c → ∀ H : HookParams,
    (c.withHooks H).sortsOf (p.xs.map A.val) = some (sig p.f).args ∧
    (c.withHooks H).sortOf p.v.val = some (sig p.f).result ∧
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map A.val) ≡ den (c.withHooks H) p.v.val) := by
  intro p hp c hI H
  have h := List.all_eq_true.mp vals_sig p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hk, hname⟩, hargs⟩, hok⟩, hvok⟩, hres⟩ := h
  have hh : hook p.f (p.xs.map A.val) = some (some p.v.val) := by
    simpa using List.all_eq_true.mp vals_hook p hp
  have hvs : (c.withHooks H).sortsOf (p.xs.map A.val) = some (sig p.f).args := by
    rw [hargs]; exact A.sortsOf (hI.withHooks H) _ hok
  exact ⟨hvs, by rw [hres]; exact A.sorted (hI.withHooks H) _ hvok,
    gamma_val _ hk hvs (by rw [hname]; exact hh)⟩

/-! ## Statement 3: no silent region; the prose covers every argument list -/

/-- **None of the eleven is a key of `silentTable`.** -/
theorem map_not_silentKey : ∀ r ∈ mapRows, silentKey r.1 = false := by decide +kernel

/-- **The silent predicate of each is false at every argument list**: the region the prose leaves
unstated is empty. -/
theorem map_not_silent : ∀ r ∈ mapRows, ∀ vs : List GroundTerm, silent r.1 vs = false :=
  fun r hr vs => silent_of_not_silentKey (map_not_silentKey r hr) vs

theorem sig_args : ∀ r ∈ mapSigs, sig r.1 ∈ hookSigs ∧ (sig r.1).name = r.1 ∧ (sig r.1).args = r.2.1 := by
  decide +kernel

/-- **The nine operations declared `total` have a value at every argument list of their
signature**, the one `*_at` describes. -/
theorem covered_total {c : Semantics} (hs : c.shapesOK = true) : ∀ f ∈ totals,
    ∀ vs : List GroundTerm, c.sortsOf vs = some (sig f).args → ∃ v, hook f vs = some (some v) := by
  intro f hf vs hvs
  simp only [totals, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show (sig mapUnit).args = [] by decide +kernel] at hvs
    obtain rfl := sortsOf_inv_nil hvs
    exact ⟨_, unit_at⟩
  · rw [show (sig mapElem).args = [Srt.kitem, Srt.kitem] by decide +kernel] at hvs
    obtain ⟨k, v, rfl, -, -⟩ := sortsOf_two hvs
    exact ⟨_, elem_at k v⟩
  · rw [show (sig mapUpdate).args = [Srt.map, Srt.kitem, Srt.kitem] by decide +kernel] at hvs
    obtain ⟨w, k, v, rfl, h₁, -, -⟩ := sortsOf_three hvs
    obtain ⟨m, rfl⟩ := shape_map hs h₁
    exact ⟨_, rfl⟩
  · rw [show (sig mapRemove).args = [Srt.map, Srt.kitem] by decide +kernel] at hvs
    obtain ⟨w, k, rfl, h₁, -⟩ := sortsOf_two hvs
    obtain ⟨m, rfl⟩ := shape_map hs h₁
    exact ⟨_, rfl⟩
  · rw [show (sig mapLookupOrDefault).args = [Srt.map, Srt.kitem, Srt.kitem] by decide +kernel] at hvs
    obtain ⟨w, k, d, rfl, h₁, -, -⟩ := sortsOf_three hvs
    obtain ⟨m, rfl⟩ := shape_map hs h₁
    exact ⟨_, hook_lookupOrDefault m k d⟩
  · rw [show (sig mapInKeys).args = [Srt.kitem, Srt.map] by decide +kernel] at hvs
    obtain ⟨k, w, rfl, -, h₂⟩ := sortsOf_two hvs
    obtain ⟨m, rfl⟩ := shape_map hs h₂
    exact ⟨_, hook_mapInKeys Srt.map m k⟩
  · rw [show (sig mapSize).args = [Srt.map] by decide +kernel] at hvs
    obtain ⟨w, rfl, h₁⟩ := sortsOf_one hvs
    obtain ⟨m, rfl⟩ := shape_map hs h₁
    exact ⟨_, size_at m⟩
  · rw [show (sig mapRemoveAll).args = [Srt.map, Srt.set] by decide +kernel] at hvs
    obtain ⟨w, x, rfl, h₁, h₂⟩ := sortsOf_two hvs
    obtain ⟨m, rfl⟩ := shape_map hs h₁
    obtain ⟨ks, rfl⟩ := shape_set hs h₂
    exact ⟨_, rfl⟩
  · rw [show (sig mapKeys).args = [Srt.map] by decide +kernel] at hvs
    obtain ⟨w, rfl, h₁⟩ := sortsOf_one hvs
    obtain ⟨m, rfl⟩ := shape_map hs h₁
    exact ⟨_, rfl⟩

/-- **`_Map_` at every argument list of its signature**: two maps, with a value where they have no
key in common and none where they have one (DOM 227-228). -/
theorem covered_concat {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.map, Srt.map]) :
    ∃ a b, vs = [mp a, mp b] ∧ (Apart a b → ∃ m, hook mapConcat vs = some (some (mp m))) ∧
      (¬ Apart a b → hook mapConcat vs = some none) := by
  obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := sortsOf_two hvs
  obtain ⟨a, rfl⟩ := shape_map hs h₁
  obtain ⟨b, rfl⟩ := shape_map hs h₂
  refine ⟨a, b, rfl, fun h => ?_, concat_common⟩
  obtain ⟨m, hm, -, -⟩ := concat_at (Map.canon_of_sortOf h₁) (Map.canon_of_sortOf h₂) h
  exact ⟨m, hm⟩

/-- **The lookup at every argument list of its signature**: a map and a key, with the bound value
where the map binds the key and none where it does not (DOM 265-268). -/
theorem covered_lookup {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.map, Srt.kitem]) :
    ∃ m k, vs = [mp m, k] ∧ (∀ v, (k, v) ∈ m → hook mapLookup vs = some (some v)) ∧
      (¬ Bound m k → hook mapLookup vs = some none) := by
  obtain ⟨w₁, k, rfl, h₁, -⟩ := sortsOf_two hvs
  obtain ⟨m, rfl⟩ := shape_map hs h₁
  exact ⟨m, k, rfl, fun v h => lookup_at (Map.canon_of_sortOf h₁) h, lookup_off⟩

/-! ## Statement 2: the prose says `#False`, and Γ states ⊥ for every interpretation -/

/-- **Γ of every semantics states ⊥ at two maps with a key in common** (DOM 227-228: "The result is
`#False` if the maps have keys in common"). -/
theorem concat_common_gamma (c : Semantics) {a b : Entries}
    (hvs : c.sortsOf [mp a, mp b] = some [Srt.map, Srt.map]) (h : ¬ Apart a b) :
    Γ c (appP c (sig mapConcat) [mp a, mp b] ≡ ⊥) :=
  gamma_bot c (sig_args (mapConcat, [Srt.map, Srt.map], Srt.map) (by decide)).1 hvs (concat_common h)
    (map_not_silent (mapConcat, "MAP.concat") (by decide) _)

/-- **Γ of every semantics states ⊥ at a map and a key it does not bind** (DOM 267-268: "The value
is `#False` if the key is not in the map"). -/
theorem lookup_off_gamma (c : Semantics) {m : Entries} {k : GroundTerm}
    (hvs : c.sortsOf [mp m, k] = some [Srt.map, Srt.kitem]) (h : ¬ Bound m k) :
    Γ c (appP c (sig mapLookup) [mp m, k] ≡ ⊥) :=
  gamma_bot c (sig_args (mapLookup, [Srt.map, Srt.kitem], Srt.kitem) (by decide)).1 hvs (lookup_off h)
    (map_not_silent (mapLookup, "MAP.lookup") (by decide) _)

/-- Points of the two regions (the expected value is unused): `{1 ↦ 2} {1 ↦ 3}` and
`{1 ↦ 2} {1 ↦ 2}` (the key 1 in both, with another value and with the same),
`{1 ↦ 2, 3 ↦ 4} {3 ↦ 9}`; `{1 ↦ 2}[3]`, `.Map[1]`, `{1 ↦ 2}[2]` (2 is a value, no key). -/
def bots : List Pt :=
  [⟨mapConcat, "MAP.concat", [.m [(1, 2)], .m [(1, 3)]], .i 0⟩,
   ⟨mapConcat, "MAP.concat", [.m [(1, 2)], .m [(1, 2)]], .i 0⟩,
   ⟨mapConcat, "MAP.concat", [.m [(1, 2), (3, 4)], .m [(3, 9)]], .i 0⟩,
   ⟨mapLookup, "MAP.lookup", [.m [(1, 2)], .k 3], .i 0⟩,
   ⟨mapLookup, "MAP.lookup", [.m [], .k 1], .i 0⟩,
   ⟨mapLookup, "MAP.lookup", [.m [(1, 2)], .k 2], .i 0⟩]

theorem bots_ok : bots.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.xs.map A.srt && p.xs.all A.ok && partials.contains p.f &&
    hook p.f (p.xs.map A.val) == some none && !silent p.f (p.xs.map A.val)) = true := by
  decide +kernel

/-- **At each, Γ states ⊥ under every interpretation**, in every semantics with Int below KItem. -/
theorem bots_gamma : ∀ p ∈ bots, ∀ (c : Semantics), IntBelow c → ∀ H : HookParams,
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map A.val) ≡ ⊥) := by
  intro p hp c hI H
  have h := List.all_eq_true.mp bots_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hk, hname⟩, hargs⟩, hok⟩, -⟩, hh⟩, hsl⟩ := h
  exact gamma_bot _ hk (by rw [hargs]; exact A.sortsOf (hI.withHooks H) _ hok)
    (by rw [hname]; exact hh) (by rw [hname]; exact hsl)

/-- **So no interpretation gives these points a value**: over all H, Γ entails ⊥ there, the
negation of the first half of the `param_undetermined` shape (which says Γ entails neither ⊥ nor a
value). MAP has no point of that shape among these rows. -/
theorem bots_entails : ∀ p ∈ bots, ∀ (c : Semantics), IntBelow c → ∀ H : HookParams,
    Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig p.f) (p.xs.map A.val) ≡ ⊥) := by
  intro p hp c hI H M _ I hI'
  exact hI' _ (bots_gamma p hp c hI H)

/-! ## Axioms -/

/-- info: 'KCore.HooksMapTest.vals_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vals_gamma

/-- info: 'KCore.HooksMapTest.vals_hookRes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vals_hookRes

/-- info: 'KCore.HooksMapTest.bots_entails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bots_entails

/-- info: 'KCore.HooksMapTest.concat_common_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concat_common_gamma

/-- info: 'KCore.HooksMapTest.lookup_off_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lookup_off_gamma

/-- info: 'KCore.HooksMapTest.covered_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_total

/-- info: 'KCore.HooksMapTest.covered_concat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_concat

/-- info: 'KCore.HooksMapTest.covered_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_lookup

/-- info: 'KCore.HooksMapTest.map_not_silent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms map_not_silent

/-- info: 'KCore.HooksMapTest.map_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms map_only

/-- info: 'KCore.HooksMapTest.concat_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concat_assoc

/-- info: 'KCore.HooksMapTest.update_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms update_at

/-- info: 'KCore.HooksMapTest.remove_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms remove_at

/-- info: 'KCore.HooksMapTest.removeAll_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms removeAll_at

end KCore.HooksMapTest
