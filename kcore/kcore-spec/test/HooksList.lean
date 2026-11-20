/-
  The supported hook rows of LIST (test/constructs/rows.toml, `hook:LIST.*` with status
  `supported`): the sort row `LIST.List` and the eight operations `LIST.concat`, `unit`, `element`,
  `push`, `get`, `range`, `in`, `size` (`listRows`). Each has its three statements (DONE-0 C2,
  evidence row "supported hook (E6)"). The expectation is the builtin file's prose, cited by line:
  DOM is K 7.1.337's `k-distribution/include/kframework/builtin/domains.md`. No expected value
  below is taken from a run or from `hook`'s text: each value of `vals` is derived by hand from the
  cited sentence (the derivation is written at the point), and at every argument list an operation
  is stated by the sequence of its result (a list is its elements in order, `list_ext`). Run from
  the package root: `lake env lean test/HooksList.lean`. Kernel-checked.

  A list value is `lst es`: `es` its elements in order. An element is a KItem; the points below
  use injected integers (`ki n`), which are KItems in the semantics where Int is below KItem
  (`IntBelow`; `sem_intBelow` and `cU_intBelow` are two).

  1. One in-domain value per operation (`vals`, most operations two or more): `hook`'s value there
     is the hand-derived one (`vals_hook`), it is the result under every interpretation
     (`vals_hookRes`; so also for `L[I]` and `range`, the two keys of `silentTable`), and Γ states
     it under every interpretation (`vals_gamma`).
  2. The regions the prose excludes or leaves unstated. Two of the eight are not declared `total`
     (`L[I]`, DOM 968; `range`, DOM 1017), and of neither does the prose write a `#False`:
     - `L[I]`: "Positive `Int` indices are 0-indexed from the beginning of the list, and negative
       indices are -1-indexed from the end of the list. In other words, 0 is the first element and
       -1 is the last element" (DOM 961-963). An index that is none of the list's (`I < -size` or
       `size ≤ I`) is not spoken of: unstated (DOM 14-16: "some functions in the K prelude
       functions are not total, that is, they are not defined on all possible input values. When
       you invoke such a function on an undefined input, the behavior is undefined").
     - `range`: "removing `fromFront` elements from the front of the list and `fromBack` elements
       from the back of the list" (DOM 1012-1013). A negative count is not spoken of: unstated.
       More elements than the list has (`fromFront + fromBack > size`): two readings, below.
     At a point of each region the `param_undetermined` shape holds: over all interpretations H, Γ
     entails neither ⊥ nor a value (`undetermined`, the schema of test/SilentPoints.lean, at every
     semantics with `coreOK`; `get_off_undetermined`, `range_off_undetermined`; the points `opens`
     and `opensOver` in the semantics `cU`, `opens_undetermined`).
  3. The silent predicate. Six rows are no key of `silentTable` (`list_silentKey`,
     `total_not_silent`) and declared `total`: under `shapesOK` a value of sort List is a list of
     KItems (`list_only`), and they have a value at every argument list of their signature
     (`covered_total`). `L[I]` and `range` are keys with the predicate `fun _ => true`, which is
     read only where `hook` gives no value (`Semantics.hookRes`), so the silent region of each is
     where `hook` gives none: at every argument list of the signature that is exactly the region
     of statement 2 (`covered_get`: a value where `-size ≤ I < size`, none and silent elsewhere;
     `covered_range`: a value where `0 ≤ fromFront`, `0 ≤ fromBack` and
     `fromFront + fromBack ≤ size`, none and silent elsewhere), where the result is the
     interpretation's (`off_hookRes`).

  One row where the text does not say one thing, reported with the ticket (a finding):
  - `range(L, fromFront, fromBack)` at non-negative counts with `fromFront + fromBack > size(L)`.
    The prose (DOM 1012-1013) defines the result by a removal and the production (DOM 1017) is
    not declared `total`. Reading A (taken by `silentTable`, and by the statements below):
    unstated; the sentence names `fromFront` elements of the front and `fromBack` of the back,
    which a shorter list has not, and the function is not `total`, so it has undefined inputs
    (DOM 14-16) and these are the ones a removal of elements that are not there names (beside the
    negative counts). Reading B (a removal is defined whether or not what it removes is present,
    as MAP's `M[K <- undef]`, DOM 295-299, which however is declared `total`): the result is
    `.List`, nothing being left; a stated value, and then `silentTable`'s entry for `range` is
    too wide (it should hold the negative counts only) and `hook` should give `.List` there.
    The points of this part are `opensOver`, kept apart from `opens` (the negative counts, and
    `L[I]` off the list, unstated under both readings).

  The rule of LIST itself, `pushList(K, L1) => ListItem(K) L1` (DOM 955), is proved at every
  argument list (`rule_955`).

  The sort row `LIST.List` (DOM 902-903, 914, 919): `list_value`, `list_ext`, `list_only`; a sort
  has no argument list, so no key of `silentTable` is about it.

  The four rows `LIST.update`, `LIST.make`, `LIST.updateAll`, `LIST.fill` (`stRows`, the last
  section), none declared `total`. The prose names one value on a region of each: "a new `List`
  with a new value at a particular index" (DOM 974-975), at an index of the list; "a list with
  `length` elements, each containing `value`" (984-985), at `length ≥ 0`; "a new `List` which is
  equal to `dest` except the `N` elements starting at `index` are replaced with the contents of
  `src`" (993-994), at `0 ≤ index` and `index + N ≤ K`; "a new `List` where the `length` elements
  starting at `index` are replaced with `value`" (1003-1004), within the list. There `hook` gives
  that value at every argument list (`set_at`, `make_at`, `updateAll_at`, `fill_at`; `set_spec`,
  `updateAll_spec` by the elements of the result) and Γ states it under every interpretation
  (`stVals_gamma`). Elsewhere the prose writes no `#False` ("Having `index + N > K` yields an
  exception", 995, is of a run): `hook` gives no value and every such point is silent
  (`st_silent`, `stOff`), where Γ states the interpretation's (the schema of
  test/SilentPoints.lean). A negative index of `L[I <- V]` is off the list: whether it counts from
  the back, as `L[I]`'s does (961-963), is not said, so no one value is stated there and the point
  is silent.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.HooksListTest

open KCore ML Faithful

/-! ## Γ at an interpreted symbol's application (as test/SilentPoints.lean writes it) -/

/-- The interpreted symbol `k` applied to the values `vs`, as Γ writes it. -/
abbrev appP (c : Semantics) (k : CtorSig) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))

/-- Where `hook` gives a value, Γ states it, in every semantics. -/
theorem gamma_val (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) {v : GroundTerm} (hh : hook k.name vs = some (some v)) :
    Γ c (appP c k vs ≡ den c v) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, some v, hk, hvs, hh, (fun h => nomatch h), rfl⟩)))))

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

/-- The eight supported operation rows of LIST: the symbol and its `hook` attribute in the prose's
productions (DOM 930 `LIST.concat`, 938 `LIST.unit`, 946 `LIST.element`, 954 `LIST.push`,
968 `LIST.get`, 1017 `LIST.range`, 1026 `LIST.in`, 1039 `LIST.size`). The ninth row is the sort
(`LIST.List`, DOM 914). Four more, `update` (DOM 978), `make` (988), `updateAll` (998) and `fill`
(1007), are `stRows` (the last section); `getMInt` 969, `updateMInt` 979, `sizeMInt` 1040 are
refused. -/
def listRows : List (Sym × String) :=
  [(listConcat, "LIST.concat"), (listUnit, "LIST.unit"), (listElem, "LIST.element"),
   (listPush, "LIST.push"), (listGet, "LIST.get"), (listRange, "LIST.range"),
   (listIn, "LIST.in"), (listSize, "LIST.size")]

/-- `L[I <- V]`, `makeList`, `updateList`, `fillList`: the symbol and its `hook` attribute (DOM 978,
988, 998, 1007), none declared `total`. -/
def stRows : List (Sym × String) :=
  [(listSet, "LIST.update"), (listMake, "LIST.make"), (listUpdateAll, "LIST.updateAll"), (listFill, "LIST.fill")]

/-- The two the prose does not declare `total` (DOM 968, 1017). -/
def partials : List Sym := [listGet, listRange]

/-- The six the prose declares `total` (DOM 930, 938, 946, 954, 1026, 1039). -/
def totals : List Sym := [listConcat, listUnit, listElem, listPush, listIn, listSize]

/-- The rows are the registry's entries with a `LIST.` hook, each with its hook name, before the
four of `stRows`. -/
theorem listRows_registry :
    regHookNames.filter (fun e => e.2.toList.take 5 == "LIST.".toList) = listRows ++ stRows := by
  decide +kernel

/-- The signatures, as the prose's productions give them (the lines of `listRows`). -/
def listSigs : List (Sym × List Srt × Srt) :=
  [(listConcat, [Srt.list, Srt.list], Srt.list), (listUnit, [], Srt.list),
   (listElem, [Srt.kitem], Srt.list), (listPush, [Srt.kitem, Srt.list], Srt.list),
   (listGet, [Srt.list, Srt.int], Srt.kitem), (listRange, [Srt.list, Srt.int, Srt.int], Srt.list),
   (listIn, [Srt.kitem, Srt.list], Srt.bool), (listSize, [Srt.list], Srt.int)]

/-- Each row's symbol has that signature among `hookSigs`. -/
theorem listRows_sig : (listRows.map (·.1) == listSigs.map (·.1) &&
    listSigs.all (fun r => decide (sig r.1 ∈ hookSigs) && (sig r.1).name == r.1 &&
      (sig r.1).args == r.2.1 && (sig r.1).result == r.2.2)) = true := by
  decide +kernel

/-- `partialHooks` (the interpreted symbols the totality deciders do not count as total) holds of
these rows exactly the two the prose does not declare `total`; the rows are those two and the six. -/
theorem listRows_partial : (listRows.all (fun r => partialHooks.contains r.1 == partials.contains r.1) &&
    listRows.all (fun r => partials.contains r.1 != totals.contains r.1)) = true := by
  decide +kernel

/-- **The keys of `silentTable` among the rows are exactly those two.** -/
theorem list_silentKey : listRows.all (fun r => silentKey r.1 == partials.contains r.1) = true := by
  decide +kernel

/-! ## Values -/

/-- An integer as a KItem. -/
def ki (n : Int) : GroundTerm := .inj Srt.int Srt.kitem (int n)
/-- A list of the library's sort, by its elements in order. -/
abbrev lst (es : List GroundTerm) : GroundTerm := .list Srt.list es

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

/-! ## The sort row `LIST.List` -/

/-- KItems in any order, with any repetition, are a value of sort List, in every semantics: "lists
of `KItem`" (DOM 902-903), the sort declared at DOM 914; "an ordered collection that may contain
duplicate elements" (DOM 919). -/
theorem list_value (c : Semantics) {es : List GroundTerm}
    (he : ∀ e ∈ es, c.sortOf e = some Srt.kitem) : c.sortOf (lst es) = some Srt.list :=
  sortOf_list_of he

/-- "an ordered collection that may contain duplicate elements" (DOM 919): a list is its elements
in order; two lists are the same value exactly when they have the same elements at the same
places (so `[1, 2]`, `[2, 1]` and `[1, 1, 2]` are three values, `list_distinct`). -/
theorem list_ext {a b : List GroundTerm} : lst a = lst b ↔ a = b := List'.ext

theorem list_distinct : lst [ki 1, ki 2] ≠ lst [ki 2, ki 1] ∧ lst [ki 1, ki 2] ≠ lst [ki 1, ki 1, ki 2] := by
  decide +kernel

/-- Nothing else is a value of sort List (where the sorts the interpreted symbols read have their
shapes, `shapesOK`): a sequence of KItems. -/
theorem list_only {c : Semantics} (hs : c.shapesOK = true) {v : GroundTerm}
    (h : c.sortOf v = some Srt.list) : ∃ es, v = lst es ∧ ∀ e ∈ es, c.sortOf e = some Srt.kitem := by
  obtain ⟨es, rfl⟩ := shape_list hs h
  exact ⟨es, rfl, listOK_of h⟩

/-! ## `hook` at every argument list, by the sequence of the result -/

/-- "concatenating two lists" (DOM 921; "List concatenation", DOM 917), `total` (DOM 930): the
elements of the first, then those of the second. -/
theorem concat_at (a b : List GroundTerm) : hook listConcat [lst a, lst b] = some (some (lst (a ++ b))) := rfl

/-- `assoc` (DOM 930; "associative lists", DOM 902-903). -/
theorem concat_assoc (a b d : List GroundTerm) :
    hook listConcat [lst (a ++ b), lst d] = hook listConcat [lst a, lst (b ++ d)] := by
  rw [concat_at, concat_at, List.append_assoc]

/-- `unit(.List)` (DOM 930): `.List` on either side gives the other list. -/
theorem concat_unit_left (b : List GroundTerm) : hook listConcat [lst [], lst b] = some (some (lst b)) := rfl

theorem concat_unit_right (a : List GroundTerm) : hook listConcat [lst a, lst []] = some (some (lst a)) := by
  rw [concat_at, List.append_nil]

/-- "The list with zero elements is represented by `.List`" (DOM 935): no element. -/
theorem unit_at : hook listUnit [] = some (some (lst [])) := rfl

/-- "An element of a `List` is constucted via the `ListItem` operator" (DOM 943): the one element
`k`. -/
theorem elem_at (k : GroundTerm) : hook listElem [k] = some (some (lst [k])) := rfl

/-- "An element can be added to the front of a `List` using the `pushList` operator" (DOM 951),
`total` (DOM 954): the element, then the list's. -/
theorem push_at (k : GroundTerm) (a : List GroundTerm) :
    hook listPush [k, lst a] = some (some (lst (k :: a))) := rfl

/-- `pushList(K::KItem, L1::List) => ListItem(K) L1` (DOM 955), at every argument list. -/
theorem rule_955 (k : GroundTerm) (a : List GroundTerm) :
    hook listPush [k, lst a] = hook listConcat [lst [k], lst a] := rfl

theorem get_front {a : List GroundTerm} {i : Int} (h0 : 0 ≤ i) (h1 : i < a.length) :
    hook listGet [lst a, int i] = some a[i.toNat]? := by
  show some ((listIndex a.length i).bind (a[·]?)) = _
  unfold listIndex
  simp only [h0, h1, ite_true]; rfl

theorem get_back {a : List GroundTerm} {i : Int} (h0 : i < 0) (h1 : -(a.length : Int) ≤ i) :
    hook listGet [lst a, int i] = some a[a.length - i.natAbs]? := by
  show some ((listIndex a.length i).bind (a[·]?)) = _
  unfold listIndex
  have hn : ¬ 0 ≤ i := by omega
  simp only [hn, h1, ite_true, ite_false]; rfl

/-- "Positive `Int` indices are 0-indexed from the beginning of the list … 0 is the first element"
(DOM 961-963): the index that is the number of elements before it gives the element. -/
theorem get_at_front (f : List GroundTerm) (e : GroundTerm) (b : List GroundTerm) :
    hook listGet [lst (f ++ e :: b), int f.length] = some (some e) := by
  rw [get_front (by omega) (by simp only [List.length_append, List.length_cons]; omega)]
  simp

/-- "negative indices are -1-indexed from the end of the list … -1 is the last element"
(DOM 962-963): minus one, minus the number of elements after it, gives the element. -/
theorem get_at_back (f : List GroundTerm) (e : GroundTerm) (b : List GroundTerm) :
    hook listGet [lst (f ++ e :: b), int (-((b.length : Int) + 1))] = some (some e) := by
  rw [get_back (by omega) (by simp only [List.length_append, List.length_cons]; omega)]
  have : (f ++ e :: b).length - (-((b.length : Int) + 1)).natAbs = f.length := by
    simp only [List.length_append, List.length_cons]; omega
  rw [this]
  simp

/-- An index of the list has a value, an element of the list. -/
theorem get_in {a : List GroundTerm} {i : Int} (h : -(a.length : Int) ≤ i ∧ i < a.length) :
    ∃ e, e ∈ a ∧ hook listGet [lst a, int i] = some (some e) := by
  by_cases h0 : 0 ≤ i
  · have hl : i.toNat < a.length := by omega
    exact ⟨a[i.toNat], List.getElem_mem hl, by rw [get_front h0 h.2, List.getElem?_eq_getElem hl]⟩
  · have hl : a.length - i.natAbs < a.length := by omega
    exact ⟨a[a.length - i.natAbs], List.getElem_mem hl,
      by rw [get_back (by omega) h.1, List.getElem?_eq_getElem hl]⟩

/-- An index that is none of the list's: `hook` gives no value (and the prose says nothing,
DOM 960-968). -/
theorem get_off {a : List GroundTerm} {i : Int} (h : ¬ (-(a.length : Int) ≤ i ∧ i < a.length)) :
    hook listGet [lst a, int i] = some none := by
  show some ((listIndex a.length i).bind (a[·]?)) = _
  unfold listIndex
  by_cases h0 : 0 ≤ i
  · have hn : ¬ i < a.length := by omega
    simp only [h0, hn, ite_true, ite_false]; rfl
  · have hn : ¬ -(a.length : Int) ≤ i := by omega
    simp only [h0, hn, ite_false]; rfl

/-- "removing `fromFront` elements from the front of the list and `fromBack` elements from the
back of the list" (DOM 1012-1013): of `f`, then `r`, then `b`, without the `f.length` first and
the `b.length` last, `r`. -/
theorem range_at (f r b : List GroundTerm) :
    hook listRange [lst (f ++ r ++ b), int f.length, int b.length] = some (some (lst r)) := by
  show some ((listRangeOf (f ++ r ++ b) f.length b.length).map (GroundTerm.list Srt.list)) = _
  unfold listRangeOf
  have hc : 0 ≤ ((f.length : Nat) : Int) ∧ 0 ≤ ((b.length : Nat) : Int) ∧
      ((f.length : Nat) : Int) + (b.length : Nat) ≤ ((f ++ r ++ b).length : Nat) := by
    simp only [List.length_append]; omega
  simp only [hc, and_self, ite_true]
  have h1 : ((f.length : Nat) : Int).toNat = f.length := Int.toNat_natCast _
  have h2 : ((b.length : Nat) : Int).toNat = b.length := Int.toNat_natCast _
  have h3 : (f ++ r ++ b).length - f.length - b.length = r.length := by
    simp only [List.length_append]; omega
  rw [h1, h2, h3, List.append_assoc, List.drop_left, List.take_left]
  rfl

/-- Non-negative counts with as many elements as the list has or fewer split the list so. -/
theorem range_split {a : List GroundTerm} {x y : Int} (h0 : 0 ≤ x) (h1 : 0 ≤ y) (h2 : x + y ≤ a.length) :
    ∃ f r b, a = f ++ r ++ b ∧ (f.length : Int) = x ∧ (b.length : Int) = y := by
  refine ⟨a.take x.toNat, (a.drop x.toNat).take (a.length - x.toNat - y.toNat),
    a.drop (a.length - y.toNat), ?_, ?_, ?_⟩
  · have hd : a.drop (a.length - y.toNat) = (a.drop x.toNat).drop (a.length - x.toNat - y.toNat) := by
      rw [List.drop_drop]; congr 1; omega
    rw [hd, List.append_assoc, List.take_append_drop, List.take_append_drop]
  · rw [List.length_take]; omega
  · rw [List.length_drop]; omega

/-- So at such counts `range` has a value, the middle of the split. -/
theorem range_in {a : List GroundTerm} {x y : Int} (h : 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ a.length) :
    ∃ f r b, a = f ++ r ++ b ∧ (f.length : Int) = x ∧ (b.length : Int) = y ∧
      hook listRange [lst a, int x, int y] = some (some (lst r)) := by
  obtain ⟨f, r, b, rfl, rfl, rfl⟩ := range_split h.1 h.2.1 h.2.2
  exact ⟨f, r, b, rfl, rfl, rfl, range_at f r b⟩

/-- A negative count, or more elements than the list has: `hook` gives no value. -/
theorem range_off {a : List GroundTerm} {x y : Int} (h : ¬ (0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ a.length)) :
    hook listRange [lst a, int x, int y] = some none := by
  show some ((listRangeOf a x y).map (GroundTerm.list Srt.list)) = _
  unfold listRangeOf
  simp only [h, ite_false]; rfl

/-- "You can compute whether an element is in a list" (DOM 1022), `total` (DOM 1026). -/
theorem in_at {a : List GroundTerm} {k : GroundTerm} (h : k ∈ a) :
    hook listIn [k, lst a] = some (some (bool true)) := by
  rw [List'.hook_in, decide_eq_true h]

theorem in_off {a : List GroundTerm} {k : GroundTerm} (h : k ∉ a) :
    hook listIn [k, lst a] = some (some (bool false)) := by
  rw [List'.hook_in, decide_eq_false h]

/-- "You can get the number of elements of a list" (DOM 1031), `total` (DOM 1039): the length,
every occurrence counted. -/
theorem size_at (a : List GroundTerm) : hook listSize [lst a] = some (some (int a.length)) := rfl

/-! ## Statement 1: in-domain values, derived from the prose -/

/-- An argument or a result of a point: a KItem `ki n`, an Int, a Bool, or a list of integers. -/
inductive A where
  | k (n : Int)
  | i (n : Int)
  | b (x : Bool)
  | ls (l : List Int)

def A.val : A → GroundTerm
  | .k n => ki n
  | .i n => int n
  | .b x => bool x
  | .ls l => lst (l.map ki)

def A.srt : A → Srt
  | .k _ => Srt.kitem
  | .i _ => Srt.int
  | .b _ => Srt.bool
  | .ls _ => Srt.list

/-- Such a term is a value of its sort, in every semantics with Int below KItem. -/
theorem A.sorted {c : Semantics} (hI : IntBelow c) : ∀ a : A, c.sortOf a.val = some a.srt
  | .k n => ki_value hI n
  | .i n => int_value c n
  | .b x => bool_value c x
  | .ls l => list_value c fun e he => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
      exact ki_value hI x

theorem A.sortsOf {c : Semantics} (hI : IntBelow c) : ∀ xs : List A,
    c.sortsOf (xs.map A.val) = some (xs.map A.srt)
  | [] => by simp [Semantics.sortsOf]
  | a :: xs => by
    simp [Semantics.sortsOf, A.sorted hI a, A.sortsOf hI xs]

/-- A point: the operation, its hook name, its arguments and a value (the expected one, or at a
point of statement 2 a value of the result sort). -/
structure Pt where
  f : Sym
  name : String
  xs : List A
  v : A

/-- The expected values, each derived by hand from the cited sentence (`n` is the KItem `ki n`,
`[1, 2]` the list of 1 then 2).
- `_List_`: "concatenating two lists" (DOM 921): `[1, 2] [3]` is `[1, 2, 3]`; `[3] [1, 2]` is
  `[3, 1, 2]` (the order of the arguments is the order of the result); `[1] [1]` is `[1, 1]` ("may
  contain duplicate elements", DOM 919); `.List [1]` is `[1]`.
- `.List`: "The list with zero elements" (DOM 935): `[]`.
- `ListItem(1)`: DOM 943: `[1]`.
- `pushList(1, [2, 3])`: "added to the front" (DOM 951): `[1, 2, 3]`; `pushList(2, [2])` is
  `[2, 2]`.
- `L[I]` (DOM 961-963) at `L = [5, 6, 7]`: "0 is the first element": `L[0]` is 5; 0-indexed from
  the beginning, `L[1]` is 6 and `L[2]` is 7; "-1 is the last element": `L[-1]` is 7; -1-indexed
  from the end, `L[-2]` is 6 and `L[-3]` is 5.
- `range` (DOM 1012-1013): `range([1, 2, 3, 4, 5], 1, 2)`: without the first one (1) and the last
  two (4, 5), `[2, 3]`; `range([1, 2], 0, 0)` is `[1, 2]`; `range([1, 2], 1, 1)` is `.List` (both
  removed, as many as the list has); `range([1, 2], 2, 0)` is `.List`; `range([1, 2, 3], 0, 1)` is
  `[1, 2]`.
- `in`: "whether an element is in a list" (DOM 1022): 2 in `[1, 2]`, true; 3 in `[1, 2]`, false.
- `size`: "the number of elements of a list" (DOM 1031): of `[1, 1, 2]`, 3 (the two 1s are two
  elements, DOM 919); of `.List`, 0. -/
def vals : List Pt :=
  [⟨listConcat, "LIST.concat", [.ls [1, 2], .ls [3]], .ls [1, 2, 3]⟩,
   ⟨listConcat, "LIST.concat", [.ls [3], .ls [1, 2]], .ls [3, 1, 2]⟩,
   ⟨listConcat, "LIST.concat", [.ls [1], .ls [1]], .ls [1, 1]⟩,
   ⟨listConcat, "LIST.concat", [.ls [], .ls [1]], .ls [1]⟩,
   ⟨listUnit, "LIST.unit", [], .ls []⟩,
   ⟨listElem, "LIST.element", [.k 1], .ls [1]⟩,
   ⟨listPush, "LIST.push", [.k 1, .ls [2, 3]], .ls [1, 2, 3]⟩,
   ⟨listPush, "LIST.push", [.k 2, .ls [2]], .ls [2, 2]⟩,
   ⟨listGet, "LIST.get", [.ls [5, 6, 7], .i 0], .k 5⟩,
   ⟨listGet, "LIST.get", [.ls [5, 6, 7], .i 1], .k 6⟩,
   ⟨listGet, "LIST.get", [.ls [5, 6, 7], .i 2], .k 7⟩,
   ⟨listGet, "LIST.get", [.ls [5, 6, 7], .i (-1)], .k 7⟩,
   ⟨listGet, "LIST.get", [.ls [5, 6, 7], .i (-2)], .k 6⟩,
   ⟨listGet, "LIST.get", [.ls [5, 6, 7], .i (-3)], .k 5⟩,
   ⟨listRange, "LIST.range", [.ls [1, 2, 3, 4, 5], .i 1, .i 2], .ls [2, 3]⟩,
   ⟨listRange, "LIST.range", [.ls [1, 2], .i 0, .i 0], .ls [1, 2]⟩,
   ⟨listRange, "LIST.range", [.ls [1, 2], .i 1, .i 1], .ls []⟩,
   ⟨listRange, "LIST.range", [.ls [1, 2], .i 2, .i 0], .ls []⟩,
   ⟨listRange, "LIST.range", [.ls [1, 2, 3], .i 0, .i 1], .ls [1, 2]⟩,
   ⟨listIn, "LIST.in", [.k 2, .ls [1, 2]], .b true⟩,
   ⟨listIn, "LIST.in", [.k 3, .ls [1, 2]], .b false⟩,
   ⟨listSize, "LIST.size", [.ls [1, 1, 2]], .i 3⟩,
   ⟨listSize, "LIST.size", [.ls []], .i 0⟩]

/-- Every row has a point, and every point is of a row. -/
theorem vals_rows : (listRows.all (fun r => vals.any fun p => p.f == r.1 && p.name == r.2) &&
    vals.all (fun p => listRows.contains (p.f, p.name))) = true := by
  decide +kernel

/-- **`hook`'s value at each point is the one derived from the prose.** -/
theorem vals_hook : vals.all (fun p => hook p.f (p.xs.map A.val) == some (some p.v.val)) = true := by
  decide +kernel

/-- The arguments of each point are of the signature's argument sorts, and the expected value of
its result sort. -/
theorem vals_sig : vals.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.xs.map A.srt && (sig p.f).result == p.v.srt) = true := by
  decide +kernel

/-- **At each point the result is that value, under every interpretation, in every semantics**
(also at the points of `L[I]` and `range`, the keys of `silentTable`: the interpretation is read
only where `hook` gives no value). -/
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
  obtain ⟨⟨⟨hk, hname⟩, hargs⟩, hres⟩ := h
  have hh : hook p.f (p.xs.map A.val) = some (some p.v.val) := by
    simpa using List.all_eq_true.mp vals_hook p hp
  have hvs : (c.withHooks H).sortsOf (p.xs.map A.val) = some (sig p.f).args := by
    rw [hargs]; exact A.sortsOf (hI.withHooks H) _
  exact ⟨hvs, by rw [hres]; exact A.sorted (hI.withHooks H) _,
    gamma_val _ hk hvs (by rw [hname]; exact hh)⟩

/-! ## Statement 3: the silent predicate against the prose's regions -/

/-- **The six `total` rows are no key of `silentTable`: no point of theirs is silent.** -/
theorem total_not_silent : ∀ f ∈ totals, ∀ vs : List GroundTerm, silent f vs = false :=
  fun f hf vs => silent_of_not_silentKey
    ((by decide +kernel : ∀ f ∈ totals, silentKey f = false) f hf) vs

/-- The predicate of the two keys is `fun _ => true`: it is `hook` giving no value that makes a
point one where the interpretation is read. -/
theorem get_silent (vs : List GroundTerm) : silent listGet vs = true := rfl
theorem range_silent (vs : List GroundTerm) : silent listRange vs = true := rfl

/-- Where `hook` gives no value at a silent point, the result is the interpretation's. -/
theorem off_hookRes (c : Semantics) (H : HookParams) {f : Sym} {vs : List GroundTerm}
    (he : hook f vs = some none) (hs : silent f vs = true) :
    (c.withHooks H).hookRes f vs = some ((c.withHooks H).fallback f vs) :=
  Semantics.hookRes_of_silent he hs

/-- **The six operations declared `total` have a value at every argument list of their
signature**, the one `*_at` describes. -/
theorem covered_total {c : Semantics} (hs : c.shapesOK = true) : ∀ f ∈ totals,
    ∀ vs : List GroundTerm, c.sortsOf vs = some (sig f).args → ∃ v, hook f vs = some (some v) := by
  intro f hf vs hvs
  simp only [totals, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show (sig listConcat).args = [Srt.list, Srt.list] by decide +kernel] at hvs
    obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := sortsOf_two hvs
    obtain ⟨a, rfl⟩ := shape_list hs h₁
    obtain ⟨b, rfl⟩ := shape_list hs h₂
    exact ⟨_, concat_at a b⟩
  · rw [show (sig listUnit).args = [] by decide +kernel] at hvs
    obtain rfl := sortsOf_inv_nil hvs
    exact ⟨_, unit_at⟩
  · rw [show (sig listElem).args = [Srt.kitem] by decide +kernel] at hvs
    obtain ⟨k, rfl, -⟩ := sortsOf_one hvs
    exact ⟨_, elem_at k⟩
  · rw [show (sig listPush).args = [Srt.kitem, Srt.list] by decide +kernel] at hvs
    obtain ⟨k, w, rfl, -, h₂⟩ := sortsOf_two hvs
    obtain ⟨a, rfl⟩ := shape_list hs h₂
    exact ⟨_, push_at k a⟩
  · rw [show (sig listIn).args = [Srt.kitem, Srt.list] by decide +kernel] at hvs
    obtain ⟨k, w, rfl, -, h₂⟩ := sortsOf_two hvs
    obtain ⟨a, rfl⟩ := shape_list hs h₂
    exact ⟨_, List'.hook_in Srt.list a k⟩
  · rw [show (sig listSize).args = [Srt.list] by decide +kernel] at hvs
    obtain ⟨w, rfl, h₁⟩ := sortsOf_one hvs
    obtain ⟨a, rfl⟩ := shape_list hs h₁
    exact ⟨_, size_at a⟩

/-- **`L[I]` at every argument list of its signature**: a list and an integer; where the integer
is an index of the list (`-size ≤ I < size`, DOM 961-963) the value is an element of the list, and
everywhere else `hook` gives none and the point is silent: the silent region is the region the
prose does not speak of. -/
theorem covered_get {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.list, Srt.int]) :
    ∃ a i, vs = [lst a, int i] ∧
      ((-(a.length : Int) ≤ i ∧ i < a.length) → ∃ e, e ∈ a ∧ hook listGet vs = some (some e)) ∧
      (¬ (-(a.length : Int) ≤ i ∧ i < a.length) →
        hook listGet vs = some none ∧ silent listGet vs = true) := by
  obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := sortsOf_two hvs
  obtain ⟨a, rfl⟩ := shape_list hs h₁
  obtain ⟨i, rfl⟩ := shape_int hs h₂
  exact ⟨a, i, rfl, get_in, fun h => ⟨get_off h, rfl⟩⟩

/-- **`range` at every argument list of its signature**: a list and two integers; where both are
non-negative and their sum is at most the size (DOM 1012-1013) the value is the list without that
many first and last elements, and everywhere else `hook` gives none and the point is silent (under
reading B of the header the part `0 ≤ fromFront`, `0 ≤ fromBack`, `fromFront + fromBack > size` of
that region would be stated; see the header). -/
theorem covered_range {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.list, Srt.int, Srt.int]) :
    ∃ a x y, vs = [lst a, int x, int y] ∧
      ((0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ a.length) → ∃ f r b, a = f ++ r ++ b ∧ (f.length : Int) = x ∧
        (b.length : Int) = y ∧ hook listRange vs = some (some (lst r))) ∧
      (¬ (0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ a.length) →
        hook listRange vs = some none ∧ silent listRange vs = true) := by
  obtain ⟨w₁, w₂, w₃, rfl, h₁, h₂, h₃⟩ := sortsOf_three hvs
  obtain ⟨a, rfl⟩ := shape_list hs h₁
  obtain ⟨x, rfl⟩ := shape_int hs h₂
  obtain ⟨y, rfl⟩ := shape_int hs h₃
  exact ⟨a, x, y, rfl, range_in, fun h => ⟨range_off h, rfl⟩⟩

/-! ## Statement 2: the `param_undetermined` shape at the regions the prose leaves unstated -/

theorem sig_get : lookupSig hookSigs listGet = some ⟨listGet, [Srt.list, Srt.int], Srt.kitem⟩ := by
  decide +kernel

theorem sig_range :
    lookupSig hookSigs listRange = some ⟨listRange, [Srt.list, Srt.int, Srt.int], Srt.list⟩ := by
  decide +kernel

/-- **`L[I]` at an index that is none of the list's has the `param_undetermined` shape**, in every
semantics with `coreOK`: over all interpretations Γ entails neither ⊥ nor the KItem `v`. -/
theorem get_off_undetermined (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {a : List GroundTerm} {i : Int} (hvs : c.sortsOf [lst a, int i] = some [Srt.list, Srt.int])
    (h : ¬ (-(a.length : Int) ≤ i ∧ i < a.length)) {v : GroundTerm} (hv : c.sortOf v = some Srt.kitem)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constH v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appP (c.withHooks H) ⟨listGet, [Srt.list, Srt.int], Srt.kitem⟩ [lst a, int i] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appP (c.withHooks H) ⟨listGet, [Srt.list, Srt.int], Srt.kitem⟩ [lst a, int i] ≡
        den (c.withHooks H) v)) :=
  undetermined c hok hr (k := ⟨listGet, [Srt.list, Srt.int], Srt.kitem⟩) sig_get hvs (get_off h) rfl hv
    hfn₀ hfnv

/-- **`range` off its described counts has the `param_undetermined` shape**, in every semantics
with `coreOK` (at the negative counts under both readings of the header; at more elements than the
list has under reading A). -/
theorem range_off_undetermined (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {a : List GroundTerm} {x y : Int}
    (hvs : c.sortsOf [lst a, int x, int y] = some [Srt.list, Srt.int, Srt.int])
    (h : ¬ (0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ a.length)) {v : GroundTerm} (hv : c.sortOf v = some Srt.list)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constH v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appP (c.withHooks H) ⟨listRange, [Srt.list, Srt.int, Srt.int], Srt.list⟩ [lst a, int x, int y] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appP (c.withHooks H) ⟨listRange, [Srt.list, Srt.int, Srt.int], Srt.list⟩ [lst a, int x, int y] ≡
        den (c.withHooks H) v)) :=
  undetermined c hok hr (k := ⟨listRange, [Srt.list, Srt.int, Srt.int], Srt.list⟩) sig_range hvs
    (range_off h) rfl hv hfn₀ hfnv

/-- A semantics with `coreOK`, Int below KItem, the configuration `<k> K </k>` with the generated
counter, and no function (the cells as in ModelSetIdemWitness.lean). -/
def cU : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
    ctors := [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
      ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
      ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
    fns := []
    userSubsorts := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK cU := .of_nil rfl (by decide +kernel)

theorem cU_coreOK : cU.coreOK = true := by decide_cheap

theorem cU_intBelow : IntBelow cU := by unfold IntBelow; decide +kernel

theorem cU_noRaw : ∀ k ∈ cU.params, k.raw = false := by decide +kernel

theorem fnHypU (H : HookParams) : FnHyp (cU.withHooks H) := by
  have h : (cU.withHooks H).fns = [] := rfl
  have hrc : (cU.withHooks H).readsConfined = false :=
    (Semantics.readsConfined_withHooks cU H).trans (by decide +kernel)
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrc, openLaws_of_plain (c := cU.withHooks H) cU_noRaw⟩ <;> intro fn hfn <;> rw [h] at hfn <;>
    exact absurd hfn List.not_mem_nil

/-- Points the prose leaves unstated under every reading; `v` is a value of the result sort (the
KItem 0, `.List`). `[1][3]`, `[1][1]` (the size is no index), `.List[0]`, `[1, 2][-3]` (one before
the first from the end); `range([1], -1, 0)`, `range([1, 2], 0, -1)`, `range(.List, -1, -1)`. -/
def opens : List Pt :=
  [⟨listGet, "LIST.get", [.ls [1], .i 3], .k 0⟩,
   ⟨listGet, "LIST.get", [.ls [1], .i 1], .k 0⟩,
   ⟨listGet, "LIST.get", [.ls [], .i 0], .k 0⟩,
   ⟨listGet, "LIST.get", [.ls [1, 2], .i (-3)], .k 0⟩,
   ⟨listRange, "LIST.range", [.ls [1], .i (-1), .i 0], .ls []⟩,
   ⟨listRange, "LIST.range", [.ls [1, 2], .i 0, .i (-1)], .ls []⟩,
   ⟨listRange, "LIST.range", [.ls [], .i (-1), .i (-1)], .ls []⟩]

/-- Points of `range` with more elements to remove than the list has, unstated under reading A of
the header only (reading B: `.List`): `range([1], 1, 1)`, `range([1, 2, 3], 5, 0)`,
`range(.List, 0, 1)`. -/
def opensOver : List Pt :=
  [⟨listRange, "LIST.range", [.ls [1], .i 1, .i 1], .ls []⟩,
   ⟨listRange, "LIST.range", [.ls [1, 2, 3], .i 5, .i 0], .ls []⟩,
   ⟨listRange, "LIST.range", [.ls [], .i 0, .i 1], .ls []⟩]

/-- At every point: the symbol's signature, its arguments of the argument sorts, no value of
`hook`, a silent point, `v` of exactly the result sort, and a row not declared `total`. -/
theorem opens_ok : (opens ++ opensOver).all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
    cU.sortsOf (p.xs.map A.val) == some (sig p.f).args && hook p.f (p.xs.map A.val) == some none &&
    silent p.f (p.xs.map A.val) && cU.sortOf p.v.val == some (sig p.f).result &&
    partials.contains p.f && listRows.contains (p.f, p.name)) = true := by
  decide +kernel

/-- The points of `opens` lie in the regions unstated under both readings (an index that is none
of the list's; a negative count), those of `opensOver` in the other part of `range`'s. -/
theorem opens_regions :
    (opens.all (fun p => match p.xs with
      | [.ls a, .i i] => p.f == listGet && !(decide (-(a.length : Int) ≤ i) && decide (i < a.length))
      | [.ls _, .i x, .i y] => p.f == listRange && (decide (x < 0) || decide (y < 0))
      | _ => false) &&
    opensOver.all (fun p => match p.xs with
      | [.ls a, .i x, .i y] => p.f == listRange && decide (0 ≤ x) && decide (0 ≤ y) &&
          decide ((a.length : Int) < x + y)
      | _ => false)) = true := by
  decide +kernel

/-- **Γ determines none of the points**: over all interpretations it entails neither that the
application has no value nor that it is the point's `v`. -/
theorem opens_undetermined : ∀ p ∈ opens ++ opensOver,
    ¬ (∀ H : HookParams, Γ (cU.withHooks H) ⊧ (appP (cU.withHooks H) (sig p.f) (p.xs.map A.val) ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (cU.withHooks H) ⊧
      (appP (cU.withHooks H) (sig p.f) (p.xs.map A.val) ≡ den (cU.withHooks H) p.v.val)) := by
  intro p hp
  have h := List.all_eq_true.mp opens_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hks, hvs⟩, hh⟩, hs⟩, hv⟩, -⟩, -⟩ := h
  have hname : (sig p.f).name = p.f := (lookupSig_spec hks).2
  exact undetermined cU cU_coreOK cU_noRaw (by rw [hname]; exact hks) hvs (by rw [hname]; exact hh)
    (by rw [hname]; exact hs) hv (fnHypU _) (fnHypU _)

/-! ## Axioms -/

/-- info: 'KCore.HooksListTest.vals_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vals_gamma

/-- info: 'KCore.HooksListTest.vals_hookRes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vals_hookRes

/-- info: 'KCore.HooksListTest.opens_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms opens_undetermined

/-- info: 'KCore.HooksListTest.get_off_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms get_off_undetermined

/-- info: 'KCore.HooksListTest.range_off_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms range_off_undetermined

/-- info: 'KCore.HooksListTest.covered_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_total

/-- info: 'KCore.HooksListTest.covered_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_get

/-- info: 'KCore.HooksListTest.covered_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_range

/-- info: 'KCore.HooksListTest.total_not_silent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms total_not_silent

/-- info: 'KCore.HooksListTest.off_hookRes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms off_hookRes

/-- info: 'KCore.HooksListTest.list_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms list_only

/-- info: 'KCore.HooksListTest.range_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms range_at

/-- info: 'KCore.HooksListTest.get_at_front' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms get_at_front

/-- info: 'KCore.HooksListTest.get_at_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms get_at_back

/-! ## `L[I <- V]`, `makeList`, `updateList`, `fillList`

The four rows of `stRows`, none declared `total` (DOM 978, 988, 998, 1007). Each is a key of
`silentTable` with `fun _ => true`: where `hook` gives no value the prose names none and writes no
`#False`, so the point is silent. On the described region `hook` gives the one value the prose
names. -/

/-- The signatures, as the prose's productions give them. -/
def stSigs : List (Sym × List Srt × Srt) :=
  [(listSet, [Srt.list, Srt.int, Srt.kitem], Srt.list), (listMake, [Srt.int, Srt.kitem], Srt.list),
   (listUpdateAll, [Srt.list, Srt.int, Srt.list], Srt.list),
   (listFill, [Srt.list, Srt.int, Srt.int, Srt.kitem], Srt.list)]

theorem stRows_sig : (stRows.map (·.1) == stSigs.map (·.1) &&
    stSigs.all (fun r => decide (sig r.1 ∈ hookSigs) && (sig r.1).name == r.1 &&
      (sig r.1).args == r.2.1 && (sig r.1).result == r.2.2) &&
    stRows.all (fun r => partialHooks.contains r.1 && regHookOf r.2 == some r.1)) = true := by
  decide +kernel

/-- No library module has one of the four among its parameter symbols. -/
theorem st_not_param : (List.range library.length).all (fun i =>
    (libParams [i]).all fun p => !(stRows.map (·.1)).contains p.sig.name) = true := by
  decide +kernel

/-- **Every point of the four where `hook` gives no value is silent.** -/
theorem st_silent : ∀ r ∈ stRows, ∀ vs : List GroundTerm, silent r.1 vs = true := by
  intro r hr vs
  simp only [stRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> rfl

/-- "You can create a new `List` with a new value at a particular index" (DOM 974-975), at an index
of the list, `0 ≤ I < size`: the list with `V` at `I`. Off it (a negative index among them: the
prose's convention of DOM 961-963 is stated of `L[I]`), no value and silent. -/
theorem set_at (a : List GroundTerm) (i : Int) (v : GroundTerm) :
    hook listSet [lst a, int i, v] =
      some (if 0 ≤ i ∧ i < a.length then some (lst (a.set i.toNat v)) else none) := by
  show some ((asInt (int i)).bind fun i => if 0 ≤ i ∧ i < a.length then
    some (GroundTerm.list Srt.list (a.set i.toNat v)) else none) = _
  simp [asInt, int]

/-- "a list with `length` elements, each containing `value`" (DOM 984-985), at `length ≥ 0`. -/
theorem make_at (n : Int) (v : GroundTerm) :
    hook listMake [int n, v] = some (if 0 ≤ n then some (lst (List.replicate n.toNat v)) else none) := by
  show some ((asInt (int n)).bind fun n => if 0 ≤ n then
    some (GroundTerm.list Srt.list (List.replicate n.toNat v)) else none) = _
  simp [asInt, int]

/-- "a new `List` which is equal to `dest` except the `N` elements starting at `index` are replaced
with the contents of `src`" (DOM 993-994), `N` the size of `src`, at `0 ≤ index` and
`index + N ≤ size(dest)`. -/
theorem updateAll_at (d : List GroundTerm) (i : Int) (s : List GroundTerm) :
    hook listUpdateAll [lst d, int i, lst s] =
      some (if 0 ≤ i ∧ i + s.length ≤ d.length then
        some (lst (d.take i.toNat ++ s ++ d.drop (i.toNat + s.length))) else none) := by
  show some ((asInt (int i)).bind fun i => if 0 ≤ i ∧ i + s.length ≤ d.length then
    some (GroundTerm.list Srt.list (d.take i.toNat ++ s ++ d.drop (i.toNat + s.length))) else none) = _
  simp [asInt, int]

/-- "a new `List` where the `length` elements starting at `index` are replaced with `value`"
(DOM 1003-1004), at `0 ≤ index`, `0 ≤ length` and `index + length ≤ size`. -/
theorem fill_at (d : List GroundTerm) (i n : Int) (v : GroundTerm) :
    hook listFill [lst d, int i, int n, v] =
      some (if 0 ≤ i ∧ 0 ≤ n ∧ i + n ≤ d.length then
        some (lst (d.take i.toNat ++ List.replicate n.toNat v ++ d.drop (i.toNat + n.toNat))) else none) := by
  show some ((asInt (int i)).bind fun i => (asInt (int n)).bind fun n => if 0 ≤ i ∧ 0 ≤ n ∧ i + n ≤ d.length then
    some (GroundTerm.list Srt.list (d.take i.toNat ++ List.replicate n.toNat v ++ d.drop (i.toNat + n.toNat)))
    else none) = _
  simp [asInt, int]

/-- In range, `L[I <- V]` has `V` at `I` and the elements of `L` at every other index, and the
size of `L` (the list "with a new value at a particular index"). -/
theorem set_spec {a : List GroundTerm} {i : Int} (v : GroundTerm) (h0 : 0 ≤ i) (h1 : i < a.length) :
    ∃ r, hook listSet [lst a, int i, v] = some (some (lst r)) ∧ r.length = a.length ∧
      r[i.toNat]? = some v ∧ ∀ j, j ≠ i.toNat → r[j]? = a[j]? := by
  refine ⟨a.set i.toNat v, by rw [set_at, if_pos ⟨h0, h1⟩], List.length_set, ?_, ?_⟩
  · rw [List.getElem?_set_self (by omega)]
  · intro j hj; rw [List.getElem?_set_ne (Ne.symm hj)]

/-- In range, `updateList(D, I, S)` has the elements of `S` at `I` … `I + size(S) - 1` and those of
`D` elsewhere, and the size of `D`. -/
theorem updateAll_spec {d s : List GroundTerm} {i : Int} (h0 : 0 ≤ i) (h1 : i + s.length ≤ d.length) :
    ∃ r, hook listUpdateAll [lst d, int i, lst s] = some (some (lst r)) ∧ r.length = d.length ∧
      (∀ j < s.length, r[i.toNat + j]? = s[j]?) ∧
      (∀ j, (j < i.toNat ∨ i.toNat + s.length ≤ j) → r[j]? = d[j]?) := by
  refine ⟨d.take i.toNat ++ s ++ d.drop (i.toNat + s.length), by rw [updateAll_at, if_pos ⟨h0, h1⟩], ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_take, List.length_drop]; omega
  · intro j hj
    have ht : (d.take i.toNat).length = i.toNat := by rw [List.length_take]; omega
    rw [List.append_assoc, List.getElem?_append_right (by omega), ht, Nat.add_sub_cancel_left,
      List.getElem?_append_left hj]
  · intro j hj
    have ht : (d.take i.toNat).length = i.toNat := by rw [List.length_take]; omega
    rcases hj with hj | hj
    · rw [List.append_assoc, List.getElem?_append_left (by omega), List.getElem?_take_of_lt hj]
    · rw [List.append_assoc, List.getElem?_append_right (by omega), ht, List.getElem?_append_right (by omega),
        List.getElem?_drop]
      congr 1; omega

/-- In-range points, each derived from the prose: `[1, 2][1 <- 3]` is `[1, 3]` (the value at index
1, the second, replaced); `makeList(2, 7)` is `[7, 7]`, `makeList(0, 7)` is `.List`;
`updateList([1, 2, 3], 1, [8, 9])` is `[1, 8, 9]` (the two elements from index 1 replaced by 8 and
9); `fillList([1, 2, 3], 1, 2, 7)` is `[1, 7, 7]` (the two elements from index 1 replaced by 7). -/
def stVals : List Pt :=
  [⟨listSet, "LIST.update", [.ls [1, 2], .i 1, .k 3], .ls [1, 3]⟩,
   ⟨listMake, "LIST.make", [.i 2, .k 7], .ls [7, 7]⟩, ⟨listMake, "LIST.make", [.i 0, .k 7], .ls []⟩,
   ⟨listUpdateAll, "LIST.updateAll", [.ls [1, 2, 3], .i 1, .ls [8, 9]], .ls [1, 8, 9]⟩,
   ⟨listFill, "LIST.fill", [.ls [1, 2, 3], .i 1, .i 2, .k 7], .ls [1, 7, 7]⟩]

theorem stVals_ok : stVals.all (fun p => stRows.contains (p.f, p.name) && decide (sig p.f ∈ hookSigs) &&
    (sig p.f).name == p.f && (sig p.f).args == p.xs.map A.srt && (sig p.f).result == p.v.srt &&
    hook p.f (p.xs.map A.val) == some (some p.v.val)) = true := by
  decide +kernel

/-- **At each in-range point Γ states the value under every interpretation**, in every semantics
with Int below KItem. -/
theorem stVals_gamma : ∀ p ∈ stVals, ∀ (c : Semantics), IntBelow c → ∀ H : HookParams,
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map A.val) ≡ den (c.withHooks H) p.v.val) := by
  intro p hp c hI H
  have h := List.all_eq_true.mp stVals_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hk⟩, hname⟩, hargs⟩, -⟩, hh⟩ := h
  have hvs : (c.withHooks H).sortsOf (p.xs.map A.val) = some (sig p.f).args := by
    rw [hargs]; exact A.sortsOf (hI.withHooks H) _
  exact gamma_val _ hk hvs (by rw [hname]; exact hh)

/-- Off-range points: `[1][1 <- 3]` (an index equal to the size), `[1][-1 <- 3]` (a negative index:
whether it counts from the back, as of `L[I]`, is not said), `makeList(-1, 7)`,
`updateList([1, 2], 1, [8, 9])` (`index + N > K`, which "yields an exception", DOM 995, no
`#False`), `updateList([1], -1, .List)`, `fillList([1], 0, 2, 7)`, `fillList([1], 0, -1, 7)`: `hook`
gives no value, and the point is silent. The value component is not read. -/
def stOff : List Pt :=
  [⟨listSet, "LIST.update", [.ls [1], .i 1, .k 3], .ls []⟩,
   ⟨listSet, "LIST.update", [.ls [1], .i (-1), .k 3], .ls []⟩,
   ⟨listMake, "LIST.make", [.i (-1), .k 7], .ls []⟩,
   ⟨listUpdateAll, "LIST.updateAll", [.ls [1, 2], .i 1, .ls [8, 9]], .ls []⟩,
   ⟨listUpdateAll, "LIST.updateAll", [.ls [1], .i (-1), .ls []], .ls []⟩,
   ⟨listFill, "LIST.fill", [.ls [1], .i 0, .i 2, .k 7], .ls []⟩,
   ⟨listFill, "LIST.fill", [.ls [1], .i 0, .i (-1), .k 7], .ls []⟩]

theorem stOff_ok : stOff.all (fun p => stRows.contains (p.f, p.name) && (sig p.f).args == p.xs.map A.srt &&
    hook p.f (p.xs.map A.val) == some none && silent p.f (p.xs.map A.val)) = true := by
  decide +kernel

/-- At every point of `stOff`, in the semantics `cU`: the symbol's signature, its arguments of the
argument sorts, no value of `hook`, a silent point, and `.List` a value of the result sort. -/
theorem stOff_cU : stOff.all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
    cU.sortsOf (p.xs.map A.val) == some (sig p.f).args && hook p.f (p.xs.map A.val) == some none &&
    silent p.f (p.xs.map A.val) && cU.sortOf p.v.val == some (sig p.f).result) = true := by
  decide +kernel

/-- **Γ determines none of the off-range points of the four**: over all interpretations it entails
neither that the application has no value nor that it is `.List` (the `param_undetermined` shape,
by the schema `undetermined`, in the semantics `cU`). -/
theorem stOff_undetermined : ∀ p ∈ stOff,
    ¬ (∀ H : HookParams, Γ (cU.withHooks H) ⊧ (appP (cU.withHooks H) (sig p.f) (p.xs.map A.val) ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (cU.withHooks H) ⊧
      (appP (cU.withHooks H) (sig p.f) (p.xs.map A.val) ≡ den (cU.withHooks H) p.v.val)) := by
  intro p hp
  have h := List.all_eq_true.mp stOff_cU p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hks, hvs⟩, hh⟩, hs⟩, hv⟩ := h
  have hname : (sig p.f).name = p.f := (lookupSig_spec hks).2
  exact undetermined cU cU_coreOK cU_noRaw (by rw [hname]; exact hks) hvs (by rw [hname]; exact hh)
    (by rw [hname]; exact hs) hv (fnHypU _) (fnHypU _)

/-- info: 'KCore.HooksListTest.stOff_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stOff_undetermined

/-- `HookParams.lib` (LibAdmitted.lean) gives none of the four a value at any point, as it gave
none while they were parameter symbols: the values above are `hook`'s, at points where it gave
none, and off range it gives none still. -/
theorem lib_st_none : ∀ r ∈ stRows, ∀ vs : List GroundTerm, HookParams.lib.app r.1 vs = none := by
  intro r hr vs
  simp only [stRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> rfl

#print axioms set_spec
#print axioms updateAll_spec
#print axioms stVals_gamma
#print axioms st_silent
#print axioms lib_st_none

end KCore.HooksListTest
