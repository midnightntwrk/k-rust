/-
  The supported hook rows of SET (test/constructs/rows.toml, `hook:SET.*` with status `supported`):
  the sort row `SET.Set` and the nine operations `SET.unit`, `element`, `concat`, `union`,
  `intersection`, `difference`, `in`, `inclusion`, `size` (`setRows`). Each has its three statements
  (DONE-0 C2, evidence row "supported hook (E6)"). The expectation is the builtin file's prose,
  cited by line: DOM is K 7.1.337's `k-distribution/include/kframework/builtin/domains.md`. No
  expected value below is taken from a run or from `hook`'s text: each value of `vals` is derived by
  hand from the cited sentence (the derivation is written at the point), and at every argument list
  an operation is stated by the members of its result (which elements a set holds is what the prose
  speaks of), the result being the one set with those members (`set_ext`). Run from the package
  root: `lake env lean test/HooksSet.lean`. Kernel-checked.

  A set value is `st es`: `es` its members, strictly increasing. A member is a KItem; the points
  below use injected integers (`ki n`), which are KItems in the semantics where Int is below KItem
  (`IntBelow`; every statement at a point is for every such semantics and every interpretation H,
  `sem_intBelow` is one).

  1. One in-domain value per operation (`vals`, most operations two): `hook`'s value there is the
     hand-derived one (`vals_hook`), it is the result under every interpretation (`vals_hookRes`),
     and Γ states it under every interpretation (`vals_gamma`).
  2. The regions the prose excludes or leaves unstated. One of the nine is not declared `total`
     (`_Set_`, DOM 721), and the prose states its value off its domain: "the concatenation of two
     sets containing elements in common is `#False`" (DOM 706-707). `#False` is a statement of the
     value (none), so the region is stated, not left open: Γ states ⊥ at every point of it
     (`concat_common_gamma`), under every interpretation (`bots_entails`), which is the negation of
     the first half of the `param_undetermined` shape (over all H, Γ entails neither ⊥ nor a
     value). The other eight are declared `total`. No point of these rows has the
     `param_undetermined` shape. The sentence goes on "(note however, this may be silently allowed
     during concrete execution)": that is said of a run, beside the `#False`, and takes nothing
     from it.
  3. The silent predicate: none of the nine is a key of `silentTable` (`set_not_silentKey`), so its
     silent region is empty (`set_not_silent`), and the prose covers every argument list: under
     `shapesOK` a value of sort Set is a set of KItems with strictly increasing members
     (`set_only`), the eight `total` operations have a value at every argument list of their
     signature (`covered_total`), and `_Set_` has one where no member is common and none where one
     is (`covered_concat`).

  Two rows where the text does not say one thing. Both are written with their two readings; the
  one the statements below take is named, and both are reported with the ticket.
  - `_Set_` at two sets with a common member. The prose: "The sets are nilpotent, i.e., the
    concatenation of two sets containing elements in common is `#False`" (DOM 706-707), and "If you
    intend to add an element to a set that might already be present in the set, use the `|Set`
    operator instead" (DOM 708-709). The production (DOM 721) carries the attribute `idem`, which
    read as an equation says `S S = S`, a value at two equal sets. Reading A (taken, the prose's
    sentence, a stated value): no value wherever a member is common, so none at `S S` for a
    nonempty `S` (`concat_self`). Reading B (the attribute): `S S` is `S`. They differ at every
    nonempty set. Neither leaves the value unstated, so under either the point has not the
    `param_undetermined` shape and the row is no key of `silentTable`.
  - `<=Set` at two equal sets. The prose: "You can determine whether a `Set` is a strict subset of
    another `Set`" (DOM 782-783), under the heading "Set inclusion" (DOM 780), the symbol written
    `<=Set` and hooked `SET.inclusion` (DOM 786), declared `total`. Reading A (taken): inclusion,
    every member of the first is a member of the second, true at two equal sets (the heading, the
    symbol and the hook name; "another `Set`" speaks of two different sets, where an included set
    is a strict subset). Reading B (the word "strict" at every pair): false at two equal sets. They
    differ at equal sets only. `vals` holds no point at equal sets; the value there under reading
    A is `incl_at` at `a = b` (`incl_refl`) and the points `readingA`.
  Neither row's two readings leave a value open, so neither is a finding against `silentTable`.

  The rule of SET itself, `S1 |Set S2 => S1 (S2 -Set S1)` (DOM 749, `[concrete]`), is proved at
  every pair of sets (`rule_749`). The rules of SET-KORE-SYMBOLIC are introduced as "lemmas …
  simplifications that the Haskell backend can apply to simplify expressions of sort `Set`" (DOM
  813-814): consequences the file states, not definitions; those proved below (`rule_835`,
  `rule_836`, `rule_855`, `rule_865`, `rule_876`) follow from the `*_at` statements.

  The sort row `SET.Set` (DOM 689-690, 700, 705): `set_value`, `set_of_members`, `set_nodup`,
  `set_ext`, `set_only`; a sort has no argument list, so no key of `silentTable` is about it.
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.HooksSetTest

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

/-- The nine supported operation rows of SET: the symbol and its `hook` attribute in the prose's
productions (DOM 729 `SET.unit`, 737 `SET.element`, 721 `SET.concat`, 748 `SET.union`,
759 `SET.intersection`, 769 `SET.difference`, 777 `SET.in`, 786 `SET.inclusion`, 794 `SET.size`).
The tenth row is the sort (`SET.Set`, DOM 700). SET's other hook (`choice`, DOM 804) is a
parameter in rows.toml, not a supported row. -/
def setRows : List (Sym × String) :=
  [(setUnit, "SET.unit"), (setElem, "SET.element"), (setConcat, "SET.concat"),
   (setUnion, "SET.union"), (setIntersect, "SET.intersection"), (setDifference, "SET.difference"),
   (setIn, "SET.in"), (setInclusion, "SET.inclusion"), (setSize, "SET.size")]

/-- The one the prose does not declare `total` (DOM 721), with its `#False` sentence
(DOM 706-707). -/
def partials : List Sym := [setConcat]

/-- The eight the prose declares `total` (DOM 729, 737, 748, 759, 769, 777, 786, 794). -/
def totals : List Sym :=
  [setUnit, setElem, setUnion, setIntersect, setDifference, setIn, setInclusion, setSize]

/-- The rows are the registry's entries with a `SET.` hook, each with its hook name. -/
theorem setRows_registry :
    regHookNames.filter (fun e => e.2.toList.take 4 == "SET.".toList) = setRows := by
  decide +kernel

/-- The signatures, as the prose's productions give them (the lines of `setRows`). -/
def setSigs : List (Sym × List Srt × Srt) :=
  [(setUnit, [], Srt.set), (setElem, [Srt.kitem], Srt.set),
   (setConcat, [Srt.set, Srt.set], Srt.set), (setUnion, [Srt.set, Srt.set], Srt.set),
   (setIntersect, [Srt.set, Srt.set], Srt.set), (setDifference, [Srt.set, Srt.set], Srt.set),
   (setIn, [Srt.kitem, Srt.set], Srt.bool), (setInclusion, [Srt.set, Srt.set], Srt.bool),
   (setSize, [Srt.set], Srt.int)]

/-- Each row's symbol has that signature among `hookSigs`. -/
theorem setRows_sig : (setRows.map (·.1) == setSigs.map (·.1) &&
    setSigs.all (fun r => decide (sig r.1 ∈ hookSigs) && (sig r.1).name == r.1 &&
      (sig r.1).args == r.2.1 && (sig r.1).result == r.2.2)) = true := by
  decide +kernel

/-- `partialHooks` (the interpreted symbols the totality deciders do not count as total) holds of
these rows exactly the one the prose does not declare `total`; the rows are that one and the
eight. -/
theorem setRows_partial : (setRows.all (fun r => partialHooks.contains r.1 == partials.contains r.1) &&
    setRows.all (fun r => partials.contains r.1 != totals.contains r.1)) = true := by
  decide +kernel

/-! ## Values -/

/-- An integer as a KItem. -/
def ki (n : Int) : GroundTerm := .inj Srt.int Srt.kitem (int n)
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

/-! ## The sort row `SET.Set` -/

/-- No member of `a` is a member of `b`. -/
def Apart (a b : List GroundTerm) : Prop := ∀ x ∈ a, x ∉ b

theorem Apart.symm {a b : List GroundTerm} (h : Apart a b) : Apart b a :=
  fun x hb ha => h x ha hb

/-- KItems, strictly increasing, are a value of sort Set, in every semantics: "sets of `KItem`"
(DOM 689-690), the sort declared at DOM 700. -/
theorem set_value (c : Semantics) {es : List GroundTerm} (hs : elemsSorted es = true)
    (he : ∀ e ∈ es, c.sortOf e = some Srt.kitem) : c.sortOf (st es) = some Srt.set :=
  sortOf_setS.mpr ⟨_, collOf_set, rfl, hs, he, rfl⟩

/-- Every finite list of elements is the members of one strictly increasing list: every finite
collection of KItems is represented, whatever its order and its repetitions. -/
theorem set_of_members (L : List GroundTerm) : ∃ es, elemsSorted es = true ∧ ∀ x, x ∈ es ↔ x ∈ L :=
  ⟨unionS L [], Set.union_canon rfl, fun x => by rw [Set.mem_union]; simp⟩

/-- "a mathematical set (A collection of unique items)" (DOM 705): a set holds no element twice. -/
theorem set_nodup {es : List GroundTerm} (hs : elemsSorted es = true) : es.Nodup :=
  (elemsSorted_iff.mp hs).imp fun h he => by rw [he, GroundTerm.cmp_refl] at h; cases h

/-- "associative, commutative sets" (DOM 689-690): a set is its members, in no order; two sets with
the same members are the same value. -/
theorem set_ext {a b : List GroundTerm} (ha : elemsSorted a = true) (hb : elemsSorted b = true)
    (h : ∀ x, x ∈ a ↔ x ∈ b) : st a = st b := by
  rw [Set.ext ha hb h]

/-- Nothing else is a value of sort Set (where the sorts the interpreted symbols read have their
shapes, `shapesOK`): KItems, strictly increasing. -/
theorem set_only {c : Semantics} (hs : c.shapesOK = true) {v : GroundTerm}
    (h : c.sortOf v = some Srt.set) : ∃ es, v = st es ∧ elemsSorted es = true ∧
      ∀ e ∈ es, c.sortOf e = some Srt.kitem := by
  obtain ⟨es, rfl⟩ := shape_set hs h
  exact ⟨es, rfl, Set.canon_of_sortOf h, (setOK_of h).2⟩

/-! ## `hook` at every argument list, by the members of the result -/

/-- "The set with zero elements is represented by `.Set`" (DOM 726): no member. -/
theorem unit_at : hook setUnit [] = some (some (st [])) := rfl

/-- "An element of a `Set` is constructed via the `SetItem` operator" (DOM 734): the one member
`k`. -/
theorem elem_at (k : GroundTerm) : hook setElem [k] = some (some (st [k])) := rfl

theorem concat_val {a b u : List GroundTerm} (h : concatS a b = some u) :
    hook setConcat [st a, st b] = some (some (st u)) := by
  rw [hook_setConcat, h]; rfl

/-- The concatenation (DOM 703-709, 721) of two sets with no member in common: the set whose
members are those of the one and of the other. -/
theorem concat_at {a b : List GroundTerm} (hb : elemsSorted b = true) (h : Apart a b) :
    ∃ u, hook setConcat [st a, st b] = some (some (st u)) ∧ elemsSorted u = true ∧
      ∀ x, x ∈ u ↔ x ∈ a ∨ x ∈ b :=
  ⟨unionS a b, concat_val (Model.concatS_iff.mpr ⟨h, rfl⟩), Set.union_canon hb, fun x => Set.mem_union x a b⟩

/-- "the concatenation of two sets containing elements in common is `#False`" (DOM 706-707): no
value. -/
theorem concat_common {a b : List GroundTerm} (h : ¬ Apart a b) : hook setConcat [st a, st b] = some none := by
  rw [hook_setConcat]
  cases hu : concatS a b with
  | none => rfl
  | some u => exact absurd (Model.concatS_iff.mp hu).1 h

/-- The same at a common member named. -/
theorem concat_common_mem {a b : List GroundTerm} {x : GroundTerm} (ha : x ∈ a) (hb : x ∈ b) :
    hook setConcat [st a, st b] = some none :=
  concat_common fun h => h x ha hb

/-- "The sets are nilpotent" (DOM 706): a nonempty set with itself has no value (reading A of the
header; the attribute `idem` of DOM 721, read as `S S = S`, says otherwise). -/
theorem concat_self {a : List GroundTerm} (h : a ≠ []) : hook setConcat [st a, st a] = some none := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil a h
  exact concat_common_mem hx hx

/-- `comm` (DOM 721; "commutative", DOM 689-690): the two orders give the same result, a value or
none. -/
theorem concat_comm {a b : List GroundTerm} (ha : elemsSorted a = true) (hb : elemsSorted b = true) :
    hook setConcat [st a, st b] = hook setConcat [st b, st a] := by
  by_cases h : Apart a b
  · obtain ⟨u, h1, s1, m1⟩ := concat_at hb h
    obtain ⟨u', h2, s2, m2⟩ := concat_at ha h.symm
    have hu : u = u' := Set.ext s1 s2 fun x => by rw [m1, m2, or_comm]
    rw [h1, h2, hu]
  · rw [concat_common h, concat_common fun h' => h h'.symm]

/-- `unit(.Set)` (DOM 721): `.Set` on either side gives the other set. -/
theorem concat_unit_left (b : List GroundTerm) : hook setConcat [st [], st b] = some (some (st b)) := rfl

theorem concat_unit_right {a : List GroundTerm} (ha : elemsSorted a = true) :
    hook setConcat [st a, st []] = some (some (st a)) := by
  rw [concat_comm ha rfl]; rfl

/-- "The union consists of all the elements present in either set" (DOM 744-745), `total`
(DOM 748). -/
theorem union_at (a : List GroundTerm) {b : List GroundTerm} (hb : elemsSorted b = true) :
    ∃ u, hook setUnion [st a, st b] = some (some (st u)) ∧ elemsSorted u = true ∧
      ∀ x, x ∈ u ↔ x ∈ a ∨ x ∈ b :=
  ⟨unionS a b, rfl, Set.union_canon hb, fun x => Set.mem_union x a b⟩

/-- "The intersection consists of all the elements present in both sets" (DOM 755-756), `total`
(DOM 759). -/
theorem intersect_at {a : List GroundTerm} (ha : elemsSorted a = true) (b : List GroundTerm) :
    ∃ u, hook setIntersect [st a, st b] = some (some (st u)) ∧ elemsSorted u = true ∧
      ∀ x, x ∈ u ↔ x ∈ a ∧ x ∈ b :=
  ⟨a.filter (memS · b), rfl, Set.filter_canon ha _, fun x => Set.mem_inter x a b⟩

/-- "This is the set of elements in the first set that are not present in the second set"
(DOM 765-766), `total` (DOM 769). -/
theorem difference_at {a : List GroundTerm} (ha : elemsSorted a = true) (b : List GroundTerm) :
    ∃ u, hook setDifference [st a, st b] = some (some (st u)) ∧ elemsSorted u = true ∧
      ∀ x, x ∈ u ↔ x ∈ a ∧ x ∉ b :=
  ⟨a.filter (!memS · b), rfl, Set.filter_canon ha _, fun x => Set.mem_diff x a b⟩

/-- "You can compute whether an element is a member of a set" (DOM 774), `total` (DOM 777). -/
theorem in_at {a : List GroundTerm} {k : GroundTerm} (h : k ∈ a) :
    hook setIn [k, st a] = some (some (bool true)) := by
  rw [hook_setIn, (Set.memS_iff k a).mpr h]

theorem in_off {a : List GroundTerm} {k : GroundTerm} (h : k ∉ a) :
    hook setIn [k, st a] = some (some (bool false)) := by
  rw [hook_setIn, Bool.eq_false_iff.mpr fun hm => h ((Set.memS_iff k a).mp hm)]

theorem hook_inclusion (a b : List GroundTerm) :
    hook setInclusion [st a, st b] = some (some (bool (a.all (memS · b)))) := rfl

/-- "Set inclusion" (DOM 780-783), `total` (DOM 786): true where every member of the first set is a
member of the second (reading A of the header at two equal sets). -/
theorem incl_at {a b : List GroundTerm} (h : ∀ x ∈ a, x ∈ b) :
    hook setInclusion [st a, st b] = some (some (bool true)) := by
  rw [hook_inclusion, List.all_eq_true.mpr fun x hx => (Set.memS_iff x b).mpr (h x hx)]

/-- False where a member of the first set is no member of the second (under both readings). -/
theorem incl_off {a b : List GroundTerm} {x : GroundTerm} (ha : x ∈ a) (hb : x ∉ b) :
    hook setInclusion [st a, st b] = some (some (bool false)) := by
  rw [hook_inclusion, Bool.eq_false_iff.mpr fun hall =>
    hb ((Set.memS_iff x b).mp (List.all_eq_true.mp hall x ha))]

/-- At two equal sets: true (reading A; reading B, "strict subset" at every pair, says false). -/
theorem incl_refl (a : List GroundTerm) : hook setInclusion [st a, st a] = some (some (bool true)) :=
  incl_at fun _ h => h

/-- "the number of elements (the cardinality) of a set" (DOM 791), `total` (DOM 794): the number of
members (a set holds none twice, `set_nodup`). -/
theorem size_at (a : List GroundTerm) : hook setSize [st a] = some (some (int a.length)) := rfl

/-! ## The rule of SET, and rules of SET-KORE-SYMBOLIC (DOM 813-814 on their status) -/

/-- `S1:Set |Set S2:Set => S1 (S2 -Set S1)` (DOM 749): the union is the concatenation of the first
set and the second without the first's members, at every pair of sets. -/
theorem rule_749 {a b : List GroundTerm} (hb : elemsSorted b = true) :
    ∃ d, hook setDifference [st b, st a] = some (some (st d)) ∧
      hook setConcat [st a, st d] = hook setUnion [st a, st b] := by
  obtain ⟨d, hd, sd, md⟩ := difference_at hb a
  refine ⟨d, hd, ?_⟩
  have hu : concatS a d = some (unionS a b) :=
    Model.concatS_of sd (Set.union_canon hb) (fun x hx hxd => ((md x).mp hxd).2 hx) fun x => by
      rw [Set.mem_union, md]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · by_cases hx : x ∈ a
          · exact Or.inl hx
          · exact Or.inr ⟨h, hx⟩
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr h.1
  rw [concat_val hu]; rfl

/-- `S -Set .Set => S` (DOM 835). -/
theorem rule_835 {a : List GroundTerm} (ha : elemsSorted a = true) :
    hook setDifference [st a, st []] = some (some (st a)) := by
  obtain ⟨u, h, su, mu⟩ := difference_at ha []
  rw [h, set_ext su ha fun x => by rw [mu]; simp]

/-- `.Set -Set _ => .Set` (DOM 836). -/
theorem rule_836 (b : List GroundTerm) : hook setDifference [st [], st b] = some (some (st [])) := rfl

/-- `S |Set S => S` (DOM 855). -/
theorem rule_855 {a : List GroundTerm} (ha : elemsSorted a = true) :
    hook setUnion [st a, st a] = some (some (st a)) := by
  obtain ⟨u, h, su, mu⟩ := union_at a ha
  rw [h, set_ext su ha fun x => by rw [mu, or_self]]

/-- `intersectSet(S, S) => S` (DOM 865). -/
theorem rule_865 {a : List GroundTerm} (ha : elemsSorted a = true) :
    hook setIntersect [st a, st a] = some (some (st a)) := by
  obtain ⟨u, h, su, mu⟩ := intersect_at ha a
  rw [h, set_ext su ha fun x => by rw [mu, and_self]]

/-- `_E in .Set => false` (DOM 876). -/
theorem rule_876 (k : GroundTerm) : hook setIn [k, st []] = some (some (bool false)) :=
  in_off (by simp)

/-! ## Statement 1: in-domain values, derived from the prose -/

/-- An argument or a result of a point: a KItem `ki n`, an Int, a Bool, or a set of integers (its
members, as written). -/
inductive A where
  | k (n : Int)
  | i (n : Int)
  | b (x : Bool)
  | s (l : List Int)

def A.val : A → GroundTerm
  | .k n => ki n
  | .i n => int n
  | .b x => bool x
  | .s l => st (l.map ki)

def A.srt : A → Srt
  | .k _ => Srt.kitem
  | .i _ => Srt.int
  | .b _ => Srt.bool
  | .s _ => Srt.set

/-- The members are written strictly increasing, as a value has them. -/
def A.ok : A → Bool
  | .s l => elemsSorted (l.map ki)
  | _ => true

/-- Such a term is a value of its sort, in every semantics with Int below KItem. -/
theorem A.sorted {c : Semantics} (hI : IntBelow c) : ∀ a : A, a.ok = true → c.sortOf a.val = some a.srt
  | .k n, _ => ki_value hI n
  | .i n, _ => int_value c n
  | .b x, _ => bool_value c x
  | .s l, h => set_value c h fun e he => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
      exact ki_value hI x

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
`{1, 2}` the set of 1 and 2).
- `.Set`: "The set with zero elements" (DOM 726): no member.
- `SetItem(1)`: "An element of a `Set` is constructed via the `SetItem` operator" (DOM 734): `{1}`.
- `_Set_` (DOM 703-709): of `{1}` and `{2, 3}`, which have no member in common, `{1, 2, 3}`, in
  either order; of `.Set` and `{1}`, `{1}`.
- `|Set`: "all the elements present in either set" (DOM 744-745): of `{1, 2}` and `{2, 3}`, the
  elements 1, 2 (of the first) and 2, 3 (of the second): `{1, 2, 3}`; of `{1}` and `{1}`, `{1}`
  (where `_Set_` has no value).
- `intersectSet`: "all the elements present in both sets" (DOM 755-756): of `{1, 2, 3}` and
  `{2, 3, 4}`, 2 and 3 are in both, 1 and 4 in one: `{2, 3}`; of `{1}` and `{2}`, `.Set`.
- `-Set`: "the set of elements in the first set that are not present in the second set"
  (DOM 765-766): `{1, 2, 3} -Set {2, 4}`: 1 and 3 are not in `{2, 4}`, 2 is: `{1, 3}` (4 is not in
  the first); `{1} -Set {1, 2}` is `.Set`.
- `in`: "whether an element is a member of a set" (DOM 774): 2 in `{1, 2}`, true; 3 in `{1, 2}`,
  false.
- `<=Set` (DOM 780-783), at pairs of different sets, where both readings of the header agree:
  `{1} <=Set {1, 2}`, true (1 is in the second, and the second has 2 besides);
  `{1, 3} <=Set {1, 2}`, false (3 is not in the second); `.Set <=Set {1}`, true;
  `{1, 2} <=Set {1}`, false (2 is not in the second).
- `size`: "the number of elements (the cardinality)" (DOM 791): of `{1, 2, 3}`, 3; of `.Set`, 0. -/
def vals : List Pt :=
  [⟨setUnit, "SET.unit", [], .s []⟩,
   ⟨setElem, "SET.element", [.k 1], .s [1]⟩,
   ⟨setConcat, "SET.concat", [.s [1], .s [2, 3]], .s [1, 2, 3]⟩,
   ⟨setConcat, "SET.concat", [.s [2, 3], .s [1]], .s [1, 2, 3]⟩,
   ⟨setConcat, "SET.concat", [.s [], .s [1]], .s [1]⟩,
   ⟨setUnion, "SET.union", [.s [1, 2], .s [2, 3]], .s [1, 2, 3]⟩,
   ⟨setUnion, "SET.union", [.s [1], .s [1]], .s [1]⟩,
   ⟨setIntersect, "SET.intersection", [.s [1, 2, 3], .s [2, 3, 4]], .s [2, 3]⟩,
   ⟨setIntersect, "SET.intersection", [.s [1], .s [2]], .s []⟩,
   ⟨setDifference, "SET.difference", [.s [1, 2, 3], .s [2, 4]], .s [1, 3]⟩,
   ⟨setDifference, "SET.difference", [.s [1], .s [1, 2]], .s []⟩,
   ⟨setIn, "SET.in", [.k 2, .s [1, 2]], .b true⟩,
   ⟨setIn, "SET.in", [.k 3, .s [1, 2]], .b false⟩,
   ⟨setInclusion, "SET.inclusion", [.s [1], .s [1, 2]], .b true⟩,
   ⟨setInclusion, "SET.inclusion", [.s [1, 3], .s [1, 2]], .b false⟩,
   ⟨setInclusion, "SET.inclusion", [.s [], .s [1]], .b true⟩,
   ⟨setInclusion, "SET.inclusion", [.s [1, 2], .s [1]], .b false⟩,
   ⟨setSize, "SET.size", [.s [1, 2, 3]], .i 3⟩,
   ⟨setSize, "SET.size", [.s []], .i 0⟩]

/-- `<=Set` at two equal sets, under reading A of the header (true); reading B says false at
both. Kept apart from `vals`: the prose does not settle these two values. -/
def readingA : List Pt :=
  [⟨setInclusion, "SET.inclusion", [.s [1, 2], .s [1, 2]], .b true⟩,
   ⟨setInclusion, "SET.inclusion", [.s [], .s []], .b true⟩]

/-- Every row has a point, and every point is of a row. -/
theorem vals_rows : (setRows.all (fun r => vals.any fun p => p.f == r.1 && p.name == r.2) &&
    (vals ++ readingA).all (fun p => setRows.contains (p.f, p.name))) = true := by
  decide +kernel

/-- **`hook`'s value at each point is the one derived from the prose.** -/
theorem vals_hook : vals.all (fun p => hook p.f (p.xs.map A.val) == some (some p.v.val)) = true := by
  decide +kernel

/-- `hook`'s value at two equal sets is reading A's. -/
theorem readingA_hook : readingA.all (fun p => hook p.f (p.xs.map A.val) == some (some p.v.val)) = true := by
  decide +kernel

/-- The arguments of each point are written as values (increasing members) of the signature's
argument sorts, and the expected value as one of its result sort. -/
def sigOK (p : Pt) : Bool :=
  decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    (sig p.f).args == p.xs.map A.srt && p.xs.all A.ok && p.v.ok && (sig p.f).result == p.v.srt

theorem vals_sig : (vals ++ readingA).all sigOK = true := by
  decide +kernel

/-- **At each point the result is that value, under every interpretation, in every semantics.** -/
theorem vals_hookRes : ∀ p ∈ vals, ∀ (c : Semantics) (H : HookParams),
    (c.withHooks H).hookRes p.f (p.xs.map A.val) = some (some p.v.val) :=
  fun p hp _ _ => Semantics.hookRes_of_value (by simpa using List.all_eq_true.mp vals_hook p hp)

/-- Γ at a point whose value `hook` gives and which is written at its signature. -/
theorem pt_gamma {p : Pt} (hs : sigOK p = true)
    (hh : hook p.f (p.xs.map A.val) = some (some p.v.val)) (c : Semantics) (hI : IntBelow c)
    (H : HookParams) :
    (c.withHooks H).sortsOf (p.xs.map A.val) = some (sig p.f).args ∧
    (c.withHooks H).sortOf p.v.val = some (sig p.f).result ∧
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map A.val) ≡ den (c.withHooks H) p.v.val) := by
  simp only [sigOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨hk, hname⟩, hargs⟩, hok⟩, hvok⟩, hres⟩ := hs
  have hvs : (c.withHooks H).sortsOf (p.xs.map A.val) = some (sig p.f).args := by
    rw [hargs]; exact A.sortsOf (hI.withHooks H) _ hok
  exact ⟨hvs, by rw [hres]; exact A.sorted (hI.withHooks H) _ hvok,
    gamma_val _ hk hvs (by rw [hname]; exact hh)⟩

/-- **At each point Γ states that value, under every interpretation**, in every semantics with Int
below KItem: there the arguments are values of the signature's sorts and the expected value one of
the result sort. -/
theorem vals_gamma : ∀ p ∈ vals, ∀ (c : Semantics), IntBelow c → ∀ H : HookParams,
    (c.withHooks H).sortsOf (p.xs.map A.val) = some (sig p.f).args ∧
    (c.withHooks H).sortOf p.v.val = some (sig p.f).result ∧
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map A.val) ≡ den (c.withHooks H) p.v.val) :=
  fun p hp c hI H =>
    pt_gamma (List.all_eq_true.mp vals_sig p (List.mem_append_left _ hp))
      (by simpa using List.all_eq_true.mp vals_hook p hp) c hI H

/-- At two equal sets Γ states reading A's value (true), under every interpretation: what KCore
takes there, whichever reading is confirmed. -/
theorem readingA_gamma : ∀ p ∈ readingA, ∀ (c : Semantics), IntBelow c → ∀ H : HookParams,
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) (p.xs.map A.val) ≡ den (c.withHooks H) p.v.val) :=
  fun p hp c hI H =>
    (pt_gamma (List.all_eq_true.mp vals_sig p (List.mem_append_right _ hp))
      (by simpa using List.all_eq_true.mp readingA_hook p hp) c hI H).2.2

/-! ## Statement 3: no silent region; the prose covers every argument list -/

/-- **None of the nine is a key of `silentTable`.** -/
theorem set_not_silentKey : ∀ r ∈ setRows, silentKey r.1 = false := by decide +kernel

/-- **The silent predicate of each is false at every argument list**: the region the prose leaves
unstated is empty. -/
theorem set_not_silent : ∀ r ∈ setRows, ∀ vs : List GroundTerm, silent r.1 vs = false :=
  fun r hr vs => silent_of_not_silentKey (set_not_silentKey r hr) vs

theorem sig_args : ∀ r ∈ setSigs, sig r.1 ∈ hookSigs ∧ (sig r.1).name = r.1 ∧ (sig r.1).args = r.2.1 := by
  decide +kernel

/-- **The eight operations declared `total` have a value at every argument list of their
signature**, the one `*_at` describes. -/
theorem covered_total {c : Semantics} (hs : c.shapesOK = true) : ∀ f ∈ totals,
    ∀ vs : List GroundTerm, c.sortsOf vs = some (sig f).args → ∃ v, hook f vs = some (some v) := by
  intro f hf vs hvs
  simp only [totals, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show (sig setUnit).args = [] by decide +kernel] at hvs
    obtain rfl := sortsOf_inv_nil hvs
    exact ⟨_, unit_at⟩
  · rw [show (sig setElem).args = [Srt.kitem] by decide +kernel] at hvs
    obtain ⟨k, rfl, -⟩ := sortsOf_one hvs
    exact ⟨_, elem_at k⟩
  · rw [show (sig setUnion).args = [Srt.set, Srt.set] by decide +kernel] at hvs
    obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := sortsOf_two hvs
    obtain ⟨a, rfl⟩ := shape_set hs h₁
    obtain ⟨b, rfl⟩ := shape_set hs h₂
    exact ⟨_, rfl⟩
  · rw [show (sig setIntersect).args = [Srt.set, Srt.set] by decide +kernel] at hvs
    obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := sortsOf_two hvs
    obtain ⟨a, rfl⟩ := shape_set hs h₁
    obtain ⟨b, rfl⟩ := shape_set hs h₂
    exact ⟨_, rfl⟩
  · rw [show (sig setDifference).args = [Srt.set, Srt.set] by decide +kernel] at hvs
    obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := sortsOf_two hvs
    obtain ⟨a, rfl⟩ := shape_set hs h₁
    obtain ⟨b, rfl⟩ := shape_set hs h₂
    exact ⟨_, rfl⟩
  · rw [show (sig setIn).args = [Srt.kitem, Srt.set] by decide +kernel] at hvs
    obtain ⟨k, w, rfl, -, h₂⟩ := sortsOf_two hvs
    obtain ⟨a, rfl⟩ := shape_set hs h₂
    exact ⟨_, hook_setIn Srt.set a k⟩
  · rw [show (sig setInclusion).args = [Srt.set, Srt.set] by decide +kernel] at hvs
    obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := sortsOf_two hvs
    obtain ⟨a, rfl⟩ := shape_set hs h₁
    obtain ⟨b, rfl⟩ := shape_set hs h₂
    exact ⟨_, hook_inclusion a b⟩
  · rw [show (sig setSize).args = [Srt.set] by decide +kernel] at hvs
    obtain ⟨w, rfl, h₁⟩ := sortsOf_one hvs
    obtain ⟨a, rfl⟩ := shape_set hs h₁
    exact ⟨_, size_at a⟩

/-- **`_Set_` at every argument list of its signature**: two sets, with a value where they have no
member in common and none where they have one (DOM 706-707). -/
theorem covered_concat {c : Semantics} (hs : c.shapesOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.set, Srt.set]) :
    ∃ a b, vs = [st a, st b] ∧ (Apart a b → ∃ u, hook setConcat vs = some (some (st u))) ∧
      (¬ Apart a b → hook setConcat vs = some none) := by
  obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := sortsOf_two hvs
  obtain ⟨a, rfl⟩ := shape_set hs h₁
  obtain ⟨b, rfl⟩ := shape_set hs h₂
  refine ⟨a, b, rfl, fun h => ?_, concat_common⟩
  obtain ⟨u, hu, -, -⟩ := concat_at (Set.canon_of_sortOf h₂) h
  exact ⟨u, hu⟩

/-! ## Statement 2: the prose says `#False`, and Γ states ⊥ for every interpretation -/

/-- **Γ of every semantics states ⊥ at two sets with a member in common** (DOM 706-707: "the
concatenation of two sets containing elements in common is `#False`"). -/
theorem concat_common_gamma (c : Semantics) {a b : List GroundTerm}
    (hvs : c.sortsOf [st a, st b] = some [Srt.set, Srt.set]) (h : ¬ Apart a b) :
    Γ c (appP c (sig setConcat) [st a, st b] ≡ ⊥) :=
  gamma_bot c (sig_args (setConcat, [Srt.set, Srt.set], Srt.set) (by decide)).1 hvs (concat_common h)
    (set_not_silent (setConcat, "SET.concat") (by decide) _)

/-- Points of the region (the expected value is unused): `{1} {1}` and `{1, 2} {1, 2}` (a nonempty
set with itself, where the attribute `idem` read as an equation would give the set),
`{1, 2} {2, 3}` (the member 2 in both). -/
def bots : List Pt :=
  [⟨setConcat, "SET.concat", [.s [1], .s [1]], .i 0⟩,
   ⟨setConcat, "SET.concat", [.s [1, 2], .s [1, 2]], .i 0⟩,
   ⟨setConcat, "SET.concat", [.s [1, 2], .s [2, 3]], .i 0⟩]

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
value). SET has no point of that shape among these rows. -/
theorem bots_entails : ∀ p ∈ bots, ∀ (c : Semantics), IntBelow c → ∀ H : HookParams,
    Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig p.f) (p.xs.map A.val) ≡ ⊥) := by
  intro p hp c hI H M _ I hI'
  exact hI' _ (bots_gamma p hp c hI H)

/-! ## Axioms -/

/-- info: 'KCore.HooksSetTest.vals_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vals_gamma

/-- info: 'KCore.HooksSetTest.vals_hookRes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vals_hookRes

/-- info: 'KCore.HooksSetTest.readingA_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms readingA_gamma

/-- info: 'KCore.HooksSetTest.bots_entails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bots_entails

/-- info: 'KCore.HooksSetTest.concat_common_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concat_common_gamma

/-- info: 'KCore.HooksSetTest.covered_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_total

/-- info: 'KCore.HooksSetTest.covered_concat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covered_concat

/-- info: 'KCore.HooksSetTest.set_not_silent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms set_not_silent

/-- info: 'KCore.HooksSetTest.set_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms set_only

/-- info: 'KCore.HooksSetTest.concat_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concat_comm

/-- info: 'KCore.HooksSetTest.rule_749' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_749

/-- info: 'KCore.HooksSetTest.union_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms union_at

/-- info: 'KCore.HooksSetTest.intersect_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intersect_at

/-- info: 'KCore.HooksSetTest.difference_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms difference_at

end KCore.HooksSetTest
