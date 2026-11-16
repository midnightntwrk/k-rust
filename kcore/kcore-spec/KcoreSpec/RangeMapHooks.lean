/-
  KCore. RANGEMAP's interpreted symbols (domains.md 468-696, K 7.1.337), on the carrier the
  collection kind `CollKind.rangeMap` names: a range map is `GroundTerm.map` whose keys are the
  `Range` terms `[a, b)` (`RangeMap:Range` applied to two Ints injected into KItem, `a < b`) of
  the maximal intervals of a partial function from Int to KItem, in the order of their lower
  bounds (`rangesOK`, with the range terms in Value.lean, where `sortOf` reads it).

  The fifteen symbols RANGEMAP hooks to a function of its values are interpreted: fourteen in
  `rangeMapHooks`, and `keys` (620-625: "a `Set` of all the ranges in a `RangeMap`", `total`) in
  `rangeMapKeysHooks`, its function `rmKeysHook`; the two are the last parts of `hookTable`, and
  they and the functions they read are in Hooks.lean, which `hookTable` is in, with `rmV`. `keys`
  stands apart because of what its value is. A Set's members are KItems, and the only KItem a
  range gives is its injection `inj{Range, KItem}`, which is a value exactly in a semantics where
  Range is below KItem. `r r|-> v` at a Range value r and a KItem value v is a range map value in
  every semantics that has them, and in one where Range is not below KItem the member of its keys
  is no value. So the fourteen give a value of their result sort in every semantics
  (`rangeMapHook_sorted`), and `keys` where every Range value is a KItem (`RangeBelow`,
  `rmK_keys_sorted`), which every semantics with a range term of sort Range that `srReady`
  accepts is (`rangeKeysOK`); a semantics with no Range value has only the empty range map, whose
  keys are the empty Set.

  What the text states (line numbers of domains.md):
  - 498-500: a map "whose keys are stored as ranges, bounded inclusively below and exclusively
    above. Contiguous or overlapping ranges that map to the same value are merged into a single
    range": a value is the function, its description by maximal intervals is unique, and two
    descriptions of one function are one value (`rmCanon`).
  - 471-477: keys are Ints only.
  - 600-602: concatenation is "a partial function only defined on range maps with non overlapping
    ranges": undefined where two intervals meet (`rmConcat`), not silent (503-504 also name a run's
    exception there; "only defined on" states that there is no value, as for `_Map_`, 228-229).
  - 534-535, 555-556: `lookup` and `find_range` off the keys "yield an exception during concrete
    execution", of a run, and no `#False` (Map lookup writes one, 267-268): silent there (the
    reading `silentTable` takes for `memsetBytes`).
  - `r|->`, update, `[_ <- undef]` and `removeAll` at a range that is no proper Int range: the text
    describes only ranges of Int keys bounded inclusively below and exclusively above (471-477,
    498-499): silent there. These six are `silentTable`'s RANGEMAP rows (`rangeMapSilent`).
  - 663-671: `<=RangeMap`, `total`, the template of `<=Set` (780-786): inclusion of functions,
    `true` at two equal maps (the reading `setHooks` takes; the sentence at 665 speaks of two
    different maps, where a subset is a strict subset).
  - `choice` (676-679, "an arbitrarily chosen key"), `keys_list` and `values` (630, 648: a List "of
    all" ranges or values, no order stated) are not interpreted: parameters, the text leaving
    their values open.
-/
import KcoreSpec.Hooks

set_option autoImplicit false

namespace KCore

/-- RANGEMAP's silent points: where `rangeMapHooks` gives no value and the text does not say
there is none. A range argument that is not a proper Int range (`r|->`, `update`, `[_ <- undef]`,
`removeAll`), and a key in no interval (`lookup`, `find_range`). These are the RANGEMAP rows of
`silentTable` (`rangeMapSilent_silentTable`). -/
def rangeMapSilent : List (Sym × (List GroundTerm → Bool)) :=
  [(rmElem, fun _ => true), (rmLookup, fun _ => true), (rmFindRange, fun _ => true),
   (rmUpdate, fun _ => true), (rmRemove, fun _ => true), (rmRemoveAll, fun _ => true)]

/-- `silentTable` holds `rangeMapSilent`'s rows: the same keys, each silent everywhere. -/
theorem rangeMapSilent_silentTable : ∀ e ∈ rangeMapSilent, silentKey e.1 = true ∧ ∀ vs, silent e.1 vs = true := by
  intro e he
  simp only [rangeMapSilent, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide +kernel, fun _ => rfl⟩

/-- The value of an interpreted RANGEMAP symbol at `vs`, by the table. -/
def rmHook (f : Sym) (vs : List GroundTerm) : Option (Option GroundTerm) :=
  (rangeMapHooks.find? (·.1 == f)).map fun (_, h) => h vs

/-! ## The carrier's lemmas -/


/-- An Int injected into KItem has one sort whatever the Int. -/
theorem sortOf_kint (c : Semantics) (a b : Int) : c.sortOf (kint a) = c.sortOf (kint b) := by
  simp [kint, int, Semantics.sortOf, dvOK, GroundTerm.isInj]

/-- Whether an overload covers two injected Ints does not depend on the Ints (`lies` reads the
injection's sort only). -/
theorem uncovered_kint (c : Semantics) (f : Sym) (a b a' b' : Int) :
    c.uncovered f [kint a, kint b] = c.uncovered f [kint a', kint b'] := by
  unfold Semantics.uncovered Semantics.ovlCovers
  rcases c.lookupOvl f with _ | o
  · rfl
  · simp only
    congr 1; funext kg
    congr 1
    generalize kg.args.zip o.sig.args = l
    rcases l with _ | ⟨p, _ | ⟨q, l⟩⟩ <;> rfl

/-- **A range's sort does not depend on its bounds**, in every semantics: the new range terms that
merging and cutting build have the sort of the ranges given. -/
theorem sortOf_rangeT (c : Semantics) (a b a' b' : Int) : c.sortOf (rangeT a b) = c.sortOf (rangeT a' b') := by
  have hs : c.sortsOf [kint a, kint b] = c.sortsOf [kint a', kint b'] := by
    simp only [Semantics.sortsOf, sortOf_kint c a a', sortOf_kint c b b']
  simp only [rangeT, Semantics.sortOf, hs, uncovered_kint c rangeCtor a b a' b']

/-- The entries of a range map value are triples: every key is a proper range. -/
theorem rmTriples_of_rangesOK : ∀ {es : Entries}, rangesOK es = true → (rmTriples es).isSome = true
  | [], _ => rfl
  | [(k, v)], h => by
    simp only [rangesOK] at h
    obtain ⟨⟨x, y⟩, hk⟩ := Option.isSome_iff_exists.mp h
    simp [rmTriples, hk]
  | (k, v) :: (k', v') :: es, h => by
    simp only [rangesOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have ih := rmTriples_of_rangesOK h2
    cases hk : asRange k with
    | none => simp [hk] at h1
    | some p =>
      unfold rmTriples at ih ⊢
      rw [List.mapM_cons]
      simp only [hk]
      obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.mp ih
      simp [hts]


/-- A proper range term reads back as its bounds. -/
theorem asRange_rangeT {a b : Int} (h : a < b) : asRange (rangeT a b) = some (a, b) := by
  simp [asRange, rangeT, asKInt, kint, asInt, int, h]

/-- Insertion by lower bound permutes. -/
theorem rmInsert_perm (t : RmTriple) : ∀ l : List RmTriple, (rmInsert t l).Perm (t :: l)
  | [] => .refl _
  | u :: us => by
    unfold rmInsert
    split
    · exact .refl _
    · exact ((rmInsert_perm t us).cons u).trans (.swap t u us)

/-- Insertion keeps the lower bounds in order. -/
theorem rmInsert_sorted (t : RmTriple) : ∀ l : List RmTriple, l.Pairwise (fun x y => x.1 ≤ y.1) →
    (rmInsert t l).Pairwise (fun x y => x.1 ≤ y.1)
  | [], _ => by simp [rmInsert]
  | u :: us, h => by
    unfold rmInsert
    split
    · rename_i htu
      refine List.Pairwise.cons (fun x hx => ?_) h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact htu
      · exact Int.le_trans htu (List.rel_of_pairwise_cons h hx)
    · rename_i htu
      refine List.Pairwise.cons (fun x hx => ?_) (rmInsert_sorted t us h.of_cons)
      rcases List.mem_cons.mp ((rmInsert_perm t us).mem_iff.mp hx) with rfl | hx
      · omega
      · exact List.rel_of_pairwise_cons h hx

/-- Insertion sort by lower bound. -/
theorem rmSort_perm : ∀ ts : List RmTriple, (ts.foldr rmInsert []).Perm ts
  | [] => .refl _
  | t :: ts => (rmInsert_perm t _).trans ((rmSort_perm ts).cons t)

theorem rmSort_sorted : ∀ ts : List RmTriple, (ts.foldr rmInsert []).Pairwise (fun x y => x.1 ≤ y.1)
  | [] => .nil
  | t :: ts => rmInsert_sorted t _ (rmSort_sorted ts)

/-- Merging keeps the lower bound and the value of the first interval. -/
theorem rmMerge_head : ∀ (t : RmTriple) (ts : List RmTriple), ∃ b, (rmMerge (t :: ts)).head? = some (t.1, b, t.2.2)
  | (_, b, _), [] => ⟨b, by simp [rmMerge]⟩
  | (a, b, v), (a', b', v') :: ts => by
    unfold rmMerge
    split
    · obtain ⟨b'', h⟩ := rmMerge_head (a, b', v) ts
      exact ⟨b'', h⟩
    · exact ⟨b, rfl⟩
  termination_by _ ts => ts.length

/-- Each interval ends at or before the next begins. -/
def RChain : List RmTriple → Prop
  | t :: u :: r => t.2.1 ≤ u.1 ∧ RChain (u :: r)
  | _ => True

/-- The first key of a range map value is a proper range. -/
theorem rangesOK_head {k v : GroundTerm} {es : Entries} (h : rangesOK ((k, v) :: es) = true) :
    (asRange k).isSome = true := by
  cases es with
  | nil => simpa [rangesOK] using h
  | cons e es =>
    obtain ⟨k', v'⟩ := e
    simp only [rangesOK, Bool.and_eq_true] at h
    cases hk : asRange k with
    | none => simp [hk] at h
    | some _ => rfl

/-- Proper intervals, each ending at or before the next begins, merged: maximal intervals in order. -/
theorem rangesOK_rmMerge : ∀ (l : List RmTriple), (∀ t ∈ l, t.1 < t.2.1) →
    RChain l → rangesOK ((rmMerge l).map fun (a, b, v) => (rangeT a b, v)) = true
  | [], _, _ => by simp [rmMerge, rangesOK]
  | [(a, b, v)], hp, _ => by
    have := hp _ (List.mem_singleton_self _)
    simp [rmMerge, rangesOK, asRange_rangeT this]
  | (a, b, v) :: (a', b', v') :: ts, hp, hc => by
    have h1 := hp _ (List.mem_cons_self ..)
    have h2 := hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only at h1 h2
    have hbb : b ≤ a' := hc.1
    have hc' : RChain ((a', b', v') :: ts) := hc.2
    unfold rmMerge
    split
    · apply rangesOK_rmMerge
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · simp only; omega
        · exact hp t (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht))
      · cases ts with
        | nil => trivial
        | cons u us => exact hc'
    · rename_i hne
      have ih := rangesOK_rmMerge ((a', b', v') :: ts) (fun t ht => hp t (List.mem_cons_of_mem _ ht)) hc'
      obtain ⟨b'', hh⟩ := rmMerge_head (a', b', v') ts
      generalize rmMerge ((a', b', v') :: ts) = r at ih hh
      rcases r with _ | ⟨⟨x, y, w⟩, r⟩
      · cases hh
      · simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, -, rfl⟩ := hh
        simp only [List.map_cons] at ih ⊢
        obtain ⟨p, hp'⟩ := Option.isSome_iff_exists.mp (rangesOK_head ih)
        obtain ⟨p1, p2⟩ := p
        have hq := hp'
        simp only [asRange, rangeT, asKInt, kint, asInt, int, beq_self_eq_true, Bool.and_self, ↓reduceIte,
          Option.bind_some, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hq
        obtain ⟨-, rfl, rfl⟩ := hq
        simp only [rangesOK, asRange_rangeT h1, hp', Bool.and_eq_true, ih, and_true, decide_eq_true_eq]
        simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hne
        refine ⟨hbb, ?_⟩
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        by_cases hb : b = x
        · exact .inr (by have := hne hb; simpa using this)
        · exact .inl hb
  termination_by l => l.length

/-- Pairwise disjoint proper intervals in the order of their lower bounds end before the next begins. -/
theorem rchain_of_sorted : ∀ (l : List RmTriple), (∀ t ∈ l, t.1 < t.2.1) → l.Pairwise (fun x y => x.1 ≤ y.1) →
    l.Pairwise (fun t u => t.2.1 ≤ u.1 ∨ u.2.1 ≤ t.1) → RChain l
  | [], _, _, _ => trivial
  | [_], _, _, _ => trivial
  | t :: u :: r, hp, hs, hd => by
    refine ⟨?_, rchain_of_sorted (u :: r) (fun x hx => hp x (List.mem_cons_of_mem _ hx)) hs.of_cons hd.of_cons⟩
    have h1 := List.rel_of_pairwise_cons hs (List.mem_cons_self ..)
    have h2 := List.rel_of_pairwise_cons hd (List.mem_cons_self ..)
    have h3 := hp u (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    omega

/-- **The canonical entries of pairwise disjoint proper intervals are maximal intervals in order**
(`rangesOK`), whatever their values. -/
theorem rangesOK_rmCanon {ts : List RmTriple} (hp : ∀ t ∈ ts, t.1 < t.2.1)
    (hd : ts.Pairwise fun t u => t.2.1 ≤ u.1 ∨ u.2.1 ≤ t.1) : rangesOK (rmCanon ts) = true := by
  have hperm := rmSort_perm ts
  apply rangesOK_rmMerge
  · exact fun t ht => hp t (hperm.mem_iff.mp ht)
  · refine rchain_of_sorted _ (fun t ht => hp t (hperm.mem_iff.mp ht)) (rmSort_sorted ts) ?_
    exact (hperm.pairwise_iff (fun h => h.symm)).mpr hd

end KCore
