/-
  KCore. RANGEMAP's fourteen interpreted symbols (`rangeMapHooks`) return, at arguments of their
  signatures' sorts, a value of the result sort, in every semantics whose collection at the sort
  RangeMap is the library's (`builtinColl .rangeMap`):
  - `rangeMapHook_sorted_read`: `.RangeMap`, `r|->`, `find_range`, `lookup`, `lookupOrDefault`,
    `in_keys`, `size`, `<=RangeMap`. The result is the empty map, a map of one given range and
    value, an argument, a key or value of an argument map, or a literal.
  - `rangeMapHook_sorted_build`: `_RangeMap_`, `update`, `[_ <- undef]`, `-RangeMap`,
    `updateRangeMap`, `removeAll`. The result is `rmCanon` of new intervals, each a part of an
    interval of an argument or a given range, with that interval's value; they are proper and
    pairwise disjoint, so their canonical entries are maximal intervals in order
    (`rangesOK_rmCanon`), and a range term's sort does not read its bounds (`sortOf_rangeT`).

  `rangeMapSigs` are the fourteen signatures in the order of `rangeMapHooks`, as the text declares
  them (domains.md 480-683).
-/
import KcoreSpec.RangeMapLaws
import KcoreSpec.FaithOK

set_option autoImplicit false

namespace KCore

/-- The signatures of `rangeMapHooks`' symbols, in its order. -/
def rangeMapSigs : List CtorSig :=
  [⟨rmUnit, [], Srt.rangeMap⟩, ⟨rmElem, [Srt.range, Srt.kitem], Srt.rangeMap⟩,
   ⟨rmConcat, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩,
   ⟨rmLookup, [Srt.rangeMap, Srt.kitem], Srt.kitem⟩,
   ⟨rmLookupOrDefault, [Srt.rangeMap, Srt.kitem, Srt.kitem], Srt.kitem⟩,
   ⟨rmFindRange, [Srt.rangeMap, Srt.kitem], Srt.range⟩,
   ⟨rmUpdate, [Srt.rangeMap, Srt.range, Srt.kitem], Srt.rangeMap⟩,
   ⟨rmRemove, [Srt.rangeMap, Srt.range], Srt.rangeMap⟩,
   ⟨rmDifference, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩,
   ⟨rmUpdateAll, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩,
   ⟨rmRemoveAll, [Srt.rangeMap, Srt.set], Srt.rangeMap⟩,
   ⟨rmInKeys, [Srt.kitem, Srt.rangeMap], Srt.bool⟩,
   ⟨rmSize, [Srt.rangeMap], Srt.int⟩,
   ⟨rmInclusion, [Srt.rangeMap, Srt.rangeMap], Srt.bool⟩]

theorem rangeMapSigs_names : rangeMapSigs.map (·.name) = rangeMapHooks.map (·.1) := rfl

/-! ## Sorts of terms -/

theorem rmS_sortOf_int (c : Semantics) (i : Int) : c.sortOf (int i) = some Srt.int := by
  simp [int, Semantics.sortOf, dvOK]

theorem rmS_sortOf_bool (c : Semantics) (b : Bool) : c.sortOf (bool b) = some Srt.bool := by
  cases b <;> rfl

theorem rmS_sortsOf_cons {c : Semantics} {t : GroundTerm} {ts : List GroundTerm} {s : Srt} {ss : List Srt} :
    c.sortsOf (t :: ts) = some (s :: ss) ↔ c.sortOf t = some s ∧ c.sortsOf ts = some ss := by
  simp only [Semantics.sortsOf]
  cases h1 : c.sortOf t <;> cases h2 : c.sortsOf ts <;> simp

theorem rmS_entriesOK_iff {c : Semantics} {ks vs : Srt} : ∀ {es : Entries},
    c.entriesOK ks vs es = true ↔ ∀ e ∈ es, c.sortOf e.1 = some ks ∧ c.sortOf e.2 = some vs
  | [] => by simp [Semantics.entriesOK]
  | (k, v) :: es => by
    simp only [Semantics.entriesOK, Bool.and_eq_true, rmS_entriesOK_iff, List.mem_cons, forall_eq_or_imp]
    simp only [Semantics.entryOK, Bool.and_eq_true, beq_iff_eq]

/-- A range map value, where the collection at RangeMap is the library's: maximal intervals in
order, keys of sort Range, values of sort KItem. -/
theorem rmS_sortOf_map {c : Semantics} (hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap))
    {s : Srt} {es : Entries} :
    c.sortOf (.map s es) = some Srt.rangeMap ↔ s = Srt.rangeMap ∧ rangesOK es = true ∧
      ∀ e ∈ es, c.sortOf e.1 = some Srt.range ∧ c.sortOf e.2 = some Srt.kitem := by
  constructor
  · intro h
    obtain ⟨k, vs, hk, hv, h1, h2, rfl⟩ := c.sortOf_map_inv h
    rw [hco] at hk; cases hk; cases hv
    exact ⟨rfl, h1, rmS_entriesOK_iff.mp h2⟩
  · rintro ⟨rfl, h1, h2⟩
    have h2' := rmS_entriesOK_iff.mpr h2
    simp only [Semantics.sortOf, hco, builtinColl] at h2' ⊢
    simp [h1, h2']

/-- The values of `rmV`: a list of triples, proper, each of Range and KItem sort. -/
def RmSorted (c : Semantics) (ts : List RmTriple) : Prop :=
  ∀ t ∈ ts, t.1 < t.2.1 ∧ c.sortOf (rangeT t.1 t.2.1) = some Srt.range ∧ c.sortOf t.2.2 = some Srt.kitem

/-- Two intervals that do not meet. -/
abbrev rmDj (t u : RmTriple) : Prop := t.2.1 ≤ u.1 ∨ u.2.1 ≤ t.1

/-- An argument of sort RangeMap: its triples are sorted and pairwise disjoint. -/
theorem rmS_arg {c : Semantics} (hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap))
    {s : Srt} {m : Entries} {ts : List RmTriple} (h : c.sortOf (.map s m) = some Srt.rangeMap)
    (hts : rmTriples m = some ts) : RmSorted c ts ∧ ts.Pairwise rmDj ∧ m = rmEntries ts := by
  obtain ⟨-, hr, he⟩ := (rmS_sortOf_map hco).mp h
  obtain ⟨us, hus, hm, hok⟩ := rmOK_of_value hr
  rw [hus] at hts; cases hts
  refine ⟨fun t ht => ?_, rmOK_pairwise hok, hm⟩
  have hp := rmOK_proper hok t ht
  have := he (rangeT t.1 t.2.1, t.2.2) (by
    rw [hm]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)
  exact ⟨hp, this.1, this.2⟩

/-! ## The hooks that read their result off the arguments -/

/-- The value an interval of a range map gives a key. -/
theorem rmS_find_mem {i : Int} {ts : List RmTriple} {t : RmTriple} (h : rmFind i ts = some t) : t ∈ ts :=
  List.mem_of_find?_eq_some h

/-- **The eight that read their result off the arguments**: `.RangeMap`, `r|->`, `find_range`,
`lookup`, `lookupOrDefault`, `in_keys`, `size`, `<=RangeMap` give, at arguments of their
signature's sorts, a value of the result sort. -/
theorem rangeMapHook_sorted_read {c : Semantics} (hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap))
    {f : Sym} {g : List GroundTerm → Option GroundTerm} {k : CtorSig} {ws : List GroundTerm} {v : GroundTerm}
    (hmem : (f, g) ∈ rangeMapHooks)
    (hf : f ∈ [rmUnit, rmElem, rmFindRange, rmLookup, rmLookupOrDefault, rmInKeys, rmSize, rmInclusion])
    (hk : lookupSig rangeMapSigs f = some k) (hws : c.sortsOf ws = some k.args)
    (hev : g ws = some v) : c.sortOf v = some k.result := by
  simp only [rangeMapHooks, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first | (exfalso; revert hf; decide) | skip
  · rw [show lookupSig rangeMapSigs rmUnit = some ⟨rmUnit, [], Srt.rangeMap⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · cases hev; exact (rmS_sortOf_map hco).mpr ⟨rfl, rfl, fun _ h => nomatch h⟩
    · cases hev
  · rw [show lookupSig rangeMapSigs rmElem = some ⟨rmElem, [Srt.range, Srt.kitem], Srt.rangeMap⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [rmS_sortsOf_cons] at hws
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Option.map_eq_some_iff.mp hev
      obtain ⟨rfl, hlt⟩ := asRange_some hab
      refine (rmS_sortOf_map hco).mpr ⟨rfl, by simp [rangesOK, asRange_rangeT hlt], fun e he => ?_⟩
      rw [List.mem_singleton] at he; subst he
      exact ⟨hws.1, hws.2.1⟩
    · cases hev
  · rw [show lookupSig rangeMapSigs rmLookup = some ⟨rmLookup, [Srt.rangeMap, Srt.kitem], Srt.kitem⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [rmS_sortsOf_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨ts, hts, i, -, t, ht, rfl⟩ := hev
      exact ((rmS_arg hco hws.1 hts).1 t (rmS_find_mem ht)).2.2
    · cases hev
  · rw [show lookupSig rangeMapSigs rmLookupOrDefault =
      some ⟨rmLookupOrDefault, [Srt.rangeMap, Srt.kitem, Srt.kitem], Srt.kitem⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [rmS_sortsOf_cons] at hws
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hev
      have hs := (rmS_arg hco hws.1 hts).1
      cases hfind : (asKInt _).bind fun i => rmFind i ts with
      | none => simpa using hws.2.2.1
      | some t =>
        obtain ⟨i, -, ht⟩ := Option.bind_eq_some_iff.mp hfind
        simpa using (hs t (rmS_find_mem ht)).2.2
    · cases hev
  · rw [show lookupSig rangeMapSigs rmFindRange = some ⟨rmFindRange, [Srt.rangeMap, Srt.kitem], Srt.range⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [rmS_sortsOf_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨ts, hts, i, -, ⟨a, b, w⟩, ht, rfl⟩ := hev
      exact ((rmS_arg hco hws.1 hts).1 _ (rmS_find_mem ht)).2.1
    · cases hev
  · rw [show lookupSig rangeMapSigs rmInKeys = some ⟨rmInKeys, [Srt.kitem, Srt.rangeMap], Srt.bool⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hev
      exact rmS_sortOf_bool c _
    · cases hev
  · rw [show lookupSig rangeMapSigs rmSize = some ⟨rmSize, [Srt.rangeMap], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · cases hev; exact rmS_sortOf_int c _
    · cases hev
  · rw [show lookupSig rangeMapSigs rmInclusion = some ⟨rmInclusion, [Srt.rangeMap, Srt.rangeMap], Srt.bool⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨_, -, _, -, rfl⟩ := hev
      exact rmS_sortOf_bool c _
    · cases hev

/-! ## Canonical entries -/

/-- Each merged interval carries the value of an interval merged. -/
theorem rmS_merge_val : ∀ (l : List RmTriple) (x : RmTriple), x ∈ rmMerge l → ∃ t ∈ l, x.2.2 = t.2.2
  | [], x, h => by simp [rmMerge] at h
  | [t], x, h => by
    simp only [rmMerge, List.mem_singleton] at h
    exact ⟨t, List.mem_singleton_self _, by rw [h]⟩
  | (a, b, v) :: (a', b', v') :: ts, x, h => by
    unfold rmMerge at h
    split at h
    · obtain ⟨t, ht, hx⟩ := rmS_merge_val ((a, b', v) :: ts) x h
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨(a, b, v), List.mem_cons_self .., hx⟩
      · exact ⟨t, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht), hx⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨_, List.mem_cons_self .., rfl⟩
      · obtain ⟨t, ht, hx⟩ := rmS_merge_val ((a', b', v') :: ts) x h
        exact ⟨t, List.mem_cons_of_mem _ ht, hx⟩
  termination_by l _ => l.length

/-- **The canonical entries of sorted, pairwise disjoint intervals are a range map value.** -/
theorem rmS_canon_sorted {c : Semantics} (hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap))
    {ts : List RmTriple} (hs : RmSorted c ts) (hd : ts.Pairwise rmDj) :
    c.sortOf (rmV (rmCanon ts)) = some Srt.rangeMap := by
  refine (rmS_sortOf_map hco).mpr ⟨rfl, rangesOK_rmCanon (fun t ht => (hs t ht).1) hd, fun e he => ?_⟩
  rw [rmCanon_eq] at he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  obtain ⟨t, ht, hv⟩ := rmS_merge_val _ x hx
  have ht' := (rmSort_perm ts).mem_iff.mp ht
  obtain ⟨-, hr, hk⟩ := hs t ht'
  exact ⟨(sortOf_rangeT c x.1 x.2.1 t.1 t.2.1).trans hr, hv ▸ hk⟩

/-! ## Cutting -/

/-- A part of `t` less `[a, b)`: proper, inside `t`, with its value, outside `[a, b)`. -/
theorem rmS_cutOne_mem {a b : Int} {t x : RmTriple} (h : x ∈ rmCutOne a b t) :
    x.1 < x.2.1 ∧ t.1 ≤ x.1 ∧ x.2.1 ≤ t.2.1 ∧ x.2.2 = t.2.2 ∧ (x.2.1 ≤ a ∨ b ≤ x.1) := by
  obtain ⟨p, q, v⟩ := t
  have h1 := Int.min_le_left q a; have h2 := Int.min_le_right q a
  have h3 := Int.le_max_left p b; have h4 := Int.le_max_right p b
  simp only [rmCutOne, List.mem_append] at h
  generalize min q a = m at h h1 h2
  generalize max p b = M at h h3 h4
  rcases h with h | h
  · split at h
    · rw [List.mem_singleton] at h; subst h; refine ⟨?_, ?_, ?_, rfl, ?_⟩ <;> dsimp only <;> omega
    · cases h
  · split at h
    · rw [List.mem_singleton] at h; subst h; refine ⟨?_, ?_, ?_, rfl, ?_⟩ <;> dsimp only <;> omega
    · cases h

/-- The two parts of `t` less a range do not meet. -/
theorem rmS_cutOne_dj {a b : Int} (hab : a ≤ b) (t : RmTriple) : (rmCutOne a b t).Pairwise rmDj := by
  obtain ⟨p, q, v⟩ := t
  have h2 := Int.min_le_right q a; have h4 := Int.le_max_right p b
  simp only [rmCutOne]
  generalize min q a = m at h2 ⊢
  generalize max p b = M at h4 ⊢
  split <;> split <;> simp [rmDj] <;> omega

/-- Replacing each interval by parts of it keeps the triples sorted and disjoint. -/
theorem rmS_flatMap {c : Semantics} {F : RmTriple → List RmTriple} {ts : List RmTriple}
    (hF : ∀ t ∈ ts, ∀ x ∈ F t, x.1 < x.2.1 ∧ t.1 ≤ x.1 ∧ x.2.1 ≤ t.2.1 ∧ x.2.2 = t.2.2)
    (hFd : ∀ t, (F t).Pairwise rmDj) (hs : RmSorted c ts) (hd : ts.Pairwise rmDj) :
    RmSorted c (ts.flatMap F) ∧ (ts.flatMap F).Pairwise rmDj := by
  refine ⟨fun x hx => ?_, List.pairwise_flatMap.mpr ⟨fun t _ => hFd t, ?_⟩⟩
  · obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hx
    obtain ⟨hp, -, -, hv⟩ := hF t ht x hxt
    obtain ⟨-, hr, hk⟩ := hs t ht
    exact ⟨hp, (sortOf_rangeT c x.1 x.2.1 t.1 t.2.1).trans hr, hv ▸ hk⟩
  · refine hd.imp_of_mem fun {t u} ht hu htu x hx y hy => ?_
    obtain ⟨-, h1, h2, -⟩ := hF t ht x hx
    obtain ⟨-, h3, h4, -⟩ := hF u hu y hy
    unfold rmDj at htu ⊢
    omega

theorem rmS_cut {c : Semantics} {a b : Int} (hab : a ≤ b) {ts : List RmTriple} (hs : RmSorted c ts)
    (hd : ts.Pairwise rmDj) :
    RmSorted c (rmCut a b ts) ∧ (rmCut a b ts).Pairwise rmDj ∧ ∀ x ∈ rmCut a b ts, x.2.1 ≤ a ∨ b ≤ x.1 := by
  obtain ⟨h1, h2⟩ := rmS_flatMap (F := rmCutOne a b)
    (fun _ _ _ h => let h := rmS_cutOne_mem h; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) (rmS_cutOne_dj hab) hs hd
  refine ⟨h1, h2, fun x hx => ?_⟩
  obtain ⟨t, -, hxt⟩ := List.mem_flatMap.mp hx
  exact (rmS_cutOne_mem hxt).2.2.2.2

/-- Writing `[a, b) ↦ w` over sorted disjoint triples. -/
theorem rmS_over {c : Semantics} {a b : Int} {w : GroundTerm} (hab : a < b)
    (hr : c.sortOf (rangeT a b) = some Srt.range) (hw : c.sortOf w = some Srt.kitem)
    {ts : List RmTriple} (hs : RmSorted c ts) (hd : ts.Pairwise rmDj) :
    RmSorted c (rmCut a b ts ++ [(a, b, w)]) ∧ (rmCut a b ts ++ [(a, b, w)]).Pairwise rmDj := by
  obtain ⟨h1, h2, h3⟩ := rmS_cut (Int.le_of_lt hab) hs hd
  refine ⟨fun x hx => ?_, List.pairwise_append.mpr ⟨h2, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩⟩
  · rcases List.mem_append.mp hx with hx | hx
    · exact h1 x hx
    · rw [List.mem_singleton] at hx; subst hx; exact ⟨hab, hr, hw⟩
  · rw [List.mem_singleton] at hy; subst hy
    unfold rmDj; have := h3 x hx; simp only; omega

/-- `rmDiffT`: each interval of `us` cut from the intervals of `ts` of its value. -/
theorem rmS_diffT {c : Semantics} : ∀ {us ts : List RmTriple}, (∀ u ∈ us, u.1 < u.2.1) →
    RmSorted c ts → ts.Pairwise rmDj → RmSorted c (rmDiffT ts us) ∧ (rmDiffT ts us).Pairwise rmDj
  | [], _, _, hs, hd => ⟨hs, hd⟩
  | (a, b, w) :: us, ts, hp, hs, hd => by
    have hab : a < b := hp _ (List.mem_cons_self ..)
    have hstep := rmS_flatMap (c := c)
      (F := fun t => if GroundTerm.cmp t.2.2 w == .eq then rmCutOne a b t else [t])
      (fun t ht x h => by
        split at h
        · have h := rmS_cutOne_mem h; exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
        · rw [List.mem_singleton] at h; rw [h]; exact ⟨(hs t ht).1, Int.le_refl _, Int.le_refl _, rfl⟩)
      (fun _ => by split <;> first | exact rmS_cutOne_dj (Int.le_of_lt hab) _ | exact List.pairwise_singleton _ _)
      hs hd
    exact rmS_diffT (us := us) (fun u hu => hp u (List.mem_cons_of_mem _ hu)) hstep.1 hstep.2

/-- `rmOverT`: the intervals of `us` written over `ts` in turn. -/
theorem rmS_overT {c : Semantics} : ∀ {us ts : List RmTriple}, RmSorted c us →
    RmSorted c ts → ts.Pairwise rmDj → RmSorted c (rmOverT ts us) ∧ (rmOverT ts us).Pairwise rmDj
  | [], _, _, hs, hd => ⟨hs, hd⟩
  | (a, b, w) :: us, ts, hu, hs, hd => by
    obtain ⟨hab, hr, hw⟩ := hu _ (List.mem_cons_self ..)
    have hstep := rmS_over hab hr hw hs hd
    exact rmS_overT (us := us) (fun u h => hu u (List.mem_cons_of_mem _ h)) hstep.1 hstep.2

/-- `removeAll`'s cuts, in turn. -/
theorem rmS_cuts {c : Semantics} : ∀ {ps : List (Int × Int)} {ts : List RmTriple}, (∀ p ∈ ps, p.1 < p.2) →
    RmSorted c ts → ts.Pairwise rmDj →
    RmSorted c (ps.foldl (fun acc (a, b) => rmCut a b acc) ts) ∧
      (ps.foldl (fun acc (a, b) => rmCut a b acc) ts).Pairwise rmDj
  | [], _, _, hs, hd => ⟨hs, hd⟩
  | (a, b) :: ps, ts, hp, hs, hd => by
    have hab : a < b := hp _ (List.mem_cons_self ..)
    obtain ⟨h1, h2, -⟩ := rmS_cut (Int.le_of_lt hab) hs hd
    exact rmS_cuts (ps := ps) (fun p h => hp p (List.mem_cons_of_mem _ h)) h1 h2

/-- The members of a Set of proper ranges read as their bounds. -/
theorem rmS_mapM_asKRange : ∀ {rs : List GroundTerm} {ps : List (Int × Int)}, rs.mapM asKRange = some ps →
    ∀ p ∈ ps, p.1 < p.2
  | [], ps, h, p, hp => by simp at h; subst h; cases hp
  | r :: rs, ps, h, p, hp => by
    rw [List.mapM_cons] at h
    cases hr : asKRange r with
    | none => simp [hr] at h
    | some ab =>
      cases hqs : rs.mapM asKRange with
      | none => simp [hr, hqs] at h
      | some qs =>
        rw [hr, hqs] at h
        have h : ab :: qs = ps := Option.some.inj h
        subst h
        rcases List.mem_cons.mp hp with rfl | hp
        · unfold asKRange at hr
          split at hr
          · split at hr
            · exact (asRange_some hr).2
            · cases hr
          · cases hr
        · exact rmS_mapM_asKRange hqs p hp

/-! ## The hooks that build a new range map -/

/-- **The six that build a new range map**: `_RangeMap_`, `update`, `[_ <- undef]`, `-RangeMap`,
`updateRangeMap`, `removeAll` give, at arguments of their signature's sorts, a range map value. -/
theorem rangeMapHook_sorted_build {c : Semantics} (hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap))
    {f : Sym} {g : List GroundTerm → Option GroundTerm} {k : CtorSig} {ws : List GroundTerm} {v : GroundTerm}
    (hmem : (f, g) ∈ rangeMapHooks)
    (hf : f ∈ [rmConcat, rmUpdate, rmRemove, rmDifference, rmUpdateAll, rmRemoveAll])
    (hk : lookupSig rangeMapSigs f = some k) (hws : c.sortsOf ws = some k.args)
    (hev : g ws = some v) : c.sortOf v = some k.result := by
  simp only [rangeMapHooks, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first | (exfalso; revert hf; decide) | skip
  · rw [show lookupSig rangeMapSigs rmConcat = some ⟨rmConcat, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [rmS_sortsOf_cons] at hws
      simp only [Option.bind_eq_some_iff] at hev
      obtain ⟨ts, hts, us, hus, hev⟩ := hev
      split at hev
      · rename_i hdj
        cases hev
        obtain ⟨hs, hd, -⟩ := rmS_arg hco hws.1 hts
        obtain ⟨hs', hd', -⟩ := rmS_arg hco hws.2.1 hus
        refine rmS_canon_sorted hco (fun t ht => (List.mem_append.mp ht).elim (hs t) (hs' t))
          (List.pairwise_append.mpr ⟨hd, hd', fun t ht u hu => ?_⟩)
        simp only [rmDisjoint, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hdj
        exact hdj t ht u hu
      · cases hev
    · cases hev
  · rw [show lookupSig rangeMapSigs rmUpdate = some ⟨rmUpdate, [Srt.rangeMap, Srt.range, Srt.kitem], Srt.rangeMap⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [rmS_sortsOf_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨ts, hts, ⟨a, b⟩, hab, rfl⟩ := hev
      obtain ⟨rfl, hlt⟩ := asRange_some hab
      obtain ⟨hs, hd, -⟩ := rmS_arg hco hws.1 hts
      obtain ⟨h1, h2⟩ := rmS_over hlt hws.2.1 hws.2.2.1 hs hd
      exact rmS_canon_sorted hco h1 h2
    · cases hev
  · rw [show lookupSig rangeMapSigs rmRemove = some ⟨rmRemove, [Srt.rangeMap, Srt.range], Srt.rangeMap⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [rmS_sortsOf_cons] at hws
      simp only [Option.bind_eq_some_iff] at hev
      obtain ⟨ts, hts, ⟨a, b⟩, hab, hev⟩ := hev
      have hev : (if rmMeets a b ts then some (rmV (rmCanon (rmCut a b ts))) else none) = some v := hev
      split at hev
      · cases hev
        obtain ⟨-, hlt⟩ := asRange_some hab
        obtain ⟨hs, hd, -⟩ := rmS_arg hco hws.1 hts
        obtain ⟨h1, h2, -⟩ := rmS_cut (Int.le_of_lt hlt) hs hd
        exact rmS_canon_sorted hco h1 h2
      · cases hev
    · cases hev
  · rw [show lookupSig rangeMapSigs rmDifference = some ⟨rmDifference, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [rmS_sortsOf_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨ts, hts, us, hus, rfl⟩ := hev
      obtain ⟨hs, hd, -⟩ := rmS_arg hco hws.1 hts
      obtain ⟨hs', -, -⟩ := rmS_arg hco hws.2.1 hus
      obtain ⟨h1, h2⟩ := rmS_diffT (fun u hu => (hs' u hu).1) hs hd
      exact rmS_canon_sorted hco h1 h2
    · cases hev
  · rw [show lookupSig rangeMapSigs rmUpdateAll = some ⟨rmUpdateAll, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [rmS_sortsOf_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨ts, hts, us, hus, rfl⟩ := hev
      obtain ⟨hs, hd, -⟩ := rmS_arg hco hws.1 hts
      obtain ⟨hs', -, -⟩ := rmS_arg hco hws.2.1 hus
      obtain ⟨h1, h2⟩ := rmS_overT hs' hs hd
      exact rmS_canon_sorted hco h1 h2
    · cases hev
  · rw [show lookupSig rangeMapSigs rmRemoveAll = some ⟨rmRemoveAll, [Srt.rangeMap, Srt.set], Srt.rangeMap⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [rmS_sortsOf_cons] at hws
      simp only [Option.bind_eq_some_iff] at hev
      obtain ⟨ts, hts, ps, hps, hev⟩ := hev
      split at hev
      · cases hev
        obtain ⟨hs, hd, -⟩ := rmS_arg hco hws.1 hts
        obtain ⟨h1, h2⟩ := rmS_cuts (rmS_mapM_asKRange hps) hs hd
        exact rmS_canon_sorted hco h1 h2
      · cases hev
    · cases hev

/-! ## The fourteen together -/

/-- `hookSigs` gives each of `rangeMapHooks`' symbols its signature in `rangeMapSigs`. -/
theorem rangeMapSigs_hookSigs : ∀ f ∈ rangeMapSigs.map (·.name), lookupSig hookSigs f = lookupSig rangeMapSigs f := by
  decide +kernel

/-- **RANGEMAP's interpreted symbols are sorted**: at arguments of its signature's sorts, each of
`rangeMapHooks`' fourteen gives a value of its result sort, in every semantics (the collection at
RangeMap is `builtinColls`' fourth row in all of them). -/
theorem rangeMapHook_sorted {c : Semantics} {f : Sym} {g : List GroundTerm → Option GroundTerm} {k : CtorSig}
    {ws : List GroundTerm} {v : GroundTerm} (hmem : (f, g) ∈ rangeMapHooks)
    (hk : lookupSig hookSigs f = some k) (hws : c.sortsOf ws = some k.args) (hev : g ws = some v) :
    c.sortOf v = some k.result := by
  have hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap) := rfl
  have hf : f ∈ rangeMapSigs.map (·.name) := by
    rw [rangeMapSigs_names]; exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  rw [rangeMapSigs_hookSigs f hf] at hk
  have hrb : f ∈ [rmUnit, rmElem, rmFindRange, rmLookup, rmLookupOrDefault, rmInKeys, rmSize, rmInclusion] ∨
      f ∈ [rmConcat, rmUpdate, rmRemove, rmDifference, rmUpdateAll, rmRemoveAll] := by
    simp only [rangeMapSigs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rcases hrb with hr | hb
  · exact rangeMapHook_sorted_read hco hmem hr hk hws hev
  · exact rangeMapHook_sorted_build hco hmem hb hk hws hev

/-! ## The collection's three symbols at values (the model's range-map cases) -/

/-- The library's range map is a collection of every semantics. -/
theorem rmM_mem {c : Semantics} : builtinColl .rangeMap ∈ c.allColls :=
  List.mem_append_left _ (by simp [builtinColls, builtinColl])

theorem rmM_unit : hook rmUnit [] = some (some (rmV [])) := rfl

theorem rmM_elem_eq (vs : List GroundTerm) :
    hook rmElem vs = some (match vs with
      | [r, v] => (asRange r).map fun (a, b) => rmV [(rangeT a b, v)] | _ => none) := rfl

theorem rmM_concat_eq (vs : List GroundTerm) : hook rmConcat vs = rmHook rmConcat vs := rfl

/-- `r r|-> v` at a proper range is the map of the one entry. -/
theorem rmM_elem {r v : GroundTerm} (h : (asRange r).isSome = true) :
    hook rmElem [r, v] = some (some (rmV [(r, v)])) := by
  obtain ⟨⟨a, b⟩, hab⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨rfl, -⟩ := asRange_some hab
  rw [rmM_elem_eq]
  simp only [hab, Option.map_some]

theorem rmM_tail {x : GroundTerm × GroundTerm} {es : Entries} (h : rangesOK (x :: es) = true) :
    rangesOK es = true := by
  obtain ⟨k, v⟩ := x
  cases es with
  | nil => rfl
  | cons y es =>
    obtain ⟨k', v'⟩ := y
    simp only [rangesOK, Bool.and_eq_true] at h
    exact h.2

/-- **A range map value is its first entry concatenated with the rest**: no key of the first
interval is in a later one, and the union is already maximal. -/
theorem rmM_concat {x : GroundTerm × GroundTerm} {es : Entries} (h : rangesOK (x :: es) = true) :
    hook rmConcat [rmV [x], rmV es] = some (some (rmV (x :: es))) := by
  obtain ⟨ts, -, he, hok⟩ := rmOK_of_value h
  match ts, he, hok with
  | [], he, _ => cases he
  | (a, b, w) :: us, he, hok =>
    simp only [rmEntries, List.map_cons, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have h1 : RmOK [(a, b, w)] := rmOK_head hok
    have hu := rmOK_tail hok
    have hap : RmApart [(a, b, w)] us := fun k x y hx hy => by
      obtain ⟨t, ht, hl, hr, -⟩ := hx
      obtain ⟨u, hu', hl', -, -⟩ := hy
      have := rmOK_after hok u hu'
      rw [List.mem_singleton.mp ht] at hl hr
      simp only at hl hr this
      omega
    have hcov : ∀ k x, RmCov ((a, b, w) :: us) k x ↔ RmCov [(a, b, w)] k x ∨ RmCov us k x := fun k x => by
      rw [rmCov_cons, rmCov_cons (ts := [])]
      simp only [rmCov_nil, or_false]
    have hc : rmCatT [(a, b, w)] us = some ((a, b, w) :: us) := (rmCatT_some h1 hu).mpr ⟨hap, hok, hcov⟩
    have hv := rmConcat_value h1 hu
    rw [hc] at hv
    rw [rmM_concat_eq, rmV, rmV, rmHook_rmConcat] at *
    exact congrArg some hv

/-- The concatenation reads the entries of its arguments and not their sort: at the maps of any
sort it is `rmM_concat`'s value. -/
theorem rmM_concat_sortK {s : Srt} {x : GroundTerm × GroundTerm} {es : Entries} (h : rangesOK (x :: es) = true) :
    hook rmConcat [.map s [x], .map s es] = some (some (rmV (x :: es))) := by
  have : hook rmConcat [.map s [x], .map s es] = hook rmConcat [rmV [x], rmV es] := rfl
  rw [this]
  exact rmM_concat h

end KCore
