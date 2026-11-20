/-
  KCore, checked layer: the collection interface. A finite map value `.map s m`, a finite set
  value `.set s es` and a list value `.list s es` (of the collection sort s) are read through their
  meaning, not their representation:
  - a map is the partial function `find m` (`findK`); `insertE`, `eraseK`, `union` and `keysOf`
    (the hooks `Map:update`, `Map:remove`, `_Map_`, `keys`) are characterised by what `find` gives
    after them, and two canonical maps with the same `find` are the same value (`Map.ext`);
  - a set is its membership; `insertS`, `unionS` and the filters (`SetItem`, `_Set_`, `|Set`,
    `intersectSet`, `Set:difference`) are characterised by membership, and two canonical sets with
    the same members are the same value (`Set.ext`);
  - `Map.AgreeOn P a b`: two maps give the same `find` at every key satisfying P. It is preserved
    by updates that agree at P's keys and by any removal, which is the fact a relation "equal at
    the low keys" needs (the noninterference kind).
  - a list is its sequence of elements: `.List`, `ListItem`, `_List_`, `pushList`, `inList`,
    `size` and `L[I]` are characterised on it (`List'`).
  Canonical means strictly increasing keys (elements) in `GroundTerm.cmp`, which `sortOf`
  guarantees for every map and set inside a value (`Map.canon_of_sortOf`, `Set.canon_of_sortOf`).
  Theorem kinds use these lemmas, so their proofs never unfold the sorted-list representation.
-/
import KcoreSpec.MapLaws
import KcoreSpec.SetLaws

set_option autoImplicit false

namespace KCore

open GroundTerm

theorem cmp_eq_iff {a b : GroundTerm} : cmp a b = .eq ↔ a = b :=
  ⟨cmp_eq a b, fun h => h ▸ cmp_refl a⟩

/-- Equality of ground terms is decided by their order. -/
instance : DecidableEq GroundTerm := fun a b =>
  if h : cmp a b = .eq then isTrue (cmp_eq a b h) else isFalse fun e => h (cmp_eq_iff.mpr e)

namespace Map

/-- A map's entries are canonical: keys strictly increasing. -/
def Canon (m : Entries) : Prop := keysSorted m = true

/-- The meaning of a map: the value at a key. -/
abbrev find (m : Entries) (k : GroundTerm) : Option GroundTerm := findK k m

theorem find_nil (k : GroundTerm) : find [] k = none := rfl

theorem find_cons (k k' v' : GroundTerm) (es : Entries) :
    find ((k', v') :: es) k = if k = k' then some v' else find es k := by
  simp only [find, findK]
  by_cases h : k = k'
  · subst h; simp [cmp_refl]
  · have : (cmp k k' == .eq) = false := by
      cases hc : cmp k k' <;> simp_all [cmp_eq_iff]
    simp [this, h]

theorem find_none_of {k : GroundTerm} : ∀ {es : Entries}, (∀ e ∈ es, k ≠ e.1) → find es k = none
  | [], _ => rfl
  | (k', v') :: es, h => by
    rw [find_cons, if_neg (h _ (List.mem_cons_self ..))]
    exact find_none_of fun e he => h e (List.mem_cons_of_mem _ he)

theorem mem_of_find {k v : GroundTerm} : ∀ {es : Entries}, find es k = some v → (k, v) ∈ es
  | [], h => nomatch h
  | (k', v') :: es, h => by
    rw [find_cons] at h
    by_cases hk : k = k'
    · rw [if_pos hk] at h; cases h; subst hk; exact List.mem_cons_self ..
    · rw [if_neg hk] at h; exact List.mem_cons_of_mem _ (mem_of_find h)

theorem find_of_mem {k v : GroundTerm} : ∀ {es : Entries}, Canon es → (k, v) ∈ es → find es k = some v
  | [], _, h => nomatch h
  | (k', v') :: es, hc, h => by
    rw [find_cons]
    rcases List.mem_cons.mp h with he | he
    · cases he; simp
    · have hlt := keysSorted_lt_all hc _ he
      have hne : k ≠ k' := by
        intro hk; subst hk; rw [cmp_refl] at hlt; cases hlt
      rw [if_neg hne]
      exact find_of_mem (keysSorted_cons.mp hc).1 he

theorem find_iff_mem {m : Entries} (hc : Canon m) (k v : GroundTerm) :
    find m k = some v ↔ (k, v) ∈ m :=
  ⟨mem_of_find, find_of_mem hc⟩

/-- Two canonical maps with the same meaning are the same value. -/
theorem ext {a b : Entries} (ha : Canon a) (hb : Canon b) (h : ∀ k, find a k = find b k) : a = b :=
  entries_canon ha hb fun ⟨k, v⟩ => by
    rw [← find_iff_mem ha, ← find_iff_mem hb, h]

theorem hasKey_eq (k : GroundTerm) : ∀ (m : Entries), hasKey k m = (find m k).isSome
  | [] => rfl
  | (k', v') :: es => by
    rw [find_cons]
    simp only [hasKey, List.any_cons] at *
    by_cases h : k = k'
    · subst h; simp [cmp_refl]
    · have : (cmp k k' == .eq) = false := by
        cases hc : cmp k k' <;> simp_all [cmp_eq_iff]
      rw [this, if_neg h, Bool.false_or]
      exact hasKey_eq k es

/-! ### Update (`Map:update`, `M[K <- V]`) -/

theorem find_insert_self (k v : GroundTerm) : ∀ (m : Entries), find (insertE k v m) k = some v
  | [] => by simp [insertE, find_cons]
  | (k', v') :: es => by
    simp only [insertE]
    cases hc : cmp k k' with
    | lt => simp [find_cons]
    | eq => simp [find_cons]
    | gt =>
      rw [find_cons, if_neg (by intro h; subst h; rw [cmp_refl] at hc; cases hc)]
      exact find_insert_self k v es

theorem find_insert_ne {k k' : GroundTerm} (v : GroundTerm) (h : k' ≠ k) :
    ∀ (m : Entries), find (insertE k v m) k' = find m k'
  | [] => by simp [insertE, find_cons, h, find_nil]
  | (k'', v'') :: es => by
    simp only [insertE]
    cases hc : cmp k k'' with
    | lt => rw [find_cons, if_neg h]
    | eq =>
      have := cmp_eq_iff.mp hc; subst this
      rw [find_cons, if_neg h, find_cons, if_neg h]
    | gt => rw [find_cons, find_cons, find_insert_ne v h es]

theorem find_insert (k v : GroundTerm) (m : Entries) (k' : GroundTerm) :
    find (insertE k v m) k' = if k' = k then some v else find m k' := by
  by_cases h : k' = k
  · subst h; rw [if_pos rfl, find_insert_self]
  · rw [if_neg h, find_insert_ne v h]

theorem insert_canon {k v : GroundTerm} {m : Entries} (h : Canon m) : Canon (insertE k v m) :=
  insertE_sorted h

/-! ### Removal (`Map:remove`, `M[K <- undef]`) -/

theorem find_erase_ne {k k' : GroundTerm} (h : k' ≠ k) : ∀ (m : Entries), find (eraseK k m) k' = find m k'
  | [] => rfl
  | (k'', v'') :: es => by
    simp only [eraseK]
    by_cases hk : k = k''
    · subst hk; simp [cmp_refl, find_cons, h]
    · have : (cmp k k'' == .eq) = false := by
        cases hc : cmp k k'' <;> simp_all [cmp_eq_iff]
      rw [this]; simp only [Bool.false_eq_true, if_false]
      rw [find_cons, find_cons, find_erase_ne h es]

theorem find_erase_self (k : GroundTerm) : ∀ {m : Entries}, Canon m → find (eraseK k m) k = none
  | [], _ => rfl
  | (k', v') :: es, hc => by
    simp only [eraseK]
    by_cases hk : k = k'
    · subst hk; simp only [cmp_refl, beq_self_eq_true, if_true]
      exact find_none_of fun e he hke => by
        have hlt := keysSorted_lt_all hc e he
        rw [hke, cmp_refl] at hlt; cases hlt
    · have : (cmp k k' == .eq) = false := by
        cases hc : cmp k k' <;> simp_all [cmp_eq_iff]
      rw [this]; simp only [Bool.false_eq_true, if_false]
      rw [find_cons, if_neg hk]
      exact find_erase_self k (keysSorted_cons.mp hc).1

theorem find_erase {k : GroundTerm} {m : Entries} (hc : Canon m) (k' : GroundTerm) :
    find (eraseK k m) k' = if k' = k then none else find m k' := by
  by_cases h : k' = k
  · subst h; rw [if_pos rfl, find_erase_self k' hc]
  · rw [if_neg h, find_erase_ne h]

theorem erase_canon {k : GroundTerm} {m : Entries} (h : Canon m) : Canon (eraseK k m) :=
  eraseK_sorted h

/-! ### Union (`_Map_`), defined exactly when the keys are disjoint -/

theorem union_find {a b m : Entries} (ha : Canon a) (hb : Canon b) (hu : union a b = some m) :
    Canon m ∧ ∀ k, find m k = (find a k).or (find b k) := by
  have hm : Canon m := union_sorted hb hu
  obtain ⟨hmem, _, _, hd⟩ := union_spec hu
  refine ⟨hm, fun k => ?_⟩
  cases hfa : find a k with
  | some w =>
    simp only [Option.some_or]
    exact find_of_mem hm ((hmem _).mpr (Or.inl (mem_of_find hfa)))
  | none =>
    simp only [Option.none_or]
    cases hfb : find b k with
    | some w => exact find_of_mem hm ((hmem _).mpr (Or.inr (mem_of_find hfb)))
    | none =>
      cases hfm : find m k with
      | none => rfl
      | some w =>
        rcases (hmem _).mp (mem_of_find hfm) with h | h
        · rw [find_of_mem ha h] at hfa; cases hfa
        · rw [find_of_mem hb h] at hfb; cases hfb

theorem union_defined {a b : Entries} (ha : Canon a) (hb : Canon b) :
    (∃ m, union a b = some m) ↔ ∀ k, find a k = none ∨ find b k = none := by
  constructor
  · rintro ⟨m, hu⟩ k
    obtain ⟨_, _, _, hd⟩ := union_spec hu
    cases hfa : find a k with
    | none => exact Or.inl rfl
    | some v =>
      right
      cases hfb : find b k with
      | none => rfl
      | some w =>
        have := hd _ (mem_of_find hfa) _ (mem_of_find hfb)
        simp [cmp_refl] at this
  · intro h
    obtain ⟨m, hu, _⟩ := union_exists (sorted_apart ha) (fun e he e' he' hc => by
      have hk := cmp_eq_iff.mp hc
      rcases h e.1 with h1 | h1
      · rw [find_of_mem ha (by simpa using he)] at h1; cases h1
      · rw [hk, find_of_mem hb (by simpa using he')] at h1; cases h1)
    exact ⟨m, hu⟩

/-! ### Keys (`keys`, `in_keys`) -/

theorem mem_keys {m : Entries} (hc : Canon m) (k : GroundTerm) : k ∈ keysOf m ↔ (find m k).isSome := by
  unfold keysOf
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨k', v⟩, he, rfl⟩; rw [find_of_mem hc he]; rfl
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    exact ⟨(k, v), mem_of_find hv, rfl⟩

theorem keys_canon {m : Entries} (hc : Canon m) : elemsSorted (keysOf m) = true :=
  elemsSorted_iff.mpr (keysOf_sorted (keysSorted_iff.mp hc))

/-! ### Agreement at a set of keys -/

/-- The two maps give the same value at every key satisfying P. -/
def AgreeOn (P : GroundTerm → Prop) (a b : Entries) : Prop := ∀ k, P k → find a k = find b k

theorem AgreeOn.refl (P : GroundTerm → Prop) (a : Entries) : AgreeOn P a a := fun _ _ => rfl
theorem AgreeOn.symm {P : GroundTerm → Prop} {a b : Entries} (h : AgreeOn P a b) : AgreeOn P b a :=
  fun k hk => (h k hk).symm
theorem AgreeOn.trans {P : GroundTerm → Prop} {a b d : Entries} (h₁ : AgreeOn P a b)
    (h₂ : AgreeOn P b d) : AgreeOn P a d := fun k hk => (h₁ k hk).trans (h₂ k hk)

/-- An update keeps the agreement when the two new values agree at a key of P. -/
theorem AgreeOn.insert {P : GroundTerm → Prop} {a b : Entries} (h : AgreeOn P a b) (k : GroundTerm)
    {v w : GroundTerm} (hv : P k → v = w) : AgreeOn P (insertE k v a) (insertE k w b) := by
  intro k' hk'
  rw [find_insert, find_insert]
  by_cases he : k' = k
  · subst he; rw [if_pos rfl, if_pos rfl, hv hk']
  · rw [if_neg he, if_neg he]; exact h k' hk'

/-- An update at a key outside P keeps the agreement whatever the value. -/
theorem AgreeOn.insert_left {P : GroundTerm → Prop} {a b : Entries} (h : AgreeOn P a b)
    {k : GroundTerm} (hk : ¬ P k) (v : GroundTerm) : AgreeOn P (insertE k v a) b := by
  intro k' hk'
  rw [find_insert, if_neg (fun (he : k' = k) => hk (he ▸ hk'))]
  exact h k' hk'

theorem AgreeOn.erase {P : GroundTerm → Prop} {a b : Entries} (ha : Canon a) (hb : Canon b)
    (h : AgreeOn P a b) (k : GroundTerm) : AgreeOn P (eraseK k a) (eraseK k b) := by
  intro k' hk'
  rw [find_erase ha, find_erase hb]
  split
  · rfl
  · exact h k' hk'

theorem entriesOK_iff {c : Semantics} {ks vs : Srt} : ∀ {es : Entries},
    c.entriesOK ks vs es = true ↔ ∀ e ∈ es, c.entryOK ks vs e = true
  | [] => ⟨fun _ _ he => (nomatch he), fun _ => rfl⟩
  | e :: es => by
    show (c.entryOK ks vs e && c.entriesOK ks vs es) = true ↔ _
    rw [Bool.and_eq_true, entriesOK_iff, List.forall_mem_cons]

/-- A map of the library's sort `Map`: sorted keys, entries of sort KItem. -/
theorem sortOf_map {c : Semantics} {m : Entries} :
    c.sortOf (.map Srt.map m) =
      if keysSorted m && c.entriesOK Srt.kitem Srt.kitem m then some Srt.map else none := by
  rw [Semantics.sortOf]; rfl

/-- Agreement at every key is equality, for canonical maps. -/
theorem AgreeOn.eq_of_all {a b : Entries} (ha : Canon a) (hb : Canon b)
    (h : AgreeOn (fun _ => True) a b) : a = b :=
  ext ha hb fun k => h k trivial

end Map

namespace Set

/-- A set's elements are canonical: strictly increasing. -/
def Canon (s : List GroundTerm) : Prop := elemsSorted s = true

theorem memS_iff (k : GroundTerm) (s : List GroundTerm) : memS k s = true ↔ k ∈ s := by
  unfold memS
  rw [List.any_eq_true]
  constructor
  · rintro ⟨e, he, h⟩; rw [cmp_eq_iff.mp (beq_iff_eq.mp h)]; exact he
  · intro h; exact ⟨k, h, by simp [cmp_refl]⟩

theorem mem_insert (k x : GroundTerm) : ∀ (s : List GroundTerm), x ∈ insertS k s ↔ x = k ∨ x ∈ s
  | [] => by simp [insertS]
  | e :: es => by
    simp only [insertS]
    cases hc : cmp k e with
    | lt => simp
    | eq =>
      have := cmp_eq_iff.mp hc; subst this
      simp only [List.mem_cons]
      constructor
      · rintro (h | h); exact Or.inl h; exact Or.inr (Or.inr h)
      · rintro (h | h | h); exact Or.inl h; exact Or.inl h; exact Or.inr h
    | gt =>
      simp only [List.mem_cons, mem_insert k x es]
      constructor
      · rintro (h | h | h); exact Or.inr (Or.inl h); exact Or.inl h; exact Or.inr (Or.inr h)
      · rintro (h | h | h); exact Or.inr (Or.inl h); exact Or.inl h; exact Or.inr (Or.inr h)

theorem mem_union (x : GroundTerm) : ∀ (a b : List GroundTerm), x ∈ unionS a b ↔ x ∈ a ∨ x ∈ b
  | [], b => by simp [unionS]
  | e :: a, b => by
    simp only [unionS, List.foldr_cons] at *
    rw [mem_insert]
    have ih := mem_union x a b
    simp only [unionS] at ih
    rw [ih, List.mem_cons]
    constructor
    · rintro (h | h | h); exact Or.inl (Or.inl h); exact Or.inl (Or.inr h); exact Or.inr h
    · rintro ((h | h) | h); exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)

theorem mem_inter (x : GroundTerm) (a b : List GroundTerm) :
    x ∈ a.filter (memS · b) ↔ x ∈ a ∧ x ∈ b := by
  rw [List.mem_filter, memS_iff]

theorem mem_diff (x : GroundTerm) (a b : List GroundTerm) :
    x ∈ a.filter (!memS · b) ↔ x ∈ a ∧ x ∉ b := by
  rw [List.mem_filter, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, memS_iff]

theorem insert_canon {k : GroundTerm} {s : List GroundTerm} (h : Canon s) : Canon (insertS k s) :=
  elemsSorted_iff.mpr (insertS_sorted (elemsSorted_iff.mp h))

theorem union_canon {a b : List GroundTerm} (hb : Canon b) : Canon (unionS a b) :=
  elemsSorted_iff.mpr (unionS_sorted (elemsSorted_iff.mp hb))

theorem filter_canon {s : List GroundTerm} (h : Canon s) (p : GroundTerm → Bool) : Canon (s.filter p) :=
  elemsSorted_iff.mpr ((elemsSorted_iff.mp h).filter p)

/-- A set as a map of each element to itself: the same sortedness. -/
theorem keysSorted_diag : ∀ (s : List GroundTerm), keysSorted (s.map fun x => (x, x)) = elemsSorted s
  | [] => rfl
  | [_] => rfl
  | x :: y :: s => by
    have ih := keysSorted_diag (y :: s)
    simp only [List.map_cons] at ih
    simp only [List.map_cons, keysSorted, elemsSorted, ih]

/-- Two canonical sets with the same members are the same value. -/
theorem ext {a b : List GroundTerm} (ha : Canon a) (hb : Canon b) (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := by
  have hd := entries_canon (a := a.map fun x => (x, x)) (b := b.map fun x => (x, x))
    (by rw [keysSorted_diag]; exact ha) (by rw [keysSorted_diag]; exact hb) (fun ⟨k, v⟩ => by
      simp only [List.mem_map, Prod.mk.injEq]
      constructor
      · rintro ⟨x, hx, rfl, rfl⟩; exact ⟨x, (h x).mp hx, rfl, rfl⟩
      · rintro ⟨x, hx, rfl, rfl⟩; exact ⟨x, (h x).mpr hx, rfl, rfl⟩)
  simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) hd

end Set

/-! ### Values: every map and set of a value is canonical -/

theorem Map.canon_of_sortOf {c : Semantics} {t : Srt} {m : Entries} {s : Srt}
    (h : c.sortOf (.map t m) = some s) : Map.Canon m := by
  obtain ⟨_, _, _, _, h1, _, _⟩ := c.sortOf_map_inv h
  exact (mapKeys_sorted h1).2

theorem Set.canon_of_sortOf {c : Semantics} {t : Srt} {es : List GroundTerm} {s : Srt}
    (h : c.sortOf (.set t es) = some s) : Set.Canon es := by
  simp only [Semantics.sortOf] at h
  split at h
  · split at h
    next hh => exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hh).1).2
    · cases h
  · cases h

/-! ### The hooks read through the interface -/

theorem hook_mapUpdate (s : Srt) (m : Entries) (k v : GroundTerm) :
    hook mapUpdate [.map s m, k, v] = some (some (.map Srt.map (insertE k v m))) := rfl
theorem hook_mapRemove (s : Srt) (m : Entries) (k : GroundTerm) :
    hook mapRemove [.map s m, k] = some (some (.map Srt.map (eraseK k m))) := rfl
theorem hook_mapLookup (s : Srt) (m : Entries) (k : GroundTerm) :
    hook mapLookup [.map s m, k] = some (Map.find m k) := rfl
theorem hook_mapInKeys (s : Srt) (m : Entries) (k : GroundTerm) :
    hook mapInKeys [k, .map s m] = some (some (bool (Map.find m k).isSome)) := by
  show some (some (bool (hasKey k m))) = _
  rw [Map.hasKey_eq]
theorem hook_mapConcat (s t : Srt) (a b : Entries) :
    hook mapConcat [.map s a, .map t b] = some ((union a b).map (.map Srt.map)) := rfl
theorem hook_mapKeys (s : Srt) (m : Entries) :
    hook mapKeys [.map s m] = some (some (.set Srt.set (keysOf m))) := rfl
theorem hook_setIn (t : Srt) (s : List GroundTerm) (k : GroundTerm) :
    hook setIn [k, .set t s] = some (some (bool (memS k s))) := rfl
theorem hook_setConcat (s t : Srt) (a b : List GroundTerm) :
    hook setConcat [.set s a, .set t b] = some ((concatS a b).map (.set Srt.set)) := rfl

/-! ### Lists

A list value `.list s es` is the sequence `es`: its hooks are concatenation, the element, the
unit, `pushList`, membership, size, the indexed element and the range, and nothing else reads
its representation. -/

namespace List'

/-- `_List_` is concatenation (total). -/
theorem hook_concat (s t : Srt) (a b : List GroundTerm) :
    hook listConcat [.list s a, .list t b] = some (some (.list Srt.list (a ++ b))) := rfl
theorem hook_unit : hook listUnit [] = some (some (.list Srt.list [])) := rfl
theorem hook_elem (k : GroundTerm) : hook listElem [k] = some (some (.list Srt.list [k])) := rfl
theorem hook_push (s : Srt) (k : GroundTerm) (a : List GroundTerm) :
    hook listPush [k, .list s a] = some (some (.list Srt.list (k :: a))) := rfl
theorem hook_size (s : Srt) (a : List GroundTerm) :
    hook listSize [.list s a] = some (some (int a.length)) := rfl
theorem hook_in (s : Srt) (a : List GroundTerm) (k : GroundTerm) :
    hook listIn [k, .list s a] = some (some (bool (decide (k ∈ a)))) := by
  show some (some (bool (a.any fun e => cmp k e == .eq))) = _
  congr 3
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨e, he, h⟩; rw [cmp_eq_iff.mp (beq_iff_eq.mp h)]; exact he
  · intro h; exact ⟨k, h, by simp [cmp_refl]⟩

/-- `L[I]`: the element at I from the front (`0 ≤ I`) or from the back (`I < 0`); `hook` gives no value out
of range (a silent point of `L[I]`, `silentTable`). -/
theorem hook_get_nonneg (s : Srt) (a : List GroundTerm) (i : Nat) :
    hook listGet [.list s a, int i] = some a[i]? := by
  show some ((listIndex a.length i).bind (a[·]?)) = _
  unfold listIndex
  by_cases h : i < a.length
  · simp [h]
  · simp [h]

theorem hook_get_neg (s : Srt) (a : List GroundTerm) (i : Nat) (h : i < a.length) :
    hook listGet [.list s a, int (-(i + 1 : Nat))] = some a[a.length - (i + 1)]? := by
  show some ((listIndex a.length (-(i + 1 : Nat))).bind (a[·]?)) = _
  unfold listIndex
  have h1 : ¬ (0 : Int) ≤ -((i + 1 : Nat) : Int) := by omega
  have h2 : -(a.length : Int) ≤ -((i + 1 : Nat) : Int) := by omega
  simp only [h1, h2, if_false, if_true, Option.bind_some]
  have : (-((i + 1 : Nat) : Int)).natAbs = i + 1 := by omega
  rw [this]

/-- A list of the library's sort `List`: elements of sort KItem. -/
theorem sortOf_list {c : Semantics} {es : List GroundTerm} :
    c.sortOf (.list Srt.list es) = match c.sortsOf es with
      | some ss => if ss.all (· == Srt.kitem) then some Srt.list else none
      | none => none := by
  rw [Semantics.sortOf]
  cases c.sortsOf es <;> rfl

end List'

/-- Two lists of the same collection sort are equal exactly when their elements are. -/
theorem List'.ext {s : Srt} {a b : List GroundTerm} : GroundTerm.list s a = .list s b ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ rfl⟩

end KCore
