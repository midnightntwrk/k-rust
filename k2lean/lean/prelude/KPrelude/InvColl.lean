import KPrelude.Ext
import KPrelude.InvAttr

/-!
# Collection preservation lemmas

A predicate on the keys, values or entries of a `Map` (on the elements of a `Set` or a `List`)
kept by each hook operation the prelude defines, and read off each pattern a rule's left-hand
side can match.

- Maps: `MapHook.EntriesOn Q m` (every binding `(k, v)` satisfies `Q`). `KeysOn` (also used by
  `KPrelude.Relate` for pointwise map translations) and `ValuesOn` are the special cases
  `Q p := P p.1` and `Q p := R p.2`, and the `@[k2l_pres]` lemmas `keysOn_eq`, `valuesOn_eq`
  rewrite them into `EntriesOn`, so one lemma per operation serves all three.
- Sets: `SetHook.ElemsOn Q s`; lists: `ListHook.ElemsOn Q l`.

Lemmas whose conclusion is the predicate on an operation's result carry `@[k2l_coll]`, so
`k2l_preserve` tries them by `apply`. Lemmas that read a fact off a pattern
(`entry_of_concat_element`: the bound key and value of `K |-> V REST` satisfy `Q`) are stated
for direct use; the ones whose conclusion is again an `EntriesOn` are `@[k2l_coll]` too.
`k2l_preserve` also uses the pattern lemmas forwards (`entriesOn_of_concat_left`, `_right`,
`entry_of_concat_element`, `entry_of_concat_element_right`): from the invariant of a matched
collection and the rule's match `concat a b = some m` it adds the facts about the parts, which is
how the invariant of one element of a cell map (a free-key match `K |-> E REST`) reaches the
element the rule rebuilds.

The `Sorted`-list facts these lemmas rest on (`SAL.mem_insert_self`, `SAL.mem_concat`, ...) are in
`KPrelude.SAL`.

The map lemmas need the order laws (`Std.TransOrd`, `Std.LawfulEqOrd`), which every generated
key sort has.
-/

set_option linter.unusedSectionVars false

namespace KPrelude

/-! ## Maps -/

namespace MapHook

open ListIso

section

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]

/-- Every key of `m` satisfies `P`. -/
def KeysOn (P : K → Prop) (m : M) : Prop := ∀ p ∈ toList m, P p.1

end

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]
  [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- Every binding of `m` satisfies `Q`. -/
def EntriesOn (Q : K × V → Prop) (m : M) : Prop := ∀ p ∈ toList m, Q p

/-- Every value of `m` satisfies `Q`. -/
def ValuesOn (Q : V → Prop) (m : M) : Prop := ∀ p ∈ toList m, Q p.2

variable {Q : K × V → Prop} {m a b r : M} {k : K} {v : V}

@[k2l_pres] theorem keysOn_eq (P : K → Prop) (m : M) :
    KeysOn P m = EntriesOn (fun p => P p.1) m := rfl

@[k2l_pres] theorem valuesOn_eq (R : V → Prop) (m : M) :
    ValuesOn R m = EntriesOn (fun p => R p.2) m := rfl

theorem mem_toList_of_concat (h : concat a b = some m) {p : K × V} :
    p ∈ toList m ↔ p ∈ toList a ∨ p ∈ toList b := by
  unfold concat at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨l, hl, rfl⟩ := h
  rw [toList_ofList]
  exact SAL.mem_concat hl

@[k2l_coll] theorem entriesOn_unit : EntriesOn Q (unit : M) := by
  intro p hp
  unfold unit at hp
  rw [toList_ofList] at hp
  simp at hp

@[k2l_coll] theorem entriesOn_element (h : Q (k, v)) : EntriesOn Q (element k v : M) := by
  intro p hp
  unfold element at hp
  rw [toList_ofList, List.mem_singleton] at hp
  exact hp ▸ h

/-- `M[K <- V]` (and a map pattern's right-hand side `K |-> V REST` built by `update`). -/
@[k2l_coll] theorem entriesOn_update (hm : EntriesOn Q m) (h : Q (k, v)) :
    EntriesOn Q (update m k v) := by
  intro p hp
  rw [update_def, toList_ofList] at hp
  rcases SAL.mem_insert hp with rfl | hp
  · exact h
  · exact hm p hp

theorem keysOn_update {P : K → Prop} (hm : KeysOn P m) (hk : P k) : KeysOn P (update m k v) :=
  entriesOn_update (Q := fun p => P p.1) hm hk

/-- `M[K <- undef]` -/
@[k2l_coll] theorem entriesOn_remove (hm : EntriesOn Q m) : EntriesOn Q (remove m k) := by
  intro p hp
  rw [remove_def, toList_ofList] at hp
  exact hm p (SAL.mem_erase hp)

/-- `M₁ M₂` built on a right-hand side (the result is defined). -/
@[k2l_coll] theorem entriesOn_concat (h : concat a b = some m) (ha : EntriesOn Q a)
    (hb : EntriesOn Q b) : EntriesOn Q m := by
  intro p hp
  rcases (mem_toList_of_concat h).1 hp with hp | hp
  · exact ha p hp
  · exact hb p hp

/-- The left operand of a matched `M₁ M₂`. -/
@[k2l_coll] theorem entriesOn_of_concat_left (h : concat a b = some m) (hm : EntriesOn Q m) :
    EntriesOn Q a :=
  fun p hp => hm p ((mem_toList_of_concat h).2 (Or.inl hp))

/-- The right operand of a matched `M₁ M₂`; for the pattern `K |-> V REST`, the rest. -/
@[k2l_coll] theorem entriesOn_of_concat_right (h : concat a b = some m) (hm : EntriesOn Q m) :
    EntriesOn Q b :=
  fun p hp => hm p ((mem_toList_of_concat h).2 (Or.inr hp))

/-- The bound key and value of a matched `K |-> V REST`. -/
theorem entry_of_concat_element (h : concat (element k v) r = some m) (hm : EntriesOn Q m) :
    Q (k, v) := by
  refine hm (k, v) ((mem_toList_of_concat h).2 (Or.inl ?_))
  unfold element; rw [toList_ofList]; simp

/-- The bound key and value of a matched `REST K |-> V`. -/
theorem entry_of_concat_element_right (h : concat r (element k v) = some m) (hm : EntriesOn Q m) :
    Q (k, v) := by
  refine hm (k, v) ((mem_toList_of_concat h).2 (Or.inr ?_))
  unfold element; rw [toList_ofList]; simp

/-- A defined lookup `M[K]`. -/
theorem entry_of_lookup (hm : EntriesOn Q m) (h : lookup m k = some v) : Q (k, v) := by
  rw [lookup_def] at h
  exact hm _ (SAL.lookup_mem h)

/-- `M[K] orDefault D`. -/
theorem value_of_lookupOrDefault {R : V → Prop} {d : V} (hm : EntriesOn (fun p => R p.2) m)
    (hd : R d) : R (lookupOrDefault m k d) := by
  unfold lookupOrDefault
  rw [MapRepr.lookupR_eq]
  cases hl : SAL.lookup k (toList m) with
  | none => exact hd
  | some w => exact hm (k, w) (SAL.lookup_mem hl)

/-- Every binding of a well-formed map is one of its matches `K |-> V REST` (`MapHook.choose`
enumerates them); its key and value satisfy `Q`. -/
theorem entry_of_mem (hm : EntriesOn Q m) {p : K × V} (hp : p ∈ toList m) : Q p := hm p hp

theorem entriesOn_foldl_update {l : List (K × V)} (hl : ∀ p ∈ l, Q p) :
    ∀ {a : M}, EntriesOn Q a → EntriesOn Q (l.foldl (fun m p => update m p.1 p.2) a) := by
  induction l with
  | nil => intro a ha; exact ha
  | cons q t ih =>
    intro a ha
    simp only [List.foldl_cons]
    exact ih (fun p hp => hl p (List.mem_cons_of_mem _ hp))
      (entriesOn_update ha (hl q (by simp)))

/-- `updateMap(M, N)` -/
@[k2l_coll] theorem entriesOn_updateAll (ha : EntriesOn Q a) (hb : EntriesOn Q b) :
    EntriesOn Q (updateAll a b) :=
  entriesOn_foldl_update hb ha

/-- `removeAll(M, S)` -/
@[k2l_coll] theorem entriesOn_removeAll {S : Type} [ListIso S (K × Unit)] {s : S}
    (ha : EntriesOn Q a) : EntriesOn Q (removeAll a s) := by
  unfold removeAll
  generalize toList s = l
  induction l generalizing a with
  | nil => exact ha
  | cons q t ih => simp only [List.foldl_cons]; exact ih (entriesOn_remove ha)

/-- `M -Map N` -/
@[k2l_coll] theorem entriesOn_difference [DecidableEq V] (ha : EntriesOn Q a) :
    EntriesOn Q (difference a b) := by
  intro p hp
  unfold difference at hp
  rw [toList_ofList] at hp
  exact ha p (List.mem_filter.1 hp).1

/-- A map built by a recursion on an `Int` range, `.Map` above the bound `b` and `key a |-> v`
added to the map from `a + 1` up to it (SIMPLE's array allocation `N ... M |-> K`), binds `v`
at each of its keys, so it satisfies every `Q` that holds of `(key a, v)` for all `a`. By
induction on the number of keys left, `(b + 1 - a).toNat`, which the second equation lowers by
one; the hypotheses are the function's two equations, so the lemma holds of whatever the
function does outside the range. -/
theorem entriesOn_of_range {Q : K × V → Prop} {f : Int → Option M} {b : Int} {key : Int → K}
    {v : V} (h1 : ∀ a, IntHook.gt a b = true → f a = some unit)
    (h2 : ∀ a, IntHook.le a b = true →
      f a = (f (IntHook.add a 1)).bind fun r => concat (element (key a) v) r)
    (hq : ∀ a, Q (key a, v)) {a : Int} {r : M} (h : f a = some r) : EntriesOn Q r := by
  suffices H : ∀ n a r, (b + 1 - a).toNat = n → f a = some r → EntriesOn Q r from
    H _ a r rfl h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a r hn h
    by_cases hab : IntHook.gt a b = true
    · rw [h1 a hab] at h
      obtain rfl := Option.some.inj h
      exact entriesOn_unit
    · have hle : IntHook.le a b = true := by
        simp only [IntHook.gt, IntHook.le, decide_eq_true_eq] at hab ⊢
        omega
      rw [h2 a hle] at h
      cases hrest : f (IntHook.add a 1) with
      | none => simp [hrest] at h
      | some r' =>
        simp only [hrest, Option.bind_some] at h
        refine entriesOn_concat h (entriesOn_element (hq a)) ?_
        have hlt : (b + 1 - IntHook.add a 1).toNat < n := by
          simp only [IntHook.le, decide_eq_true_eq] at hle
          simp only [IntHook.add]
          omega
        exact ih _ hlt _ _ rfl hrest

end MapHook

/-! ## Sets -/

namespace SetHook

open ListIso

variable {S K : Type} [Ord K] [ListIso S (K × Unit)] [MapRepr S K Unit]
  [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- Every element of `s` satisfies `Q`. -/
def ElemsOn (Q : K → Prop) (s : S) : Prop := ∀ p ∈ toList s, Q p.1

variable {Q : K → Prop} {s a b : S} {k : K}

theorem elemsOn_iff_keysOn : ElemsOn Q s ↔ MapHook.KeysOn Q s := Iff.rfl

theorem elemsOn_iff_entriesOn : ElemsOn Q s ↔ MapHook.EntriesOn (fun p => Q p.1) s := Iff.rfl

@[k2l_coll] theorem elemsOn_unit : ElemsOn Q (unit : S) := MapHook.entriesOn_unit

@[k2l_coll] theorem elemsOn_element (h : Q k) : ElemsOn Q (element k : S) :=
  MapHook.entriesOn_element (Q := fun p => Q p.1) h

@[k2l_coll] theorem elemsOn_concat {c : S} (h : concat a b = some c) (ha : ElemsOn Q a)
    (hb : ElemsOn Q b) : ElemsOn Q c :=
  MapHook.entriesOn_concat (Q := fun p => Q p.1) h ha hb

@[k2l_coll] theorem elemsOn_of_concat_left {c : S} (h : concat a b = some c) (hc : ElemsOn Q c) :
    ElemsOn Q a :=
  MapHook.entriesOn_of_concat_left (Q := fun p => Q p.1) h hc

@[k2l_coll] theorem elemsOn_of_concat_right {c : S} (h : concat a b = some c) (hc : ElemsOn Q c) :
    ElemsOn Q b :=
  MapHook.entriesOn_of_concat_right (Q := fun p => Q p.1) h hc

/-- The element of a matched `SetItem(K) REST`. -/
theorem elem_of_concat_element {r c : S} (h : concat (element k) r = some c) (hc : ElemsOn Q c) :
    Q k :=
  MapHook.entry_of_concat_element (Q := fun p => Q p.1) h hc

theorem elemsOn_foldl_update {l : List (K × Unit)} (hl : ∀ p ∈ l, Q p.1) :
    ∀ {a : S}, ElemsOn Q a → ElemsOn Q (l.foldl (fun s p => MapHook.update s p.1 ()) a) := by
  induction l with
  | nil => intro a ha; exact ha
  | cons q t ih =>
    intro a ha
    simp only [List.foldl_cons]
    exact ih (fun p hp => hl p (List.mem_cons_of_mem _ hp))
      (MapHook.entriesOn_update (Q := fun p => Q p.1) ha (hl q (by simp)))

/-- `S₁ |Set S₂` -/
@[k2l_coll] theorem elemsOn_union (ha : ElemsOn Q a) (hb : ElemsOn Q b) : ElemsOn Q (union a b) :=
  elemsOn_foldl_update hb ha

/-- `S₁ -Set S₂` -/
@[k2l_coll] theorem elemsOn_difference (ha : ElemsOn Q a) : ElemsOn Q (difference a b) := by
  intro p hp
  unfold difference at hp
  rw [toList_ofList] at hp
  exact ha p (List.mem_filter.1 hp).1

/-- `intersectSet(S₁, S₂)` -/
@[k2l_coll] theorem elemsOn_intersection (ha : ElemsOn Q a) : ElemsOn Q (intersection a b) := by
  intro p hp
  unfold intersection at hp
  rw [toList_ofList] at hp
  exact ha p (List.mem_filter.1 hp).1

/-- A set literal. -/
@[k2l_coll] theorem elemsOn_ofElems {l : List K} (hl : ∀ x ∈ l, Q x) : ElemsOn Q (ofElems l : S) := by
  unfold ofElems
  suffices ∀ (l : List K) (a : S), (∀ x ∈ l, Q x) → ElemsOn Q a →
      ElemsOn Q (l.foldl (fun s k => MapHook.update s k ()) a) from this l _ hl elemsOn_unit
  intro l
  induction l with
  | nil => intro a _ ha; exact ha
  | cons x t ih =>
    intro a hl ha
    simp only [List.foldl_cons]
    exact ih _ (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      (MapHook.entriesOn_update (Q := fun p => Q p.1) ha (hl x (by simp)))

/-- `keys(M)` -/
@[k2l_coll] theorem elemsOn_keys {M V : Type} [ListIso M (K × V)] [MapRepr M K V] {m : M}
    (hm : MapHook.EntriesOn (fun p => Q p.1) m) : ElemsOn Q (MapHook.keys m : S) := by
  intro p hp
  unfold MapHook.keys at hp
  rw [toList_ofList, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact hm q hq

end SetHook

/-! ## Lists -/

namespace ListHook

open ListIso

variable {L E : Type} [ListIso L E]

/-- Every element of `l` satisfies `Q`. -/
def ElemsOn (Q : E → Prop) (l : L) : Prop := ∀ x ∈ toList l, Q x

variable {Q : E → Prop} {l a b t : L} {x : E}

@[k2l_coll] theorem elemsOn_unit : ElemsOn Q (unit : L) := by
  intro y hy; unfold unit at hy; rw [toList_ofList] at hy; simp at hy

@[k2l_coll] theorem elemsOn_element (h : Q x) : ElemsOn Q (element x : L) := by
  intro y hy; unfold element at hy; rw [toList_ofList, List.mem_singleton] at hy; exact hy ▸ h

theorem elemsOn_concat_iff : ElemsOn Q (concat a b) ↔ ElemsOn Q a ∧ ElemsOn Q b := by
  unfold ElemsOn concat
  rw [toList_ofList]
  simp only [List.mem_append]
  exact ⟨fun h => ⟨fun y hy => h y (.inl hy), fun y hy => h y (.inr hy)⟩,
    fun ⟨ha, hb⟩ y hy => hy.elim (ha y) (hb y)⟩

/-- `L₁ L₂` (and `ListItem(X) REST`, `REST ListItem(X)` on a right-hand side). -/
@[k2l_coll] theorem elemsOn_concat (ha : ElemsOn Q a) (hb : ElemsOn Q b) : ElemsOn Q (concat a b) :=
  elemsOn_concat_iff.2 ⟨ha, hb⟩

/-- `pushList(E, L)` -/
@[k2l_coll] theorem elemsOn_push (hx : Q x) (hl : ElemsOn Q l) : ElemsOn Q (push x l) := by
  intro y hy
  unfold push at hy
  rw [toList_ofList, List.mem_cons] at hy
  exact hy.elim (fun h => h ▸ hx) (hl y)

/-- A defined `L[I]`. -/
theorem elem_of_get {i : Int} (hl : ElemsOn Q l) (h : get l i = some x) : Q x := by
  unfold get at h
  simp only at h
  split at h
  · exact hl x (List.mem_of_getElem? h)
  · split at h
    · exact hl x (List.mem_of_getElem? h)
    · simp at h

/-- A defined `L[I <- V]`. -/
@[k2l_coll] theorem elemsOn_update {i : Int} {l' : L} (h : update l i x = some l')
    (hl : ElemsOn Q l) (hx : Q x) : ElemsOn Q l' := by
  unfold update at h
  simp only at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    intro y hy
    rw [toList_ofList] at hy
    rcases List.mem_or_eq_of_mem_set hy with hy | rfl
    · exact hl y hy
    · exact hx
  · simp at h

/-- A defined `makeList(N, V)`. -/
@[k2l_coll] theorem elemsOn_make {n : Int} {l' : L} (h : make n x = some l') (hx : Q x) :
    ElemsOn Q l' := by
  unfold make at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    intro y hy
    rw [toList_ofList] at hy
    exact (List.eq_of_mem_replicate hy) ▸ hx
  · simp at h

/-- A defined `range(L, A, B)`. -/
@[k2l_coll] theorem elemsOn_range {i j : Int} {l' : L} (h : range l i j = some l')
    (hl : ElemsOn Q l) : ElemsOn Q l' := by
  unfold range at h
  simp only at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    intro y hy
    rw [toList_ofList] at hy
    exact hl y (List.mem_of_mem_drop (List.mem_of_mem_take hy))
  · simp at h

/-- The head of a matched `ListItem(X) REST`. -/
theorem elem_of_uncons (h : uncons l = some (x, t)) (hl : ElemsOn Q l) : Q x := by
  rw [← concat_element_of_uncons h] at hl
  exact (elemsOn_concat_iff.1 hl).1 x (by unfold element; rw [toList_ofList]; simp)

/-- The rest of a matched `ListItem(X) REST`. -/
@[k2l_coll] theorem elemsOn_of_uncons (h : uncons l = some (x, t)) (hl : ElemsOn Q l) :
    ElemsOn Q t := by
  rw [← concat_element_of_uncons h] at hl
  exact (elemsOn_concat_iff.1 hl).2

/-- The last element of a matched `REST ListItem(X)`. -/
theorem elem_of_unsnoc (h : unsnoc l = some (t, x)) (hl : ElemsOn Q l) : Q x := by
  rw [← concat_element_of_unsnoc h] at hl
  exact (elemsOn_concat_iff.1 hl).2 x (by unfold element; rw [toList_ofList]; simp)

/-- The front of a matched `REST ListItem(X)`. -/
@[k2l_coll] theorem elemsOn_of_unsnoc (h : unsnoc l = some (t, x)) (hl : ElemsOn Q l) :
    ElemsOn Q t := by
  rw [← concat_element_of_unsnoc h] at hl
  exact (elemsOn_concat_iff.1 hl).1

/-- A list literal. -/
@[k2l_coll] theorem elemsOn_ofElems {l : List E} (hl : ∀ y ∈ l, Q y) : ElemsOn Q (ofElems l : L) := by
  intro y hy; unfold ofElems at hy; rw [toList_ofList] at hy; exact hl y hy

/-- `values(M)` -/
@[k2l_coll] theorem elemsOn_values {M K : Type} [Ord K] [ListIso M (K × E)] [MapRepr M K E]
    {m : M} (hm : MapHook.EntriesOn (fun p => Q p.2) m) : ElemsOn Q (MapHook.values m : L) := by
  intro y hy
  unfold MapHook.values at hy
  rw [toList_ofList, List.mem_map] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  exact hm q hq

/-- `keys_list(M)` -/
@[k2l_coll] theorem elemsOn_keysList {M V : Type} [Ord E] [ListIso M (E × V)] [MapRepr M E V]
    {m : M} (hm : MapHook.EntriesOn (fun p => Q p.1) m) : ElemsOn Q (MapHook.keysList m : L) := by
  intro y hy
  unfold MapHook.keysList at hy
  rw [toList_ofList, List.mem_map] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  exact hm q hq

end ListHook

end KPrelude
