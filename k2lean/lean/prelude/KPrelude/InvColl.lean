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


section

variable [Std.TransOrd K] [Std.LawfulEqOrd K]

/-! ### Map walks: `f(.Map) => true`, `f((K |-> V) REST) => φ(K, V) andBool f(REST)` -/

/-- Erasing a bound key shortens a sorted association list. -/
theorem _root_.KPrelude.SAL.length_erase_lt {α β : Type} [Ord α] {k : α} {v : β} :
    ∀ {m : List (α × β)}, SAL.lookup k m = some v → (SAL.erase k m).length < m.length
  | [], h => by simp [SAL.lookup] at h
  | (k', v') :: t, h => by
    cases hc : compare k k' with
    | lt => simp [SAL.lookup, hc] at h
    | eq => simp [SAL.erase, hc]
    | gt =>
      simp only [SAL.lookup, hc] at h
      simp only [SAL.erase, hc, List.length_cons]
      have := SAL.length_erase_lt h
      omega

/-- The first nonempty list of one list is that list. -/
theorem _root_.KPrelude.firstNonempty_singleton {β : Type} (l : List β) : firstNonempty [l] = l := by
  cases l <;> rfl

/-- A function on maps that satisfies the equations of a K walk `f(.Map) => true`,
`f((K |-> V) REST) => φ(K, V) andBool f(REST)`, read through the walk's instances (a value
`true` at a nonempty map comes from a binding whose test `ψ` holds and whose rest is `true`; a
well-formed nonempty map whose every binding passes and has a `true` rest is `true`), is `true`
exactly on the well-formed maps whose every binding passes. By induction on the number of
bindings, the rest at a binding having one fewer. -/
theorem all_iff_of_walk {f : M → Option Bool} {ψ : K → V → Prop}
    (h1 : f unit = some true)
    (h2 : ∀ m, m ≠ unit → f m = some true →
      WF m ∧ ∃ k v, (k, v) ∈ toList m ∧ ψ k v ∧ f (remove m k) = some true)
    (h3 : ∀ m, m ≠ unit → WF m →
      (∀ k v, (k, v) ∈ toList m → ψ k v ∧ f (remove m k) = some true) → f m = some true)
    (m : M) : f m = some true ↔ WF m ∧ EntriesOn (fun p => ψ p.1 p.2) m := by
  suffices H : ∀ n (m : M), (toList m).length = n →
      (f m = some true ↔ WF m ∧ EntriesOn (fun p => ψ p.1 p.2) m) from H _ m rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hn
    have shorter : ∀ {k v}, WF m → (k, v) ∈ toList m → (toList (remove m k)).length < n := by
      intro k v hw hk
      rw [remove_def, toList_ofList, ← hn]
      exact SAL.length_erase_lt (by rw [← lookup_def]; exact lookup_of_mem_toList hw hk)
    by_cases hu : m = unit
    · subst hu
      exact ⟨fun _ => ⟨wf_unit, entriesOn_unit⟩, fun _ => h1⟩
    constructor
    · intro h
      obtain ⟨hw, k, v, hk, hψ, hr⟩ := h2 m hu h
      have hl := lookup_of_mem_toList hw hk
      obtain ⟨-, hrest⟩ := (ih _ (shorter hw hk) (remove m k) rfl).1 hr
      exact ⟨hw, entriesOn_concat (concat_element_remove hw hl) (entriesOn_element hψ) hrest⟩
    · rintro ⟨hw, he⟩
      refine h3 m hu hw fun k v hk => ⟨he (k, v) hk, ?_⟩
      exact (ih _ (shorter hw hk) (remove m k) rfl).2 ⟨wf_remove hw, entriesOn_remove he⟩


/-- A nonempty map has a binding. -/
theorem toList_ne_nil_of_ne_unit {m : M} (h : m ≠ unit) : toList m ≠ [] := by
  intro hl
  apply h
  rw [← ofList_toList m, hl]
  rfl

/-- The first instance of a free-key equation is an instance at some binding. -/
theorem mem_of_head?_chooseAll {β : Type} {m : M} {g : K → V → List β} {b : β}
    (h : (chooseAll m g).head? = some b) : ∃ k v, (k, v) ∈ toList m ∧ b ∈ g k v := by
  unfold chooseAll at h
  obtain ⟨p, hp, hb⟩ := List.mem_flatMap.1 (List.mem_of_mem_head? h)
  exact ⟨p.1, p.2, hp, hb⟩

/-- A nonempty map at whose every binding the instances are `[b]` has the first instance `b`. -/
theorem head?_chooseAll_of_forall {β : Type} {m : M} {g : K → V → List β} {b : β}
    (hm : toList m ≠ []) (h : ∀ k v, (k, v) ∈ toList m → g k v = [b]) :
    (chooseAll m g).head? = some b := by
  unfold chooseAll
  cases hl : toList m with
  | nil => exact absurd hl hm
  | cons p t =>
    rw [List.flatMap_cons, h p.1 p.2 (by rw [hl]; exact List.mem_cons_self ..)]
    rfl


/-- A defined `M₁ M₂` is well formed: `concat` is defined only on sorted operands with disjoint
keys, and inserts the bindings of one into the other. -/
theorem wf_of_concat {a b m : M} (h : concat a b = some m) : WF m := by
  unfold concat SAL.concat at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    unfold WF
    rw [toList_ofList]
    simp only [Bool.and_eq_true] at hc
    have hb : SAL.Sorted (toList b) := (SAL.sortedb_iff _).1 hc.1.2
    induction toList a with
    | nil => exact hb
    | cons p t ih => exact SAL.sorted_insert ih
  · simp at h

/- The facts that a rule's rebuilt map is well formed, for the collections closer (a map walk's
element-wise form, `all_iff_of_walk`, states it). -/
attribute [k2l_coll] wf_of_concat wf_rest_of_concat_element wf_update wf_remove wf_unit wf_element

/-! ### Keys of a map that a rule extends or updates -/

theorem inKeys_iff_lookup {x : K} {m : M} : inKeys x m = true ↔ ∃ v, lookup m x = some v := by
  show (lookup m x).isSome = true ↔ _
  cases lookup m x <;> simp

/-- A key of the right operand of a defined `M₁ M₂` is a key of the result. -/
@[k2l_coll] theorem inKeys_of_concat_right {a b m : M} {x : K} (h : concat a b = some m)
    (hx : inKeys x b = true) : inKeys x m = true := by
  obtain ⟨v, hv⟩ := inKeys_iff_lookup.1 hx
  rw [lookup_def] at hv
  have hm := (mem_toList_of_concat h).2 (Or.inr (SAL.lookup_mem hv))
  exact inKeys_iff_lookup.2 ⟨v, lookup_of_mem_toList (wf_of_concat h) hm⟩

/-- A key of the left operand of a defined `M₁ M₂` is a key of the result. -/
@[k2l_coll] theorem inKeys_of_concat_left {a b m : M} {x : K} (h : concat a b = some m)
    (hx : inKeys x a = true) : inKeys x m = true := by
  obtain ⟨v, hv⟩ := inKeys_iff_lookup.1 hx
  rw [lookup_def] at hv
  have hm := (mem_toList_of_concat h).2 (Or.inl (SAL.lookup_mem hv))
  exact inKeys_iff_lookup.2 ⟨v, lookup_of_mem_toList (wf_of_concat h) hm⟩

/-- Rebinding a key keeps the keys: a key of `K |-> W REST` is a key of `K |-> V REST`. -/
@[k2l_coll] theorem inKeys_of_concat_element_rebind {k x : K} {v w : V} {r m m' : M}
    (h : concat (element k v) r = some m') (hx : inKeys x m = true)
    (h' : concat (element k w) r = some m) : inKeys x m' = true := by
  obtain ⟨u, hu⟩ := inKeys_iff_lookup.1 hx
  rw [lookup_def] at hu
  rcases (mem_toList_of_concat h').1 (SAL.lookup_mem hu) with hp | hp
  · have : x = k := by
      unfold element at hp; rw [toList_ofList] at hp; simp at hp; exact hp.1
    subst this
    exact inKeys_of_concat_left h (inKeys_iff_lookup.2 ⟨v, by
      rw [lookup_def]; unfold element; rw [toList_ofList]; simp [SAL.lookup]⟩)
  · exact inKeys_of_concat_right h (inKeys_iff_lookup.2 ⟨u, lookup_of_mem_toList (wf_rest_of_concat_element h) hp⟩)
/-- A key stays a key after `M[K <- V]`. -/
@[k2l_coll] theorem inKeys_update_of_inKeys {m : M} {x k : K} {v : V} (hx : inKeys x m = true) :
    inKeys x (update m k v) = true := by
  by_cases hk : x = k
  · subst hk; exact inKeys_iff_lookup.2 ⟨v, lookup_update_self m x v⟩
  · obtain ⟨w, hw⟩ := inKeys_iff_lookup.1 hx
    exact inKeys_iff_lookup.2 ⟨w, (lookup_update_ne m v hk).trans hw⟩

/-- The key of `M[K <- V]`. -/
@[k2l_coll] theorem inKeys_update_self {m : M} {k : K} {v : V} : inKeys k (update m k v) = true :=
  inKeys_iff_lookup.2 ⟨v, lookup_update_self m k v⟩

/-- `EntriesOn` of a weaker predicate. -/
theorem entriesOn_mono {Q Q' : K × V → Prop} {m : M} (h : EntriesOn Q m) (hq : ∀ p, Q p → Q' p) :
    EntriesOn Q' m := fun p hp => hq p (h p hp)

/-- Every key of `S` is a key of `S'`: what an invariant that reads `S` only through its keys
(`inKeys x S = true`, a map walk's test) needs of the map a rule leaves there. -/
def KeysIncl (S S' : M) : Prop := ∀ x, inKeys x S = true → inKeys x S' = true

/-- A map rebound at one key keeps its keys. -/
theorem keysIncl_rebind {k : K} {v w : V} {r m m' : M} (h' : concat (element k w) r = some m)
    (h : concat (element k v) r = some m') : KeysIncl m m' :=
  fun _ hx => inKeys_of_concat_element_rebind h hx h'

@[k2l_coll] theorem keysIncl_update {S : M} {k : K} {v : V} : KeysIncl S (update S k v) :=
  fun _ hx => inKeys_update_of_inKeys hx

/-- Each operand of a defined `concat` has its keys in the result. -/
@[k2l_coll] theorem keysIncl_concat_left {S T S' : M} (h : concat S T = some S') : KeysIncl S S' :=
  fun _ hx => inKeys_of_concat_left h hx

theorem keysIncl_concat_right {S T S' : M} (h : concat S T = some S') : KeysIncl T S' :=
  fun _ hx => inKeys_of_concat_right h hx

/-- The key of a binding added by `concat` is a key of the result. -/
theorem inKeys_of_concat_element_self {k : K} {v : V} {r m : M} (h : concat (element k v) r = some m) :
    inKeys k m = true := by
  obtain ⟨_, _, rfl⟩ := concat_element_iff.1 h
  exact inKeys_update_self

/-- Monotonicity in the referenced map, in the normal form of a test that a value is one of its
keys (a walk's test after the unfolding set): every value of `m` stays a key when the keys only
grow. -/
@[k2l_coll] theorem entriesOn_inKeys_mono {M₂ K₂ : Type} [ListIso M₂ (K₂ × K)] {m : M₂} {S S' : M}
    (hm : EntriesOn (fun q => inKeys q.2 S = true) m) (h : KeysIncl S S') :
    EntriesOn (fun q => inKeys q.2 S' = true) m :=
  fun p hp => h _ (hm p hp)

end

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
