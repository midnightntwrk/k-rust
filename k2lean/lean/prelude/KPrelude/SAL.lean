import KPrelude.Order

/-!
# Sorted association lists

K's `Map` is a finite map with extensional equality (`domains.md`, `MAP`: `_Map_` is
associative, commutative, has unit `.Map`, and is undefined when the two maps share a key).
A canonical representation makes Lean's `=` coincide with that equality: the entries sorted
strictly by key under a lawful linear order. `Sorted` is the well-formedness invariant; every
operation here preserves it, and the lemmas below are what the generated adequacy and
determinism proofs use for map patterns.

`Set` values use the same lists with `Unit` values (`SetItem` is a key with no value).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace KPrelude.SAL

variable {α β : Type} [Ord α]

/-- Keys strictly increasing. -/
inductive Sorted : List (α × β) → Prop
  | nil : Sorted []
  | cons {k : α} {v : β} {t : List (α × β)} :
      (∀ p ∈ t, compare k p.1 = .lt) → Sorted t → Sorted ((k, v) :: t)

/-- The executable check of `Sorted`. -/
def sortedb : List (α × β) → Bool
  | [] => true
  | (k, _) :: t => t.all (fun p => compare k p.1 == .lt) && sortedb t

theorem sortedb_iff : ∀ (m : List (α × β)), sortedb m = true ↔ Sorted m
  | [] => by simp [sortedb, Sorted.nil]
  | (k, v) :: t => by
    simp only [sortedb, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, sortedb_iff t]
    constructor
    · rintro ⟨h1, h2⟩; exact Sorted.cons h1 h2
    · rintro (_ | ⟨h1, h2⟩); exact ⟨h1, h2⟩

def lookup (k : α) : List (α × β) → Option β
  | [] => none
  | (k', v) :: t =>
    match compare k k' with
    | .lt => none
    | .eq => some v
    | .gt => lookup k t

def insert (k : α) (v : β) : List (α × β) → List (α × β)
  | [] => [(k, v)]
  | (k', v') :: t =>
    match compare k k' with
    | .lt => (k, v) :: (k', v') :: t
    | .eq => (k, v) :: t
    | .gt => (k', v') :: insert k v t

def erase (k : α) : List (α × β) → List (α × β)
  | [] => []
  | (k', v') :: t =>
    match compare k k' with
    | .lt => (k', v') :: t
    | .eq => t
    | .gt => (k', v') :: erase k t

/-- `_Map_`: defined only on well-formed operands with disjoint keys. -/
def concat (m₁ m₂ : List (α × β)) : Option (List (α × β)) :=
  if sortedb m₁ && sortedb m₂ && m₁.all (fun p => (lookup p.1 m₂).isNone) then
    some (m₁.foldr (fun p acc => insert p.1 p.2 acc) m₂)
  else none

section Laws

variable [Std.TransOrd α] [Std.LawfulEqOrd α]

/-- The linear-time check of `Sorted` (adjacent keys), used by the executable matchers. -/
def sortedAdj : List (α × β) → Bool
  | [] => true
  | [_] => true
  | (k₁, _) :: (k₂, v₂) :: t => compare k₁ k₂ == .lt && sortedAdj ((k₂, v₂) :: t)

theorem cmp_self (k : α) : compare k k = .eq := Std.ReflOrd.compare_self

theorem eq_of_cmp {k k' : α} (h : compare k k' = .eq) : k = k' := Std.LawfulEqOrd.eq_of_compare h

theorem gt_of_lt {k k' : α} (h : compare k k' = .lt) : compare k' k = .gt :=
  Std.OrientedCmp.gt_of_lt h

theorem lt_of_gt {k k' : α} (h : compare k k' = .gt) : compare k' k = .lt :=
  Std.OrientedCmp.lt_of_gt h

theorem lt_trans {a b c : α} (h₁ : compare a b = .lt) (h₂ : compare b c = .lt) : compare a c = .lt :=
  Std.TransCmp.lt_trans h₁ h₂

theorem sortedAdj_iff : ∀ (m : List (α × β)), sortedAdj m = true ↔ Sorted m
  | [] => by simp [sortedAdj, Sorted.nil]
  | [(k, v)] => ⟨fun _ => Sorted.cons (by simp) Sorted.nil, fun _ => rfl⟩
  | (k₁, v₁) :: (k₂, v₂) :: t => by
    simp only [sortedAdj, Bool.and_eq_true, beq_iff_eq, sortedAdj_iff ((k₂, v₂) :: t)]
    constructor
    · rintro ⟨h12, hs⟩
      refine Sorted.cons ?_ hs
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact h12
      · cases hs with | cons hlt _ => exact lt_trans h12 (hlt p hp)
    · rintro (_ | ⟨hlt, hs⟩)
      exact ⟨hlt (k₂, v₂) (by simp), hs⟩

theorem mem_insert {k : α} {v : β} {p : α × β} :
    ∀ {m : List (α × β)}, p ∈ insert k v m → p = (k, v) ∨ p ∈ m
  | [], h => by simp [insert] at h; exact Or.inl h
  | (k', v') :: t, h => by
    unfold insert at h
    split at h
    · simpa only [List.mem_cons] using h
    · simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · rcases mem_insert h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem mem_erase {k : α} {p : α × β} : ∀ {m : List (α × β)}, p ∈ erase k m → p ∈ m
  | [], h => by simp [erase] at h
  | (k', v') :: t, h => by
    unfold erase at h
    split at h
    · exact h
    · exact List.mem_cons_of_mem _ h
    · simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (mem_erase h)

theorem sorted_insert {k : α} {v : β} : ∀ {m : List (α × β)}, Sorted m → Sorted (insert k v m)
  | [], _ => Sorted.cons (by simp) Sorted.nil
  | (k', v') :: t, hs => by
    cases hs with
    | cons hlt ht =>
      unfold insert
      split
      · next h =>
        refine Sorted.cons ?_ (Sorted.cons hlt ht)
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact h
        · exact lt_trans h (hlt p hp)
      · next h =>
        cases eq_of_cmp h
        exact Sorted.cons hlt ht
      · next h =>
        refine Sorted.cons ?_ (sorted_insert ht)
        intro p hp
        rcases mem_insert hp with rfl | hp
        · exact lt_of_gt h
        · exact hlt p hp

theorem sorted_erase {k : α} : ∀ {m : List (α × β)}, Sorted m → Sorted (erase k m)
  | [], _ => Sorted.nil
  | (k', v') :: t, hs => by
    cases hs with
    | cons hlt ht =>
      unfold erase
      split
      · exact Sorted.cons hlt ht
      · exact ht
      · exact Sorted.cons (fun p hp => hlt p (mem_erase hp)) (sorted_erase ht)

theorem lookup_insert_self (k : α) (v : β) : ∀ (m : List (α × β)), lookup k (insert k v m) = some v
  | [] => by simp [insert, lookup, cmp_self]
  | (k', v') :: t => by
    unfold insert
    split
    · simp [lookup, cmp_self]
    · simp [lookup, cmp_self]
    · next h => simp only [lookup, h]; exact lookup_insert_self k v t

/-- A lookup after an insert at another key is unchanged. No sortedness is needed: `insert`
keeps the entries it passes, and `lookup k'` reads the same entries up to the place where
`insert` puts the new one, which it skips because `k' ≠ k`. -/
theorem lookup_insert_ne {k k' : α} (v : β) (hne : k' ≠ k) :
    ∀ (m : List (α × β)), lookup k' (insert k v m) = lookup k' m
  | [] => by
    simp only [insert, lookup]
    cases hc : compare k' k
    · rfl
    · exact absurd (eq_of_cmp hc) hne
    · rfl
  | (k₁, v₁) :: t => by
    unfold insert
    split
    · next h₁ =>
      simp only [lookup]
      cases hc : compare k' k
      · simp only [lt_trans hc h₁]
      · exact absurd (eq_of_cmp hc) hne
      · rfl
    · next h₁ =>
      cases eq_of_cmp h₁
      simp only [lookup]
      cases hc : compare k' k
      · rfl
      · exact absurd (eq_of_cmp hc) hne
      · rfl
    · simp only [lookup]
      split
      · rfl
      · rfl
      · exact lookup_insert_ne v hne t

/-- Below the least key, lookup finds nothing. -/
theorem lookup_of_lt {k : α} : ∀ {m : List (α × β)}, (∀ p ∈ m, compare k p.1 = .lt) → lookup k m = none
  | [], _ => rfl
  | (k', v') :: t, h => by
    have := h (k', v') (by simp)
    simp only [lookup, this]

theorem lookup_mem {k : α} {v : β} : ∀ {m : List (α × β)}, lookup k m = some v → (k, v) ∈ m
  | [], h => by simp [lookup] at h
  | (k', v') :: t, h => by
    unfold lookup at h
    split at h
    · simp at h
    · next hc => cases eq_of_cmp hc; simp at h; subst h; simp
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_erase_self (k : α) : ∀ {m : List (α × β)}, Sorted m → lookup k (erase k m) = none
  | [], _ => rfl
  | (k', v') :: t, hs => by
    cases hs with
    | cons hlt ht =>
      unfold erase
      split
      · next h => simp only [lookup, h]
      · next h =>
        cases eq_of_cmp h
        exact lookup_of_lt hlt
      · next h => simp only [lookup, h]; exact lookup_erase_self k ht

theorem insert_erase_of_lookup {k : α} {v : β} :
    ∀ {m : List (α × β)}, Sorted m → lookup k m = some v → insert k v (erase k m) = m
  | [], _, h => by simp [lookup] at h
  | (k', v') :: t, hs, h => by
    cases hs with
    | cons hlt ht =>
      unfold lookup at h
      split at h
      · simp at h
      · next hc =>
        cases eq_of_cmp hc
        simp at h; subst h
        simp only [erase, cmp_self]
        cases t with
        | nil => rfl
        | cons p t' =>
          obtain ⟨k'', v''⟩ := p
          have := hlt (k'', v'') (by simp)
          simp only [insert, this]
      · next hc =>
        simp only [erase, hc, insert]
        rw [insert_erase_of_lookup ht h]

theorem erase_insert_of_lookup_none {k : α} {v : β} :
    ∀ {m : List (α × β)}, Sorted m → lookup k m = none → erase k (insert k v m) = m
  | [], _, _ => by simp [insert, erase, cmp_self]
  | (k', v') :: t, hs, h => by
    cases hs with
    | cons hlt ht =>
      unfold lookup at h
      split at h
      · next hc => simp only [insert, hc, erase, cmp_self]
      · simp at h
      · next hc =>
        simp only [insert, hc, erase]
        rw [erase_insert_of_lookup_none ht h]

/-- The decomposition `m = K |-> V REST` of a map pattern with a bound key. -/
theorem concat_singleton_iff {k : α} {v : β} {r m : List (α × β)} :
    concat [(k, v)] r = some m ↔ Sorted r ∧ lookup k r = none ∧ m = insert k v r := by
  unfold concat
  have e : (sortedb [(k, v)] && sortedb r && [(k, v)].all (fun p => (lookup p.1 r).isNone)) =
      (sortedb r && (lookup k r).isNone) := by simp [sortedb]
  rw [e]
  by_cases hc : (sortedb r && (lookup k r).isNone) = true
  · rw [ite_eq_left hc]
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, sortedb_iff] at hc
    simp only [List.foldr_cons, List.foldr_nil, Option.some.injEq]
    exact ⟨fun h => ⟨hc.1, hc.2, h.symm⟩, fun h => h.2.2.symm⟩
  · rw [ite_eq_right hc]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h1, h2, _⟩
    apply hc
    simp [(sortedb_iff r).2 h1, h2]

theorem sorted_of_concat_singleton {k : α} {v : β} {r m : List (α × β)}
    (h : concat [(k, v)] r = some m) : Sorted m := by
  obtain ⟨h1, _, rfl⟩ := concat_singleton_iff.1 h
  exact sorted_insert h1

theorem lookup_of_concat_singleton {k : α} {v : β} {r m : List (α × β)}
    (h : concat [(k, v)] r = some m) : lookup k m = some v := by
  obtain ⟨_, _, rfl⟩ := concat_singleton_iff.1 h
  exact lookup_insert_self k v r

theorem concat_singleton_erase {k : α} {v : β} {m : List (α × β)}
    (hs : Sorted m) (h : lookup k m = some v) : concat [(k, v)] (erase k m) = some m :=
  concat_singleton_iff.2 ⟨sorted_erase hs, lookup_erase_self k hs, (insert_erase_of_lookup hs h).symm⟩

/-- A map pattern `K |-> V REST` with `K` bound has at most one match. -/
theorem concat_singleton_unique {k : α} {v₁ v₂ : β} {r₁ r₂ m : List (α × β)}
    (h₁ : concat [(k, v₁)] r₁ = some m) (h₂ : concat [(k, v₂)] r₂ = some m) : v₁ = v₂ ∧ r₁ = r₂ := by
  have l₁ := lookup_of_concat_singleton h₁
  have l₂ := lookup_of_concat_singleton h₂
  rw [l₁] at l₂
  simp only [Option.some.injEq] at l₂
  refine ⟨l₂, ?_⟩
  obtain ⟨s₁, n₁, e₁⟩ := concat_singleton_iff.1 h₁
  obtain ⟨s₂, n₂, e₂⟩ := concat_singleton_iff.1 h₂
  rw [← erase_insert_of_lookup_none s₁ n₁ (v := v₁), ← erase_insert_of_lookup_none s₂ n₂ (v := v₂),
    ← e₁, ← e₂]

/-- In a sorted list, a member binding is what lookup finds. -/
theorem lookup_of_mem {k : α} {v : β} : ∀ {m : List (α × β)}, Sorted m → (k, v) ∈ m → lookup k m = some v
  | [], _, h => by simp at h
  | (k', v') :: t, hs, h => by
    cases hs with
    | cons hlt ht =>
      simp only [List.mem_cons] at h
      rcases h with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [lookup, cmp_self]
      · have hk := hlt (k, v) h
        simp only [lookup, gt_of_lt hk]
        exact lookup_of_mem ht h

/-! ### Membership after an update or a concatenation (for the collection preservation lemmas
of `KPrelude.InvColl`) -/

theorem mem_insert_self (k : α) (v : β) : ∀ (m : List (α × β)), (k, v) ∈ insert k v m
  | [] => by simp [insert]
  | (k', v') :: t => by
    unfold insert
    split
    · simp
    · simp
    · exact List.mem_cons_of_mem _ (mem_insert_self k v t)

theorem mem_insert_of_mem_ne {k : α} {v : β} {p : α × β} :
    ∀ {m : List (α × β)}, p ∈ m → p.1 ≠ k → p ∈ insert k v m
  | [], h, _ => by simp at h
  | (k', v') :: t, h, hne => by
    unfold insert
    split
    · exact List.mem_cons_of_mem _ h
    · next heq =>
      have he := eq_of_cmp heq
      subst he
      rcases List.mem_cons.1 h with rfl | h
      · exact absurd rfl hne
      · exact List.mem_cons_of_mem _ h
    · rcases List.mem_cons.1 h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (mem_insert_of_mem_ne h hne)

theorem mem_foldr_insert {p : α × β} {b : List (α × β)} :
    ∀ {a : List (α × β)}, p ∈ a.foldr (fun q acc => insert q.1 q.2 acc) b → p ∈ a ∨ p ∈ b
  | [], h => Or.inr h
  | q :: t, h => by
    simp only [List.foldr_cons] at h
    rcases mem_insert h with rfl | h
    · exact Or.inl (by simp)
    · rcases mem_foldr_insert h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

theorem mem_foldr_insert_of_mem_right {p : α × β} {b : List (α × β)} (hp : p ∈ b) :
    ∀ {a : List (α × β)}, (∀ q ∈ a, q.1 ≠ p.1) → p ∈ a.foldr (fun q acc => insert q.1 q.2 acc) b
  | [], _ => hp
  | q :: t, hd => by
    simp only [List.foldr_cons]
    exact mem_insert_of_mem_ne
      (mem_foldr_insert_of_mem_right hp fun q' hq' => hd q' (List.mem_cons_of_mem _ hq'))
      (fun he => hd q (by simp) he.symm)

theorem mem_foldr_insert_of_mem_left {p : α × β} {b : List (α × β)} :
    ∀ {a : List (α × β)}, Sorted a → p ∈ a → p ∈ a.foldr (fun q acc => insert q.1 q.2 acc) b
  | [], _, h => by simp at h
  | _ :: _, hs, h => by
    simp only [List.foldr_cons]
    cases hs with
    | @cons k v t hlt hst =>
      rcases List.mem_cons.1 h with rfl | h
      · exact mem_insert_self _ _ _
      · refine mem_insert_of_mem_ne (mem_foldr_insert_of_mem_left hst h) fun he => ?_
        have hl := hlt p h
        rw [he, cmp_self] at hl
        cases hl

/-- The bindings of a defined `_Map_` are those of its two operands. -/
theorem mem_concat {a b m : List (α × β)} (h : concat a b = some m) {p : α × β} :
    p ∈ m ↔ p ∈ a ∨ p ∈ b := by
  unfold concat at h
  split at h
  · next hc =>
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨⟨ha, hb⟩, hd⟩ := hc
    have ha := (sortedb_iff a).1 ha
    have hb := (sortedb_iff b).1 hb
    constructor
    · exact mem_foldr_insert
    · rintro (hp | hp)
      · exact mem_foldr_insert_of_mem_left ha hp
      · refine mem_foldr_insert_of_mem_right hp fun q hq he => ?_
        have h1 := hd q hq
        rw [he, lookup_of_mem (k := p.1) (v := p.2) hb hp] at h1
        simp at h1
  · simp at h

/-! ### Canonicity (for the `SET` law `SetHook.union_eqn` of `KPrelude.HookLaws`) -/

/-- Two sorted lists with the same members are equal: on well-formed values, the representation
is canonical. -/
theorem eq_of_mem_iff :
    ∀ {a b : List (α × β)}, Sorted a → Sorted b → (∀ p, p ∈ a ↔ p ∈ b) → a = b
  | [], [], _, _, _ => rfl
  | [], q :: _, _, _, h => absurd ((h q).2 List.mem_cons_self) (by simp)
  | q :: _, [], _, _, h => absurd ((h q).1 List.mem_cons_self) (by simp)
  | (k, v) :: t, (k', v') :: t', ha, hb, h => by
    cases ha with
    | cons hlt ht =>
    cases hb with
    | cons hlt' ht' =>
    rcases List.mem_cons.1 ((h (k, v)).1 List.mem_cons_self) with e | h1
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      congr 1
      refine eq_of_mem_iff ht ht' fun p => ⟨fun hp => ?_, fun hp => ?_⟩
      · rcases List.mem_cons.1 ((h p).1 (List.mem_cons_of_mem _ hp)) with rfl | hp'
        · have hk := hlt _ hp; simp only [cmp_self] at hk; cases hk
        · exact hp'
      · rcases List.mem_cons.1 ((h p).2 (List.mem_cons_of_mem _ hp)) with rfl | hp'
        · have hk := hlt' _ hp; simp only [cmp_self] at hk; cases hk
        · exact hp'
    · have l1 := hlt' _ h1
      rcases List.mem_cons.1 ((h (k', v')).2 List.mem_cons_self) with e | h2
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        simp only [cmp_self] at l1; cases l1
      · have l2 := hlt _ h2
        simp only [gt_of_lt l1] at l2; cases l2

theorem sorted_filter (f : α × β → Bool) : ∀ {m : List (α × β)}, Sorted m → Sorted (m.filter f)
  | [], _ => Sorted.nil
  | (k, v) :: t, hs => by
    cases hs with
    | cons hlt ht =>
      rw [List.filter_cons]
      split
      · exact Sorted.cons (fun p hp => hlt p (List.mem_filter.1 hp).1) (sorted_filter f ht)
      · exact sorted_filter f ht

theorem sorted_foldr_insert {b : List (α × β)} (hb : Sorted b) :
    ∀ (a : List (α × β)), Sorted (a.foldr (fun q acc => insert q.1 q.2 acc) b)
  | [] => hb
  | _ :: t => by rw [List.foldr_cons]; exact sorted_insert (sorted_foldr_insert hb t)

/-- With `Unit` values (sets), inserting `k` adds exactly the member with key `k`. -/
theorem mem_insert_unit {k : α} {p : α × Unit} {m : List (α × Unit)} :
    p ∈ insert k () m ↔ p.1 = k ∨ p ∈ m := by
  constructor
  · intro h
    rcases mem_insert h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr h
  · intro h
    by_cases hk : p.1 = k
    · obtain ⟨k', ⟨⟩⟩ := p
      cases hk
      exact mem_insert_self _ _ _
    · exact mem_insert_of_mem_ne (h.resolve_left hk) hk

/-! ### Associativity of `_Map_` (for the no-match premises of `owise` equations) -/

/-- In a sorted list, a key without a binding is the key of no member. -/
theorem lookup_eq_none_iff {k : α} {m : List (α × β)} (hs : Sorted m) :
    lookup k m = none ↔ ∀ p ∈ m, p.1 ≠ k := by
  constructor
  · intro h p hp e
    rw [← e, lookup_of_mem hs hp] at h
    cases h
  · intro h
    cases hl : lookup k m with
    | none => rfl
    | some v => exact absurd rfl (h _ (lookup_mem hl))

/-- When `_Map_` is defined: both operands sorted, no key of the first a key of the second. -/
theorem concat_eq_some_iff {a b m : List (α × β)} :
    concat a b = some m ↔ Sorted a ∧ Sorted b ∧ (∀ p ∈ a, lookup p.1 b = none) ∧
      m = a.foldr (fun q acc => insert q.1 q.2 acc) b := by
  unfold concat
  split
  · next hc =>
    simp only [Bool.and_eq_true, List.all_eq_true, sortedb_iff, Option.isNone_iff_eq_none] at hc
    simp only [Option.some.injEq]
    exact ⟨fun h => ⟨hc.1.1, hc.1.2, hc.2, h.symm⟩, fun h => h.2.2.2.symm⟩
  · next hc =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h1, h2, h3, -⟩
    apply hc
    simp only [Bool.and_eq_true, List.all_eq_true, sortedb_iff, Option.isNone_iff_eq_none]
    exact ⟨⟨h1, h2⟩, h3⟩

theorem sorted_of_concat {a b m : List (α × β)} (h : concat a b = some m) : Sorted m := by
  obtain ⟨-, hb, -, rfl⟩ := concat_eq_some_iff.1 h
  exact sorted_foldr_insert hb a

/-- `_Map_` is associative where defined: `a (b c)` defined gives `(a b) c`, the same map. -/
theorem concat_assoc_left {a b c bc m : List (α × β)} (h₁ : concat b c = some bc)
    (h₂ : concat a bc = some m) : ∃ ab, concat a b = some ab ∧ concat ab c = some m := by
  obtain ⟨sb, sc, dbc, -⟩ := concat_eq_some_iff.1 h₁
  obtain ⟨sa, sbc, dabc, -⟩ := concat_eq_some_iff.1 h₂
  -- a key of `a` is no key of `b c`, so none of `b` and none of `c`
  have nb : ∀ p ∈ a, lookup p.1 b = none := fun p hp =>
    (lookup_eq_none_iff sb).2 fun q hq => (lookup_eq_none_iff sbc).1 (dabc p hp) q
      ((mem_concat h₁).2 (Or.inl hq))
  have nc : ∀ p ∈ a, lookup p.1 c = none := fun p hp =>
    (lookup_eq_none_iff sc).2 fun q hq => (lookup_eq_none_iff sbc).1 (dabc p hp) q
      ((mem_concat h₁).2 (Or.inr hq))
  have hab := concat_eq_some_iff.2 ⟨sa, sb, nb, rfl⟩
  refine ⟨_, hab, ?_⟩
  have dab : ∀ p ∈ a.foldr (fun q acc => insert q.1 q.2 acc) b, lookup p.1 c = none := by
    intro p hp
    rcases (mem_concat hab).1 hp with hp | hp
    · exact nc p hp
    · exact dbc p hp
  have hm := concat_eq_some_iff.2 ⟨sorted_of_concat hab, sc, dab, rfl⟩
  rw [hm]
  congr 1
  refine eq_of_mem_iff (sorted_of_concat hm) (sorted_of_concat h₂) fun p => ?_
  rw [mem_concat hm, mem_concat hab, mem_concat h₂, mem_concat h₁, or_assoc]

end Laws

end KPrelude.SAL
