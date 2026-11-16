/-
  KCore, checked layer: the set operations of Hooks.lean keep set elements in canonical form
  (strictly increasing in `GroundTerm.cmp`) and only hold elements of their arguments, and the
  map operations `keys` and `removeAll` keep a map's keys sorted. Used by subject reduction
  (SubjectReduction.lean): a set hook returns a set value, `keys` a set, `removeAll` a map.
-/
import KcoreSpec.OrderLaws

set_option autoImplicit false

namespace KCore

open GroundTerm

/-! ## Sortedness as a pairwise relation -/

theorem elemsSorted_iff : ∀ {l : List GroundTerm},
    elemsSorted l = true ↔ l.Pairwise fun a b => cmp a b = .lt
  | [] => by simp [elemsSorted]
  | [a] => by simp [elemsSorted]
  | a :: b :: l => by
    have ih := elemsSorted_iff (l := b :: l)
    simp only [elemsSorted, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨hab, hbl⟩
      refine List.Pairwise.cons (fun x hx => ?_) hbl
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hab
      · exact cmp_trans _ _ _ hab (List.rel_of_pairwise_cons hbl hx)
    · intro h
      exact ⟨List.rel_of_pairwise_cons h (List.mem_cons_self ..), h.of_cons⟩

theorem keysSorted_iff : ∀ {l : Entries},
    keysSorted l = true ↔ l.Pairwise fun a b => cmp a.1 b.1 = .lt
  | [] => by simp [keysSorted]
  | [a] => by obtain ⟨k, v⟩ := a; simp [keysSorted]
  | a :: b :: l => by
    obtain ⟨k, v⟩ := a
    obtain ⟨k', v'⟩ := b
    have ih := keysSorted_iff (l := (k', v') :: l)
    simp only [keysSorted, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨hab, hbl⟩
      refine List.Pairwise.cons (fun x hx => ?_) hbl
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hab
      · exact cmp_trans _ _ _ hab (List.rel_of_pairwise_cons hbl hx)
    · intro h
      exact ⟨List.rel_of_pairwise_cons h (List.mem_cons_self ..), h.of_cons⟩

/-! ## Sets -/

theorem insertS_mem {k : GroundTerm} : ∀ {es : List GroundTerm} {e : GroundTerm},
    e ∈ insertS k es → e = k ∨ e ∈ es
  | [], e, h => by simp [insertS] at h; exact Or.inl h
  | e' :: es, e, h => by
    simp only [insertS] at h
    split at h
    · simpa using h
    · exact Or.inr h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr (h ▸ List.mem_cons_self ..)
      · rcases insertS_mem h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem insertS_sorted {k : GroundTerm} : ∀ {es : List GroundTerm},
    es.Pairwise (fun a b => cmp a b = .lt) → (insertS k es).Pairwise (fun a b => cmp a b = .lt)
  | [], _ => by simp [insertS]
  | e :: es, h => by
    simp only [insertS]
    split
    · rename_i hlt
      refine List.Pairwise.cons (fun x hx => ?_) h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hlt
      · exact cmp_trans _ _ _ hlt (List.rel_of_pairwise_cons h hx)
    · exact h
    · rename_i hgt
      refine List.Pairwise.cons (fun x hx => ?_) (insertS_sorted h.of_cons)
      rcases insertS_mem hx with rfl | hx
      · exact cmp_gt_swap hgt
      · exact List.rel_of_pairwise_cons h hx

theorem unionS_mem : ∀ {a b : List GroundTerm} {e : GroundTerm}, e ∈ unionS a b → e ∈ a ∨ e ∈ b
  | [], b, e, h => Or.inr h
  | x :: a, b, e, h => by
    simp only [unionS, List.foldr_cons] at h
    rcases insertS_mem h with rfl | h
    · exact Or.inl (List.mem_cons_self ..)
    · rcases unionS_mem (a := a) h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

theorem unionS_sorted : ∀ {a b : List GroundTerm}, b.Pairwise (fun x y => cmp x y = .lt) →
    (unionS a b).Pairwise (fun x y => cmp x y = .lt)
  | [], _, h => h
  | x :: a, b, h => by
    simp only [unionS, List.foldr_cons]
    exact insertS_sorted (unionS_sorted (a := a) h)

/-- `_Set_`'s value is the union, where it is defined. -/
theorem concatS_some {a b u : List GroundTerm} (h : concatS a b = some u) : unionS a b = u := by
  unfold concatS at h
  split at h
  · exact Option.some.inj h
  · cases h

/-- A sorted set is its first member's set and the rest, which are disjoint. -/
theorem concatS_first {x : GroundTerm} {es : List GroundTerm} (h : (x :: es).Pairwise fun a b => cmp a b = .lt) :
    concatS [x] es = some (x :: es) := by
  have hm : memS x es = false := by
    unfold memS
    exact List.any_eq_false.mpr fun e he => by rw [List.rel_of_pairwise_cons h he]; decide
  have hu : unionS [x] es = x :: es := by
    show insertS x es = x :: es
    cases es with
    | nil => rfl
    | cons y es => simp [insertS, List.rel_of_pairwise_cons h (List.mem_cons_self ..)]
  simp [concatS, hm, hu]

/-! ## The maps' keys -/

theorem keysOf_sorted {m : Entries} (h : m.Pairwise fun a b => cmp a.1 b.1 = .lt) :
    (keysOf m).Pairwise fun a b => cmp a b = .lt := by
  unfold keysOf
  exact List.pairwise_map.mpr h

end KCore
