/-
  A decision over a list, cut into decisions over consecutive ranges. A statement
  `l.all p = true` whose one kernel decision is too large (the signature's converse of a tie over a
  text of some hundred items) is stated range by range, `((l.drop a).take n).all p = true`, each its
  own theorem and so its own kernel decision, and joined here. The last range is stated without a
  bound, `(l.drop a).all p = true`, so the join needs no fact on the list's length.
-/

set_option autoImplicit false

namespace KCore

/-- `p` holds from `a` on where it holds on the `n` members from `a` and from `a + n` on. -/
theorem tieAll_range {α : Type} {l : List α} {p : α → Bool} {a n : Nat}
    (h : ((l.drop a).take n).all p = true) (ht : (l.drop (a + n)).all p = true) :
    (l.drop a).all p = true := by
  rw [← List.take_append_drop n (l.drop a), List.all_append, h, List.drop_drop, ht]; rfl

/-- `p` holds of the whole list where it holds from `0` on. -/
theorem tieAll_whole {α : Type} {l : List α} {p : α → Bool} (h : (l.drop 0).all p = true) :
    l.all p = true := h

/-- The equality of two lists from their ranges, as `tieAll_range`: the `n` members from `a` are
equal and the lists from `a + n` on are. -/
theorem tieEq_range {α : Type} {l m : List α} {a n : Nat}
    (h : (l.drop a).take n = (m.drop a).take n) (ht : l.drop (a + n) = m.drop (a + n)) :
    l.drop a = m.drop a := by
  rw [← List.take_append_drop n (l.drop a), ← List.take_append_drop n (m.drop a), h, List.drop_drop,
    List.drop_drop, ht]

/-- `l.all (fun x => (f x.2).contains x.1)` from one check per group: each member's second component
is one of `cs`, and for each `n` of `cs` the first components of the members whose second component
is `n`, in the list's order, are a sublist of `f n`. Each group's check reads `f n` once, where
deciding the statement directly reads `f x.2` once per member. -/
theorem tieAll_of_groups {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    {l : List (α × β)} {cs : List β} {f : β → List α}
    (hc : l.all (fun x => cs.contains x.2) = true)
    (hs : cs.all (fun n => ((l.filter (·.2 == n)).map (·.1)).isSublist (f n)) = true) :
    l.all (fun x => (f x.2).contains x.1) = true := by
  rw [List.all_eq_true] at hc hs ⊢
  intro x hx
  have hn : x.2 ∈ cs := by simpa using hc x hx
  have h1 : x.1 ∈ (l.filter (·.2 == x.2)).map (·.1) :=
    List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, by simp⟩, rfl⟩
  simpa using (List.isSublist_iff_sublist.mp (hs x.2 hn)).subset h1

end KCore
