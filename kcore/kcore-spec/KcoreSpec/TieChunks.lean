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

end KCore
