/-!
# Equality of builtin values that the kernel decides by structural recursion

The generated term universe decides `a = b` with a Boolean equality on terms
(`Term.beq`, generated), which compares the builtin values at the leaves with `LeafEq.beq`.
Its instances only use definitions by structural recursion and the kernel's arithmetic on
`Nat` literals, so the kernel evaluates `decide (a = b)` on closed terms without unfolding a
definition by well-founded recursion:

- `Int` and `Bool` by their `DecidableEq` (a constructor split, then `Nat.decEq` on literals);
- byte sequences (`List UInt8`) by `List.beq`, element by element, the recursive call last,
  so the comparison of two long sequences does not nest;
- a `String` by the bytes of its UTF-8 encoding, as a list, the same way. Its characters are not
  decoded: decoding (`String.toList`) is by well-founded recursion.
-/

namespace KPrelude

/-- A Boolean equality that is `=`. -/
class LeafEq (α : Type) where
  beq : α → α → Bool
  eq_of_beq : ∀ {a b : α}, beq a b = true → a = b
  beq_self : ∀ a : α, beq a a = true

namespace LeafEq

instance : LeafEq Int where
  beq a b := decide (a = b)
  eq_of_beq h := of_decide_eq_true h
  beq_self _ := decide_eq_true rfl

instance : LeafEq Bool where
  beq a b := decide (a = b)
  eq_of_beq h := of_decide_eq_true h
  beq_self _ := decide_eq_true rfl

instance : LeafEq (List UInt8) where
  beq a b := a == b
  eq_of_beq h := LawfulBEq.eq_of_beq h
  beq_self a := _root_.beq_self_eq_true a

/-- The bytes of a string's UTF-8 encoding, as a list. -/
def strBytes (s : String) : List UInt8 := s.toByteArray.data.toList

theorem strBytes_inj {a b : String} (h : strBytes a = strBytes b) : a = b := by
  rcases a with ⟨⟨⟨la⟩⟩, ha⟩
  rcases b with ⟨⟨⟨lb⟩⟩, hb⟩
  cases (h : la = lb)
  rfl

instance : LeafEq String where
  beq a b := strBytes a == strBytes b
  eq_of_beq h := strBytes_inj (LawfulBEq.eq_of_beq h)
  beq_self a := _root_.beq_self_eq_true (strBytes a)

/-- A token sort's values are strings (`structure S where val : String`): its equality is the
strings', through `val`, which must be injective. -/
@[instance_reducible] def ofVal {α : Type} (val : α → String) (inj : ∀ a b : α, val a = val b → a = b) : LeafEq α where
  beq a b := LeafEq.beq (val a) (val b)
  eq_of_beq h := inj _ _ (LeafEq.eq_of_beq h)
  beq_self a := LeafEq.beq_self (val a)

end LeafEq

end KPrelude
