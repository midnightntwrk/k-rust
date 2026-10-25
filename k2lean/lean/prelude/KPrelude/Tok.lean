/-!
# Serialization tokens and their order

Every generated term type gets an injective serialization into `List Tok`.
The order on terms (used to keep `Map` and `Set` values canonical) is the lexicographic order
of their serializations, so its laws reduce to the laws proved here for `Tok`.
-/

namespace KPrelude

/-- A serialization token: a constructor tag, or a payload of a builtin carrier. -/
inductive Tok where
  | c (n : Nat)
  | i (x : Int)
  | s (x : String)
  | b (x : Bool)
  deriving DecidableEq, Repr, Inhabited

namespace Tok

def rank : Tok → Nat
  | c _ => 0 | i _ => 1 | s _ => 2 | b _ => 3

def cmp : Tok → Tok → Ordering
  | c x, c y => compare x y
  | i x, i y => compare x y
  | s x, s y => compare x y
  | b x, b y => compare x y
  | x, y => compare x.rank y.rank

instance : Ord Tok := ⟨cmp⟩

theorem compare_def (x y : Tok) : compare x y = cmp x y := rfl

instance : Std.OrientedOrd Tok where
  eq_swap {a b} := by
    cases a <;> cases b <;> simp only [compare_def, cmp, rank] <;>
      first | exact Std.OrientedOrd.eq_swap | rfl

instance : Std.TransOrd Tok where
  isLE_trans {a b c} hab hbc := by
    cases a <;> cases b <;> cases c <;> simp only [compare_def, cmp, rank] at hab hbc ⊢ <;>
      first
        | exact Std.TransOrd.isLE_trans hab hbc
        | exact (absurd hab (by decide))
        | exact (absurd hbc (by decide))
        | decide

instance : Std.LawfulEqOrd Tok where
  eq_of_compare {a b} h := by
    cases a <;> cases b <;> simp only [compare_def, cmp, rank] at h <;>
      first
        | (congr; exact Std.LawfulEqOrd.eq_of_compare h)
        | exact (absurd h (by decide))

end Tok

end KPrelude
