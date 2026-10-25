import KPrelude.Tok

/-!
# The order on generated term types

A generated type `α` comes with `ser : α → List Tok` and a proof that `ser` is injective
(generated from a decoder). Its order is `compare` on serializations, which is a lawful linear
order by the laws of `List.compareLex` and `Tok`.
-/

namespace KPrelude

/-- The order on `α` induced by a serialization. -/
@[instance_reducible] def ordOfSer {α : Type} (ser : α → List Tok) : Ord α := ⟨fun a b => compare (ser a) (ser b)⟩

theorem transOrdOfSer {α : Type} (ser : α → List Tok) :
    @Std.TransOrd α (ordOfSer ser) :=
  { eq_swap := fun {a b} => Std.OrientedOrd.eq_swap (a := ser a) (b := ser b)
    isLE_trans := fun {a b c} hab hbc =>
      Std.TransOrd.isLE_trans (a := ser a) (b := ser b) (c := ser c) hab hbc }

theorem lawfulEqOrdOfSer {α : Type} (ser : α → List Tok) (inj : ∀ a b, ser a = ser b → a = b) :
    @Std.LawfulEqOrd α (ordOfSer ser) :=
  { compare_self := fun {a} => Std.ReflOrd.compare_self (a := ser a)
    eq_of_compare := fun {a b} h =>
      inj a b (Std.LawfulEqOrd.eq_of_compare (a := ser a) (b := ser b) h) }

end KPrelude

/-! ## A direct comparison equal to the serialization order

Generated types also get a structural `cmp` (no allocation), proved equal to `compare` on
serializations. The proof needs serializations to be prefix-free, which follows from the
decoder. -/

namespace KPrelude

theorem compare_cons_cons (a b : Tok) (xs ys : List Tok) :
    compare (a :: xs) (b :: ys) = (compare a b).then (compare xs ys) := by
  rw [List.compare_eq_compareLex, List.compareLex_cons_cons]

@[simp] theorem compare_nil_nil : compare ([] : List Tok) [] = .eq := by
  rw [List.compare_eq_compareLex]; exact List.compareLex_nil_nil

@[simp] theorem Tok.compare_c (i j : Nat) : compare (Tok.c i) (Tok.c j) = compare i j := rfl
@[simp] theorem Tok.compare_i (x y : Int) : compare (Tok.i x) (Tok.i y) = compare x y := rfl
@[simp] theorem Tok.compare_s (x y : String) : compare (Tok.s x) (Tok.s y) = compare x y := rfl
@[simp] theorem Tok.compare_b (x y : Bool) : compare (Tok.b x) (Tok.b y) = compare x y := rfl

/-- Comparing two lists, neither a proper prefix of the other, followed by anything. -/
theorem compare_append_of_prefixFree :
    ∀ (x y r r' : List Tok), (∀ t, y = x ++ t → t = []) → (∀ t, x = y ++ t → t = []) →
      compare (x ++ r) (y ++ r') = (compare x y).then (compare r r')
  | [], [], r, r', _, _ => by simp
  | [], b :: ys, _, _, hx, _ => by simp at hx
  | a :: xs, [], _, _, _, hy => by simp at hy
  | a :: xs, b :: ys, r, r', hx, hy => by
    simp only [List.cons_append, compare_cons_cons]
    cases h : compare a b with
    | eq =>
      have hab : a = b := Std.LawfulEqOrd.eq_of_compare h
      subst hab
      rw [compare_append_of_prefixFree xs ys r r'
        (fun t ht => hx t (by simp [ht])) (fun t ht => hy t (by simp [ht]))]
      simp
    | lt => rfl
    | gt => rfl

/-- A serialization with a left-inverse decoder is prefix-free. -/
theorem prefixFree_of_dec {α : Type} (ser : α → List Tok) (dec : Nat → List Tok → Option (α × List Tok))
    (hdec : ∀ a r n, (ser a).length ≤ n → dec n (ser a ++ r) = some (a, r)) :
    ∀ a b t, ser b = ser a ++ t → t = [] := by
  intro a b t h
  have h1 := hdec b [] (ser b).length (Nat.le_refl _)
  have h2 := hdec a t (ser b).length (by rw [h]; simp)
  rw [List.append_nil] at h1
  rw [← h, h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact h2.2.symm

theorem compare_append_ser {α : Type} (ser : α → List Tok) (dec : Nat → List Tok → Option (α × List Tok))
    (hdec : ∀ a r n, (ser a).length ≤ n → dec n (ser a ++ r) = some (a, r)) (a b : α) (r r' : List Tok) :
    compare (ser a ++ r) (ser b ++ r') = (compare (ser a) (ser b)).then (compare r r') :=
  compare_append_of_prefixFree _ _ _ _ (prefixFree_of_dec ser dec hdec a b) (prefixFree_of_dec ser dec hdec b a)

theorem transOrd_of_cmp {α : Type} (cmp : α → α → Ordering) (ser : α → List Tok)
    (h : ∀ a b, cmp a b = compare (ser a) (ser b)) : @Std.TransOrd α ⟨cmp⟩ :=
  { eq_swap := fun {a b} => by
      show cmp a b = (cmp b a).swap
      rw [h, h]; exact Std.OrientedOrd.eq_swap
    isLE_trans := fun {a b c} hab hbc => by
      change (cmp a b).isLE = true at hab
      change (cmp b c).isLE = true at hbc
      show (cmp a c).isLE = true
      rw [h] at hab hbc ⊢; exact Std.TransOrd.isLE_trans hab hbc }

theorem lawfulEqOrd_of_cmp {α : Type} (cmp : α → α → Ordering) (ser : α → List Tok)
    (h : ∀ a b, cmp a b = compare (ser a) (ser b)) (inj : ∀ a b, ser a = ser b → a = b) :
    @Std.LawfulEqOrd α ⟨cmp⟩ :=
  { compare_self := fun {a} => by show cmp a a = .eq; rw [h]; exact Std.ReflOrd.compare_self
    eq_of_compare := fun {a b} e => by
      change cmp a b = .eq at e
      rw [h] at e; exact inj a b (Std.LawfulEqOrd.eq_of_compare e) }

end KPrelude

namespace KPrelude

/-- Length bounds through an append. The generated round trips of the arity-indexed universe
bound each argument's serialization with these instead of `omega`, whose cost grows quickly
with the number of arguments of a constructor (38 s for one of arity 21). -/
theorem len_left {α : Type} {x y : List α} {n : Nat} (h : (x ++ y).length ≤ n) : x.length ≤ n := by
  simp only [List.length_append] at h; omega
theorem len_right {α : Type} {x y : List α} {n : Nat} (h : (x ++ y).length ≤ n) : y.length ≤ n := by
  simp only [List.length_append] at h; omega

end KPrelude
