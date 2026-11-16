/-
  A permutation of two lists of blocks, checked a slice at a time (checked layer, generic).

  `B` is a list of blocks (lists), `S` another. `SliceIs B S a n σ` says: the `n` blocks of `B`
  from position `a`, concatenated, are the blocks of `S` at the indices `σ`, concatenated, in
  that order. Slices that follow each other join (`SliceIs.join`); when one slice covers all of
  `B` and its indices are a permutation of `S`'s, `B.flatten` is a permutation of `S.flatten`
  (`SliceIs.perm`). Each slice is one closed equation the kernel checks on its own, so the
  check of a long list is cut into decisions of bounded size; the indices are an untrusted hint,
  and a wrong one only makes a decision fail.

  `Rows f a n`: `f i = true` for `i` from `a` to `a + n`, joined and closed the same way.
-/
set_option autoImplicit false

namespace KoreAML.Blocks

variable {α : Type}

/-- The `n` blocks of `B` from `a`, concatenated, are the blocks of `S` at `σ`, in order. -/
def SliceIs (B S : List (List α)) (a n : Nat) (σ : List Nat) : Prop :=
  ((B.drop a).take n).flatten = (σ.map (S.getD · [])).flatten

theorem SliceIs.join {B S : List (List α)} {a n m k : Nat} {σ τ : List Nat}
    (h₁ : SliceIs B S a n σ) (h₂ : SliceIs B S (a + n) m τ) (hk : n + m = k) :
    SliceIs B S a k (σ ++ τ) := by
  subst hk
  unfold SliceIs at *
  rw [List.take_add, List.flatten_append, h₁, List.drop_drop, h₂,
    List.map_append, List.flatten_append]

theorem map_getD_range (S : List (List α)) :
    (List.range S.length).map (S.getD · []) = S := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range, List.getD]
    rw [List.getElem?_eq_getElem h₂, Option.getD_some]

/-- A slice covering `B` whose indices are a permutation of `S`'s positions. -/
theorem SliceIs.perm {B S : List (List α)} {σ : List Nat}
    (h : SliceIs B S 0 B.length σ) (hp : σ.isPerm (List.range S.length) = true) :
    B.flatten.Perm S.flatten := by
  unfold SliceIs at h
  rw [List.drop_zero, List.take_length] at h
  rw [h]
  have hσ := (List.isPerm_iff.mp hp).map (S.getD · [])
  rw [map_getD_range] at hσ
  exact hσ.flatten

/-! ## Rows: a Boolean condition on consecutive positions -/

/-- `f i = true` for every `i` from `a` to `a + n`. -/
def Rows (f : Nat → Bool) (a n : Nat) : Bool := (List.range n).all fun i => f (a + i)

theorem Rows.join {f : Nat → Bool} {a n m k : Nat} (h₁ : Rows f a n = true) (h₂ : Rows f (a + n) m = true)
    (hk : n + m = k) : Rows f a k = true := by
  subst hk
  simp only [Rows, List.all_eq_true, List.mem_range] at *
  intro i hi
  by_cases hin : i < n
  · exact h₁ i hin
  · have := h₂ (i - n) (by omega)
    rwa [show a + n + (i - n) = a + i by omega] at this

theorem Rows.all {f : Nat → Bool} {n : Nat} (h : Rows f 0 n = true) : ∀ i, i < n → f i = true := by
  intro i hi
  simp only [Rows, List.all_eq_true, List.mem_range] at h
  simpa using h i hi

end KoreAML.Blocks
