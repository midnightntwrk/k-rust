/-
  Distinct strings, decided in linear time (checked layer, generic).

  `nodup` (Base.lean) compares every pair of strings: quadratic, and each comparison makes the
  kernel encode both strings. Here each string is encoded once, as a natural number (`strCode`:
  its UTF-8 bytes in base 256 behind a leading 1, so different strings get different numbers),
  the numbers are sorted, and the sorted list is checked strictly ascending. The kernel compares
  natural numbers in one step, so the cost is one encoding per string and `n log n` steps.

  `nodup_of_codes`: if the sorted codes are strictly ascending, `nodup l = true`. The sort is
  bottom-up merging with fuel; whatever the fuel, its result is a permutation of its input
  (`msort_perm`), so a fuel too small only makes the check fail.
-/
import KcoreSpec.Kore.ReorderTheory

set_option autoImplicit false

namespace KoreAML.Distinct

/-! ## Codes -/

/-- A byte list as a number: base 256, behind a leading 1. -/
def bytesCode : List UInt8 → Nat
  | [] => 1
  | b :: bs => bytesCode bs * 256 + b.toNat

theorem bytesCode_pos : ∀ l : List UInt8, 0 < bytesCode l
  | [] => by simp [bytesCode]
  | b :: bs => by have := bytesCode_pos bs; simp only [bytesCode]; omega

theorem bytesCode_inj : ∀ {l l' : List UInt8}, bytesCode l = bytesCode l' → l = l'
  | [], [], _ => rfl
  | [], b :: bs, h => by
    have := bytesCode_pos bs
    simp only [bytesCode] at h; omega
  | b :: bs, [], h => by
    have := bytesCode_pos bs
    simp only [bytesCode] at h; omega
  | b :: bs, b' :: bs', h => by
    simp only [bytesCode] at h
    have hb : b.toNat < 256 := b.toNat_lt
    have hb' : b'.toNat < 256 := b'.toNat_lt
    have h1 : b.toNat = b'.toNat := by omega
    have h2 : bytesCode bs = bytesCode bs' := by omega
    rw [bytesCode_inj h2, UInt8.toNat_inj.mp h1]

/-- A string's code: its UTF-8 bytes as a number. -/
def strCode (s : String) : Nat := bytesCode s.toByteArray.data.toList

theorem strCode_inj {s t : String} (h : strCode s = strCode t) : s = t := by
  have hb := bytesCode_inj h
  obtain ⟨⟨⟨l⟩⟩, hs⟩ := s
  obtain ⟨⟨⟨l'⟩⟩, ht⟩ := t
  simp only at hb
  subst hb
  rfl

/-! ## Sorting with fuel -/

/-- Merge two lists (fuel: the steps allowed; out of fuel, append). -/
def merge : Nat → List Nat → List Nat → List Nat
  | 0, l, l' => l ++ l'
  | _ + 1, [], l' => l'
  | _ + 1, l, [] => l
  | f + 1, a :: l, b :: l' => if a ≤ b then a :: merge f l (b :: l') else b :: merge f (a :: l) l'

theorem merge_perm : ∀ (f : Nat) (l l' : List Nat), (merge f l l').Perm (l ++ l')
  | 0, l, l' => by simp [merge]
  | _ + 1, [], l' => by simp [merge]
  | _ + 1, a :: l, [] => by simp [merge]
  | f + 1, a :: l, b :: l' => by
    simp only [merge]
    split
    · exact (merge_perm f l (b :: l')).cons a
    · have := (merge_perm f (a :: l) l').cons b
      exact this.trans List.perm_middle.symm

/-- Merge adjacent pairs of runs. -/
def mergePairs (f : Nat) : List (List Nat) → List (List Nat)
  | a :: b :: rs => merge f a b :: mergePairs f rs
  | rs => rs

theorem mergePairs_perm (f : Nat) : ∀ rs : List (List Nat), (mergePairs f rs).flatten.Perm rs.flatten
  | [] => by simp [mergePairs]
  | [a] => by simp [mergePairs]
  | a :: b :: rs => by
    simp only [mergePairs, List.flatten_cons, ← List.append_assoc]
    exact (merge_perm f a b).append (mergePairs_perm f rs)

/-- `p` passes of merging adjacent runs, from singletons. -/
def passes (f : Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, rs => rs
  | p + 1, rs => passes f p (mergePairs f rs)

theorem passes_perm (f : Nat) : ∀ (p : Nat) (rs : List (List Nat)), (passes f p rs).flatten.Perm rs.flatten
  | 0, rs => by simp [passes]
  | p + 1, rs => (passes_perm f p (mergePairs f rs)).trans (mergePairs_perm f rs)

/-- Bottom-up merge sort: `l.length` merge steps and `p` passes (enough when `2^p ≥ l.length`). -/
def msort (p : Nat) (l : List Nat) : List Nat := (passes l.length p (l.map fun a => [a])).flatten

theorem msort_perm (p : Nat) (l : List Nat) : (msort p l).Perm l := by
  unfold msort
  refine (passes_perm _ p _).trans ?_
  have : (l.map fun a => [a]).flatten = l := by
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, List.flatten_cons, ih, List.singleton_append]
  rw [this]

/-- Strictly ascending. -/
def ascending : List Nat → Bool
  | a :: b :: l => decide (a < b) && ascending (b :: l)
  | _ => true

theorem pairwise_of_ascending : ∀ {l : List Nat}, ascending l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_ascending h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

/-- The strings are distinct: their codes, sorted, are strictly ascending. -/
def codesDistinct (p : Nat) (l : List String) : Bool := ascending (msort p (l.map strCode))

theorem nodup_of_codes {p : Nat} {l : List String} (h : codesDistinct p l = true) : nodup l = true := by
  rw [ReorderTheory.nodup_true_iff]
  have hn := (msort_perm p (l.map strCode)).nodup_iff.mp ((pairwise_of_ascending h).imp Nat.ne_of_lt)
  exact (List.pairwise_map.mp hn).imp fun hne e => hne (congrArg strCode e)

/-- The passes enough for a list of length `n`: the bits of `n`. -/
def passesFor (n : Nat) : Nat := Nat.log2 n + 1

end KoreAML.Distinct
