/-
  The account of a text's sentences where their indices are a range.

  A tie's account states that the class lists, concatenated, are a permutation of the indices of
  the user module's sentences, and that those indices are distinct. Decided directly, both are
  quadratic in the number of sentences. Where the indices are the range `a, …, a+n-1`, it is
  enough that the class lists, sorted, are that range: sorting gives a permutation of its input
  (`msort_perm`), so the class lists are a permutation of the range, and a range has no duplicate.
  The kernel then compares numbers once per element after `n log n` merge steps.
-/
import KcoreSpec.Kore.Distinct

set_option autoImplicit false

namespace KCore

/-- **The account from a sort**: if `l` sorted is the range `a, …, a+n-1` and `m` is that range,
`l` is a permutation of `m` and `m` has no duplicate. -/
theorem tacAccount_of_msort {l m : List Nat} {p a n : Nat}
    (hl : KoreAML.Distinct.msort p l = List.range' a n) (hm : m = List.range' a n) :
    l.isPerm m = true ∧ m.Nodup := by
  subst hm
  refine ⟨List.isPerm_iff.mpr ?_, List.nodup_range'⟩
  rw [← hl]
  exact (KoreAML.Distinct.msort_perm p l).symm

end KCore
