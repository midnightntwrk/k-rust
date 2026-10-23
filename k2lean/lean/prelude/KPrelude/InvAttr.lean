import Lean

/-!
# Attributes read by `k2l_preserve`

Registered in their own file because an attribute cannot be used in the file that declares it.

- `@[k2l_pres]`: a simp lemma that unfolds or normalizes an invariant (added to the simp set
  `k2l_preserve` unfolds `P` with).
- `@[k2l_coll]`: a preservation lemma whose conclusion is a predicate on the result of an
  operation (`EntriesOn Q (update m k v)`); `k2l_preserve` tries each by `apply`, then closes
  the premises from the hypotheses or by simp.
-/

/-- Simp lemmas that unfold or normalize an invariant for `k2l_preserve`. -/
register_simp_attr k2l_pres

/-- Preservation lemmas that `k2l_preserve` tries by `apply`. -/
register_label_attr k2l_coll
