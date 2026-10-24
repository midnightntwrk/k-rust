import Lean

/-!
# Attributes read by `k2l_preserve`

Registered in their own file because an attribute cannot be used in the file that declares it.

- `@[k2l_pres]`: a simp lemma that unfolds or normalizes an invariant (added to the simp set
  `k2l_preserve` unfolds `P` with).
- `@[k2l_coll]`: a preservation lemma whose conclusion is a predicate on the result of an
  operation (`EntriesOn Q (update m k v)`); `k2l_preserve` tries each by `apply`, then closes
  the premises from the hypotheses or by simp.
- `@[k2l_arith]`: a simp lemma that states a hook of `Int` or `Bool` in Lean's own arithmetic
  and logic (`IntHook.add a b = a + b`, `decide p = true ↔ p`), so that `omega` reads the goal;
  `k2l_preserve` rewrites with them before calling `omega`.
-/

/-- Simp lemmas that unfold or normalize an invariant for `k2l_preserve`. -/
register_simp_attr k2l_pres

/-- Simp lemmas that turn `Int` and `Bool` hooks into Lean arithmetic for `omega`. -/
register_simp_attr k2l_arith

/-- Preservation lemmas that `k2l_preserve` tries by `apply`. -/
register_label_attr k2l_coll
