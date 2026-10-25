import Lean

/-! The simp set of a generated translation between two generated libraries (`k2lean relate`):
constructor folding (`B.c (tr x) = tr (A.c x)`), injections, projections and functions that
commute with the translation. Registered in its own file because an attribute cannot be used in
the file that declares it. -/

register_simp_attr k2l_rel

/-- The equations of a translation in the arity-indexed universe, one per constructor
(`tr_S (A.c x) = B.c (tr x)`): what unfolding `tr_S` gives on a type per sort, which `k2l_inv`
uses to invert `d = tr_S x` after splitting `x`. -/
register_simp_attr k2l_tr
