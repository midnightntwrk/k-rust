import Lean

/-! The simp set of a generated translation between two generated libraries (`k2lean relate`):
constructor folding (`B.c (tr x) = tr (A.c x)`), injections, projections and functions that
commute with the translation. Registered in its own file because an attribute cannot be used in
the file that declares it. -/

register_simp_attr k2l_rel
