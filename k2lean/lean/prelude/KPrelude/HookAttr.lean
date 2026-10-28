import Lean

/-! The simp set of the collection laws that K states as simplifications (`HookLaws.lean`,
`MAP-KORE-SYMBOLIC` and `SET-KORE-SYMBOLIC`): the generated proof of a simplification over a
`Set` or `Map` passes it to the generic tactics. Registered in its own file because an attribute
cannot be used in the file that declares it. -/

register_simp_attr k2l_hook

/-- The simp set of the generic equation proofs (`Equations.lean`'s `k2l_eqn_*`): the hook
definitions they unfold (`KPrelude.EqBase`) and each library's projection lemmas (`NS/EqBase.lean`).
One named set rather than the list in every `simp` call: the set is built once, where a list is
elaborated again by each call (CT-4c: kimp's `Equations` 114M to 35M heartbeats). -/
register_simp_attr k2l_eq
