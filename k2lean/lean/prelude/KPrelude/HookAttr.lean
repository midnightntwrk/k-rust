import Lean

/-! The simp set of the collection laws that K states as simplifications (`HookLaws.lean`,
`MAP-KORE-SYMBOLIC` and `SET-KORE-SYMBOLIC`): the generated proof of a simplification over a
`Set` or `Map` passes it to the generic tactics. Registered in its own file because an attribute
cannot be used in the file that declares it. -/

register_simp_attr k2l_hook
