import KPrelude.Hooks
import KPrelude.Ext
import KPrelude.HookAttr

/-! The hook definitions and laws the generic equation proofs unfold (`hooks::eq_unfold_names`; a unit
test keeps the two lists equal), in the simp set `k2l_eq` (CT-4c). -/

attribute [k2l_eq]
  KPrelude.IntHook.add
  KPrelude.IntHook.sub
  KPrelude.IntHook.mul
  KPrelude.IntHook.lt
  KPrelude.IntHook.le
  KPrelude.IntHook.gt
  KPrelude.IntHook.ge
  KPrelude.IntHook.eq
  KPrelude.IntHook.ne
  KPrelude.BoolHook.not
  KPrelude.BoolHook.and
  KPrelude.BoolHook.or
  KPrelude.BoolHook.xor
  KPrelude.BoolHook.implies
  KPrelude.BoolHook.eq
  KPrelude.BoolHook.ne
  KPrelude.KEqHook.eq
  KPrelude.KEqHook.ne
  KPrelude.KEqHook.ite
  KPrelude.IntHook.tdiv
  KPrelude.IntHook.tmod
  KPrelude.IntHook.ediv
  KPrelude.IntHook.emod
  KPrelude.IntHook.pow
  KPrelude.IntHook.shl
  KPrelude.IntHook.shr
  KPrelude.IntHook.abs
  KPrelude.IntHook.min
  KPrelude.IntHook.max
  KPrelude.StringHook.eq
  KPrelude.StringHook.ne
  KPrelude.IntHook.int_ediv_eq_tdiv_sub_emod
  KPrelude.IntHook.int_emod_eq_of_lt
  Int.tmod_eq_of_lt
