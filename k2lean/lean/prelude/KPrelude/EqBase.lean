import KPrelude.Hooks
import KPrelude.Ext
import KPrelude.HookAttr

/-! The hook definitions and laws the generic equation proofs unfold (`hooks::eq_unfold_names`; a unit
test keeps the two lists equal), in the simp set `k2l_eq` (CT-4c).

The total `Int`-valued hooks are unfolded by the theorems below, not by their definitions (EQ-22). An
unfolding by definition is a definitional rewrite, which simp makes inside `@decide p inst` in `p`
alone: `IntHook.lt M (IntHook.add N 1)` becomes `@decide (M < N + 1) (Int.decLt M (IntHook.add N 1))`,
whose instance is no longer syntactically one of its proposition (`IntHook.add` is not unfolded at
instance transparency), so `decide_eq_true_eq` does not apply and `omega` sees an atom. A theorem's
rewrite goes through `decide` by congruence, which rebuilds the instance. -/

namespace KPrelude.IntHook

theorem add_eq (a b : Int) : IntHook.add a b = a + b := by rw [IntHook.add]
theorem sub_eq (a b : Int) : IntHook.sub a b = a - b := by rw [IntHook.sub]
theorem mul_eq (a b : Int) : IntHook.mul a b = a * b := by rw [IntHook.mul]
theorem abs_eq (a : Int) : IntHook.abs a = if a < 0 then -a else a := by rw [IntHook.abs]
theorem min_eq (a b : Int) : IntHook.min a b = if a ≤ b then a else b := by rw [IntHook.min]
theorem max_eq (a b : Int) : IntHook.max a b = if a ≤ b then b else a := by rw [IntHook.max]

end KPrelude.IntHook

attribute [k2l_eq]
  KPrelude.IntHook.add_eq
  KPrelude.IntHook.sub_eq
  KPrelude.IntHook.mul_eq
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
  KPrelude.IntHook.abs_eq
  KPrelude.IntHook.min_eq
  KPrelude.IntHook.max_eq
  KPrelude.StringHook.eq
  KPrelude.StringHook.ne
  KPrelude.IntHook.int_ediv_eq_tdiv_sub_emod
  KPrelude.IntHook.int_emod_eq_of_lt
  Int.tmod_eq_of_lt
