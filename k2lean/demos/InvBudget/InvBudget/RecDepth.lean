import KPrelude.InvTactic
import KPrelude.Tactic

/-! The recursion-depth limit in the collections closer.

`maxRecDepth` is a runtime exception, which `try … catch` rethrows, like the heartbeat limit. A
closer step that reaches it fails like any other step, so the steps after it are tried. Here the
`@[k2l_coll]` lemma `viaDeep` applies to `Good 0` and leaves `Good (deep 3000)`, to which it
applies again by unifying `0` with `deep 3000`, unfolding `deep` to the limit; that alternative
fails, and the discharger closes `Good 0` by `simp`. Before, the error ended `k2l_coll_close` (and `k2l_preserve`, whose
rule steps run the same closers). `#guard_msgs` checks that the lemma does reach the limit, so
the test is not vacuous. -/

namespace InvBudget.RecDepth

def deep : Nat → Nat
  | 0 => 0
  | n + 1 => deep n

theorem deep_eq (n : Nat) : deep n = 0 := by
  induction n with | zero => rfl | succ n ih => simp [deep, ih]

@[k2l_coll] theorem viaDeep (P : Nat → Prop) (h : P (deep 3000)) : P 0 := deep_eq 3000 ▸ h

def Good (n : Nat) : Prop := n = 0

@[simp] theorem good_zero : Good 0 := rfl

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : Good (deep 3000) := by apply viaDeep

theorem good : Good 0 := by k2l_coll_close

#k2l_assert_axioms good

end InvBudget.RecDepth
