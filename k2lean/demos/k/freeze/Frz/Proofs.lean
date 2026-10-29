import Frz.Spec

/-! The proofs of the freeze fixture: two guarded theorems, an obligation with a frozen statement
that is proved, one that is open, and one that is refuted. -/

namespace Frz

theorem f_double (n : Nat) : f n = 2 * n := by
  induction n <;> simp_all [f] <;> omega

theorem g_id (n : Nat) : g n = n := by
  induction n with
  | zero => simp [g]
  | succ k ih => rw [g]; simp [ih]

def two.statement : Prop := f 1 = 2

theorem two : two.statement := by
  simp [two.statement, f]

def bound.statement : Prop := ∀ n, g n ≤ n

def three.statement : Prop := f 1 = 3

theorem three.refuted : ¬ three.statement := by
  simp [three.statement, f]

end Frz
