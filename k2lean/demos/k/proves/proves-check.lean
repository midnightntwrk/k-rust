import KPrelude.Tactic

/-! The checks of `#k2l_proves` (`KPrelude.Tactic`): a proof of an obligation is
`theorem X : X.statement`, or the statement written out (as the generator writes its proofs), over
the statement's own binders (the `[Hooks]` instance when it reads the library's parameters); a
theorem of another statement, even an equivalent one, a theorem in the wrong closure, and other
axioms are rejected. The gate runs this file (`lake env lean` in the prelude) and fails on any
unexpected message. -/

namespace ProvesCheck

class Hooks where
  recov : Nat → Option Nat

/-- an obligation, proved by naming its statement -/
def Eqn.p1.statement : Prop := ∀ (n : Nat), n + 0 = n
theorem Eqn.p1 : Eqn.p1.statement := fun n => Nat.add_zero n

/-- written out, with other binder names -/
def Eqn.p2.statement : Prop := ∀ (n : Nat) (_ : n = 1), n + 0 = 1
theorem Eqn.p2 (m : Nat) (hm : m = 1) : m + 0 = 1 := by simp [hm]

/-- an equivalent but other statement is rejected -/
def Eqn.p3.statement : Prop := ∀ (n : Nat), n + 0 = n
theorem Eqn.p3 (n : Nat) : n + 0 = n ∧ True := ⟨Nat.add_zero n, trivial⟩

/-- an extra premise is rejected -/
def Eqn.p4.statement : Prop := ∀ (n : Nat), n + 0 = n
theorem Eqn.p4 (n : Nat) (_ : n = n) : n + 0 = n := Nat.add_zero n

/-- another axiom is rejected (`native_decide` trusts the compiler, through an axiom of its own;
the gate bans the `sorry` token itself, so `sorry` is not written here) -/
def Eqn.p5.statement : Prop := (1 : Nat) + 1 = 2
theorem Eqn.p5 : Eqn.p5.statement := by unfold Eqn.p5.statement; native_decide

section
variable [Hooks]

/-- an obligation that reads a hook: stated, and proved, for every implementation -/
def Eqn.p6.statement : Prop := ∀ (v : Nat), Hooks.recov v = Hooks.recov v
theorem Eqn.p6 : Eqn.p6.statement := fun _ => rfl
theorem Eqn.p7.lit (v : Nat) : Hooks.recov v = Hooks.recov v := rfl
end

/-- info: ProvesCheck.Eqn.p1 proves ProvesCheck.Eqn.p1.statement; depends on axioms: [] -/
#guard_msgs (info, drop warning) in
#k2l_proves Eqn.p1

/-- info: ProvesCheck.Eqn.p2 proves ProvesCheck.Eqn.p2.statement; depends on axioms: [propext] -/
#guard_msgs (info, drop warning) in
#k2l_proves Eqn.p2

/--
error: ProvesCheck.Eqn.p3 : ∀ (n : Nat), n + 0 = n ∧ True, but the obligation ProvesCheck.Eqn.p3.statement is Eqn.p3.statement, or ∀ (n : Nat), n + 0 = n
-/
#guard_msgs (whitespace := lax, error, drop warning) in
#k2l_proves Eqn.p3

/--
error: ProvesCheck.Eqn.p4 : ∀ (n : Nat), n = n → n + 0 = n, but the obligation ProvesCheck.Eqn.p4.statement is Eqn.p4.statement, or ∀ (n : Nat), n + 0 = n
-/
#guard_msgs (whitespace := lax, error, drop warning) in
#k2l_proves Eqn.p4

/--
error: ProvesCheck.Eqn.p5 depends on disallowed axioms [ProvesCheck.Eqn.p5._native.native_decide.ax_1_1]
-/
#guard_msgs (whitespace := lax, error, drop warning) in
#k2l_proves Eqn.p5

/-- info: ProvesCheck.Eqn.p6 proves ProvesCheck.Eqn.p6.statement; depends on axioms: [] -/
#guard_msgs (info, drop warning) in
#k2l_proves Eqn.p6

/-- info: ProvesCheck.Eqn.p7.lit proves ProvesCheck.Eqn.p6.statement; depends on axioms: [] -/
#guard_msgs (info, drop warning) in
#k2l_proves Eqn.p6.statement Eqn.p7.lit

end ProvesCheck
