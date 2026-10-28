import KPrelude.Tactic

/-! The checks of `#k2l_refuted` (`KPrelude.Tactic`): a refutation of an obligation is
`¬ X.statement`, or `¬ ∀ [Hooks], X.statement` when the statement reads the library's parameters;
a restatement, the naive form inside the parameters' section, and `sorry` are rejected. The gate
runs this file (`lake env lean` in the prelude) and fails on any unexpected message. -/

namespace RefutedCheck

class Hooks where
  recov : Nat → Option Nat

section
variable [Hooks]

/-- an obligation that reads a hook -/
def Eqn.e2.statement : Prop := ∀ (v : Nat), Hooks.recov v = Hooks.recov (v + 1)

omit [Hooks] in
/-- the obligation is the statement for every implementation; refuting it picks one -/
theorem Eqn.e2.refuted : ¬ ∀ [Hooks], Eqn.e2.statement := by
  intro h
  have := @h ⟨fun v => if v = 0 then some 0 else none⟩ 0
  simp at this

/-- written naively in the section, the theorem is `∀ [Hooks], ¬ statement`: a stronger claim than
refuting the obligation, and not its form -/
def Eqn.e6.statement : Prop := ∀ (v : Nat), Hooks.recov v = Hooks.recov v
theorem Eqn.e6.refuted : ¬ Eqn.e6.statement := by
  intro h; sorry
end

/-- an obligation without parameters -/
def Eqn.e3.statement : Prop := ∀ (n : Nat), n + 0 = n + 1
theorem Eqn.e3.refuted : ¬ Eqn.e3.statement := by
  intro h; have := h 0; simp at this

/-- a restated negation is rejected, even an equivalent one -/
def Eqn.e4.statement : Prop := ∀ (n : Nat), n = n + 1
theorem Eqn.e4.refuted : ¬ ∀ (n : Nat), n = n + 1 := by intro h; have := h 0; simp at this

/-- a refutation by `sorry` is rejected -/
def Eqn.e5.statement : Prop := ∀ (n : Nat), n = n
theorem Eqn.e5.refuted : ¬ Eqn.e5.statement := by sorry

/-- info: RefutedCheck.Eqn.e2.refuted refutes RefutedCheck.Eqn.e2.statement; depends on axioms: [propext] -/
#guard_msgs (info, drop warning) in
#k2l_refuted Eqn.e2

/-- info: RefutedCheck.Eqn.e3.refuted refutes RefutedCheck.Eqn.e3.statement; depends on axioms: [propext] -/
#guard_msgs (info, drop warning) in
#k2l_refuted Eqn.e3

/--
error: RefutedCheck.Eqn.e4.refuted : ¬∀ (n : Nat), n = n + 1, but the refutation of RefutedCheck.Eqn.e4.statement is ¬Eqn.e4.statement
-/
#guard_msgs (whitespace := lax, error, drop warning) in
#k2l_refuted Eqn.e4

/--
error: RefutedCheck.Eqn.e5.refuted depends on disallowed axioms [sorryAx]
-/
#guard_msgs (whitespace := lax, error, drop warning) in
#k2l_refuted Eqn.e5

/--
error: RefutedCheck.Eqn.e6.refuted : ∀ [inst : Hooks], ¬Eqn.e6.statement, but the refutation of RefutedCheck.Eqn.e6.statement is ¬∀ [inst : Hooks], Eqn.e6.statement
-/
#guard_msgs (whitespace := lax, error, drop warning) in
#k2l_refuted Eqn.e6

/-- a claim: the statement constant is the obligation itself, its refutation a theorem of any name -/
def Claim.copy : Prop := ∀ (n : Nat), n = n + 1
theorem copy_false : ¬ Claim.copy := by intro h; have := h 0; simp at this

/-- info: RefutedCheck.copy_false refutes RefutedCheck.Claim.copy; depends on axioms: [propext] -/
#guard_msgs (info, drop warning) in
#k2l_refuted Claim.copy copy_false

end RefutedCheck
