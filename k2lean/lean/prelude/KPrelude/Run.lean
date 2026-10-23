/-!
# Three-valued step outcomes and the fuelled run loop

`Outcome.undefined` is a step whose rule applies (its left-hand side matches and its requires
is `true`) but whose right-hand side is `⊥`: in matching logic there is no successor, so an
execution can only stop there with an error (for example a division by zero). It is distinct
from `stuck`, where no rule applies.
-/

namespace KPrelude

inductive Outcome (α : Type) where
  | next (c : α)
  | stuck
  /-- The rule that applied, by its KORE label or unique id. -/
  | undefined (rule : String)
  deriving Repr, DecidableEq

inductive Status where
  | final
  | stuck
  | undefined (rule : String)
  | outOfFuel
  deriving Repr, DecidableEq

structure RunResult (α : Type) where
  config : α
  steps : Nat
  status : Status

/-- Runs `step` from `c` for at most `fuel` steps. `final` is `stuck` with an empty
computation; that distinction belongs to the caller, which knows the configuration shape. -/
def run {α : Type} (step : α → Outcome α) : Nat → α → Nat → RunResult α
  | 0, c, n => ⟨c, n, .outOfFuel⟩
  | fuel + 1, c, n =>
    match step c with
    | .next c' => run step fuel c' (n + 1)
    | .stuck => ⟨c, n, .stuck⟩
    | .undefined r => ⟨c, n, .undefined r⟩

/-- Reflexive-transitive closure, counting steps. -/
inductive StepsN {α : Type} (R : α → α → Prop) : Nat → α → α → Prop where
  | refl (c : α) : StepsN R 0 c c
  | step {n : Nat} {a b c : α} : R a b → StepsN R n b c → StepsN R (n + 1) a c

/-- If every computed step is a `Step` from an invariant-satisfying state, and the invariant is
preserved, a run is a `StepsN` derivation. -/
theorem run_sound {α : Type} {step : α → Outcome α} {R : α → α → Prop} {I : α → Prop}
    (hsound : ∀ c c', I c → step c = .next c' → R c c')
    (hpres : ∀ c c', I c → R c c' → I c') :
    ∀ (fuel : Nat) (c : α) (n : Nat), I c →
      StepsN R ((run step fuel c n).steps - n) c (run step fuel c n).config ∧
      n ≤ (run step fuel c n).steps
  | 0, c, n, _ => by simp [run]; exact StepsN.refl c
  | fuel + 1, c, n, hI => by
    unfold run
    split
    · next c' h =>
      have hr := hsound c c' hI h
      obtain ⟨ih, hle⟩ := run_sound hsound hpres fuel c' (n + 1) (hpres c c' hI hr)
      refine ⟨?_, by omega⟩
      have e : (run step fuel c' (n + 1)).steps - n = ((run step fuel c' (n + 1)).steps - (n + 1)) + 1 := by omega
      rw [e]
      exact StepsN.step hr ih
    · simp; exact StepsN.refl c
    · simp; exact StepsN.refl c

end KPrelude
