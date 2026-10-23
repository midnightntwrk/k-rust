import KClaims.Reach
import KPrelude.Run

/-!
# Claims over a semantics with a deterministic executable step

A generated semantics (k2lean) has a relation `Step` and an executable `step` with
`step c = .next c' → Step c c'`, `step c = .stuck → ¬ Step c d`, `step c = .undefined r → ¬ Step c d`,
and, for a deterministic definition, `Step c d → step c = .next d`.
With these, `AF` unfolds along the one computed successor, which is what symbolic execution
by evaluation of `step` needs.
-/

namespace KClaims

open KPrelude

/-- `step` decides the deterministic relation `R`. -/
class ExecDet {α : Type} (R : α → α → Prop) (step : outParam (α → Outcome α)) : Prop where
  sound : ∀ {c c' : α}, step c = .next c' → R c c'
  complete : ∀ {c d : α}, R c d → step c = .next d

variable {α : Type} {R : α → α → Prop} {step : α → Outcome α} [ExecDet R step]
  {P : α → Prop} {c c' : α}

theorem ExecDet.unique (h : step c = .next c') {d : α} (hd : R c d) : d = c' := by
  have := ExecDet.complete hd
  rw [h] at this
  exact (Outcome.next.inj this).symm

theorem ExecDet.no_step (h : ∀ c', step c ≠ .next c') (d : α) : ¬ R c d :=
  fun hd => h d (ExecDet.complete hd)

theorem AF.next (h : step c = .next c') (k : AF R P c') : AF R P c :=
  AF.step ⟨c', ExecDet.sound h⟩ fun _ hd => ExecDet.unique h hd ▸ k

theorem AFn.next {n : Nat} (h : step c = .next c') (k : AFn R P n c') : AFn R P (n + 1) c :=
  AFn.step ⟨c', ExecDet.sound h⟩ fun _ hd => ExecDet.unique h hd ▸ k

/-- Refutation step: a configuration outside `P` passes `AF P` on to its successor. -/
theorem AF.next_inv (h : AF R P c) (hn : ¬ P c) (hs : step c = .next c') : AF R P c' := by
  rcases AF.unfold.1 h with hp | ⟨_, hall⟩
  · exact absurd hp hn
  · exact hall c' (ExecDet.sound hs)

theorem EF.next (h : step c = .next c') (k : EF R P c') : EF R P c := EF.step (ExecDet.sound h) k

/-- A configuration on which `step` does not return a successor (stuck, or undefined:
a rule applies with a `⊥` right-hand side) satisfies `AF P` only if it satisfies `P`. -/
theorem AF.of_no_next (h : ∀ c', step c ≠ .next c') : AF R P c ↔ P c := by
  refine ⟨fun hc => ?_, AF.here⟩
  rcases AF.unfold.1 hc with hp | ⟨⟨d, hd⟩, _⟩
  · exact hp
  · exact absurd hd (ExecDet.no_step h d)

theorem AF.stuck (h : step c = .stuck) : AF R P c ↔ P c :=
  AF.of_no_next fun c' e => by rw [h] at e; cases e

theorem AF.undefined {r : String} (h : step c = .undefined r) : AF R P c ↔ P c :=
  AF.of_no_next fun c' e => by rw [h] at e; cases e

end KClaims
