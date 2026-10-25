import KPrelude.Run
import KPrelude.Invariant

/-! `Preserved` along the prelude's counted closure `StepsN` (prelude-dependent only because
`StepsN` lives in `KPrelude.Run`). -/

namespace KPrelude

variable {α : Type} {S : α → α → Prop} {P : α → Prop}

theorem Preserved.stepsN (hP : Preserved S P) :
    ∀ {n : Nat} {c c' : α}, StepsN S n c c' → P c → P c'
  | _, _, _, .refl _, hc => hc
  | _, _, _, .step hs rest, hc => hP.stepsN rest (hP _ _ hc hs)

theorem Star.of_stepsN : ∀ {n : Nat} {c c' : α}, StepsN S n c c' → Star S c c'
  | _, _, _, .refl _ => .refl _
  | _, _, _, .step hs rest => .step hs (Star.of_stepsN rest)

theorem Star.exists_stepsN {c c' : α} (h : Star S c c') : ∃ n, StepsN S n c c' := by
  induction h with
  | refl c => exact ⟨0, .refl c⟩
  | step hs _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step hs hn⟩

/-- A counted run from a typed configuration is a counted run of the typed view. -/
theorem TStepsN_iff (hP : Preserved S P) (t : TConfig P) (n : Nat) (c' : α) :
    StepsN S n t.1 c' ↔ ∃ t' : TConfig P, t'.1 = c' ∧ StepsN (TStep S P) n t t' := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := t
    simp only at h
    induction h with
    | refl => exact ⟨⟨_, hc⟩, rfl, .refl _⟩
    | step hs _ ih =>
      obtain ⟨t', he, ht⟩ := ih (hP _ _ hc hs)
      exact ⟨t', he, .step (show TStep S P ⟨_, hc⟩ ⟨_, hP _ _ hc hs⟩ from hs) ht⟩
  · rintro ⟨t', rfl, h⟩
    induction h with
    | refl => exact .refl _
    | step hs _ ih => exact .step hs ih

end KPrelude
