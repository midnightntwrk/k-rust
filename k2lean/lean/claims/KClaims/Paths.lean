import KClaims.Reach
import KPrelude.Paths

/-!
# Claims' path notions and the prelude's (RUN-1)

The claims modalities keep their own constants, which `KClaims.Tactic` and the generated claims
match by name; these lemmas relate them to `KPrelude.Paths` and `KPrelude.Star`, so that a theorem
of another kind can be cited where a claim needs it and back. -/

namespace KClaims
open KPrelude

variable {α : Type} {R : α → α → Prop} {P : α → Prop} {c : α}

/-- Claims' `Terminates` is the prelude's. -/
theorem Terminates.iff_paths : Terminates R c ↔ Paths.Terminates R c := Iff.rfl

/-- `Reach` is a reachable configuration that satisfies `P`. -/
theorem Reach.iff_star : Reach R P c ↔ ∃ d, Star R c d ∧ P d := by
  constructor
  · intro h
    induction h with
    | here hp => exact ⟨_, Star.refl _, hp⟩
    | step hs _ ih =>
      obtain ⟨d, hd, hp⟩ := ih
      exact ⟨d, Star.step hs hd, hp⟩
  · intro ⟨d, hd, hp⟩
    induction hd with
    | refl => exact Reach.here hp
    | step hs _ ih => exact Reach.step hs (ih hp)

end KClaims
