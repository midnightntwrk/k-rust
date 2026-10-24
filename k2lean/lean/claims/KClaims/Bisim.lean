import KPrelude.Relate
import KClaims.Reach

/-!
# Claims transferred along a bisimulation

A strong bisimulation `R` between `S₁` and `S₂` (`KPrelude.Bisimulation`, which `k2lean relate`
generates for two definitions of one language) relates states whose successors correspond in
both directions. The claim modalities only look at successors and at the target predicate, so a
claim holds at `c` over `S₁` exactly when the corresponding claim holds at a related `d` over
`S₂`, provided the two targets agree on related states:

- `AF.of_bisim`, `EF.of_bisim`, `Reach.of_bisim`: from `S₁` to `S₂`, when `P a → Q b` for every
  related pair; `AF.of_bisim_symm`, `EF.of_bisim_symm` go back, when `Q b → P a`;
- `AF_bisim_iff`, `EF_bisim_iff`: the equivalences, when `P a ↔ Q b` for every related pair;
- `AF.image_of_bisim`, `EF.image_of_bisim`: with no condition, for the image target
  `fun d => ∃ a, R a d ∧ P a` (the states related to one satisfying `P`).

The all-path transfer uses both directions of the bisimulation: `fwd` gives the related state a
successor whenever the original has one, and `bwd` sends each of its successors back to a
successor of the original. The one-path and reachability transfers use only `fwd`.
-/

namespace KClaims

open KPrelude

variable {α β : Type} {S₁ : α → α → Prop} {S₂ : β → β → Prop} {R : α → β → Prop}
  {P : α → Prop} {Q : β → Prop} {c : α} {d : β}

/-- The converse of a bisimulation is a bisimulation. -/
theorem bisim_flip (h : Bisimulation S₁ S₂ R) : Bisimulation S₂ S₁ (fun b a => R a b) where
  fwd := fun hr hs => h.bwd hr hs
  bwd := fun hr hs => h.fwd hr hs

/-! ## All-path -/

/-- An all-path claim over `S₁` holds at every related state over `S₂`, for a target `Q` implied
by `P` on related states. -/
theorem AF.of_bisim (hb : Bisimulation S₁ S₂ R) (hPQ : ∀ a b, R a b → P a → Q b) (hr : R c d)
    (h : AF S₁ P c) : AF S₂ Q d := by
  refine AF.coind (fun d => ∃ c, R c d ∧ AF S₁ P c) ?_ ⟨c, hr, h⟩
  rintro d ⟨c, hr, hc⟩
  rcases AF.unfold.1 hc with hp | ⟨⟨c', hc'⟩, hall⟩
  · exact Or.inl (hPQ c d hr hp)
  · obtain ⟨d', hd', -⟩ := hb.fwd hr hc'
    refine Or.inr ⟨⟨d', hd'⟩, fun e he => ?_⟩
    obtain ⟨c'', hc'', hr''⟩ := hb.bwd hr he
    exact ⟨c'', hr'', hall c'' hc''⟩

/-- The converse transfer, from `S₂` back to `S₁`. -/
theorem AF.of_bisim_symm (hb : Bisimulation S₁ S₂ R) (hQP : ∀ a b, R a b → Q b → P a) (hr : R c d)
    (h : AF S₂ Q d) : AF S₁ P c :=
  AF.of_bisim (bisim_flip hb) (fun b a hr hq => hQP a b hr hq) hr h

/-- Related states satisfy corresponding all-path claims. -/
theorem AF_bisim_iff (hb : Bisimulation S₁ S₂ R) (hPQ : ∀ a b, R a b → (P a ↔ Q b)) (hr : R c d) :
    AF S₁ P c ↔ AF S₂ Q d :=
  ⟨AF.of_bisim hb (fun a b hr => (hPQ a b hr).1) hr,
   AF.of_bisim_symm hb (fun a b hr => (hPQ a b hr).2) hr⟩

/-- An all-path claim over `S₁` holds over `S₂` for the image of its target. -/
theorem AF.image_of_bisim (hb : Bisimulation S₁ S₂ R) (hr : R c d) (h : AF S₁ P c) :
    AF S₂ (fun d => ∃ a, R a d ∧ P a) d :=
  AF.of_bisim hb (fun a _ hr hp => ⟨a, hr, hp⟩) hr h

/-! ## One-path -/

/-- A one-path claim over `S₁` holds at every related state over `S₂`. -/
theorem EF.of_bisim (hb : Bisimulation S₁ S₂ R) (hPQ : ∀ a b, R a b → P a → Q b) (hr : R c d)
    (h : EF S₁ P c) : EF S₂ Q d := by
  refine EF.coind (fun d => ∃ c, R c d ∧ EF S₁ P c) ?_ ⟨c, hr, h⟩
  rintro d ⟨c, hr, hc⟩
  rcases EF.unfold.1 hc with hp | ⟨c', hc', hef⟩
  · exact Or.inl (hPQ c d hr hp)
  · obtain ⟨d', hd', hr'⟩ := hb.fwd hr hc'
    exact Or.inr ⟨d', hd', c', hr', hef⟩

theorem EF.of_bisim_symm (hb : Bisimulation S₁ S₂ R) (hQP : ∀ a b, R a b → Q b → P a) (hr : R c d)
    (h : EF S₂ Q d) : EF S₁ P c :=
  EF.of_bisim (bisim_flip hb) (fun b a hr hq => hQP a b hr hq) hr h

theorem EF_bisim_iff (hb : Bisimulation S₁ S₂ R) (hPQ : ∀ a b, R a b → (P a ↔ Q b)) (hr : R c d) :
    EF S₁ P c ↔ EF S₂ Q d :=
  ⟨EF.of_bisim hb (fun a b hr => (hPQ a b hr).1) hr,
   EF.of_bisim_symm hb (fun a b hr => (hPQ a b hr).2) hr⟩

theorem EF.image_of_bisim (hb : Bisimulation S₁ S₂ R) (hr : R c d) (h : EF S₁ P c) :
    EF S₂ (fun d => ∃ a, R a d ∧ P a) d :=
  EF.of_bisim hb (fun a _ hr hp => ⟨a, hr, hp⟩) hr h

/-! ## Reachability (total, one-path) -/

/-- A finite path to `P` over `S₁` gives one to `Q` over `S₂` of the same length. -/
theorem Reach.of_bisim (hb : Bisimulation S₁ S₂ R) (hPQ : ∀ a b, R a b → P a → Q b) (hr : R c d)
    (h : Reach S₁ P c) : Reach S₂ Q d := by
  induction h generalizing d with
  | here hp => exact Reach.here (hPQ _ _ hr hp)
  | step hs _ ih =>
    obtain ⟨d', hd', hr'⟩ := hb.fwd hr hs
    exact Reach.step hd' (ih hr')

theorem Reach_bisim_iff (hb : Bisimulation S₁ S₂ R) (hPQ : ∀ a b, R a b → (P a ↔ Q b)) (hr : R c d) :
    Reach S₁ P c ↔ Reach S₂ Q d :=
  ⟨Reach.of_bisim hb (fun a b hr => (hPQ a b hr).1) hr,
   Reach.of_bisim (bisim_flip hb) (fun b a hr => (hPQ a b hr).2) hr⟩

end KClaims
