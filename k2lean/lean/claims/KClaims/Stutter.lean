import KPrelude.Scaffold
import KClaims.Reach

/-!
# Claims transferred along a stuttering simulation

`k2lean refine` relates two definitions whose steps do not correspond one to one by a stuttering
bisimulation (`KPrelude.StutterBisim`): a step of one side from a related state is matched by
one or more steps of the other, or by none while a measure decreases. A claim that some path
reaches its target (`Reach`, `EF`) carries forward along the simulation alone, to the image target
`fun d => ∃ a, R a d ∧ P a` (or any target that `P` implies on related states):

- `Reach.of_stutter`: by induction on the finite path; a matched step contributes its steps, a
  stutter none;
- `EF.of_stutter`: by coinduction on the states that reach a related one, with the stuttering
  bounded by the measure.

An all-path claim (`AF`) does not carry this way in general: one step of the other side may stand
for several steps of the first, and the first may meet its target only at one of the intermediate
states, which nothing relates (`StutterSim` relates the end of the matching steps only). For
`SA`: `c₀ → c₁ → c₂`, `SB`: `d₀ → d₁`, `d₀ → d₂`, `d₁ → d₂`, `R` relating each `cᵢ` to `dᵢ` (a
stuttering bisimulation: `SB`'s step `d₀ → d₂` is matched by `SA`'s two) and `P` true at `c₁`
only, `AF SA P c₀` holds, but `SB`'s path `d₀ → d₂` meets no state related to `c₁`. So `AF`
transfers only for a target that, once reached, stays reached (or is terminal); not stated here.
When `SB` is deterministic, `AF` and `EF` coincide on it (`AF_iff_EF_of_det`), so an all-path claim
carries as its one-path weakening and back. -/

namespace KClaims

open KPrelude

variable {α β : Type} {SA : α → α → Prop} {SB : β → β → Prop} {R : α → β → Prop}
  {μ : α → Nat} {P : α → Prop} {Q : β → Prop}

/-- A nonempty run starts with a step, then a run. -/
theorem transGen_head {r : β → β → Prop} {a b : β} (h : Relation.TransGen r a b) :
    ∃ c, r a c ∧ Star r c b := by
  induction h with
  | single hs => exact ⟨_, hs, .refl _⟩
  | tail _ hs ih =>
    obtain ⟨c, hc, hst⟩ := ih
    exact ⟨c, hc, hst.trans (.step hs (.refl _))⟩

/-- A nonempty run in front of a finite path to the target. -/
theorem Reach.of_transGen {r : β → β → Prop} {a b : β} (h : Relation.TransGen r a b)
    (hb : Reach r Q b) : Reach r Q a := by
  induction h with
  | single hs => exact Reach.step hs hb
  | tail _ hs ih => exact ih (Reach.step hs hb)

/-- A finite path of `SA` to `P` from `c` is matched by one of `SB` from every related `d` to
`Q`, for a target `Q` that `P` implies on related states. -/
theorem Reach.of_stutter (h : StutterSim SA SB R μ) (hPQ : ∀ a b, R a b → P a → Q b) :
    ∀ {c : α} {d : β}, R c d → Reach SA P c → Reach SB Q d := by
  intro c d hr hc
  induction hc generalizing d with
  | here hp => exact Reach.here (hPQ _ _ hr hp)
  | step hs _ ih =>
    rcases h _ _ _ hs hr with ⟨d', ht, hr'⟩ | ⟨hr', _⟩
    · exact Reach.of_transGen ht (ih hr')
    · exact ih hr'

/-- The one-path claims of `SA` hold of every related state of `SB`, for a target `Q` that `P`
implies on related states: the states of `SB` that reach a state related to one where the claim
holds satisfy `Q` or have a successor that does too, since the measure bounds `SA`'s stuttering
against one state of `SB`. -/
theorem EF.of_stutter (h : StutterSim SA SB R μ) (hPQ : ∀ a b, R a b → P a → Q b) {c : α} {d : β}
    (hr : R c d) (hc : EF SA P c) : EF SB Q d := by
  let X : β → Prop := fun d => ∃ c d', Star SB d d' ∧ R c d' ∧ EF SA P c
  -- at a related state: `Q`, or a step of `SB` into `X`, by induction on the measure
  have here : ∀ (c : α) (d : β), R c d → EF SA P c → Q d ∨ ∃ e, SB d e ∧ X e := by
    intro c
    induction c using measure_ind μ with
    | h c ih =>
      intro d hr hc
      rcases EF.unfold.1 hc with hp | ⟨c', hs, hc'⟩
      · exact Or.inl (hPQ _ _ hr hp)
      · rcases h _ _ _ hs hr with ⟨d', ht, hr'⟩ | ⟨hr', hlt⟩
        · obtain ⟨d₁, hd₁, hst⟩ := transGen_head ht
          exact Or.inr ⟨d₁, hd₁, c', d', hst, hr', hc'⟩
        · exact ih c' hlt d hr' hc'
  refine EF.coind X ?_ ⟨c, d, .refl _, hr, hc⟩
  rintro d ⟨c, d', hst, hr, hc⟩
  cases hst with
  | refl => exact here c d hr hc
  | step hs rest => exact Or.inr ⟨_, hs, c, d', rest, hr, hc⟩

/-- `Reach.of_stutter` and `EF.of_stutter` to the image target, with no condition. -/
theorem Reach.image_of_stutter (h : StutterSim SA SB R μ) {c : α} {d : β} (hr : R c d)
    (hc : Reach SA P c) : Reach SB (fun d => ∃ a, R a d ∧ P a) d :=
  Reach.of_stutter h (fun a _ hr hp => ⟨a, hr, hp⟩) hr hc

theorem EF.image_of_stutter (h : StutterSim SA SB R μ) {c : α} {d : β} (hr : R c d)
    (hc : EF SA P c) : EF SB (fun d => ∃ a, R a d ∧ P a) d :=
  EF.of_stutter h (fun a _ hr hp => ⟨a, hr, hp⟩) hr hc

end KClaims
