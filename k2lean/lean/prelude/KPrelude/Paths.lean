import KPrelude.Invariant
import KPrelude.Run

/-!
# Paths and runs of a transition relation (RUN-1)

One module for the vocabulary of paths that the theorem kinds share. `Star` (`Invariant.lean`)
and `StepsN` (`Run.lean`) keep their homes; this module adds, in `KPrelude.Paths`:

* `Inf R a`: an infinite path from `a`; `Terminates R a`: none exists (`Acc` of the converse);
  `terminates_or_inf` and `Terminates.not_inf`: always one, never both.
* Maximal runs. `Complete R` is `R` with a terminal configuration stepping to itself, and
  `IsRun R s` an infinite sequence of `Complete R` steps, so a run that halts is the sequence
  that repeats its last configuration. "P at every point of every run from `a`" is then
  "P at every configuration reachable from `a`" (`always_iff`), and a preserved invariant holds
  along every run (`always_of_preserved`).
* `FirstReach R Y a b`: a path from `a` to `b` where `b` is the first configuration with `Y`;
  `Segment R Y a b`: one or more steps from `a` to the first `Y` after it, such as a coroutine's
  run from a resume to its next yield. Under a deterministic `R` both are functional
  (`FirstReach.unique`, `Segment.deterministic`).

`KPrelude.Pending.Chain` is `Inf` of a partial function's graph. The claims package's `Reach`
and `Terminates` are related to these in `KClaims/Paths.lean`. -/

namespace KPrelude
namespace Paths

universe u

section
variable {α : Type u} (R : α → α → Prop)

/-- An infinite path from `a`. -/
def Inf (a : α) : Prop := ∃ s : Nat → α, s 0 = a ∧ ∀ n, R (s n) (s (n + 1))

/-- No infinite path starts at `a`. -/
def Terminates (a : α) : Prop := Acc (fun x y => R y x) a

/-- `R`, with a configuration that has no successor stepping to itself. -/
def Complete (x y : α) : Prop := R x y ∨ (x = y ∧ ∀ z, ¬ R x z)

/-- A maximal run: an infinite path of `Complete R`; a halting run repeats its last
configuration. -/
def IsRun (s : Nat → α) : Prop := ∀ n, Complete R (s n) (s (n + 1))

/-- A path from `a` to `b`, `b` the first configuration on it that satisfies `Y`. -/
inductive FirstReach (Y : α → Prop) : α → α → Prop where
  | here {a : α} : Y a → FirstReach Y a a
  | step {a a' b : α} : ¬ Y a → R a a' → FirstReach Y a' b → FirstReach Y a b

/-- One or more steps from `a`, to the first configuration after `a` that satisfies `Y`. -/
def Segment (Y : α → Prop) (a b : α) : Prop := ∃ a', R a a' ∧ FirstReach R Y a' b

end

variable {α : Type u} {R : α → α → Prop}

theorem Inf.inv {a : α} (h : Inf R a) : ∃ b, R a b ∧ Inf R b := by
  obtain ⟨s, h0, hs⟩ := h
  exact ⟨s 1, h0 ▸ hs 0, fun n => s (n + 1), rfl, fun n => hs (n + 1)⟩

theorem Inf.step {a b : α} (h : R a b) (hb : Inf R b) : Inf R a := by
  obtain ⟨s, h0, hs⟩ := hb
  refine ⟨fun n => match n with | 0 => a | n + 1 => s n, rfl, fun n => ?_⟩
  cases n with
  | zero => show R a (s 0); rw [h0]; exact h
  | succ n => exact hs n

/-- Never both. -/
theorem Terminates.not_inf {a : α} (h : Terminates R a) : ¬ Inf R a := by
  induction h with
  | intro x _ ih =>
    intro hx
    obtain ⟨b, hb, hi⟩ := Inf.inv hx
    exact ih b hb hi

/-- Always one (classical: the path is chosen through the configurations that do not
terminate). -/
theorem terminates_or_inf (a : α) : Terminates R a ∨ Inf R a := by
  classical
  by_cases h : Terminates R a
  · exact Or.inl h
  · right
    have step : ∀ x, ¬ Terminates R x → ∃ y, R x y ∧ ¬ Terminates R y := fun x hx =>
      Classical.byContradiction fun hn =>
        hx (Acc.intro x fun y hy => Classical.byContradiction fun hy' => hn ⟨y, hy, hy'⟩)
    let T := {x // ¬ Terminates R x}
    let nx : T → T := fun x => ⟨(step x.1 x.2).choose, (step x.1 x.2).choose_spec.2⟩
    let s : Nat → T := fun n => Nat.rec (motive := fun _ => T) ⟨a, h⟩ (fun _ x => nx x) n
    exact ⟨fun n => (s n).1, rfl, fun n => (step (s n).1 (s n).2).choose_spec.1⟩

/-- From every configuration there is a run (classical: a successor is chosen where one
exists). -/
theorem exists_run (a : α) : ∃ s, s 0 = a ∧ IsRun R s := by
  classical
  let nx : α → α := fun x => if h : ∃ y, R x y then h.choose else x
  let s : Nat → α := fun n => Nat.rec (motive := fun _ => α) a (fun _ x => nx x) n
  refine ⟨s, rfl, fun n => ?_⟩
  show Complete R (s n) (if h : ∃ y, R (s n) y then h.choose else s n)
  split
  · next h => exact Or.inl h.choose_spec
  · next h => exact Or.inr ⟨rfl, fun z hz => h ⟨z, hz⟩⟩

theorem Complete.star {x y : α} (h : Complete R x y) : Star R x y := by
  rcases h with h | ⟨rfl, _⟩
  · exact Star.step h (Star.refl _)
  · exact Star.refl _

theorem star_trans {a b c : α} (h : Star R a b) (h' : Star R b c) : Star R a c := by
  induction h with
  | refl => exact h'
  | step hs _ ih => exact Star.step hs (ih h')

/-- Every point of a run is reachable from its start. -/
theorem IsRun.star {s : Nat → α} (h : IsRun R s) : ∀ n, Star R (s 0) (s n)
  | 0 => Star.refl _
  | n + 1 => star_trans (IsRun.star h n) (h n).star

/-- Every reachable configuration lies on a run from the start. -/
theorem star_on_run {a c : α} (h : Star R a c) : ∃ s n, s 0 = a ∧ IsRun R s ∧ s n = c := by
  induction h with
  | refl c =>
    obtain ⟨s, h0, hs⟩ := exists_run (R := R) c
    exact ⟨s, 0, h0, hs, h0⟩
  | @step a a' _ hs _ ih =>
    obtain ⟨s, n, h0, hr, hn⟩ := ih
    refine ⟨fun k => match k with | 0 => a | k + 1 => s k, n + 1, rfl, fun k => ?_, hn⟩
    cases k with
    | zero => show Complete R a (s 0); rw [h0]; exact Or.inl hs
    | succ k => exact hr k

/-- "P at every point of every run from `a`" is "P at every configuration reachable from `a`". -/
theorem always_iff {P : α → Prop} {a : α} :
    (∀ s, s 0 = a → IsRun R s → ∀ n, P (s n)) ↔ ∀ c, Star R a c → P c := by
  constructor
  · intro h c hc
    obtain ⟨s, n, h0, hr, hn⟩ := star_on_run hc
    exact hn ▸ h s h0 hr n
  · intro h s h0 hr n
    exact h _ (h0 ▸ hr.star n)

/-- A preserved invariant holds at every point of every run from a configuration that satisfies
it. -/
theorem always_of_preserved {P : α → Prop} (hP : Preserved R P) {a : α} (ha : P a) :
    ∀ s, s 0 = a → IsRun R s → ∀ n, P (s n) :=
  always_iff.2 fun _ hc => Preserved.star hP hc ha

/-- Under a deterministic `R`, the first configuration with `Y` is unique. -/
theorem FirstReach.unique {Y : α → Prop} (hdet : ∀ {c c₁ c₂ : α}, R c c₁ → R c c₂ → c₁ = c₂)
    {a b c : α} (hb : FirstReach R Y a b) (hc : FirstReach R Y a c) : b = c := by
  induction hb with
  | here hy =>
    cases hc with
    | here _ => rfl
    | step hn _ _ => exact absurd hy hn
  | step hn hs _ ih =>
    cases hc with
    | here hy => exact absurd hy hn
    | step _ hs' hc' => exact ih (hdet hs hs' ▸ hc')

/-- Under a deterministic `R`, a segment from `a` is unique: the big step is deterministic. -/
theorem Segment.deterministic {Y : α → Prop}
    (hdet : ∀ {c c₁ c₂ : α}, R c c₁ → R c c₂ → c₁ = c₂)
    {a b c : α} (hb : Segment R Y a b) (hc : Segment R Y a c) : b = c := by
  obtain ⟨a₁, h₁, hb⟩ := hb
  obtain ⟨a₂, h₂, hc⟩ := hc
  exact FirstReach.unique (R := R) hdet hb (hdet h₂ h₁ ▸ hc)

theorem FirstReach.star {Y : α → Prop} {a b : α} (h : FirstReach R Y a b) : Star R a b := by
  induction h with
  | here => exact Star.refl _
  | step _ hs _ ih => exact Star.step hs ih

end Paths
end KPrelude
