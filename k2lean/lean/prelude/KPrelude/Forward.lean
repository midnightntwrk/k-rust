import KPrelude.Scaffold
import KPrelude.Paths

/-! One definition `A` run into another `B` in one direction: every step of `A` is matched by zero
or more steps of `B` (`Forward.Sim`). Where `A` is a reference that runs one order (a script in its
order) and `B` runs every order, this gives the result a consumer relies on: when `B`'s terminal
configurations from a start are unique up to `E` (confluence modulo `E`, `terminal_unique_of_local`),
the result of `A`'s run is the result of every run of `B` to a terminal configuration
(`result_unique_of`).

Nothing is assumed of `A`'s determinism or of `B`'s termination: the theorem is about a run of `A`
that reaches its end (`End`) and a run of `B` that reaches a terminal configuration. At `A`'s end,
`B` owes a terminal configuration that agrees with it (`Res`), reached from the related one. -/

universe u

namespace KPrelude.Forward

variable {α β : Type u} {SA : α → α → Prop} {SB : β → β → Prop} {R : α → β → Prop}

/-- `R` is a forward simulation of `A` by `B`: a step of `A` from a configuration related to `b` is
matched by zero or more steps of `B` from `b` to a configuration related to the step's target. -/
def Sim (SA : α → α → Prop) (SB : β → β → Prop) (R : α → β → Prop) : Prop :=
  ∀ (a a' : α) (b : β), R a b → SA a a' → ∃ b', Star SB b b' ∧ R a' b'

/-- A run of `A` is matched by a run of `B`. -/
theorem Sim.star (h : Sim SA SB R) {a a' : α} (ha : Star SA a a') :
    ∀ {b : β}, R a b → ∃ b', Star SB b b' ∧ R a' b' := by
  induction ha with
  | refl a => intro b hr; exact ⟨b, .refl b, hr⟩
  | step s _ ih =>
    intro b hr
    obtain ⟨b₁, h₁, hr₁⟩ := h _ _ _ hr s
    obtain ⟨b', h', hr'⟩ := ih hr₁
    exact ⟨b', Paths.star_trans h₁ h', hr'⟩

/-- A stuttering simulation (`refine`'s, `StutterSim`) is a forward simulation: the measure that
bounds `A`'s stuttering is not needed to carry a run of `A` that is given. -/
theorem _root_.KPrelude.StutterSim.forward {μ : α → Nat} (h : StutterSim SA SB R μ) : Sim SA SB R := by
  intro a a' b hr s
  rcases h _ _ _ s hr with ⟨b', ht, hr'⟩ | ⟨hr', _⟩
  · exact ⟨b', Star.of_transGen ht, hr'⟩
  · exact ⟨b, .refl b, hr'⟩

variable {End : α → Prop} {Res : α → β → Prop}

/-- A run of `A` to its end is matched by a run of `B` to a terminal configuration that agrees with
it, when `B`, at a configuration related to an end of `A`, reaches one (`hend`). -/
theorem result_of (h : Sim SA SB R)
    (hend : ∀ (a : α) (b : β), R a b → End a → ∃ b', Star SB b b' ∧ Terminal SB b' ∧ Res a b')
    {a₀ a : α} {b₀ : β} (h₀ : R a₀ b₀) (ha : Star SA a₀ a) (hd : End a) :
    ∃ b, Star SB b₀ b ∧ Terminal SB b ∧ Res a b := by
  obtain ⟨b₁, h₁, hr₁⟩ := h.star ha h₀
  obtain ⟨b, h₂, ht, hres⟩ := hend _ _ hr₁ hd
  exact ⟨b, Paths.star_trans h₁ h₂, ht, hres⟩

/-- **The result of `A`'s run is the result of every run of `B`.** If `A` runs from `a₀` to its end
`a`, and `B`'s terminal configurations reachable from `b₀` are unique up to `E` (`huniq`), with
`Res a` closed under `E` (`hres`), then every run of `B` from `b₀` to a terminal configuration ends
at one that agrees with `a`. -/
theorem result_unique_of_equiv {E : β → β → Prop} (h : Sim SA SB R)
    (hend : ∀ (a : α) (b : β), R a b → End a → ∃ b', Star SB b b' ∧ Terminal SB b' ∧ Res a b')
    {a₀ a : α} {b₀ : β}
    (huniq : ∀ (b₁ b₂ : β), Star SB b₀ b₁ → Terminal SB b₁ → Star SB b₀ b₂ → Terminal SB b₂ → E b₁ b₂)
    (hres : ∀ (b₁ b₂ : β), Res a b₁ → E b₁ b₂ → Res a b₂)
    (h₀ : R a₀ b₀) (ha : Star SA a₀ a) (hd : End a) {b : β} (hb : Star SB b₀ b)
    (ht : Terminal SB b) : Res a b := by
  obtain ⟨b₁, h₁, t₁, hr₁⟩ := result_of h hend h₀ ha hd
  exact hres _ _ hr₁ (huniq _ _ h₁ t₁ hb ht)

/-- `result_unique_of_equiv` where `B`'s terminal configurations from `b₀` are unique. -/
theorem result_unique_of (h : Sim SA SB R)
    (hend : ∀ (a : α) (b : β), R a b → End a → ∃ b', Star SB b b' ∧ Terminal SB b' ∧ Res a b')
    {a₀ a : α} {b₀ : β}
    (huniq : ∀ (b₁ b₂ : β), Star SB b₀ b₁ → Terminal SB b₁ → Star SB b₀ b₂ → Terminal SB b₂ → b₁ = b₂)
    (h₀ : R a₀ b₀) (ha : Star SA a₀ a) (hd : End a) {b : β} (hb : Star SB b₀ b)
    (ht : Terminal SB b) : Res a b :=
  result_unique_of_equiv (E := Eq) h hend huniq (fun _ _ hr e => e ▸ hr) h₀ ha hd hb ht

end KPrelude.Forward
