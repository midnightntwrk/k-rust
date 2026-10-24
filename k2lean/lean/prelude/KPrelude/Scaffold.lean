import KPrelude.Invariant

/-!
# The generic theorems behind the scaffolds (`confluence`, `refine`, `noninterference`)

Each scaffold command of k2lean states a theorem about a generated `Step` and reduces it to
obligations, one per rule or per pair of rules; the reduction is one of the theorems below,
proved once for every relation.

- **Confluence modulo an equivalence** (`k2lean confluence`): under a preserved hypothesis `H`,
  if every two steps from a state join (`DiamondMod`: in at most one step on each side, or
  `JoinMod`: in any number, with a measure that every step decreases, Newman's lemma), the
  terminal states reachable from a state are related by `E`, an equivalence that is a strong
  bisimulation of `Step` with itself (`StepEquiv`; `Eq` is one).
- **Stuttering simulation** (`k2lean refine`): each step of `A` is matched by one or more steps
  of `B`, or by none while a measure decreases (`StutterSim`); in both directions
  (`StutterBisim`), a run of `A` to a terminal state is matched by a run of `B` to a related
  terminal state.
- **Two runs** (`k2lean noninterference`): a relation on pairs of states from which, unless both
  are final, one side can be advanced by any of its steps without leaving the relation
  (`ProductInv`) relates the final states of any two runs from related states.
-/

set_option autoImplicit false

namespace KPrelude

universe u

section Basic

variable {α : Type u} {S : α → α → Prop}

/-- `c` has no successor. -/
def Terminal (S : α → α → Prop) (c : α) : Prop := ∀ c', ¬ S c c'

/-- At most one step: `a' = a` or `S a a'`. -/
def Opt (S : α → α → Prop) (a a' : α) : Prop := a' = a ∨ S a a'

theorem Opt.star {a a' : α} : Opt S a a' → Star S a a'
  | .inl h => h ▸ .refl _
  | .inr h => Star.single h

theorem Star.eq_of_terminal {c c' : α} (ht : Terminal S c) (h : Star S c c') : c' = c := by
  cases h with
  | refl => rfl
  | step hs _ => exact absurd hs (ht _)

theorem TransGen.head_step {a b : α} (h : Relation.TransGen S a b) : ∃ c, S a c := by
  induction h with
  | single hs => exact ⟨_, hs⟩
  | tail _ _ ih => exact ih

/-- Induction along a measure into `Nat`. -/
theorem measure_ind (μ : α → Nat) {P : α → Prop} (h : ∀ c, (∀ c', μ c' < μ c → P c') → P c)
    (c : α) : P c :=
  (measure μ).wf.induction c h

/-- Every state where a measure decreases along every step reaches a terminal state. -/
theorem exists_terminal {H : α → Prop} (hH : Preserved S H) (μ : α → Nat)
    (hμ : ∀ {c c'}, H c → S c c' → μ c' < μ c) :
    ∀ c, H c → ∃ n, Star S c n ∧ Terminal S n := by
  intro c
  induction c using measure_ind μ with
  | h c ih =>
    intro hc
    by_cases ht : Terminal S c
    · exact ⟨c, .refl _, ht⟩
    · simp only [Terminal, Classical.not_forall, Classical.not_not] at ht
      obtain ⟨c', hs⟩ := ht
      obtain ⟨n, hn, htn⟩ := ih c' (hμ hc hs) (hH _ _ hc hs)
      exact ⟨n, .step hs hn, htn⟩

end Basic

/-! ## Confluence modulo an equivalence -/

section Confluence

variable {α : Type u} {S : α → α → Prop} {E : α → α → Prop} {H : α → Prop}

/-- `E` is an equivalence and a strong bisimulation of `S` with itself: the states it relates
have related successors, so they are interchangeable for every property of runs. -/
structure StepEquiv (S : α → α → Prop) (E : α → α → Prop) : Prop where
  refl : ∀ a, E a a
  symm : ∀ {a b}, E a b → E b a
  trans : ∀ {a b c}, E a b → E b c → E a c
  sim : ∀ {a b a'}, E a b → S a a' → ∃ b', S b b' ∧ E a' b'

/-- Equality is a `StepEquiv` of every relation. -/
theorem StepEquiv.eq : StepEquiv S Eq where
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂
  sim h hs := by subst h; exact ⟨_, hs, rfl⟩

theorem StepEquiv.star (hE : StepEquiv S E) :
    ∀ {a b a'}, E a b → Star S a a' → ∃ b', Star S b b' ∧ E a' b'
  | _, b, _, he, .refl _ => ⟨b, .refl _, he⟩
  | _, _, _, he, .step hs rest => by
    obtain ⟨b₁, hb₁, he₁⟩ := hE.sim he hs
    obtain ⟨b', hb', he'⟩ := hE.star he₁ rest
    exact ⟨b', .step hb₁ hb', he'⟩

theorem StepEquiv.terminal (hE : StepEquiv S E) {a b : α} (he : E a b) (ha : Terminal S a) :
    Terminal S b := by
  intro b' hb
  obtain ⟨a', ha', _⟩ := hE.sim (hE.symm he) hb
  exact ha a' ha'

/-- `a` and `b` join modulo `E` in at most one step each. -/
def DiamondMod (S : α → α → Prop) (E : α → α → Prop) (a b : α) : Prop :=
  ∃ a' b', Opt S a a' ∧ Opt S b b' ∧ E a' b'

/-- `a` and `b` join modulo `E`. -/
def JoinMod (S : α → α → Prop) (E : α → α → Prop) (a b : α) : Prop :=
  ∃ a' b', Star S a a' ∧ Star S b b' ∧ E a' b'

/-- The strip lemma: a step and a run to a terminal state close modulo `E`. -/
theorem strip_of_diamond (hE : StepEquiv S E) (hH : Preserved S H)
    (hd : ∀ {c c₁ c₂}, H c → S c c₁ → S c c₂ → DiamondMod S E c₁ c₂) :
    ∀ {c n}, Star S c n → Terminal S n → ∀ {c₁}, H c → S c c₁ → ∃ n', Star S c₁ n' ∧ E n n' := by
  intro c n h ht
  induction h with
  | refl => intro c₁ _ hs; exact absurd hs (ht _)
  | @step c c₂ n hs₂ rest ih =>
    intro c₁ hc hs₁
    obtain ⟨d₁, d₂, o₁, o₂, he⟩ := hd hc hs₁ hs₂
    rcases o₂ with rfl | hs₂'
    · -- `c₂` itself is related to `d₁`: carry the rest of the run over `E`
      obtain ⟨n', hn', he'⟩ := hE.star (hE.symm he) rest
      exact ⟨n', o₁.star.trans hn', he'⟩
    · obtain ⟨n'', hn'', he''⟩ := ih ht (hH _ _ hc hs₂) hs₂'
      obtain ⟨n', hn', he'⟩ := hE.star (hE.symm he) hn''
      exact ⟨n', o₁.star.trans hn', hE.trans he'' he'⟩

/-- Confluence from the diamond property modulo `E`, with no termination hypothesis: the
terminal states reachable from a state satisfying `H` are related by `E`. -/
theorem terminal_unique_of_diamond (hE : StepEquiv S E) (hH : Preserved S H)
    (hd : ∀ {c c₁ c₂}, H c → S c c₁ → S c c₂ → DiamondMod S E c₁ c₂) :
    ∀ {c n₁ n₂}, H c → Star S c n₁ → Terminal S n₁ → Star S c n₂ → Terminal S n₂ → E n₁ n₂ := by
  intro c n₁ n₂ hc h₁
  induction h₁ generalizing n₂ with
  | refl => intro ht₁ h₂ _; rw [Star.eq_of_terminal ht₁ h₂]; exact hE.refl _
  | @step c c₁ n₁ hs₁ rest ih =>
    intro ht₁ h₂ ht₂
    obtain ⟨n₂', hn₂', he⟩ := strip_of_diamond hE hH hd h₂ ht₂ hc hs₁
    exact hE.trans (ih (hH _ _ hc hs₁) ht₁ hn₂' (hE.terminal he ht₂)) (hE.symm he)

/-- Newman's lemma modulo `E`: from local confluence modulo `E` and a measure that every step
from `H` decreases, the terminal states reachable from a state satisfying `H` are related by
`E`. -/
theorem terminal_unique_of_local (hE : StepEquiv S E) (hH : Preserved S H) (μ : α → Nat)
    (hμ : ∀ {c c'}, H c → S c c' → μ c' < μ c)
    (hl : ∀ {c c₁ c₂}, H c → S c c₁ → S c c₂ → JoinMod S E c₁ c₂) :
    ∀ {c n₁ n₂}, H c → Star S c n₁ → Terminal S n₁ → Star S c n₂ → Terminal S n₂ → E n₁ n₂ := by
  intro c
  induction c using measure_ind μ with
  | h c ih =>
    intro n₁ n₂ hc h₁ ht₁ h₂ ht₂
    cases h₁ with
    | refl => rw [Star.eq_of_terminal ht₁ h₂]; exact hE.refl _
    | @step _ a _ hsa resta =>
      cases h₂ with
      | refl => exact absurd hsa (ht₂ _)
      | @step _ b _ hsb restb =>
        obtain ⟨a', b', ha', hb', he⟩ := hl hc hsa hsb
        have Ha := hH _ _ hc hsa
        have Hb := hH _ _ hc hsb
        obtain ⟨na, hna, htna⟩ := exists_terminal hH μ hμ a' (hH.star ha' Ha)
        have e₁ := ih a (hμ hc hsa) Ha resta ht₁ (ha'.trans hna) htna
        obtain ⟨nb, hnb, he'⟩ := hE.star he hna
        have e₂ := ih b (hμ hc hsb) Hb (hb'.trans hnb) (hE.terminal he' htna) restb ht₂
        exact hE.trans e₁ (hE.trans he' e₂)

end Confluence

/-! ## Stuttering simulation -/

section Refine

variable {α β : Type u} {SA : α → α → Prop} {SB : β → β → Prop} {R : α → β → Prop}
  {μ : α → Nat} {ν : β → Nat}

/-- `SB` simulates `SA` up to stuttering through `R`: a step of `SA` from a related state is
matched by one or more steps of `SB`, or by none, and then the measure `μ` decreases (so `SA`
cannot stutter forever against one state of `SB`). -/
def StutterSim (SA : α → α → Prop) (SB : β → β → Prop) (R : α → β → Prop) (μ : α → Nat) :
    Prop :=
  ∀ c c' d, SA c c' → R c d → (∃ d', Relation.TransGen SB d d' ∧ R c' d') ∨ (R c' d ∧ μ c' < μ c)

/-- A stuttering bisimulation: `R` is a stuttering simulation in both directions. -/
structure StutterBisim (SA : α → α → Prop) (SB : β → β → Prop) (R : α → β → Prop) (μ : α → Nat)
    (ν : β → Nat) : Prop where
  fwd : StutterSim SA SB R μ
  bwd : StutterSim SB SA (fun d c => R c d) ν

theorem StutterBisim.symm (h : StutterBisim SA SB R μ ν) :
    StutterBisim SB SA (fun d c => R c d) ν μ :=
  ⟨h.bwd, h.fwd⟩

/-- Runs of `SA` are matched by runs of `SB`. -/
theorem StutterSim.star (h : StutterSim SA SB R μ) :
    ∀ {c c' d}, Star SA c c' → R c d → ∃ d', Star SB d d' ∧ R c' d'
  | _, _, d, .refl _, hr => ⟨d, .refl _, hr⟩
  | _, _, _, .step hs rest, hr => by
    rcases h _ _ _ hs hr with ⟨d₁, ht, hr₁⟩ | ⟨hr₁, _⟩
    · obtain ⟨d', hd', hr'⟩ := h.star rest hr₁
      exact ⟨d', (Star.of_transGen ht).trans hd', hr'⟩
    · exact h.star rest hr₁

/-- A state related to a terminal state of `SA` reaches a terminal state of `SB` that is still
related to it: `SB` can only stutter there, and its measure bounds the stuttering. -/
theorem StutterBisim.terminal (h : StutterBisim SA SB R μ ν) {c : α} (hc : Terminal SA c) :
    ∀ d, R c d → ∃ d', Star SB d d' ∧ Terminal SB d' ∧ R c d' := by
  intro d
  induction d using measure_ind ν with
  | h d ih =>
    intro hr
    by_cases ht : Terminal SB d
    · exact ⟨d, .refl _, ht, hr⟩
    · simp only [Terminal, Classical.not_forall, Classical.not_not] at ht
      obtain ⟨d₁, hs⟩ := ht
      rcases h.bwd _ _ _ hs hr with ⟨c', hc', _⟩ | ⟨hr₁, hlt⟩
      · obtain ⟨c₁, hc₁⟩ := TransGen.head_step hc'
        exact absurd hc₁ (hc _)
      · obtain ⟨d', hd', ht', hr'⟩ := ih d₁ hlt hr₁
        exact ⟨d', .step hs hd', ht', hr'⟩

/-- A run of `SA` to a terminal state is matched by a run of `SB` to a terminal state related
to it. -/
theorem StutterBisim.terminal_run (h : StutterBisim SA SB R μ ν) {c c' : α} {d : β}
    (hr : R c d) (hrun : Star SA c c') (ht : Terminal SA c') :
    ∃ d', Star SB d d' ∧ Terminal SB d' ∧ R c' d' := by
  obtain ⟨d₁, hd₁, hr₁⟩ := h.fwd.star hrun hr
  obtain ⟨d', hd', ht', hr'⟩ := h.terminal ht d₁ hr₁
  exact ⟨d', hd₁.trans hd', ht', hr'⟩

namespace Stutter

variable (tr : α → β) (SA : α → α → Prop) (SB : β → β → Prop) (X : α → β → Prop)

/-- The relation of a refinement whose local part is a translation `tr`: `d` is the translation
of `c`, or the non-local part `X` (supplied) relates them. -/
def Rel (c : α) (d : β) : Prop := d = tr c ∨ X c d

/-- What a step `c → c'` of `SA` owes forward. -/
def FwdQ (μ : α → Nat) (c c' : α) : Prop :=
  ∀ d, Rel tr X c d → (∃ d', Relation.TransGen SB d d' ∧ Rel tr X c' d') ∨ (Rel tr X c' d ∧ μ c' < μ c)

/-- The part of `FwdQ` at the translation of `c`. -/
def FwdTr (μ : α → Nat) (c c' : α) : Prop :=
  (∃ d', Relation.TransGen SB (tr c) d' ∧ Rel tr X c' d') ∨ (Rel tr X c' (tr c) ∧ μ c' < μ c)

/-- The part of `FwdQ` at the states `X` relates to `c`. -/
def FwdX (μ : α → Nat) (c c' : α) : Prop :=
  ∀ d, X c d → (∃ d', Relation.TransGen SB d d' ∧ Rel tr X c' d') ∨ (Rel tr X c' d ∧ μ c' < μ c)

/-- What a step `d → d'` of `SB` owes backward. -/
def BwdQ (ν : β → Nat) (d d' : β) : Prop :=
  ∀ c, Rel tr X c d → (∃ c', Relation.TransGen SA c c' ∧ Rel tr X c' d') ∨ (Rel tr X c d' ∧ ν d' < ν d)

/-- The part of `BwdQ` where `d` is a translation. -/
def BwdTr (ν : β → Nat) (d d' : β) : Prop :=
  ∀ c, d = tr c → (∃ c', Relation.TransGen SA c c' ∧ Rel tr X c' d') ∨ (Rel tr X c d' ∧ ν d' < ν d)

/-- The part of `BwdQ` at the states `X` relates to `d`. -/
def BwdX (ν : β → Nat) (d d' : β) : Prop :=
  ∀ c, X c d → (∃ c', Relation.TransGen SA c c' ∧ Rel tr X c' d') ∨ (Rel tr X c d' ∧ ν d' < ν d)

variable {tr SA SB X}

theorem fwdQ_of {μ : α → Nat} {c c' : α} (ht : FwdTr tr SB X μ c c') (hx : FwdX tr SB X μ c c') :
    FwdQ tr SB X μ c c' := by
  rintro d (rfl | h)
  · exact ht
  · exact hx d h

theorem bwdQ_of {ν : β → Nat} {d d' : β} (ht : BwdTr tr SA X ν d d') (hx : BwdX tr SA X ν d d') :
    BwdQ tr SA X ν d d' := by
  rintro c (h | h)
  · exact ht c h
  · exact hx c h

/-- The stuttering bisimulation from what every step owes. -/
theorem bisim_of {μ : α → Nat} {ν : β → Nat}
    (hf : ∀ {c c'}, SA c c' → FwdQ tr SB X μ c c') (hb : ∀ {d d'}, SB d d' → BwdQ tr SA X ν d d') :
    StutterBisim SA SB (Rel tr X) μ ν :=
  ⟨fun _ _ d h hr => hf h d hr, fun _ _ c h hr => hb h c hr⟩

end Stutter

end Refine

/-! ## Two runs -/

section NonInterference

variable {α : Type u} {S : α → α → Prop} {Final : α → Prop} {Rel : α → α → Prop}

/-- `Rel` relates pairs of states of two runs of `S` such that, unless both are final, one side
that is not final can be advanced by any of its steps without leaving `Rel` (a stuck side has no
step, so it is advanced vacuously: it never reaches a final state). -/
structure ProductInv (S : α → α → Prop) (Final : α → Prop) (Rel : α → α → Prop) : Prop where
  move : ∀ {c₁ c₂}, Rel c₁ c₂ → ¬ (Final c₁ ∧ Final c₂) →
    (¬ Final c₁ ∧ ∀ c₁', S c₁ c₁' → Rel c₁' c₂) ∨ (¬ Final c₂ ∧ ∀ c₂', S c₂ c₂' → Rel c₁ c₂')

/-- Two runs from related states that both end in final states end in related states. -/
theorem ProductInv.final (h : ProductInv S Final Rel) (hfin : ∀ {c c'}, Final c → ¬ S c c') :
    ∀ {c₁ f₁}, Star S c₁ f₁ → Final f₁ →
      ∀ {c₂ f₂}, Star S c₂ f₂ → Final f₂ → Rel c₁ c₂ → Rel f₁ f₂ := by
  intro c₁ f₁ h₁ hf₁
  induction h₁ with
  | refl c =>
    intro c₂ f₂ h₂ hf₂ hr
    induction h₂ with
    | refl => exact hr
    | step hs _ ih =>
      rcases h.move hr (fun ⟨_, f⟩ => hfin f hs) with ⟨n₁, _⟩ | ⟨_, hm⟩
      · exact absurd hf₁ n₁
      · exact ih hf₂ (hm _ hs)
  | step hs₁ rest₁ ih₁ =>
    intro c₂ f₂ h₂ hf₂ hr
    induction h₂ with
    | refl =>
      rcases h.move hr (fun ⟨f, _⟩ => hfin f hs₁) with ⟨_, hm⟩ | ⟨n₂, _⟩
      · exact ih₁ hf₁ (.refl _) hf₂ (hm _ hs₁)
      · exact absurd hf₂ n₂
    | step hs₂ rest₂ ih₂ =>
      rcases h.move hr (fun ⟨f, _⟩ => hfin f hs₁) with ⟨_, hm⟩ | ⟨_, hm⟩
      · exact ih₁ hf₁ (.step hs₂ rest₂) hf₂ (hm _ hs₁)
      · exact ih₂ hf₂ (hm _ hs₂)

end NonInterference

end KPrelude
