import KPrelude.Invariant
import KPrelude.Coll
import KPrelude.Hooks

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
- **Two bindings of a map** (the confluence of rules that match a cell map at a free key, such
  as threads): steps at two different bindings commute (`MapHook.concat_element_comm`), by the
  extensionality of canonical maps (`SAL.ext`); so do two steps that replace parts of a map with
  no key in common, one of them inserting no key (`MapHook.concat_frame`: a thread's step, its
  end, a spawn, two threads meeting).
- **Two runs** (`k2lean noninterference`): a relation on pairs of states from which, unless both
  are final, one side can be advanced by any of its steps without leaving the relation
  (`ProductInv`) relates the final states of any two runs from related states.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace KPrelude

universe u

section Basic

variable {α : Type u} {S : α → α → Prop}

/-- `c` has no successor. -/
def Terminal (S : α → α → Prop) (c : α) : Prop := ∀ c', ¬ S c c'

/-- At most one step: `a' = a` or `S a a'`. -/
abbrev Opt (S : α → α → Prop) (a a' : α) : Prop := a' = a ∨ S a a'

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
abbrev DiamondMod (S : α → α → Prop) (E : α → α → Prop) (a b : α) : Prop :=
  ∃ a' b', Opt S a a' ∧ Opt S b b' ∧ E a' b'

/-- `a` and `b` join modulo `E`. -/
abbrev JoinMod (S : α → α → Prop) (E : α → α → Prop) (a b : α) : Prop :=
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

/-- Close the equation of the two states a diamond joins in: equal, or equal once the integer
hooks are unfolded, up to the commutativity and associativity of addition (two updates of a
shared counter in either order). -/
macro "k2l_join_eq" : tactic => `(tactic| first
  | rfl
  | (simp only [KPrelude.IntHook.add, KPrelude.IntHook.sub, Int.add_right_comm, Int.add_assoc,
      Int.add_comm, Int.add_left_comm]; done))

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
that is not final, or both, can be advanced by any of their steps without leaving `Rel` (a stuck
side has no step, so it is advanced vacuously: it never reaches a final state). -/
structure ProductInv (S : α → α → Prop) (Final : α → Prop) (Rel : α → α → Prop) : Prop where
  move : ∀ {c₁ c₂}, Rel c₁ c₂ → ¬ (Final c₁ ∧ Final c₂) →
    (¬ Final c₁ ∧ ∀ c₁', S c₁ c₁' → Rel c₁' c₂) ∨ (¬ Final c₂ ∧ ∀ c₂', S c₂ c₂' → Rel c₁ c₂') ∨
    (¬ Final c₁ ∧ ¬ Final c₂ ∧ ∀ c₁' c₂', S c₁ c₁' → S c₂ c₂' → Rel c₁' c₂')

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
      rcases h.move hr (fun ⟨_, f⟩ => hfin f hs) with ⟨n₁, _⟩ | ⟨_, hm⟩ | ⟨n₁, _⟩
      · exact absurd hf₁ n₁
      · exact ih hf₂ (hm _ hs)
      · exact absurd hf₁ n₁
  | step hs₁ rest₁ ih₁ =>
    intro c₂ f₂ h₂ hf₂ hr
    induction h₂ with
    | refl =>
      rcases h.move hr (fun ⟨f, _⟩ => hfin f hs₁) with ⟨_, hm⟩ | ⟨n₂, _⟩ | ⟨_, n₂, _⟩
      · exact ih₁ hf₁ (.refl _) hf₂ (hm _ hs₁)
      · exact absurd hf₂ n₂
      · exact absurd hf₂ n₂
    | step hs₂ rest₂ ih₂ =>
      rcases h.move hr (fun ⟨f, _⟩ => hfin f hs₁) with ⟨_, hm⟩ | ⟨_, hm⟩ | ⟨_, _, hm⟩
      · exact ih₁ hf₁ (.step hs₂ rest₂) hf₂ (hm _ hs₁)
      · exact ih₂ hf₂ (hm _ hs₂)
      · exact ih₁ hf₁ rest₂ hf₂ (hm _ _ hs₁ hs₂)

/-- A product invariant from three modes of `Rel`: in `Sync` both sides step together, in `Left`
the left side steps alone, in `Right` the right side; `cover` says which mode a related pair is
in when not both are final. Each mode's obligation is one statement per rule of the stepping
side (`k2lean noninterference`). -/
theorem ProductInv.of_modes {Sync Left Right : α → α → Prop}
    (sync : ∀ {c₁ c₂ c₁' c₂'}, Sync c₁ c₂ → S c₁ c₁' → S c₂ c₂' → Rel c₁' c₂')
    (left : ∀ {c₁ c₂ c₁'}, Left c₁ c₂ → S c₁ c₁' → Rel c₁' c₂)
    (right : ∀ {c₁ c₂ c₂'}, Right c₁ c₂ → S c₂ c₂' → Rel c₁ c₂')
    (cover : ∀ {c₁ c₂}, Rel c₁ c₂ → ¬ (Final c₁ ∧ Final c₂) →
      (Left c₁ c₂ ∧ ¬ Final c₁) ∨ (Right c₁ c₂ ∧ ¬ Final c₂) ∨
      (Sync c₁ c₂ ∧ ¬ Final c₁ ∧ ¬ Final c₂)) :
    ProductInv S Final Rel where
  move hr hn := by
    rcases cover hr hn with ⟨hl, n⟩ | ⟨hr', n⟩ | ⟨hs, n₁, n₂⟩
    · exact Or.inl ⟨n, fun _ h => left hl h⟩
    · exact Or.inr (Or.inl ⟨n, fun _ h => right hr' h⟩)
    · exact Or.inr (Or.inr ⟨n₁, n₂, fun _ _ h₁ h₂ => sync hs h₁ h₂⟩)

end NonInterference

/-! ## Two bindings of a canonical map -/

namespace SAL

variable {α β : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]

/-- Two sorted lists with the same lookups are equal: the canonical representation is
extensional. -/
theorem ext : ∀ {a b : List (α × β)}, Sorted a → Sorted b → (∀ k, lookup k a = lookup k b) → a = b
  | [], [], _, _, _ => rfl
  | [], (k, v) :: t, _, _, h => by have := h k; simp [lookup, cmp_self] at this
  | (k, v) :: t, [], _, _, h => by have := h k; simp [lookup, cmp_self] at this
  | (k, v) :: t, (k', v') :: t', ha, hb, h => by
    cases ha with
    | cons hlt ht =>
    cases hb with
    | cons hlt' ht' =>
    cases hc : compare k k' with
    | lt => have := h k; simp [lookup, cmp_self, hc] at this
    | gt => have := h k'; simp [lookup, cmp_self, lt_of_gt hc] at this
    | eq =>
      cases eq_of_cmp hc
      have hv := h k
      simp only [lookup, cmp_self, Option.some.injEq] at hv
      subst hv
      congr 1
      refine ext ht ht' (fun j => ?_)
      have hj := h j
      cases hjk : compare j k with
      | lt =>
        rw [lookup_of_lt (fun p hp => lt_trans hjk (hlt p hp)),
          lookup_of_lt (fun p hp => lt_trans hjk (hlt' p hp))]
      | eq => cases eq_of_cmp hjk; rw [lookup_of_lt hlt, lookup_of_lt hlt']
      | gt => simpa only [lookup, hjk] using hj

theorem lookup_erase_ne {k k' : α} (hne : k' ≠ k) :
    ∀ {m : List (α × β)}, Sorted m → lookup k' (erase k m) = lookup k' m
  | [], _ => rfl
  | (k₀, v₀) :: t, hs => by
    cases hs with
    | cons hlt ht =>
      unfold erase
      split
      · rfl
      · next h =>
        cases eq_of_cmp h
        cases hc : compare k' k with
        | lt => rw [lookup_of_lt (fun p hp => lt_trans hc (hlt p hp))]; simp [lookup, hc]
        | eq => exact absurd (eq_of_cmp hc) hne
        | gt => simp [lookup, hc]
      · next h =>
        simp only [lookup]
        split
        · rfl
        · rfl
        · exact lookup_erase_ne hne ht

/-- `x` is a key of `a`. -/
abbrev HasKey (a : List (α × β)) (x : α) : Prop := ∃ q ∈ a, q.1 = x

theorem concat_disj {a b m : List (α × β)} (h : concat a b = some m) {p q : α × β}
    (hp : p ∈ a) (hq : q ∈ b) : p.1 ≠ q.1 := by
  obtain ⟨-, sb, d, -⟩ := concat_eq_some_iff.1 h
  exact fun e => (lookup_eq_none_iff sb).1 (d p hp) q hq e.symm

theorem sorted_of_concat_left {a b m : List (α × β)} (h : concat a b = some m) : Sorted a :=
  (concat_eq_some_iff.1 h).1

/-- Two members of a sorted list with one key are one member. -/
theorem eq_of_mem_key {m : List (α × β)} (hs : Sorted m) {p q : α × β} (hp : p ∈ m) (hq : q ∈ m)
    (e : p.1 = q.1) : p = q := by
  obtain ⟨k, v⟩ := p
  obtain ⟨k', v'⟩ := q
  cases e
  have h1 := lookup_of_mem hs hp
  rw [lookup_of_mem hs hq] at h1
  cases h1; rfl

/-- The part of `m₁` away from the keys of `a` matches `a` back in: `m₁ = a (m₁ ∖ a)` when every
member of `a` is one of `m₁`. -/
theorem concat_filter {a m : List (α × β)} (sa : Sorted a) (sm : Sorted m) (sub : ∀ p ∈ a, p ∈ m) :
    concat a (m.filter fun p => (lookup p.1 a).isNone) = some m := by
  have sf := sorted_filter (fun p => (lookup p.1 a).isNone) sm
  have d : ∀ p ∈ a, lookup p.1 (m.filter fun p => (lookup p.1 a).isNone) = none := by
    intro p hp
    refine (lookup_eq_none_iff sf).2 fun q hq e => ?_
    have := (List.mem_filter.1 hq).2
    rw [Option.isNone_iff_eq_none, lookup_eq_none_iff sa] at this
    exact this p hp e.symm
  have hc := concat_eq_some_iff.2 ⟨sa, sf, d, rfl⟩
  rw [hc]
  congr 1
  refine eq_of_mem_iff (sorted_of_concat hc) sm fun p => ?_
  rw [mem_concat hc, List.mem_filter]
  constructor
  · rintro (hp | ⟨hp, -⟩)
    · exact sub p hp
    · exact hp
  · intro hp
    by_cases hk : lookup p.1 a = none
    · exact Or.inr ⟨hp, by simp [hk]⟩
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hk
      have hq := lookup_mem hv
      exact Or.inl (eq_of_mem_key sm hp (sub _ hq) rfl ▸ hq)

/-- Two steps of a map at disjoint parts commute: one turns `m = a₁ R₁` into `m₁ = b₁ R₁`, the
other `m = a₂ R₂` into `m₂ = b₂ R₂`. When `a₁` and `a₂` share no key and one of `b₁`, `b₂` has no
key outside its `a` (inserts no binding), each still matches after the other, at a rest, and both
orders give one map. -/
theorem concat_frame {a₁ b₁ R₁ a₂ b₂ R₂ m m₁ m₂ : List (α × β)}
    (h₁ : concat a₁ R₁ = some m) (r₁ : concat b₁ R₁ = some m₁)
    (h₂ : concat a₂ R₂ = some m) (r₂ : concat b₂ R₂ = some m₂)
    (dA : ∀ p ∈ a₁, ∀ q ∈ a₂, p.1 ≠ q.1)
    (dB : (∀ p ∈ b₁, HasKey a₁ p.1) ∨ (∀ p ∈ b₂, HasKey a₂ p.1)) :
    ∃ R₁₂ R₂₁ m', concat a₂ R₁₂ = some m₁ ∧ concat b₂ R₁₂ = some m' ∧
      concat a₁ R₂₁ = some m₂ ∧ concat b₁ R₂₁ = some m' := by
  have sa₁ := sorted_of_concat_left h₁
  have sa₂ := sorted_of_concat_left h₂
  have sb₁ := sorted_of_concat_left r₁
  have sb₂ := sorted_of_concat_left r₂
  have sm := sorted_of_concat h₁
  have sm₁ := sorted_of_concat r₁
  have sm₂ := sorted_of_concat r₂
  have sR₁ := (concat_eq_some_iff.1 h₁).2.1
  have sR₂ := (concat_eq_some_iff.1 h₂).2.1
  -- a member of `m` is in `R₁` exactly when its key is not one of `a₁`
  have inR₁ : ∀ p ∈ m, ¬ HasKey a₁ p.1 → p ∈ R₁ := fun p hp hk =>
    ((mem_concat h₁).1 hp).resolve_left fun ha => hk ⟨p, ha, rfl⟩
  have inR₂ : ∀ p ∈ m, ¬ HasKey a₂ p.1 → p ∈ R₂ := fun p hp hk =>
    ((mem_concat h₂).1 hp).resolve_left fun ha => hk ⟨p, ha, rfl⟩
  have nR₁ : ∀ p ∈ R₁, ¬ HasKey a₁ p.1 := fun p hp ⟨q, hq, e⟩ => concat_disj h₁ hq hp e
  have nR₂ : ∀ p ∈ R₂, ¬ HasKey a₂ p.1 := fun p hp ⟨q, hq, e⟩ => concat_disj h₂ hq hp e
  -- `a₂` is in `R₁`, `a₁` in `R₂`
  have a₂R₁ : ∀ p ∈ a₂, p ∈ R₁ := fun p hp =>
    inR₁ p ((mem_concat h₂).2 (Or.inl hp)) fun ⟨q, hq, e⟩ => dA q hq p hp e
  have a₁R₂ : ∀ p ∈ a₁, p ∈ R₂ := fun p hp =>
    inR₂ p ((mem_concat h₁).2 (Or.inl hp)) fun ⟨q, hq, e⟩ => dA p hp q hq e.symm
  -- no key of `b₁` is one of `a₂`, none of `b₂` one of `a₁`
  have b₁a₂ : ∀ p ∈ b₁, ¬ HasKey a₂ p.1 := fun p hp ⟨q, hq, e⟩ =>
    concat_disj r₁ hp (a₂R₁ q hq) e.symm
  have b₂a₁ : ∀ p ∈ b₂, ¬ HasKey a₁ p.1 := fun p hp ⟨q, hq, e⟩ =>
    concat_disj r₂ hp (a₁R₂ q hq) e.symm
  -- `b₁` and `b₂` share no key
  have dB' : ∀ p ∈ b₁, ∀ q ∈ b₂, p.1 ≠ q.1 := by
    intro p hp q hq e
    rcases dB with d | d
    · obtain ⟨x, hx, ex⟩ := d p hp
      exact concat_disj r₂ hq (a₁R₂ x hx) (e.symm.trans ex.symm)
    · obtain ⟨x, hx, ex⟩ := d q hq
      exact b₁a₂ p hp ⟨x, hx, ex.trans e.symm⟩
  -- the rests
  have sub₂ : ∀ p ∈ a₂, p ∈ m₁ := fun p hp => (mem_concat r₁).2 (Or.inr (a₂R₁ p hp))
  have sub₁ : ∀ p ∈ a₁, p ∈ m₂ := fun p hp => (mem_concat r₂).2 (Or.inr (a₁R₂ p hp))
  have c₁₂ := concat_filter sa₂ sm₁ sub₂
  have c₂₁ := concat_filter sa₁ sm₂ sub₁
  generalize hF₁ : m₁.filter (fun p => (lookup p.1 a₂).isNone) = F₁ at c₁₂
  generalize hF₂ : m₂.filter (fun p => (lookup p.1 a₁).isNone) = F₂ at c₂₁
  have memF₁ : ∀ p, p ∈ F₁ ↔ p ∈ m₁ ∧ ¬ HasKey a₂ p.1 := fun p => by
    rw [← hF₁, List.mem_filter, Option.isNone_iff_eq_none, lookup_eq_none_iff sa₂]
    exact and_congr_right fun _ => ⟨fun h ⟨q, hq, e⟩ => h q hq e, fun h q hq e => h ⟨q, hq, e⟩⟩
  have memF₂ : ∀ p, p ∈ F₂ ↔ p ∈ m₂ ∧ ¬ HasKey a₁ p.1 := fun p => by
    rw [← hF₂, List.mem_filter, Option.isNone_iff_eq_none, lookup_eq_none_iff sa₁]
    exact and_congr_right fun _ => ⟨fun h ⟨q, hq, e⟩ => h q hq e, fun h q hq e => h ⟨q, hq, e⟩⟩
  have sF₁ : Sorted F₁ := (concat_eq_some_iff.1 c₁₂).2.1
  have sF₂ : Sorted F₂ := (concat_eq_some_iff.1 c₂₁).2.1
  -- `b₂ F₁` and `b₁ F₂` are defined
  have d₂ : ∀ p ∈ b₂, lookup p.1 F₁ = none := by
    intro p hp
    refine (lookup_eq_none_iff sF₁).2 fun q hq e => ?_
    obtain ⟨hq, hk⟩ := (memF₁ q).1 hq
    rcases (mem_concat r₁).1 hq with hq | hq
    · exact dB' q hq p hp e
    · exact concat_disj r₂ hp (inR₂ q ((mem_concat h₁).2 (Or.inr hq)) hk) e.symm
  have d₁ : ∀ p ∈ b₁, lookup p.1 F₂ = none := by
    intro p hp
    refine (lookup_eq_none_iff sF₂).2 fun q hq e => ?_
    obtain ⟨hq, hk⟩ := (memF₂ q).1 hq
    rcases (mem_concat r₂).1 hq with hq | hq
    · exact dB' p hp q hq e.symm
    · exact concat_disj r₁ hp (inR₁ q ((mem_concat h₂).2 (Or.inr hq)) hk) e.symm
  have e₂ := concat_eq_some_iff.2 ⟨sb₂, sF₁, d₂, rfl⟩
  have e₁ := concat_eq_some_iff.2 ⟨sb₁, sF₂, d₁, rfl⟩
  refine ⟨F₁, F₂, _, c₁₂, e₂, c₂₁, ?_⟩
  rw [e₁]
  congr 1
  -- both are `b₁`, `b₂` and the members of `m` at neither `a₁` nor `a₂`
  refine eq_of_mem_iff (sorted_of_concat e₁) (sorted_of_concat e₂) fun p => ?_
  rw [mem_concat e₁, mem_concat e₂, memF₁, memF₂, mem_concat r₁, mem_concat r₂]
  constructor
  · rintro (hp | ⟨hp | hp, hk⟩)
    · exact Or.inr ⟨Or.inl hp, b₁a₂ p hp⟩
    · exact Or.inl hp
    · have hm := (mem_concat h₂).2 (Or.inr hp)
      exact Or.inr ⟨Or.inr (inR₁ p hm hk), nR₂ p hp⟩
  · rintro (hp | ⟨hp | hp, hk⟩)
    · exact Or.inr ⟨Or.inl hp, b₂a₁ p hp⟩
    · exact Or.inl hp
    · have hm := (mem_concat h₁).2 (Or.inr hp)
      exact Or.inr ⟨Or.inr (inR₂ p hm hk), nR₁ p hp⟩

/-- `_Map_` is associative where defined: `(a b) c` defined gives `a (b c)`, the same map. -/
theorem concat_assoc_right {a b c ab m : List (α × β)} (h₁ : concat a b = some ab)
    (h₂ : concat ab c = some m) : ∃ bc, concat b c = some bc ∧ concat a bc = some m := by
  obtain ⟨sa, sb, dab, -⟩ := concat_eq_some_iff.1 h₁
  obtain ⟨sab, sc, dabc, -⟩ := concat_eq_some_iff.1 h₂
  have dbc : ∀ p ∈ b, lookup p.1 c = none := fun p hp => dabc p ((mem_concat h₁).2 (Or.inr hp))
  have hbc := concat_eq_some_iff.2 ⟨sb, sc, dbc, rfl⟩
  refine ⟨_, hbc, ?_⟩
  have da : ∀ p ∈ a, lookup p.1 (b.foldr (fun q acc => insert q.1 q.2 acc) c) = none := by
    intro p hp
    refine (lookup_eq_none_iff (sorted_of_concat hbc)).2 fun q hq e => ?_
    rcases (mem_concat hbc).1 hq with hq | hq
    · exact (lookup_eq_none_iff sb).1 (dab p hp) q hq e
    · exact (lookup_eq_none_iff sc).1 (dabc p ((mem_concat h₁).2 (Or.inl hp))) q hq e
  have hm := concat_eq_some_iff.2 ⟨sa, sorted_of_concat hbc, da, rfl⟩
  rw [hm]
  congr 1
  refine eq_of_mem_iff (sorted_of_concat hm) (sorted_of_concat h₂) fun p => ?_
  rw [mem_concat hm, mem_concat hbc, mem_concat h₂, mem_concat h₁, or_assoc]

end SAL

namespace MapHook

open ListIso

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V] [Std.TransOrd K]
  [Std.LawfulEqOrd K]

theorem ext {a b : M} (ha : WF a) (hb : WF b) (h : ∀ k, lookup a k = lookup b k) : a = b := by
  have e : toList a = toList b := SAL.ext ha hb (fun k => by rw [← lookup_def, ← lookup_def, h])
  rw [← ofList_toList a, e, ofList_toList]

theorem lookup_remove_self {m : M} (k : K) (hw : WF m) : lookup (remove m k) k = none := by
  rw [lookup_def, remove_def, toList_ofList]; exact SAL.lookup_erase_self k hw

theorem lookup_remove_ne {m : M} {k k' : K} (hne : k' ≠ k) (hw : WF m) :
    lookup (remove m k) k' = lookup m k' := by
  rw [lookup_def, remove_def, toList_ofList, SAL.lookup_erase_ne hne hw, lookup_def]

/-- Steps at two different bindings of a map commute. A step at `k₁` turns `m = (k₁ ↦ v₁) R₁`
into `m₁ = (k₁ ↦ w₁) R₁`, one at `k₂ ≠ k₁` turns `m = (k₂ ↦ v₂) R₂` into `m₂ = (k₂ ↦ w₂) R₂`:
the second still matches `m₁` (at a rest `R₁₂`), the first still matches `m₂` (at `R₂₁`), and
both orders give one map `m'`. -/
theorem concat_element_comm {k₁ k₂ : K} {v₁ v₂ w₁ w₂ : V} {R₁ R₂ m m₁ m₂ : M}
    (h₁ : concat (element k₁ v₁) R₁ = some m) (h₂ : concat (element k₂ v₂) R₂ = some m)
    (r₁ : concat (element k₁ w₁) R₁ = some m₁) (r₂ : concat (element k₂ w₂) R₂ = some m₂)
    (hne : k₁ ≠ k₂) :
    ∃ R₁₂ R₂₁ m', concat (element k₂ v₂) R₁₂ = some m₁ ∧ concat (element k₂ w₂) R₁₂ = some m' ∧
      concat (element k₁ v₁) R₂₁ = some m₂ ∧ concat (element k₁ w₁) R₂₁ = some m' := by
  obtain ⟨wR₁, n₁, rfl⟩ := concat_element_iff.1 h₁
  obtain ⟨wR₂, n₂, e⟩ := concat_element_iff.1 h₂
  obtain ⟨-, -, rfl⟩ := concat_element_iff.1 r₁
  obtain ⟨-, -, rfl⟩ := concat_element_iff.1 r₂
  have hne' : k₂ ≠ k₁ := fun h => hne h.symm
  have w₁' : WF (update R₁ k₁ w₁) := wf_update wR₁
  have w₂' : WF (update R₂ k₂ w₂) := wf_update wR₂
  -- the other binding is unchanged by each step
  have l₂ : lookup (update R₁ k₁ w₁) k₂ = some v₂ := by
    rw [lookup_update_ne _ _ hne', ← lookup_update_ne R₁ v₁ hne', e, lookup_update_self]
  have l₁ : lookup (update R₂ k₂ w₂) k₁ = some v₁ := by
    rw [lookup_update_ne _ _ hne, ← lookup_update_ne R₂ v₂ hne, ← e, lookup_update_self]
  refine ⟨remove (update R₁ k₁ w₁) k₂, remove (update R₂ k₂ w₂) k₁,
    update (remove (update R₁ k₁ w₁) k₂) k₂ w₂, concat_element_remove w₁' l₂,
    concat_element_iff.2 ⟨wf_remove w₁', lookup_remove_self k₂ w₁', rfl⟩,
    concat_element_remove w₂' l₁,
    concat_element_iff.2 ⟨wf_remove w₂', lookup_remove_self k₁ w₂', ?_⟩⟩
  -- one map whichever step comes first
  refine ext (wf_update (wf_remove w₁')) (wf_update (wf_remove w₂')) (fun j => ?_)
  by_cases j₂ : j = k₂
  · subst j₂
    rw [lookup_update_self, lookup_update_ne _ _ hne', lookup_remove_ne hne' w₂', lookup_update_self]
  by_cases j₁ : j = k₁
  · subst j₁
    rw [lookup_update_ne _ _ hne, lookup_remove_ne hne w₁', lookup_update_self, lookup_update_self]
  rw [lookup_update_ne _ _ j₂, lookup_remove_ne j₂ w₁', lookup_update_ne _ _ j₁,
    lookup_update_ne _ _ j₁, lookup_remove_ne j₁ w₂', lookup_update_ne _ _ j₂,
    ← lookup_update_ne R₁ v₁ j₁, ← lookup_update_ne R₂ v₂ j₂, e]

/-- Two matches of `K |-> V REST` in one map are one binding, or they commute
(`concat_element_comm`). -/
theorem concat_element_same_or_comm {k₁ k₂ : K} {v₁ v₂ w₁ w₂ : V} {R₁ R₂ m m₁ m₂ : M}
    (h₁ : concat (element k₁ v₁) R₁ = some m) (h₂ : concat (element k₂ v₂) R₂ = some m)
    (r₁ : concat (element k₁ w₁) R₁ = some m₁) (r₂ : concat (element k₂ w₂) R₂ = some m₂) :
    (k₁ = k₂ ∧ v₁ = v₂ ∧ R₁ = R₂) ∨
    ∃ R₁₂ R₂₁ m', concat (element k₂ v₂) R₁₂ = some m₁ ∧ concat (element k₂ w₂) R₁₂ = some m' ∧
      concat (element k₁ v₁) R₂₁ = some m₂ ∧ concat (element k₁ w₁) R₂₁ = some m' := by
  by_cases hk : k₁ = k₂
  · subst hk
    exact Or.inl ⟨rfl, concat_element_unique h₁ h₂⟩
  · exact Or.inr (concat_element_comm h₁ h₂ r₁ r₂ hk)

/-- A step at a binding `k₁` and the insertion of a fresh binding `k₂` (`(k₂ ↦ w₂) m`, defined
only when `k₂` is not a key of `m`) commute. -/
theorem concat_element_comm_insert {k₁ k₂ : K} {v₁ w₁ w₂ : V} {R₁ m m₁ m₂ : M}
    (h₁ : concat (element k₁ v₁) R₁ = some m) (r₁ : concat (element k₁ w₁) R₁ = some m₁)
    (r₂ : concat (element k₂ w₂) m = some m₂) :
    ∃ R₂₁ m', concat (element k₁ v₁) R₂₁ = some m₂ ∧ concat (element k₁ w₁) R₂₁ = some m' ∧
      concat (element k₂ w₂) m₁ = some m' := by
  have lm := lookup_of_concat_element h₁
  obtain ⟨wR₁, _, rfl⟩ := concat_element_iff.1 h₁
  obtain ⟨-, -, rfl⟩ := concat_element_iff.1 r₁
  obtain ⟨wm, n₂, rfl⟩ := concat_element_iff.1 r₂
  have hne : k₁ ≠ k₂ := fun h => by subst h; rw [lm] at n₂; exact absurd n₂ (by simp)
  have hne' : k₂ ≠ k₁ := fun h => hne h.symm
  have w₂' : WF (update (update R₁ k₁ v₁) k₂ w₂) := wf_update wm
  have l₁ : lookup (update (update R₁ k₁ v₁) k₂ w₂) k₁ = some v₁ := by
    rw [lookup_update_ne _ _ hne, lookup_update_self]
  refine ⟨remove (update (update R₁ k₁ v₁) k₂ w₂) k₁,
    update (remove (update (update R₁ k₁ v₁) k₂ w₂) k₁) k₁ w₁, concat_element_remove w₂' l₁,
    concat_element_iff.2 ⟨wf_remove w₂', lookup_remove_self k₁ w₂', rfl⟩,
    concat_element_iff.2 ⟨wf_update wR₁, ?_, ?_⟩⟩
  · rw [lookup_update_ne _ _ hne', ← lookup_update_ne R₁ v₁ hne', n₂]
  · refine ext (wf_update (wf_remove w₂')) (wf_update (wf_update wR₁)) (fun j => ?_)
    by_cases j₁ : j = k₁
    · subst j₁
      rw [lookup_update_self, lookup_update_ne _ _ hne, lookup_update_self]
    by_cases j₂ : j = k₂
    · subst j₂
      rw [lookup_update_ne _ _ j₁, lookup_remove_ne j₁ w₂', lookup_update_self, lookup_update_self]
    rw [lookup_update_ne _ _ j₁, lookup_remove_ne j₁ w₂', lookup_update_ne _ _ j₂,
      lookup_update_ne _ _ j₁, lookup_update_ne _ _ j₂, lookup_update_ne _ _ j₁]

theorem concat_toList {a b m : M} (h : concat a b = some m) :
    SAL.concat (toList a) (toList b) = some (toList m) := by
  unfold concat at h
  obtain ⟨l, e, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [toList_ofList]; exact e

theorem concat_of_toList {a b m : M} (h : SAL.concat (toList a) (toList b) = some (toList m)) :
    concat a b = some m := by
  unfold concat; rw [h]; simp [ofList_toList]

/-- Every key of `b` is one of `a`. -/
def KeysIn (b a : M) : Prop := ∀ k, lookup b k ≠ none → lookup a k ≠ none

/-- `a` binds exactly the bindings `bs`. -/
def Binds (a : M) (bs : List (K × V)) : Prop := ∀ k v, lookup a k = some v ↔ (k, v) ∈ bs

/-- Two steps of a map at bindings with no key in common commute (`SAL.concat_frame`), when one
of them inserts no key. -/
theorem concat_frame {a₁ b₁ R₁ a₂ b₂ R₂ m m₁ m₂ : M}
    (h₁ : concat a₁ R₁ = some m) (r₁ : concat b₁ R₁ = some m₁)
    (h₂ : concat a₂ R₂ = some m) (r₂ : concat b₂ R₂ = some m₂)
    (dA : ∀ k, lookup a₁ k = none ∨ lookup a₂ k = none) (dB : KeysIn b₁ a₁ ∨ KeysIn b₂ a₂) :
    ∃ R₁₂ R₂₁ m', concat a₂ R₁₂ = some m₁ ∧ concat b₂ R₁₂ = some m' ∧
      concat a₁ R₂₁ = some m₂ ∧ concat b₁ R₂₁ = some m' := by
  have H₁ := concat_toList h₁
  have H₂ := concat_toList h₂
  have S₁ := concat_toList r₁
  have S₂ := concat_toList r₂
  have wa₁ := SAL.sorted_of_concat_left H₁
  have wa₂ := SAL.sorted_of_concat_left H₂
  have wb₁ := SAL.sorted_of_concat_left S₁
  have wb₂ := SAL.sorted_of_concat_left S₂
  have dA' : ∀ p ∈ toList a₁, ∀ q ∈ toList a₂, p.1 ≠ q.1 := fun p hp q hq e => by
    have l₁ : lookup a₁ p.1 = some p.2 := by rw [lookup_def]; exact SAL.lookup_of_mem wa₁ hp
    have l₂ : lookup a₂ p.1 = some q.2 := by rw [lookup_def, e]; exact SAL.lookup_of_mem wa₂ hq
    rcases dA p.1 with h | h
    · rw [l₁] at h; cases h
    · rw [l₂] at h; cases h
  have key : ∀ {a b : M}, WF b → KeysIn b a → ∀ p ∈ toList b, SAL.HasKey (toList a) p.1 :=
    fun {a b} wb d p hp => by
      have hn := d p.1 (by rw [lookup_def, SAL.lookup_of_mem wb hp]; simp)
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hn
      rw [lookup_def] at hv
      exact ⟨(p.1, v), SAL.lookup_mem hv, rfl⟩
  have dB' := dB.imp (key wb₁) (key wb₂)
  obtain ⟨F₁, F₂, l, e₁, e₂, e₃, e₄⟩ := SAL.concat_frame H₁ S₁ H₂ S₂ dA' dB'
  refine ⟨ofList F₁, ofList F₂, ofList l, concat_of_toList ?_, concat_of_toList ?_,
    concat_of_toList ?_, concat_of_toList ?_⟩ <;> simpa only [toList_ofList]

theorem lookup_of_concat {a R m : M} (h : concat a R = some m) {k : K} {v : V}
    (hl : lookup a k = some v) : lookup m k = some v := by
  have H := concat_toList h
  rw [lookup_def] at hl ⊢
  exact SAL.lookup_of_mem (SAL.sorted_of_concat H) ((SAL.mem_concat H).2 (Or.inl (SAL.lookup_mem hl)))

/-- Two matches in one map that bind one key bind it to one value. -/
theorem binds_same {a₁ a₂ R₁ R₂ m : M} {bs₁ bs₂ : List (K × V)} (h₁ : concat a₁ R₁ = some m)
    (h₂ : concat a₂ R₂ = some m) (b₁ : Binds a₁ bs₁) (b₂ : Binds a₂ bs₂) {p q : K × V}
    (hp : p ∈ bs₁) (hq : q ∈ bs₂) (e : p.1 = q.1) : p.2 = q.2 := by
  have l₁ := lookup_of_concat h₁ ((b₁ p.1 p.2).2 hp)
  have l₂ := lookup_of_concat h₂ ((b₂ q.1 q.2).2 hq)
  rw [e, l₂] at l₁
  exact (Option.some.inj l₁).symm

/-- Matches that bind no key in common share none. -/
theorem binds_disj {a₁ a₂ : M} {bs₁ bs₂ : List (K × V)} (b₁ : Binds a₁ bs₁) (b₂ : Binds a₂ bs₂)
    (h : ¬ ∃ p ∈ bs₁, ∃ q ∈ bs₂, p.1 = q.1) : ∀ k, lookup a₁ k = none ∨ lookup a₂ k = none := by
  intro k
  cases e₁ : lookup a₁ k with
  | none => exact Or.inl rfl
  | some v =>
    cases e₂ : lookup a₂ k with
    | none => exact Or.inr rfl
    | some w => exact absurd ⟨(k, v), (b₁ k v).1 e₁, (k, w), (b₂ k w).1 e₂, rfl⟩ h

theorem binds_element {k : K} {v : V} : Binds (element k v : M) [(k, v)] := by
  intro j w
  rw [lookup_def]
  unfold element
  rw [toList_ofList]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  by_cases hj : j = k
  · subst hj; simp [SAL.lookup, eq_comm]
  · have : SAL.lookup j [(k, v)] = none :=
      (SAL.lookup_eq_none_iff (SAL.Sorted.cons (by simp) SAL.Sorted.nil)).2
        (by simpa using fun h => hj h.symm)
    simp [this, hj]

theorem keysIn_element {k : K} {v w : V} : KeysIn (element k w : M) (element k v) := by
  intro j h
  have := (binds_element (k := k) (v := v) (M := M) j v).2
  cases e : lookup (element k w : M) j with
  | none => exact absurd e h
  | some x =>
    have := (binds_element (k := k) (v := w) (M := M) j x).1 e
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
    obtain ⟨rfl, -⟩ := this
    rw [(binds_element (k := j) (v := v) (M := M) j v).2 (by simp)]; simp

theorem keysIn_refl {a : M} : KeysIn a a := fun _ h => h

theorem keysIn_unit {a : M} : KeysIn (unit : M) a := fun k h => by
  apply absurd _ h
  rw [lookup_def]; unfold unit; rw [toList_ofList]; rfl

theorem concat_unit_left {R : M} (h : WF R) : concat (unit : M) R = some R := by
  apply concat_of_toList
  unfold unit; rw [toList_ofList]
  exact SAL.concat_eq_some_iff.2 ⟨SAL.Sorted.nil, h, by simp, rfl⟩

theorem eq_of_concat_unit_left {R r : M} (h : concat (unit : M) R = some r) : r = R := by
  have H := concat_toList h
  unfold unit at H; rw [toList_ofList] at H
  obtain ⟨-, -, -, e⟩ := SAL.concat_eq_some_iff.1 H
  have e' : toList r = toList R := e
  rw [← ofList_toList r, e', ofList_toList]

/-- The match `K₁ |-> V₁ K₂ |-> V₂ R` of two bindings, as the part `a` of the two and the rest. -/
theorem concat_pair_of_chain {k₁ k₂ : K} {v₁ v₂ : V} {rest R m : M}
    (h₁ : concat (element k₁ v₁) rest = some m) (h₂ : concat (element k₂ v₂) R = some rest) :
    ∃ a, concat (element k₁ v₁) (element k₂ v₂) = some a ∧ concat a R = some m := by
  obtain ⟨ab, e₁, e₂⟩ := SAL.concat_assoc_left (concat_toList h₂) (concat_toList h₁)
  exact ⟨ofList ab, concat_of_toList (by rwa [toList_ofList]),
    concat_of_toList (by rwa [toList_ofList])⟩

theorem chain_of_pair {k₁ k₂ : K} {v₁ v₂ : V} {a R m : M}
    (h₁ : concat (element k₁ v₁) (element k₂ v₂) = some a) (h₂ : concat a R = some m) :
    ∃ rest, concat (element k₂ v₂) R = some rest ∧ concat (element k₁ v₁) rest = some m := by
  obtain ⟨bc, e₁, e₂⟩ := SAL.concat_assoc_right (concat_toList h₁) (concat_toList h₂)
  exact ⟨ofList bc, concat_of_toList (by rwa [toList_ofList]),
    concat_of_toList (by rwa [toList_ofList])⟩

theorem binds_pair {k₁ k₂ : K} {v₁ v₂ : V} {a : M}
    (h : concat (element k₁ v₁) (element k₂ v₂) = some a) : Binds a [(k₁, v₁), (k₂, v₂)] := by
  intro j w
  have H := concat_toList h
  rw [lookup_def]
  constructor
  · intro hl
    have := (SAL.mem_concat H).1 (SAL.lookup_mem hl)
    unfold element at this; rw [toList_ofList, toList_ofList] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact this
  · intro hm
    refine SAL.lookup_of_mem (SAL.sorted_of_concat H) ((SAL.mem_concat H).2 ?_)
    unfold element; rw [toList_ofList, toList_ofList]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    exact hm

theorem keysIn_pair {k₁ k₂ : K} {v₁ v₂ w₁ w₂ : V} {a b : M}
    (ha : concat (element k₁ v₁) (element k₂ v₂) = some a)
    (hb : concat (element k₁ w₁) (element k₂ w₂) = some b) : KeysIn b a := by
  intro j h
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 h
  have := ((binds_pair hb) j x).1 hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
  have hm : ∀ v, (j, v) ∈ [(k₁, v₁), (k₂, v₂)] → lookup a j ≠ none := fun v hv => by
    rw [(binds_pair ha j v).2 hv]; simp
  rcases this with ⟨e, -⟩ | ⟨e, -⟩
  · exact hm v₁ (by simp [e])
  · exact hm v₂ (by simp [e])

end MapHook

end KPrelude

namespace KPrelude

/-! ## Changes of a cell (`confluence --threads`)

The change a step makes to one cell of the configuration: none, or the value it has and the value
it gets (the same value for a cell it only reads). Two changes commute when one leaves the cell
alone or both only read it. -/

abbrev Ch (α : Type) := Option (α × α)

def Ch.pre {α : Type} (c : Ch α) (x : α) : Prop := ∀ p, c = some p → x = p.1
def Ch.apply {α : Type} (c : Ch α) (x : α) : α := match c with | some p => p.2 | none => x
def Ch.Compat {α : Type} (a b : Ch α) : Prop :=
  a = none ∨ b = none ∨ ((∃ x, a = some (x, x)) ∧ (∃ y, b = some (y, y)))

theorem Ch.pre_none {α : Type} {x : α} : Ch.pre (none : Ch α) x := fun _ h => by cases h
theorem Ch.pre_self {α : Type} {x y : α} : Ch.pre (some (x, y) : Ch α) x := fun _ h => by cases h; rfl

theorem Ch.pre_apply {α : Type} {a b : Ch α} {x : α} (h : Ch.Compat a b) (ha : a.pre x) (hb : b.pre x) :
    b.pre (a.apply x) := by
  rcases h with rfl | rfl | ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  · exact hb
  · intro p hp; cases hp
  · intro p hp; cases hp; simp only [Ch.apply]; exact (ha (u, u) rfl).symm.trans (hb (v, v) rfl)

theorem Ch.apply_comm {α : Type} {a b : Ch α} {x : α} (h : Ch.Compat a b) (ha : a.pre x) (hb : b.pre x) :
    b.apply (a.apply x) = a.apply (b.apply x) := by
  rcases h with rfl | rfl | ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  · rfl
  · rfl
  · simp only [Ch.apply]; exact (hb (v, v) rfl).symm.trans (ha (u, u) rfl)

theorem Ch.Compat.symm {α : Type} {a b : Ch α} (h : Ch.Compat a b) : Ch.Compat b a := by
  rcases h with h | h | ⟨h₁, h₂⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨h₂, h₁⟩)

end KPrelude

namespace KPrelude

/-! ## The key of a thread (`confluence --threads`)

What a rule's left-hand side fixes of the first items of a thread's `<k>`: nothing, its emptiness,
the injection of the first item into `KItem` and the constructor of the injected value, or the
same of the first two items (a cooling rule's first item is the value, a variable, and its second
the freezer), each when known. Two rules whose keys are disjoint never step one thread from one
configuration. -/

/-- What a key reads of a thread's `<k>`: its number of items up to 2, and `(injection,
constructor)` of the item at a position below it. `item` is a function so that a key that does not
read an item (a variable on a rule's left-hand side) never computes it, and the generated `len` is
`n + 1` past the first item, so that it is not `0` whatever the rest of `<k>` is. -/
structure KeyView where
  len : Nat
  item : Nat → String × String
  /-- Whether the first item is a `KResult` (a value: what a cooling rule's first item is). -/
  kres : Bool

/-- `item i o r`: the first item has the injection `i`, the constructor `o` and is a `KResult`
exactly when `r`, each when given; `item2` the same of the first item, and the injection and the
constructor of the second. -/
inductive KeyPat where
  | any
  | dotk
  | item (inj own : Option String) (kres : Option Bool)
  | item2 (inj own : Option String) (kres : Option Bool) (inj₂ own₂ : Option String)
  deriving DecidableEq

/-- Whether an item `x` has the injection `i` and the constructor `o`, each when given. -/
def KeyPat.itemOK (i o : Option String) (x : String × String) : Bool :=
  i.all (· == x.1) && o.all (· == x.2)

/-- `itemOK` of the first item, and its `KResult` flag. -/
def KeyPat.firstOK (i o : Option String) (r : Option Bool) (v : KeyView) : Bool :=
  KeyPat.itemOK i o (v.item 0) && r.all (· == v.kres)

def KeyPat.matches : KeyPat → KeyView → Bool
  | .any, _ => true
  | .dotk, v => v.len == 0
  | .item i o r, v => v.len != 0 && KeyPat.firstOK i o r v
  | .item2 i o r i₂ o₂, v => v.len == 2 && KeyPat.firstOK i o r v && KeyPat.itemOK i₂ o₂ (v.item 1)

/-- Two descriptions of one item that no item satisfies: different injections, or one injection
and different constructors. -/
def KeyPat.conf : Option String → Option String → Option String → Option String → Bool
  | some i₁, o₁, some i₂, o₂ =>
      i₁ != i₂ || (match o₁, o₂ with | some a, some b => a != b | _, _ => false)
  | _, _, _, _ => false

theorem KeyPat.conf_sound {i₁ o₁ i₂ o₂ : Option String} {x : String × String}
    (h : KeyPat.conf i₁ o₁ i₂ o₂ = true) (h₁ : KeyPat.itemOK i₁ o₁ x = true)
    (h₂ : KeyPat.itemOK i₂ o₂ x = true) : False := by
  match i₁, i₂, h with
  | some a, some b, h =>
    simp only [KeyPat.itemOK, Bool.and_eq_true, Option.all_some, beq_iff_eq] at h₁ h₂
    simp only [KeyPat.conf, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    rcases h with h | h
    · exact h (h₁.1.trans h₂.1.symm)
    · cases o₁ <;> cases o₂ <;> simp_all [Option.all]

/-- Two descriptions of the first item that no item satisfies: `conf`, or opposite `KResult`
flags. -/
def KeyPat.conf1 (i₁ o₁ : Option String) (r₁ : Option Bool) (i₂ o₂ : Option String)
    (r₂ : Option Bool) : Bool :=
  KeyPat.conf i₁ o₁ i₂ o₂ || (match r₁, r₂ with | some a, some b => a != b | _, _ => false)

theorem KeyPat.conf1_sound {i₁ o₁ i₂ o₂ : Option String} {r₁ r₂ : Option Bool} {v : KeyView}
    (h : KeyPat.conf1 i₁ o₁ r₁ i₂ o₂ r₂ = true) (h₁ : KeyPat.firstOK i₁ o₁ r₁ v = true)
    (h₂ : KeyPat.firstOK i₂ o₂ r₂ v = true) : False := by
  simp only [KeyPat.firstOK, Bool.and_eq_true] at h₁ h₂
  simp only [KeyPat.conf1, Bool.or_eq_true] at h
  rcases h with h | h
  · exact KeyPat.conf_sound h h₁.1 h₂.1
  · cases r₁ <;> cases r₂ <;> simp_all [Option.all]

def KeyPat.disj : KeyPat → KeyPat → Bool
  | .dotk, .item _ _ _ => true
  | .item _ _ _, .dotk => true
  | .dotk, .item2 _ _ _ _ _ => true
  | .item2 _ _ _ _ _, .dotk => true
  | .item i₁ o₁ r₁, .item i₂ o₂ r₂ => KeyPat.conf1 i₁ o₁ r₁ i₂ o₂ r₂
  | .item i₁ o₁ r₁, .item2 i₂ o₂ r₂ _ _ => KeyPat.conf1 i₁ o₁ r₁ i₂ o₂ r₂
  | .item2 i₁ o₁ r₁ _ _, .item i₂ o₂ r₂ => KeyPat.conf1 i₁ o₁ r₁ i₂ o₂ r₂
  | .item2 i₁ o₁ r₁ j₁ p₁, .item2 i₂ o₂ r₂ j₂ p₂ =>
      KeyPat.conf1 i₁ o₁ r₁ i₂ o₂ r₂ || KeyPat.conf j₁ p₁ j₂ p₂
  | _, _ => false

theorem KeyPat.disj_sound {p q : KeyPat} {v : KeyView} (h : p.disj q = true)
    (hp : p.matches v = true) (hq : q.matches v = true) : False := by
  match p, q, h, hp, hq with
  | .dotk, .item _ _ _, _, hp, hq => simp_all [KeyPat.matches]
  | .item _ _ _, .dotk, _, hp, hq => simp_all [KeyPat.matches]
  | .dotk, .item2 _ _ _ _ _, _, hp, hq => simp_all [KeyPat.matches]
  | .item2 _ _ _ _ _, .dotk, _, hp, hq => simp_all [KeyPat.matches]
  | .item _ _ _, .item _ _ _, h, hp, hq =>
    simp only [KeyPat.matches, Bool.and_eq_true] at hp hq
    exact KeyPat.conf1_sound h hp.2 hq.2
  | .item _ _ _, .item2 _ _ _ _ _, h, hp, hq =>
    simp only [KeyPat.matches, Bool.and_eq_true] at hp hq
    exact KeyPat.conf1_sound h hp.2 hq.1.2
  | .item2 _ _ _ _ _, .item _ _ _, h, hp, hq =>
    simp only [KeyPat.matches, Bool.and_eq_true] at hp hq
    exact KeyPat.conf1_sound h hp.1.2 hq.2
  | .item2 _ _ _ _ _, .item2 _ _ _ _ _, h, hp, hq =>
    simp only [KeyPat.matches, Bool.and_eq_true] at hp hq
    simp only [KeyPat.disj, Bool.or_eq_true] at h
    rcases h with h | h
    · exact KeyPat.conf1_sound h hp.1.2 hq.1.2
    · exact KeyPat.conf_sound h hp.2 hq.2

/-- The keys `ps` of a rule that matches the bindings `bs`, one per binding. -/
def KeyPat.Fits {K T : Type} (view : T → KeyView) : List KeyPat → List (K × T) → Prop
  | [], [] => True
  | p :: ps, b :: bs => p.matches (view b.2) = true ∧ KeyPat.Fits view ps bs
  | _, _ => False

theorem KeyPat.Fits.mem {K T : Type} {view : T → KeyView} :
    ∀ {ps : List KeyPat} {bs : List (K × T)}, KeyPat.Fits view ps bs → ∀ {b}, b ∈ bs →
      ∃ p ∈ ps, p.matches (view b.2) = true
  | [], [], _, _, h => by cases h
  | p :: ps, b :: bs, ⟨hp, ht⟩, _, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨p, List.mem_cons_self, hp⟩
    · obtain ⟨q, hq, r⟩ := KeyPat.Fits.mem ht h
      exact ⟨q, List.mem_cons_of_mem _ hq, r⟩
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

/-- Every key of one rule is disjoint from every key of the other. -/
def KeyPat.pdisj (ps qs : List KeyPat) : Bool := ps.all fun p => qs.all fun q => p.disj q

theorem KeyPat.pdisj_sound {K T : Type} {view : T → KeyView} {ps qs : List KeyPat}
    {bs₁ bs₂ : List (K × T)} (h : KeyPat.pdisj ps qs = true) (f₁ : KeyPat.Fits view ps bs₁)
    (f₂ : KeyPat.Fits view qs bs₂) {p q : K × T} (hp : p ∈ bs₁) (hq : q ∈ bs₂) (e : p.2 = q.2) :
    False := by
  obtain ⟨x, hx, mx⟩ := f₁.mem hp
  obtain ⟨y, hy, my⟩ := f₂.mem hq
  simp only [KeyPat.pdisj, List.all_eq_true] at h
  rw [e] at mx
  exact KeyPat.disj_sound (h x hx y hy) mx my

/-- One of two rules inserts no key. -/
theorem or_of_not_both {x y : Bool} {P Q : Prop} (h₁ : x = false → P) (h₂ : y = false → Q)
    (h : (!(x && y)) = true) : P ∨ Q := by
  cases x
  · exact Or.inl (h₁ rfl)
  · cases y
    · exact Or.inr (h₂ rfl)
    · cases h

end KPrelude
