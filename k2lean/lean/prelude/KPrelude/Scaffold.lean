import Lean
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

/-- Two steps of a map at parts with no key in common commute when what they put back shares no
key either: one turns `m = a₁ R₁` into `m₁ = b₁ R₁`, the other `m = a₂ R₂` into `m₂ = b₂ R₂`; the
second still matches `m₁` and the first `m₂`, and both orders give one map. -/
theorem concat_frame_b {a₁ b₁ R₁ a₂ b₂ R₂ m m₁ m₂ : List (α × β)}
    (h₁ : concat a₁ R₁ = some m) (r₁ : concat b₁ R₁ = some m₁)
    (h₂ : concat a₂ R₂ = some m) (r₂ : concat b₂ R₂ = some m₂)
    (dA : ∀ p ∈ a₁, ∀ q ∈ a₂, p.1 ≠ q.1)
    (dB' : ∀ p ∈ b₁, ∀ q ∈ b₂, p.1 ≠ q.1) :
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
  refine concat_frame_b h₁ r₁ h₂ r₂ dA fun p hp q hq e => ?_
  -- a key `b₁` keeps is one of `a₁`, so in `R₂`, which `b₂` avoids; a key `b₂` keeps is one of
  -- `a₂`, so in `R₁`, which `b₁` avoids
  have inR : ∀ {a R a' R' : List (α × β)}, concat a R = some m → concat a' R' = some m →
      (∀ p ∈ a, ∀ q ∈ a', p.1 ≠ q.1) → ∀ x ∈ a', x ∈ R := fun ha ha' d x hx =>
    ((mem_concat ha).1 ((mem_concat ha').2 (Or.inl hx))).resolve_left fun hx' => d x hx' x hx rfl
  rcases dB with d | d
  · obtain ⟨x, hx, ex⟩ := d p hp
    exact concat_disj r₂ hq (inR h₂ h₁ (fun p hp q hq e => dA q hq p hp e.symm) x hx)
      (e.symm.trans ex.symm)
  · obtain ⟨x, hx, ex⟩ := d q hq
    exact concat_disj r₁ hp (inR h₁ h₂ dA x hx) (e.trans ex.symm)

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

/-- Two steps of a map at bindings with no key in common commute when what they put back shares no
key either (`SAL.concat_frame_b`). -/
theorem concat_frame_b {a₁ b₁ R₁ a₂ b₂ R₂ m m₁ m₂ : M}
    (h₁ : concat a₁ R₁ = some m) (r₁ : concat b₁ R₁ = some m₁)
    (h₂ : concat a₂ R₂ = some m) (r₂ : concat b₂ R₂ = some m₂)
    (dA : ∀ k, lookup a₁ k = none ∨ lookup a₂ k = none)
    (dB : ∀ k, lookup b₁ k = none ∨ lookup b₂ k = none) :
    ∃ R₁₂ R₂₁ m', concat a₂ R₁₂ = some m₁ ∧ concat b₂ R₁₂ = some m' ∧
      concat a₁ R₂₁ = some m₂ ∧ concat b₁ R₂₁ = some m' := by
  have H₁ := concat_toList h₁
  have H₂ := concat_toList h₂
  have S₁ := concat_toList r₁
  have S₂ := concat_toList r₂
  have disj : ∀ {a b : M}, WF a → WF b → (∀ k, lookup a k = none ∨ lookup b k = none) →
      ∀ p ∈ toList a, ∀ q ∈ toList b, p.1 ≠ q.1 := fun {a b} wa wb d p hp q hq e => by
    have l₁ : lookup a p.1 = some p.2 := by rw [lookup_def]; exact SAL.lookup_of_mem wa hp
    have l₂ : lookup b p.1 = some q.2 := by rw [lookup_def, e]; exact SAL.lookup_of_mem wb hq
    rcases d p.1 with h | h
    · rw [l₁] at h; cases h
    · rw [l₂] at h; cases h
  obtain ⟨F₁, F₂, l, e₁, e₂, e₃, e₄⟩ := SAL.concat_frame_b H₁ S₁ H₂ S₂
    (disj (SAL.sorted_of_concat_left H₁) (SAL.sorted_of_concat_left H₂) dA)
    (disj (SAL.sorted_of_concat_left S₁) (SAL.sorted_of_concat_left S₂) dB)
  refine ⟨ofList F₁, ofList F₂, ofList l, concat_of_toList ?_, concat_of_toList ?_,
    concat_of_toList ?_, concat_of_toList ?_⟩ <;> simpa only [toList_ofList]

theorem lookup_of_concat {a R m : M} (h : concat a R = some m) {k : K} {v : V}
    (hl : lookup a k = some v) : lookup m k = some v := by
  have H := concat_toList h
  rw [lookup_def] at hl ⊢
  exact SAL.lookup_of_mem (SAL.sorted_of_concat H) ((SAL.mem_concat H).2 (Or.inl (SAL.lookup_mem hl)))

/-- A binding of `m = a R` at a key `a` does not bind is `R`'s. -/
theorem lookup_concat_right {a R m : M} (h : concat a R = some m) {k : K} (ha : lookup a k = none) :
    lookup m k = lookup R k := by
  have H := concat_toList h
  have sm := SAL.sorted_of_concat H
  have sR := (SAL.concat_eq_some_iff.1 H).2.1
  rw [lookup_def] at ha
  rw [lookup_def, lookup_def]
  cases e : SAL.lookup k (toList R) with
  | some v => exact SAL.lookup_of_mem sm ((SAL.mem_concat H).2 (Or.inr (SAL.lookup_mem e)))
  | none =>
    cases e' : SAL.lookup k (toList m) with
    | none => rfl
    | some v =>
      rcases (SAL.mem_concat H).1 (SAL.lookup_mem e') with h₁ | h₁
      · rw [SAL.lookup_of_mem (SAL.sorted_of_concat_left H) h₁] at ha; cases ha
      · rw [SAL.lookup_of_mem sR h₁] at e; cases e

/-- No key is bound on both sides of a defined `a R`. -/
theorem concat_disj_lookup {a R m : M} (h : concat a R = some m) (k : K) :
    lookup a k = none ∨ lookup R k = none := by
  cases ha : lookup a k with
  | none => exact Or.inl rfl
  | some v =>
    right
    obtain ⟨-, -, d, -⟩ := SAL.concat_eq_some_iff.1 (concat_toList h)
    rw [lookup_def] at ha ⊢
    exact d _ (SAL.lookup_mem ha)

/-- The bindings of `a R` are `a`'s, and `R`'s at the keys `a` does not bind. -/
theorem lookup_concat {a R m : M} (h : concat a R = some m) (k : K) :
    lookup m k = (lookup a k).or (lookup R k) := by
  cases ha : lookup a k with
  | none => rw [lookup_concat_right h ha]; rfl
  | some v => rw [lookup_of_concat h ha]; rfl

/-- Two well-formed maps with no key in common have a union. -/
theorem concat_exists {a R : M} (wa : WF a) (wR : WF R)
    (d : ∀ k, lookup a k = none ∨ lookup R k = none) : ∃ m, concat a R = some m := by
  have hd : ∀ p ∈ toList a, SAL.lookup p.1 (toList R) = none := by
    intro p hp
    rcases d p.1 with h | h
    · rw [lookup_def, SAL.lookup_of_mem wa hp] at h; cases h
    · rw [lookup_def] at h; exact h
  exact ⟨ofList _, concat_of_toList (by
    rw [toList_ofList]; exact SAL.concat_eq_some_iff.2 ⟨wa, wR, hd, rfl⟩)⟩

/-- A map whose bindings are all bindings of `y` matches `y`, at some rest. -/
theorem concat_sub {a y : M} (wa : WF a) (wy : WF y)
    (sub : ∀ k v, lookup a k = some v → lookup y k = some v) : ∃ R, concat a R = some y := by
  have hsub : ∀ p ∈ toList a, p ∈ toList y := by
    rintro ⟨k, v⟩ hp
    have := sub k v (by rw [lookup_def]; exact SAL.lookup_of_mem wa hp)
    rw [lookup_def] at this
    exact SAL.lookup_mem this
  exact ⟨ofList _, concat_of_toList (by rw [toList_ofList]; exact SAL.concat_filter wa wy hsub)⟩

/-- A key whose binding a step changes (`a R = m` to `b R = m'`) is one it matches or puts back. -/
theorem changed_key {a b R m m' : M} (h : concat a R = some m) (h' : concat b R = some m') {k : K}
    (hk : lookup m k ≠ lookup m' k) : lookup a k ≠ none ∨ lookup b k ≠ none := by
  cases ha : lookup a k with
  | some v => exact Or.inl (by simp)
  | none =>
    cases hb : lookup b k with
    | some w => exact Or.inr (by simp)
    | none => exact absurd ((lookup_concat_right h ha).trans (lookup_concat_right h' hb).symm) hk

/-- A key the rest binds is not one of what `concat` puts beside it. -/
theorem lookup_left_none_of_concat {b R m : M} (h : concat b R = some m) {k : K}
    (hR : lookup R k ≠ none) : lookup b k = none := by
  have H := concat_toList h
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hR
  rw [lookup_def] at hw ⊢
  cases e : SAL.lookup k (toList b) with
  | none => rfl
  | some v =>
    exact (SAL.concat_disj H (SAL.lookup_mem e) (SAL.lookup_mem hw) rfl).elim

/-- A step `a R = m` to `b R = m'` that changes the binding at a key of `m` (another value, or
none) matches that key. -/
theorem matched_of_ne {a b R m m' : M} (h : concat a R = some m) (h' : concat b R = some m')
    {k : K} (hk : lookup m k ≠ none) (hne : lookup m k ≠ lookup m' k) : lookup a k ≠ none := by
  intro ha
  have e := lookup_concat_right h ha
  have hb := lookup_left_none_of_concat h' (k := k) (by rw [← e]; exact hk)
  exact hne (by rw [lookup_concat_right h' hb, e])

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

/-- The rest of a match is unique: `a R = m` and `a R' = m` give `R = R'`. -/
theorem concat_rest_unique {a R R' m : M} (h : concat a R = some m) (h' : concat a R' = some m) :
    R = R' := by
  have H := concat_toList h
  have H' := concat_toList h'
  have sR := (SAL.concat_eq_some_iff.1 H).2.1
  have sR' := (SAL.concat_eq_some_iff.1 H').2.1
  have e : toList R = toList R' := SAL.eq_of_mem_iff sR sR' fun p => by
    constructor
    · intro hp
      rcases (SAL.mem_concat H').1 ((SAL.mem_concat H).2 (Or.inr hp)) with ha | hb
      · exact absurd rfl (SAL.concat_disj H ha hp)
      · exact hb
    · intro hp
      rcases (SAL.mem_concat H).1 ((SAL.mem_concat H').2 (Or.inr hp)) with ha | hb
      · exact absurd rfl (SAL.concat_disj H' ha hp)
      · exact hb
  rw [← ofList_toList R, e, ofList_toList]

theorem wf_right_of_concat {a R m : M} (h : concat a R = some m) : WF R :=
  (SAL.concat_eq_some_iff.1 (concat_toList h)).2.1

theorem lookup_element_ne {j k : K} {v : V} (h : j ≠ k) : lookup (element k v : M) j = none := by
  cases e : lookup (element k v : M) j with
  | none => rfl
  | some w =>
    have := (binds_element (k := k) (v := v) (M := M) j w).1 e
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
    exact absurd this.1 h

/-- A part of a map one binding wide or empty, as a keyed change's (`MCh.Small`). -/
abbrev Small (a : M) : Prop := (∃ k v, a = element k v) ∨ a = unit

/-- A step `a R = L` to `b R = L'` with `a` and `b` one binding wide at most that inserts `k ↦ v`
(`(k ↦ v) L = L'`) matches nothing and puts `k ↦ v` in. -/
theorem small_insert {a b R L L' : M} {k : K} {v : V} (ha : Small a) (hb : Small b)
    (h : concat a R = some L) (h' : concat b R = some L') (hi : concat (element k v) L = some L') :
    a = unit ∧ b = element k v := by
  obtain ⟨-, hkL, eL'⟩ := concat_element_iff.1 hi
  have hk' : lookup L' k = some v := lookup_of_concat_element hi
  have same : ∀ j, j ≠ k → lookup L' j = lookup L j := fun j hj => by
    rw [eL']; exact lookup_update_ne L v hj
  rcases ha with ⟨j, w, rfl⟩ | rfl
  · exfalso
    have hjL : lookup L j = some w := lookup_of_concat_element h
    have hjk : j ≠ k := fun e => by rw [e, hkL] at hjL; cases hjL
    have hRj : lookup R j = none := (concat_element_iff.1 h).2.1
    have hRk : lookup R k = none := by
      rw [← lookup_concat_right h (lookup_element_ne (Ne.symm hjk))]; exact hkL
    have bj : lookup b j ≠ none := fun hb' => by
      have := (lookup_concat_right h' hb').symm.trans ((same j hjk).trans hjL)
      rw [hRj] at this; cases this
    have bk : lookup b k ≠ none := fun hb' => by
      have := (lookup_concat_right h' hb').symm.trans hk'
      rw [hRk] at this; cases this
    rcases hb with ⟨i, u, rfl⟩ | rfl
    · have e₁ : j = i := Classical.byContradiction fun ne => bj (lookup_element_ne ne)
      have e₂ : k = i := Classical.byContradiction fun ne => bk (lookup_element_ne ne)
      exact hjk (e₁.trans e₂.symm)
    · exact bk (by rw [lookup_def]; unfold unit; rw [toList_ofList]; rfl)
  · refine ⟨rfl, ?_⟩
    have eR := eq_of_concat_unit_left h
    subst eR
    rcases hb with ⟨i, u, rfl⟩ | rfl
    · have hiL : lookup L i = none := (concat_element_iff.1 h').2.1
      have hi' : lookup L' i = some u := lookup_of_concat_element h'
      by_cases e : i = k
      · subst e
        rw [hk'] at hi'; cases hi'; rfl
      · rw [same i e, hiL] at hi'; cases hi'
    · have := eq_of_concat_unit_left h'
      subst this
      rw [hkL] at hk'; cases hk'

/-- A step `a R = L` to `b R = L'` with `a` and `b` one binding wide at most that removes `k ↦ v`
(`(k ↦ v) L' = L`) matches `k ↦ v` and puts nothing back. -/
theorem small_remove {a b R L L' : M} {k : K} {v : V} (ha : Small a) (hb : Small b)
    (h : concat a R = some L) (h' : concat b R = some L') (hr : concat (element k v) L' = some L) :
    a = element k v ∧ b = unit := by
  have hkL : lookup L k = some v := lookup_of_concat_element hr
  have hkL' : lookup L' k = none := (concat_element_iff.1 hr).2.1
  -- `a` matches `k`: otherwise `k` is in the rest, which the result keeps
  have ak : lookup a k ≠ none := fun ha' => by
    have e := lookup_concat_right h ha'
    rw [hkL] at e
    have hbk := lookup_left_none_of_concat h' (k := k) (by rw [← e]; simp)
    rw [lookup_concat_right h' hbk, ← e] at hkL'; cases hkL'
  rcases ha with ⟨j, w, rfl⟩ | rfl
  · have hj : j = k := Classical.byContradiction fun ne => ak (lookup_element_ne (Ne.symm ne))
    subst hj
    have hw := (lookup_of_concat_element h).symm.trans hkL
    cases hw
    refine ⟨rfl, ?_⟩
    have eR := concat_rest_unique h hr
    subst eR
    rcases hb with ⟨i, u, rfl⟩ | rfl
    · have e₁ := (concat_element_iff.1 h').2.1
      have e₂ := lookup_of_concat_element h'
      rw [e₁] at e₂; cases e₂
    · rfl
  · exact absurd (by rw [lookup_def]; unfold unit; rw [toList_ofList]; rfl) ak

/-- A binding of the rest of a match is one of the map. -/
theorem lookup_of_concat_right {a R m : M} (h : concat a R = some m) {k : K} {v : V}
    (hl : lookup R k = some v) : lookup m k = some v := by
  rw [lookup_concat_right h (lookup_left_none_of_concat h (by rw [hl]; simp)), hl]

/-- A map of one binding binds its key. -/
theorem lookup_element_self {k : K} {v : V} : lookup (element k v : M) k = some v :=
  (binds_element (M := M) k v).2 (List.mem_singleton_self _)

/-- A match `a (k ↦ v)` puts the binding of `k` in its map. -/
theorem lookup_of_concat_element_right {a m : M} {k : K} {v : V} (h : concat a (element k v) = some m) :
    lookup m k = some v :=
  lookup_of_concat_right h lookup_element_self

/-- A key a map of one binding binds is that binding's. -/
theorem key_of_lookup_element {k j : K} {v : V} (h : lookup (element k v : M) j ≠ none) : j = k :=
  Classical.byContradiction fun e => h (lookup_element_ne e)

/-- A key a map of two bindings binds is one of theirs. -/
theorem key_of_lookup_pair {k₁ k₂ j : K} {v₁ v₂ : V} {a : M}
    (h : concat (element k₁ v₁) (element k₂ v₂) = some a) (hj : lookup a j ≠ none) :
    j = k₁ ∨ j = k₂ := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hj
  have := ((binds_pair h) j u).1 hu
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
  rcases this with ⟨e, -⟩ | ⟨e, -⟩
  · exact Or.inl e
  · exact Or.inr e

/-- A key bound by what `concat` puts beside the rest is not the rest's. -/
theorem lookup_right_none {b R m : M} (h : concat b R = some m) {k : K} (hb : lookup b k ≠ none) :
    lookup R k = none := by
  cases e : lookup R k with
  | none => rfl
  | some w => exact absurd (lookup_left_none_of_concat h (by rw [e]; simp)) hb

/-- What an insertion `(k ↦ v) L = L'` does: it binds `k`, which `L` does not, and keeps every
other key. -/
theorem ins_facts {k : K} {v : V} {L L' : M} (h : concat (element k v) L = some L') :
    lookup L' k = some v ∧ lookup L k = none ∧ ∀ j, j ≠ k → lookup L' j = lookup L j :=
  ⟨lookup_of_concat_element h, (concat_element_iff.1 h).2.1,
    fun _ hj => lookup_concat_right h (lookup_element_ne hj)⟩

/-- What a removal `(k ↦ v) L' = L` does: `k` is bound in `L`, not in `L'`, and every other key
is kept. -/
theorem rem_facts {k : K} {v : V} {L L' : M} (h : concat (element k v) L' = some L) :
    lookup L' k = none ∧ lookup L k = some v ∧ ∀ j, j ≠ k → lookup L' j = lookup L j :=
  ⟨(concat_element_iff.1 h).2.1, lookup_of_concat_element h,
    fun _ hj => (lookup_concat_right h (lookup_element_ne hj)).symm⟩

/-- What a replacement of the binding at `k` (`(k ↦ v) D = L`, `(k ↦ w) D = L'`) does. -/
theorem repl_facts {k : K} {v w : V} {D L L' : M} (h : concat (element k v) D = some L)
    (h' : concat (element k w) D = some L') :
    lookup L' k = some w ∧ lookup L k = some v ∧ ∀ j, j ≠ k → lookup L' j = lookup L j :=
  ⟨lookup_of_concat_element h', lookup_of_concat_element h, fun _ hj =>
    (lookup_concat_right h' (lookup_element_ne hj)).trans
      (lookup_concat_right h (lookup_element_ne hj)).symm⟩

/-- What a read of `i ↦ v` with an insertion of `o ↦ x` beside it (`(i ↦ v) D = L`,
`(i ↦ v) (o ↦ x) = r`, `r D = L'`) does: it binds `o`, which `L` does not, and keeps every other
key. -/
theorem ext_facts {i o : K} {v x : V} {D L r L' : M} (h : concat (element i v) D = some L)
    (hp : concat (element i v) (element o x) = some r) (h' : concat r D = some L') :
    lookup L' o = some x ∧ lookup L o = none ∧ ∀ j, j ≠ o → lookup L' j = lookup L j := by
  have bp := binds_pair hp
  have ro : lookup r o = some x := (bp o x).2 (by simp)
  have ri : lookup r i = some v := (bp i v).2 (by simp)
  have hio : i ≠ o := fun e => by
    have := (concat_element_iff.1 hp).2.1
    rw [e, lookup_element_self] at this; cases this
  have nDo : lookup D o = none := by
    rcases concat_disj_lookup h' o with x' | x'
    · rw [ro] at x'; cases x'
    · exact x'
  refine ⟨lookup_of_concat h' ro, ?_, fun j hj => ?_⟩
  · rw [lookup_concat_right h (lookup_element_ne (Ne.symm hio))]; exact nDo
  · by_cases ji : j = i
    · rw [ji, lookup_of_concat h' ri, lookup_of_concat_element h]
    · have rj : lookup r j = none := by
        cases e : lookup r j with
        | none => rfl
        | some w =>
          have := (bp j w).1 e
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
          rcases this with ⟨e', -⟩ | ⟨e', -⟩
          · exact absurd e' ji
          · exact absurd e' hj
      rw [lookup_concat_right h' rj, lookup_concat_right h (lookup_element_ne ji)]

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

/-! ## Changes of a map cell at some of its bindings (`confluence --threads`)

The change a step makes to a cell holding a map, at the bindings it matches: none, or the
bindings `a` it matches, replaced by `b`, the rest of the map kept (`b = a` for a read, `b` empty
for a removal, `a` empty for an insertion). Two changes commute when one leaves the cell alone,
when they match no key in common and put back none in common (`MapHook.concat_frame_b`), or when
both only read. -/

/-- A change of a map at some of its bindings: none, or the bindings `a` and what replaces them. -/
abbrev MCh (M : Type) := Option (M × M)

section MCh

open MapHook

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V] [Std.TransOrd K]
  [Std.LawfulEqOrd K]

/-- The map matches the change's bindings, and what replaces them fits beside the rest. -/
def MCh.pre (c : MCh M) (x : M) : Prop :=
  ∀ p, c = some p → ∃ R r, concat p.1 R = some x ∧ concat p.2 R = some r

open Classical in
/-- The map with the change's bindings replaced (the rest is unique, `concat_rest_unique`). -/
noncomputable def MCh.apply (c : MCh M) (x : M) : M :=
  match c with
  | none => x
  | some (a, b) =>
    if h : ∃ r R, concat a R = some x ∧ concat b R = some r then Classical.choose h else x

/-- At every key, one of two changes leaves the map alone, or both read it: they match its binding
and put the same one back (two steps that read one output and write others). -/
def MCh.Shared (a₁ b₁ a₂ b₂ : M) : Prop :=
  ∀ k, (lookup a₁ k = none ∧ lookup b₁ k = none) ∨ (lookup a₂ k = none ∧ lookup b₂ k = none) ∨
    (lookup a₁ k = lookup b₁ k ∧ lookup a₂ k = lookup b₂ k)

theorem MCh.Shared.symm {a₁ b₁ a₂ b₂ : M} (h : MCh.Shared a₁ b₁ a₂ b₂) : MCh.Shared a₂ b₂ a₁ b₁ :=
  fun k => (h k).elim (fun e => Or.inr (Or.inl e)) fun e => e.elim Or.inl fun e => Or.inr (Or.inr ⟨e.2, e.1⟩)

def MCh.Compat (c d : MCh M) : Prop :=
  c = none ∨ d = none ∨ ∃ a₁ b₁ a₂ b₂, c = some (a₁, b₁) ∧ d = some (a₂, b₂) ∧
    (((∀ k, lookup a₁ k = none ∨ lookup a₂ k = none) ∧ (∀ k, lookup b₁ k = none ∨ lookup b₂ k = none)) ∨
      (a₁ = b₁ ∧ a₂ = b₂) ∨ MCh.Shared a₁ b₁ a₂ b₂)

theorem MCh.pre_none {x : M} : MCh.pre (none : MCh M) x := fun _ h => by cases h

theorem MCh.pre_of {a b R x r : M} (h : concat a R = some x) (h' : concat b R = some r) :
    MCh.pre (some (a, b)) x := fun _ e => by cases e; exact ⟨R, r, h, h'⟩

theorem MCh.apply_of {a b R x r : M} (h : concat a R = some x) (h' : concat b R = some r) :
    MCh.apply (some (a, b)) x = r := by
  simp only [MCh.apply]
  split
  · rename_i ex
    obtain ⟨R', e₁, e₂⟩ := Classical.choose_spec ex
    cases concat_rest_unique h e₁
    exact Option.some.inj (e₂.symm.trans h')
  · rename_i ne; exact absurd ⟨r, R, h, h'⟩ ne

theorem MCh.apply_none {x : M} : MCh.apply (none : MCh M) x = x := rfl

/-- A read leaves the map as it is. -/
theorem MCh.apply_read {a x : M} (h : MCh.pre (some (a, a)) x) : MCh.apply (some (a, a)) x = x := by
  obtain ⟨R, r, e₁, e₂⟩ := h _ rfl
  rw [MCh.apply_of e₁ e₂]
  exact Option.some.inj (e₂.symm.trans e₁)

theorem MCh.wf_apply {a b x : M} (hc : MCh.pre (some (a, b)) x) : WF (MCh.apply (some (a, b)) x) := by
  obtain ⟨R, r, h, h'⟩ := hc _ rfl
  rw [MCh.apply_of h h']
  exact SAL.sorted_of_concat (concat_toList h')

/-- A change puts back its own bindings and keeps the others. -/
theorem MCh.lookup_apply {a b x : M} (hc : MCh.pre (some (a, b)) x) (k : K) :
    lookup (MCh.apply (some (a, b)) x) k =
      if lookup a k = none ∧ lookup b k = none then lookup x k else lookup b k := by
  obtain ⟨R, r, h, h'⟩ := hc _ rfl
  rw [MCh.apply_of h h', lookup_concat h' k]
  by_cases hb : lookup b k = none
  · rw [hb]
    by_cases ha : lookup a k = none
    · rw [ite_eq_left (show lookup a k = none ∧ (none : Option V) = none from ⟨ha, rfl⟩), lookup_concat h k, ha]
    · rw [ite_eq_right (fun e : lookup a k = none ∧ (none : Option V) = none => ha e.1)]
      rcases concat_disj_lookup h k with e | e
      · exact absurd e ha
      · rw [e]; rfl
  · rw [ite_eq_right (fun e : lookup a k = none ∧ lookup b k = none => hb e.2)]
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hb
    rw [hv]; rfl

theorem MCh.lookup_apply_alone {a b x : M} (hc : MCh.pre (some (a, b)) x) {k : K}
    (u : lookup a k = none ∧ lookup b k = none) : lookup (MCh.apply (some (a, b)) x) k = lookup x k := by
  rw [MCh.lookup_apply hc, ite_eq_left u]

/-- A key a change reads keeps its binding. -/
theorem MCh.lookup_apply_read {a b x : M} (hc : MCh.pre (some (a, b)) x) {k : K}
    (e : lookup a k = lookup b k) : lookup (MCh.apply (some (a, b)) x) k = lookup x k := by
  rw [MCh.lookup_apply hc]
  split
  · rfl
  · next hn =>
    obtain ⟨R, r, h, -⟩ := hc _ rfl
    cases ha : lookup a k with
    | none => rw [ha] at e; exact absurd ⟨ha, e.symm⟩ hn
    | some w => rw [← e, ha, lookup_of_concat h ha]

theorem MCh.pre_apply_shared {a₁ b₁ a₂ b₂ x : M} (hs : MCh.Shared a₁ b₁ a₂ b₂)
    (hc : MCh.pre (some (a₁, b₁)) x) (hd : MCh.pre (some (a₂, b₂)) x) :
    MCh.pre (some (a₂, b₂)) (MCh.apply (some (a₁, b₁)) x) := by
  obtain ⟨R₂, r₂, h₂, h₂'⟩ := hd _ rfl
  have sub : ∀ k v, lookup a₂ k = some v → lookup (MCh.apply (some (a₁, b₁)) x) k = some v := by
    intro k v hv
    rcases hs k with u | ⟨e, -⟩ | ⟨e, -⟩
    · rw [MCh.lookup_apply_alone hc u]; exact lookup_of_concat h₂ hv
    · rw [e] at hv; cases hv
    · rw [MCh.lookup_apply_read hc e]; exact lookup_of_concat h₂ hv
  obtain ⟨R, hR⟩ := concat_sub (SAL.sorted_of_concat_left (concat_toList h₂)) (MCh.wf_apply hc) sub
  obtain ⟨m, hm⟩ := concat_exists (SAL.sorted_of_concat_left (concat_toList h₂'))
    (wf_right_of_concat hR) fun k => by
      cases hb : lookup b₂ k with
      | none => exact Or.inl rfl
      | some w =>
        right
        rcases concat_disj_lookup hR k with e | e
        · have hy : lookup (MCh.apply (some (a₁, b₁)) x) k = lookup R k := by
            rw [lookup_concat hR k, e]; rfl
          have hx : lookup x k = none := by
            rw [lookup_concat h₂ k, e]
            rcases concat_disj_lookup h₂' k with e' | e'
            · rw [hb] at e'; cases e'
            · exact e'
          rw [← hy]
          rcases hs k with u | ⟨-, e₂⟩ | ⟨-, e₂⟩
          · rw [MCh.lookup_apply_alone hc u]; exact hx
          · rw [hb] at e₂; cases e₂
          · rw [e, hb] at e₂; cases e₂
        · exact e
  intro p e; cases e
  exact ⟨R, m, hR, hm⟩

theorem MCh.apply_comm_shared {a₁ b₁ a₂ b₂ x : M} (hs : MCh.Shared a₁ b₁ a₂ b₂)
    (hc : MCh.pre (some (a₁, b₁)) x) (hd : MCh.pre (some (a₂, b₂)) x) :
    MCh.apply (some (a₂, b₂)) (MCh.apply (some (a₁, b₁)) x) =
      MCh.apply (some (a₁, b₁)) (MCh.apply (some (a₂, b₂)) x) := by
  have p₂ := MCh.pre_apply_shared hs hc hd
  have p₁ := MCh.pre_apply_shared hs.symm hd hc
  refine ext (MCh.wf_apply p₂) (MCh.wf_apply p₁) fun k => ?_
  rcases hs k with u | u | ⟨e₁, e₂⟩
  · rw [MCh.lookup_apply p₂, MCh.lookup_apply_alone hc u, MCh.lookup_apply_alone p₁ u,
      MCh.lookup_apply hd]
  · rw [MCh.lookup_apply_alone p₂ u, MCh.lookup_apply hc, MCh.lookup_apply p₁,
      MCh.lookup_apply_alone hd u]
  · rw [MCh.lookup_apply_read p₂ e₂, MCh.lookup_apply_read hc e₁, MCh.lookup_apply_read p₁ e₁,
      MCh.lookup_apply_read hd e₂]

theorem MCh.pre_apply {c d : MCh M} {x : M} (h : MCh.Compat c d) (hc : c.pre x) (hd : d.pre x) :
    d.pre (c.apply x) := by
  rcases h with rfl | rfl | ⟨a₁, b₁, a₂, b₂, rfl, rfl, ⟨dA, dB⟩ | ⟨rfl, rfl⟩ | hs⟩
  · exact hd
  · exact MCh.pre_none
  · obtain ⟨R₁, m₁, h₁, r₁⟩ := hc _ rfl
    obtain ⟨R₂, m₂, h₂, r₂⟩ := hd _ rfl
    obtain ⟨R₁₂, -, m', e₁, e₂, -, -⟩ := concat_frame_b h₁ r₁ h₂ r₂ dA dB
    rw [MCh.apply_of h₁ r₁]
    exact MCh.pre_of e₁ e₂
  · rw [MCh.apply_read hc]; exact hd
  · exact MCh.pre_apply_shared hs hc hd

theorem MCh.apply_comm {c d : MCh M} {x : M} (h : MCh.Compat c d) (hc : c.pre x) (hd : d.pre x) :
    d.apply (c.apply x) = c.apply (d.apply x) := by
  rcases h with rfl | rfl | ⟨a₁, b₁, a₂, b₂, rfl, rfl, ⟨dA, dB⟩ | ⟨rfl, rfl⟩ | hs⟩
  · rfl
  · rfl
  · obtain ⟨R₁, m₁, h₁, r₁⟩ := hc _ rfl
    obtain ⟨R₂, m₂, h₂, r₂⟩ := hd _ rfl
    obtain ⟨R₁₂, R₂₁, m', e₁, e₂, e₃, e₄⟩ := concat_frame_b h₁ r₁ h₂ r₂ dA dB
    rw [MCh.apply_of h₁ r₁, MCh.apply_of h₂ r₂, MCh.apply_of e₁ e₂, MCh.apply_of e₃ e₄]
  · rw [MCh.apply_read hc, MCh.apply_read hd, MCh.apply_read hc]
  · exact MCh.apply_comm_shared hs hc hd

/-- The change matches at most one binding and puts at most one in its place: what a rule's
match and its right-hand side make it, so that two changes that do not commute overlap at a key
(or both insert). -/
def MCh.Small (c : MCh M) : Prop :=
  ∀ p, c = some p → ((∃ k v, p.1 = element k v) ∨ p.1 = unit) ∧ ((∃ k v, p.2 = element k v) ∨ p.2 = unit)

theorem MCh.small_none : MCh.Small (none : MCh M) := fun _ h => by cases h

/-- A rule's change at one binding (`MCh.Small`), or a read of one binding with one binding added
beside it (a step that reads an input and writes an output). -/
def MCh.SmallR (c : MCh M) : Prop :=
  ∀ p, c = some p → (MapHook.Small p.1 ∧ MapHook.Small p.2) ∨
    ∃ k v k' w, p.1 = element k v ∧ concat p.1 (element k' w) = some p.2

theorem MCh.smallR_of_small {c : MCh M} (h : c.Small) : c.SmallR := fun p e => Or.inl (h p e)

theorem MCh.smallR_extend {k k' : K} {v w : V} {b : M} (hb : concat (element k v) (element k' w) = some b) :
    MCh.SmallR (some (element k v, b)) :=
  fun _ e => by cases e; exact Or.inr ⟨k, v, k', w, rfl, hb⟩

theorem MCh.small_of {a b : M} (ha : (∃ k v, a = element k v) ∨ a = unit)
    (hb : (∃ k v, b = element k v) ∨ b = unit) : MCh.Small (some (a, b)) :=
  fun _ e => by cases e; exact ⟨ha, hb⟩

theorem MCh.apply_of_none {x : M} : MCh.apply (none : MCh M) x = x := rfl

/-- A rule's change (`Small`) of a step that inserts `k ↦ v` (`(k ↦ v) L = L'`) is that insertion. -/
theorem MCh.insert_of {c : MCh M} {L L' : M} {k : K} {v : V} (pre : c.pre L) (ap : c.apply L = L')
    (sm : c.Small) (hi : concat (element k v) L = some L') : c = some (unit, element k v) := by
  cases c with
  | none =>
    cases (MCh.apply_none (x := L)).symm.trans ap
    have := (concat_element_iff.1 hi).2.1
    rw [lookup_of_concat_element hi] at this; cases this
  | some p =>
    obtain ⟨a, b⟩ := p
    obtain ⟨R, y, h, h'⟩ := pre _ rfl
    rw [MCh.apply_of h h'] at ap
    subst ap
    obtain ⟨rfl, rfl⟩ := small_insert (sm _ rfl).1 (sm _ rfl).2 h h' hi
    rfl

/-- A rule's change (`Small`) of a step that removes `k ↦ v` (`(k ↦ v) L' = L`) is that removal. -/
theorem MCh.remove_of {c : MCh M} {L L' : M} {k : K} {v : V} (pre : c.pre L) (ap : c.apply L = L')
    (sm : c.Small) (hr : concat (element k v) L' = some L) : c = some (element k v, unit) := by
  cases c with
  | none =>
    cases (MCh.apply_none (x := L)).symm.trans ap
    have := (concat_element_iff.1 hr).2.1
    rw [lookup_of_concat_element hr] at this; cases this
  | some p =>
    obtain ⟨a, b⟩ := p
    obtain ⟨R, y, h, h'⟩ := pre _ rfl
    rw [MCh.apply_of h h'] at ap
    subst ap
    obtain ⟨rfl, rfl⟩ := small_remove (sm _ rfl).1 (sm _ rfl).2 h h' hr
    rfl

theorem MapHook.lookup_unit {k : K} : lookup (unit : M) k = none := by
  rw [lookup_def]; unfold unit; rw [ListIso.toList_ofList]; rfl

theorem MCh.Compat.symm {c d : MCh M} (h : MCh.Compat c d) : MCh.Compat d c := by
  rcases h with h | h | ⟨a₁, b₁, a₂, b₂, e₁, e₂, ⟨dA, dB⟩ | ⟨r₁, r₂⟩ | hs⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨a₂, b₂, a₁, b₁, e₂, e₁, Or.inl ⟨fun k => (dA k).symm, fun k => (dB k).symm⟩⟩)
  · exact Or.inr (Or.inr ⟨a₂, b₂, a₁, b₁, e₂, e₁, Or.inr (Or.inl ⟨r₂, r₁⟩)⟩)
  · exact Or.inr (Or.inr ⟨a₂, b₂, a₁, b₁, e₂, e₁, Or.inr (Or.inr hs.symm)⟩)

/-! ### The key a rule's change is at

A rule changes a cell holding a map at one key, by the kind of its match: an insertion, a
removal, a replacement, or a read with an insertion beside it. Two changes at two different keys
commute when neither reads the other's key (`MCh.compat_at`); at one key they are steps of one
process or clash (`k2l_det`). `k2l_keyed` finds the keys. -/

/-- A step of a cell holding a map, from `L` to `L'`, by the change `c`. -/
def MCh.Step (c : MCh M) (L L' : M) : Prop := c.pre L ∧ c.apply L = L'

/-- The change is at `k`: at every other key of `L` it matches and puts back nothing, or reads
the binding (matches it and puts it back). -/
def MCh.At (c : MCh M) (L : M) (k : K) : Prop :=
  ∃ a b, c = some (a, b) ∧ ∀ j, j ≠ k →
    (lookup a j = none ∧ lookup b j = none) ∨ (lookup a j = lookup b j ∧ lookup L j ≠ none)

/-- The change matches and puts back no key other than `k`. -/
def MCh.Only (c : MCh M) (k : K) : Prop :=
  ∃ a b, c = some (a, b) ∧ ∀ j, j ≠ k → lookup a j = none ∧ lookup b j = none

theorem MCh.at_of_only {c : MCh M} {L : M} {k : K} (h : c.Only k) : c.At L k :=
  let ⟨a, b, e, h⟩ := h
  ⟨a, b, e, fun j hj => Or.inl (h j hj)⟩

/-- A step that changes the binding at `k` alone is at `k`. -/
theorem MCh.at_of_step {c : MCh M} {L L' : M} {k : K} (st : c.Step L L')
    (hk : lookup L' k ≠ lookup L k) (ho : ∀ j, j ≠ k → lookup L' j = lookup L j) : c.At L k := by
  obtain ⟨pre, ap⟩ := st
  cases c with
  | none => exact absurd (by rw [← ap]; rfl) hk
  | some p =>
    obtain ⟨a, b⟩ := p
    refine ⟨a, b, rfl, fun j hj => ?_⟩
    obtain ⟨R, r, h, h'⟩ := pre _ rfl
    have e := ho j hj
    rw [← ap, MCh.lookup_apply pre] at e
    by_cases u : lookup a j = none ∧ lookup b j = none
    · exact Or.inl u
    · rw [ite_eq_right u] at e
      right
      cases ha : lookup a j with
      | some v =>
        have hl := lookup_of_concat h ha
        exact ⟨(e.trans hl).symm, by rw [hl]; simp⟩
      | none =>
        exfalso
        have hb : lookup b j ≠ none := fun hb => u ⟨ha, hb⟩
        rcases concat_disj_lookup h' j with x | x
        · exact hb x
        · rw [← lookup_concat_right h ha, ← e] at x; exact hb x

/-- A rule's step (`MCh.Small`) that changes the binding at `k` alone, to a binding, matches and
puts back no other key. -/
theorem MCh.only_of_step {c : MCh M} {L L' : M} {k : K} (sm : c.Small) (st : c.Step L L')
    (hk : lookup L' k ≠ lookup L k) (ho : ∀ j, j ≠ k → lookup L' j = lookup L j)
    (hb : lookup L' k ≠ none) : c.Only k := by
  obtain ⟨a, b, rfl, hs⟩ := MCh.at_of_step st hk ho
  obtain ⟨pre, ap⟩ := st
  refine ⟨a, b, rfl, fun j hj => ?_⟩
  have hbk : lookup b k ≠ none := by
    have e := MCh.lookup_apply pre k
    rw [ap] at e
    by_cases u : lookup a k = none ∧ lookup b k = none
    · rw [ite_eq_left u] at e; exact absurd e hk
    · rw [ite_eq_right u] at e; rw [← e]; exact hb
  have hbj : lookup b j = none := by
    rcases (sm _ rfl).2 with ⟨k', w, e⟩ | e
    · change b = _ at e
      subst e
      by_cases e : k = k'
      · subst e; exact lookup_element_ne hj
      · exact absurd (lookup_element_ne e) hbk
    · change b = _ at e
      subst e; exact lookup_unit
  rcases hs j hj with u | ⟨e, -⟩
  · exact u
  · exact ⟨e.trans hbj, hbj⟩

/-- An insertion `(k ↦ v) L = L'` is at `k`, which `L` does not bind. -/
theorem MCh.fx_ins {c : MCh M} {L L' : M} {k : K} {v : V} (st : c.Step L L')
    (h : concat (element k v) L = some L') : c.At L k ∧ lookup L k = none :=
  have f := ins_facts h
  ⟨MCh.at_of_step st (by rw [f.1, f.2.1]; simp) f.2.2, f.2.1⟩

/-- A rule's insertion (`MCh.Small`) puts back no other key. -/
theorem MCh.only_ins {c : MCh M} {L L' : M} {k : K} {v : V} (sm : c.Small) (st : c.Step L L')
    (h : concat (element k v) L = some L') : c.Only k :=
  have f := ins_facts h
  MCh.only_of_step sm st (by rw [f.1, f.2.1]; simp) f.2.2 (by rw [f.1]; simp)

/-- A rule's removal `(k ↦ v) L' = L` (`MCh.Small`) is at `k` alone. -/
theorem MCh.fx_rem {c : MCh M} {L L' : M} {k : K} {v : V} (sm : c.Small) (st : c.Step L L')
    (h : concat (element k v) L' = some L) : c.At L k ∧ c.Only k := by
  have e := MCh.remove_of st.1 st.2 sm h
  have o : c.Only k := ⟨_, _, e, fun j hj => ⟨lookup_element_ne hj, lookup_unit⟩⟩
  exact ⟨MCh.at_of_only o, o⟩

/-- A rule's replacement of the binding at `k` by another (`(k ↦ v) D = L`, `(k ↦ w) D = L'`,
`v ≠ w`; `MCh.Small`) is at `k` alone. -/
theorem MCh.fx_repl {c : MCh M} {L L' D : M} {k : K} {v w : V} (sm : c.Small) (st : c.Step L L')
    (h : concat (element k v) D = some L) (h' : concat (element k w) D = some L') (hne : w ≠ v) :
    c.At L k ∧ c.Only k := by
  have f := repl_facts h h'
  have o := MCh.only_of_step sm st (by rw [f.1, f.2.1]; simpa using hne) f.2.2 (by rw [f.1]; simp)
  exact ⟨MCh.at_of_only o, o⟩

/-- A read of `i ↦ v` with an insertion of `o ↦ x` beside it (`(i ↦ v) D = L`,
`(i ↦ v) (o ↦ x) = r`, `r D = L'`) is at `o`, which `L` does not bind. -/
theorem MCh.fx_ext {c : MCh M} {L L' D r : M} {i o : K} {v x : V} (st : c.Step L L')
    (h' : concat r D = some L') (h : concat (element i v) D = some L)
    (hp : concat (element i v) (element o x) = some r) : c.At L o ∧ lookup L o = none :=
  have f := ext_facts h hp h'
  ⟨MCh.at_of_step st (by rw [f.1, f.2.1]; simp) f.2.2, f.2.1⟩

/-- Two changes at two different keys commute when neither reads the other's key: the key is not
bound, or the other change is at its own key alone. -/
theorem MCh.compat_at {c₁ c₂ : MCh M} {L : M} {k₁ k₂ : K} (hne : k₁ ≠ k₂) (a₁ : c₁.At L k₁)
    (a₂ : c₂.At L k₂) (f₁ : lookup L k₁ = none ∨ c₂.Only k₂)
    (f₂ : lookup L k₂ = none ∨ c₁.Only k₁) : MCh.Compat c₁ c₂ := by
  obtain ⟨x₁, y₁, rfl, h₁⟩ := a₁
  obtain ⟨x₂, y₂, rfl, h₂⟩ := a₂
  have n₂ : lookup x₂ k₁ = none ∧ lookup y₂ k₁ = none := by
    rcases f₁ with f | ⟨x, y, e, o⟩
    · rcases h₂ k₁ hne with u | ⟨-, u⟩
      · exact u
      · exact absurd f u
    · cases e; exact o k₁ hne
  have n₁ : lookup x₁ k₂ = none ∧ lookup y₁ k₂ = none := by
    rcases f₂ with f | ⟨x, y, e, o⟩
    · rcases h₁ k₂ (Ne.symm hne) with u | ⟨-, u⟩
      · exact u
      · exact absurd f u
    · cases e; exact o k₂ (Ne.symm hne)
  refine Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl, Or.inr (Or.inr fun j => ?_)⟩)
  by_cases j₁ : j = k₁
  · subst j₁; exact Or.inr (Or.inl n₂)
  by_cases j₂ : j = k₂
  · subst j₂; exact Or.inl n₁
  rcases h₁ j j₁ with u | ⟨e₁, -⟩
  · exact Or.inl u
  rcases h₂ j j₂ with u | ⟨e₂, -⟩
  · exact Or.inr (Or.inl u)
  exact Or.inr (Or.inr ⟨e₁, e₂⟩)

theorem MCh.compat_at_ff {c₁ c₂ : MCh M} {L : M} {k₁ k₂ : K} (hne : k₁ ≠ k₂) (a₁ : c₁.At L k₁)
    (a₂ : c₂.At L k₂) (n₁ : lookup L k₁ = none) (n₂ : lookup L k₂ = none) : MCh.Compat c₁ c₂ :=
  MCh.compat_at hne a₁ a₂ (Or.inl n₁) (Or.inl n₂)

theorem MCh.compat_at_fo {c₁ c₂ : MCh M} {L : M} {k₁ k₂ : K} (hne : k₁ ≠ k₂) (a₁ : c₁.At L k₁)
    (a₂ : c₂.At L k₂) (n₁ : lookup L k₁ = none) (o₁ : c₁.Only k₁) : MCh.Compat c₁ c₂ :=
  MCh.compat_at hne a₁ a₂ (Or.inl n₁) (Or.inr o₁)

theorem MCh.compat_at_of {c₁ c₂ : MCh M} {L : M} {k₁ k₂ : K} (hne : k₁ ≠ k₂) (a₁ : c₁.At L k₁)
    (a₂ : c₂.At L k₂) (o₂ : c₂.Only k₂) (n₂ : lookup L k₂ = none) : MCh.Compat c₁ c₂ :=
  MCh.compat_at hne a₁ a₂ (Or.inr o₂) (Or.inl n₂)

theorem MCh.compat_at_oo {c₁ c₂ : MCh M} {L : M} {k₁ k₂ : K} (hne : k₁ ≠ k₂) (a₁ : c₁.At L k₁)
    (a₂ : c₂.At L k₂) (o₂ : c₂.Only k₂) (o₁ : c₁.Only k₁) : MCh.Compat c₁ c₂ :=
  MCh.compat_at hne a₁ a₂ (Or.inr o₂) (Or.inr o₁)

/-! ### A change at several keys

A big step can change a cell holding a map at more than one key: a segment that spends its input
and writes its output removes one binding and adds another (`MCh.fx_move`). `AtL` and `OnlyL` are
`At` and `Only` at a list of keys, and two changes at keys all different commute when neither reads
the other's keys (`MCh.compat_atL`). -/

/-- The change is at the keys `ks`: at every other key of `L` it matches and puts back nothing, or
reads the binding. -/
def MCh.AtL (c : MCh M) (L : M) (ks : List K) : Prop :=
  ∃ a b, c = some (a, b) ∧ ∀ j, j ∉ ks →
    (lookup a j = none ∧ lookup b j = none) ∨ (lookup a j = lookup b j ∧ lookup L j ≠ none)

/-- The change matches and puts back no key outside `ks`. -/
def MCh.OnlyL (c : MCh M) (ks : List K) : Prop :=
  ∃ a b, c = some (a, b) ∧ ∀ j, j ∉ ks → lookup a j = none ∧ lookup b j = none

theorem MCh.atL_of_at {c : MCh M} {L : M} {k : K} (h : c.At L k) : c.AtL L [k] :=
  let ⟨a, b, e, h⟩ := h
  ⟨a, b, e, fun j hj => h j fun e => hj (e ▸ List.mem_singleton_self j)⟩

theorem MCh.onlyL_of_only {c : MCh M} {k : K} (h : c.Only k) : c.OnlyL [k] :=
  let ⟨a, b, e, h⟩ := h
  ⟨a, b, e, fun j hj => h j fun e => hj (e ▸ List.mem_singleton_self j)⟩

theorem MCh.atL_of_onlyL {c : MCh M} (L : M) {ks : List K} (h : c.OnlyL ks) : c.AtL L ks :=
  let ⟨a, b, e, h⟩ := h
  ⟨a, b, e, fun j hj => Or.inl (h j hj)⟩

theorem MCh.fresh_one {L : M} {k : K} (h : lookup L k = none) : ∀ j ∈ [k], lookup L j = none :=
  fun _ hj => (List.mem_singleton.1 hj) ▸ h

/-- A rule's move of a binding to another key (`(k ↦ v) D = L`, `(k' ↦ w) D = L'`, `k ≠ k'`;
`MCh.Small`): it removes `k` and adds `k'`, which `L` does not bind, and touches nothing else. -/
theorem MCh.fx_move {c : MCh M} {L L' D : M} {k k' : K} {v w : V} (sm : c.Small) (st : c.Step L L')
    (h : concat (element k v) D = some L) (h' : concat (element k' w) D = some L') (hne : k ≠ k') :
    c.OnlyL [k, k'] ∧ lookup L k' = none := by
  have hLk : lookup L k = some v := lookup_of_concat_element h
  have hL'k : lookup L' k = none :=
    (lookup_concat_right h' (lookup_element_ne hne)).trans (concat_element_iff.1 h).2.1
  have hLk' : lookup L k' = none :=
    (lookup_concat_right h (lookup_element_ne (Ne.symm hne))).trans (concat_element_iff.1 h').2.1
  have hL'k' : lookup L' k' = some w := lookup_of_concat_element h'
  refine ⟨?_, hLk'⟩
  obtain ⟨pre, ap⟩ := st
  cases c with
  | none =>
    have e : L = L' := ap
    subst e
    rw [hLk] at hL'k
    cases hL'k
  | some p =>
    obtain ⟨a, b⟩ := p
    -- `b` binds `k'`, which `L` does not, and it is one binding (`Small`)
    have hb : lookup b k' ≠ none := by
      have e := MCh.lookup_apply pre k'
      rw [ap, hL'k'] at e
      by_cases u : lookup a k' = none ∧ lookup b k' = none
      · rw [ite_eq_left u, hLk'] at e; cases e
      · rw [ite_eq_right u] at e; rw [← e]; simp
    have hbj : ∀ j, j ≠ k' → lookup b j = none := by
      intro j hj
      rcases (sm _ rfl).2 with ⟨k₀, w₀, eb⟩ | eb
      · change b = _ at eb
        subst eb
        by_cases e0 : k' = k₀
        · subst e0; exact lookup_element_ne hj
        · exact absurd (lookup_element_ne e0) hb
      · change b = _ at eb
        subst eb; exact lookup_unit
    refine ⟨a, b, rfl, fun j hj => ?_⟩
    have hjk : j ≠ k := fun e => hj (e ▸ List.mem_cons_self ..)
    have hjk' : j ≠ k' := fun e => hj (e ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _))
    refine ⟨?_, hbj j hjk'⟩
    -- every other key is kept, so `a` matching it would put it back in `b`, which has none
    cases ha : lookup a j with
    | none => rfl
    | some x =>
      obtain ⟨R, r, hR, hr⟩ := pre _ rfl
      have keep : lookup L' j = lookup L j :=
        (lookup_concat_right h' (lookup_element_ne hjk')).trans
          (lookup_concat_right h (lookup_element_ne hjk)).symm
      have e := MCh.lookup_apply pre j
      rw [ap, keep, lookup_of_concat hR ha, ite_eq_right (by simp [ha]), hbj j hjk'] at e
      cases e

/-- The keys of two changes are all different. -/
abbrev MCh.KeysNe (ks₁ ks₂ : List K) : Prop := ∀ k₁ ∈ ks₁, ∀ k₂ ∈ ks₂, k₁ ≠ k₂

/-- Two changes at keys all different commute when neither reads the other's keys: they are not
bound, or the other change is at its own keys alone. -/
theorem MCh.compat_atL {c₁ c₂ : MCh M} {L : M} {ks₁ ks₂ : List K} (hne : MCh.KeysNe ks₁ ks₂)
    (a₁ : c₁.AtL L ks₁) (a₂ : c₂.AtL L ks₂) (f₁ : (∀ k ∈ ks₁, lookup L k = none) ∨ c₂.OnlyL ks₂)
    (f₂ : (∀ k ∈ ks₂, lookup L k = none) ∨ c₁.OnlyL ks₁) : MCh.Compat c₁ c₂ := by
  obtain ⟨x₁, y₁, rfl, h₁⟩ := a₁
  obtain ⟨x₂, y₂, rfl, h₂⟩ := a₂
  have n₂ : ∀ k ∈ ks₁, lookup x₂ k = none ∧ lookup y₂ k = none := by
    intro k hk
    have hk₂ : k ∉ ks₂ := fun m => hne k hk k m rfl
    rcases f₁ with f | ⟨x, y, e, o⟩
    · rcases h₂ k hk₂ with u | ⟨-, u⟩
      · exact u
      · exact absurd (f k hk) u
    · cases e; exact o k hk₂
  have n₁ : ∀ k ∈ ks₂, lookup x₁ k = none ∧ lookup y₁ k = none := by
    intro k hk
    have hk₁ : k ∉ ks₁ := fun m => hne k m k hk rfl
    rcases f₂ with f | ⟨x, y, e, o⟩
    · rcases h₁ k hk₁ with u | ⟨-, u⟩
      · exact u
      · exact absurd (f k hk) u
    · cases e; exact o k hk₁
  refine Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl, Or.inr (Or.inr fun j => ?_)⟩)
  by_cases j₁ : j ∈ ks₁
  · exact Or.inr (Or.inl (n₂ j j₁))
  by_cases j₂ : j ∈ ks₂
  · exact Or.inl (n₁ j j₂)
  rcases h₁ j j₁ with u | ⟨e₁, -⟩
  · exact Or.inl u
  rcases h₂ j j₂ with u | ⟨e₂, -⟩
  · exact Or.inr (Or.inl u)
  exact Or.inr (Or.inr ⟨e₁, e₂⟩)

theorem MCh.compat_atL_ff {c₁ c₂ : MCh M} {L : M} {ks₁ ks₂ : List K} (hne : MCh.KeysNe ks₁ ks₂)
    (a₁ : c₁.AtL L ks₁) (a₂ : c₂.AtL L ks₂) (n₁ : ∀ k ∈ ks₁, lookup L k = none)
    (n₂ : ∀ k ∈ ks₂, lookup L k = none) : MCh.Compat c₁ c₂ :=
  MCh.compat_atL hne a₁ a₂ (Or.inl n₁) (Or.inl n₂)

theorem MCh.compat_atL_fo {c₁ c₂ : MCh M} {L : M} {ks₁ ks₂ : List K} (hne : MCh.KeysNe ks₁ ks₂)
    (a₁ : c₁.AtL L ks₁) (a₂ : c₂.AtL L ks₂) (n₁ : ∀ k ∈ ks₁, lookup L k = none)
    (o₁ : c₁.OnlyL ks₁) : MCh.Compat c₁ c₂ :=
  MCh.compat_atL hne a₁ a₂ (Or.inl n₁) (Or.inr o₁)

theorem MCh.compat_atL_of {c₁ c₂ : MCh M} {L : M} {ks₁ ks₂ : List K} (hne : MCh.KeysNe ks₁ ks₂)
    (a₁ : c₁.AtL L ks₁) (a₂ : c₂.AtL L ks₂) (o₂ : c₂.OnlyL ks₂)
    (n₂ : ∀ k ∈ ks₂, lookup L k = none) : MCh.Compat c₁ c₂ :=
  MCh.compat_atL hne a₁ a₂ (Or.inr o₂) (Or.inl n₂)

theorem MCh.compat_atL_oo {c₁ c₂ : MCh M} {L : M} {ks₁ ks₂ : List K} (hne : MCh.KeysNe ks₁ ks₂)
    (a₁ : c₁.AtL L ks₁) (a₂ : c₂.AtL L ks₂) (o₂ : c₂.OnlyL ks₂) (o₁ : c₁.OnlyL ks₁) :
    MCh.Compat c₁ c₂ :=
  MCh.compat_atL hne a₁ a₂ (Or.inr o₂) (Or.inr o₁)

end MCh

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

namespace KPrelude

open Lean Meta Elab Tactic

/-! ## `k2l_det`: what two instances at one configuration determine twice

Two steps from one configuration whose rules match it alike, with the same values of the same
calls, are one step: their instances agree. `k2l_det` unifies, until nothing changes, the values
of two hypotheses `e = some x` and `e = some y` (one call at the same arguments, or one key of one
map), and the rests of two matches `concat a R = some m` and `concat a R' = some m` of one part of
one map; it first states, for each match, the bindings it puts in the map (`lookup m k = some v`).
It is the determinism of one process, the same-thread joins of `confluence --threads --slots`. -/

/-- The sides `e` and `x` of a hypothesis `e = some x`. -/
def detSome? (t : Expr) : MetaM (Option (Expr × Expr)) := do
  let t ← instantiateMVars t
  let some (_, l, r) := t.eq? | return none
  if r.isAppOfArity ``Option.some 2 then return some (l, r.appArg!) else return none

/-- The last two arguments of an application of `c`. -/
def detArgs2? (c : Name) (e : Expr) : Option (Expr × Expr) :=
  if e.getAppFn.constName? == some c && e.getAppNumArgs ≥ 2 then
    let as := e.getAppArgs
    some (as[as.size - 2]!, as[as.size - 1]!)
  else none

/-- Add the hypothesis `p` unless one of its type is there. -/
def detAdd (g : MVarId) (p : Expr) : MetaM (Option MVarId) := g.withContext do
  let ty ← instantiateMVars (← inferType p)
  for d in ← getLCtx do
    if !d.isImplementationDetail && (← instantiateMVars d.type) == ty then return none
  let g ← g.assert `k2l_lk ty p
  let (_, g) ← g.intro1
  return some g

/-- One binding a match puts in its map: `lookup m k = some v` from `concat a R = some m`, with
`a` a binding `element k v` or binding `k` (`lookup a k = some v`), or `R` binding it. -/
def detLookup (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let mut cs : Array (Expr × Expr × Expr) := #[]
  let mut ls : Array (Expr × Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some (e, _) ← detSome? d.type then
      if let some (a, r) := detArgs2? ``MapHook.concat e then cs := cs.push (d.toExpr, a, r)
      if let some (m, _) := detArgs2? ``MapHook.lookup e then ls := ls.push (d.toExpr, m, e)
  for (h, a, r) in cs do
    if (detArgs2? ``MapHook.element a).isSome then
      if let some g' ← detAdd g (← mkAppM ``MapHook.lookup_of_concat_element #[h]) then return some g'
      let f ← mkAppM ``MapHook.ins_facts #[h]
      if let some g' ← detAdd g (← mkAppM ``And.left #[← mkAppM ``And.right #[f]]) then return some g'
    if (detArgs2? ``MapHook.element r).isSome then
      if let some g' ← detAdd g (← mkAppM ``MapHook.lookup_of_concat_element_right #[h]) then
        return some g'
    for (hl, x, _) in ls do
      if x == a then
        if let some g' ← detAdd g (← mkAppM ``MapHook.lookup_of_concat #[h, hl]) then return some g'
      if x == r then
        if let some g' ← detAdd g (← mkAppM ``MapHook.lookup_of_concat_right #[h, hl]) then return some g'
  return none

/-- Case on the equation `p` in `g`; `none` when its sides do not unify by `cases`. -/
def detCases (g : MVarId) (p : Expr) : MetaM (Option (Array MVarId)) := do
  let s ← saveState
  try
    let g ← g.assert `k2l_det (← inferType p) p
    let (h, g) ← g.intro1
    let gs ← g.cases h
    return some (gs.map (·.mvarId))
  catch _ =>
    s.restore
    return none

/-- One unification: two hypotheses `e = some x` and `e = some y` give `x = y`; two matches
`concat a R = some m` and `concat a R' = some m` give `R = R'`; `e = none` and `e = some x`
clash. -/
def detStep (g : MVarId) : MetaM (Option (Array MVarId)) := g.withContext do
  let mut facts : Array (Expr × Expr × Expr) := #[]
  let mut nones : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some (e, x) ← detSome? d.type then
      facts := facts.push (d.toExpr, e, x)
    else if let some (_, l, r) := (← instantiateMVars d.type).eq? then
      if r.isAppOf ``Option.none then nones := nones.push (d.toExpr, l)
  for (h₁, e₁) in nones do
    for (h₂, e₂, _) in facts do
      if ← withReducible (isDefEq e₁ e₂) then
        if let some gs ← detCases g (← mkEqTrans (← mkEqSymm h₁) h₂) then return some gs
  for i in [0:facts.size] do
    for j in [i+1:facts.size] do
      let (h₁, e₁, x₁) := facts[i]!
      let (h₂, e₂, x₂) := facts[j]!
      if x₁ != x₂ && (← withReducible (isDefEq e₁ e₂)) then
        let p ← mkAppM ``Option.some.inj #[← mkEqTrans (← mkEqSymm h₁) h₂]
        if let some gs ← detCases g p then return some gs
      if x₁ == x₂ then
        if let (some (a₁, r₁), some (a₂, r₂)) := (detArgs2? ``MapHook.concat e₁, detArgs2? ``MapHook.concat e₂) then
          if r₁ != r₂ && a₁ == a₂ then
            if let some gs ← detCases g (← mkAppM ``MapHook.concat_rest_unique #[h₁, h₂]) then
              return some gs
  return none

/-- Unify what two instances at one configuration determine twice (see above), until nothing
changes. -/
elab "k2l_det" : tactic => do
  for _ in [0:2000] do
    match ← getGoals with
    | [] => return
    | g :: rest =>
      if let some g' ← detLookup g then
        setGoals (g' :: rest)
      else match ← detStep g with
        | some gs => setGoals (gs.toList ++ rest)
        | none => return

/-- Each hypothesis `a = some v`, `v` a variable, whose `a` computes to `some u` (a sort projection
of an injection, `proj_KItem_Exp (inj_Id X) = some HOLE`, which a cooling rule's match states):
`v` replaced by `u`, so that a side condition on `v` (`isKResult(HOLE)`) can compute
(`k2l_refute_computed`). Each replacement is `subst` of `Option.some.inj`; it never fails. -/
elab "k2l_proj_compute" : tactic => do
  for _ in [0:2000] do
    let g ← getMainGoal
    let step ← g.withContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let some (_, a, b) := (← instantiateMVars d.type).consumeMData.eq? | continue
        unless b.isAppOfArity ``Option.some 2 && b.appArg!.isFVar do continue
        let v := b.appArg!
        let r ← withDefault <| whnf a
        unless r.isAppOfArity ``Option.some 2 do continue
        if r.appArg!.containsFVar v.fvarId! then continue
        let hb ← mkExpectedTypeHint (← mkEqSymm d.toExpr) (← mkEq b r)
        let (h, g₁) ← (← g.assert `k2l_pc (← mkEq v r.appArg!) (← mkAppM ``Option.some.inj #[hb])).intro1P
        try return some (← subst g₁ h) catch _ => continue
      return none
    match step with
    | some g' => replaceMainGoal [g']
    | none => return

namespace IntHook

/-! A value a step adds a nonzero constant to changes (`k2l_ne`); stated over `Int`, they apply to
a library's integer sort, which reduces to it. -/

theorem add_eq_self_iff {a b : Int} : add a b = a ↔ b = 0 := by simp only [add]; omega
theorem self_eq_add_iff {a b : Int} : a = add a b ↔ b = 0 := by simp only [add]; omega
theorem sub_eq_self_iff {a b : Int} : sub a b = a ↔ b = 0 := by simp only [sub]; omega
theorem self_eq_sub_iff {a b : Int} : a = sub a b ↔ b = 0 := by simp only [sub]; omega

end IntHook

/-- Two values that differ: by constructors, by hook arithmetic (`N +Int 1 ≠ N`), or by a term
inside itself (`sizeOf`). Each alternative closes the goal or fails. -/
syntax "k2l_ne" : tactic
macro_rules
  | `(tactic| k2l_ne) => `(tactic| first
    | (simp; done)
    | (intro h; cases h; done)
    | (simp; intro h; cases h; done)
    | (simp; intro _ h; cases h; done)
    | (simp [KPrelude.IntHook.add_eq_self_iff, KPrelude.IntHook.self_eq_add_iff,
        KPrelude.IntHook.sub_eq_self_iff, KPrelude.IntHook.self_eq_sub_iff]; done)
    | (intro h; have := congrArg sizeOf h; simp at this; omega))

/-! ## `k2l_keyed`: two changes of cells holding a map, at their keys

For `hk : ¬ ch₁.KCompat ch₂`, the changes of two steps from one configuration at the cells holding
a map: per cell, a change is `none` (a hypothesis `ch.f = none`, of the rule's class), or at the
keys its rule's match fixes (`MCh.fx_ins`, `only_ins`, `fx_rem`, `fx_repl` with `k2l_ne`, `fx_ext`
at one key; `fx_move` at two, told apart by `k2l_ne` or by a requirement `A =/=K B` of the rule;
from a hypothesis `MCh.Step ch.f L L'` and the match, found up to reducible unfolding: `L` and `L'`
as the matches state them). Per cell where both are at keys, it cases on every pair of keys: equal,
`cases` on the equation, then `k2l_det`, the goals left to the caller; all different, `hk` is
refuted by `MCh.compat_atL`. It fails when a change's keys are not found, or two changes' keys do
not show that neither change reads the other's. -/

/-- The parts of a conjunction, with their proofs from `p`. -/
partial def keyedParts (p ty : Expr) : MetaM (Array (Expr × Expr)) := do
  let ty ← instantiateMVars ty
  if ty.isAppOfArity ``And 2 then
    return (← keyedParts (← mkAppM ``And.left #[p]) ty.appFn!.appArg!) ++
      (← keyedParts (← mkAppM ``And.right #[p]) ty.appArg!)
  return #[(p, ty)]

/-- The hypotheses, conjunctions split. -/
def keyedHyps : MetaM (Array (Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    out := out ++ (← keyedParts d.toExpr d.type)
  return out

/-- A rule's requirement `A =/=K B` tells `A` and `B` apart. -/
theorem KEqHook.ne_true {α : Type} [DecidableEq α] {a b : α} (h : KEqHook.ne a b = true) : a ≠ b := by
  simpa [KEqHook.ne] using h

/-- Whether `k2l_ne` closes the goal `g`, or a requirement `A =/=K B` among the hypotheses does: a
goal `x ≠ y` where `A` becomes `B` once `x` is rewritten to `y`. -/
def keyedNe (g : MVarId) (hyps : Array (Expr × Expr) := #[]) : TacticM Bool := do
  let s ← saveState
  try
    let gs ← Tactic.run g (evalTactic (← `(tactic| k2l_ne)))
    if gs.isEmpty then return true
    s.restore
  catch _ =>
    s.restore
  for (p, ty) in hyps do
    let some (_, l, r) := ty.eq? | continue
    unless l.isAppOf ``KEqHook.ne && r.isConstOf ``Bool.true do continue
    let s ← saveState
    try
      let gs ← Tactic.run g do
        evalTactic (← `(tactic| intro k2l_h))
        let g' ← getMainGoal
        let gs' ← g'.apply (← mkAppM ``KEqHook.ne_true #[p])
        setGoals gs'
        evalTactic (← `(tactic| rw [k2l_h]))
      if gs.isEmpty then return true
      s.restore
    catch _ =>
      s.restore
  return false

/-- Whether the hypothesis type `h` may be an instance of the pattern `t` (`concat a R = some m`):
their parts the pattern fixes already are the same. -/
def keyedQuick (h t : Expr) : MetaM Bool := do
  let t ← instantiateMVars t
  let (some (_, hl, hr), some (_, tl, tr)) := (h.eq?, t.eq?) | return true
  let same (x y : Expr) := y.hasMVar || x == y
  unless same hr tr do return false
  match detArgs2? ``MapHook.concat hl, detArgs2? ``MapHook.concat tl with
  | some (ha, hR), some (ta, tR) => return same ha ta && same hR tR
  | _, _ => return true

/-- Fill the explicit arguments `is` of a lemma: a hypothesis of each one's type, or `k2l_ne` for
an inequation, in order, backtracking. -/
partial def keyedFill (ms : Array Expr) (hyps : Array (Expr × Expr)) : List Nat → TacticM Bool
  | [] => return true
  | i :: rest => do
    let m := ms[i]!
    if (← instantiateMVars m).isMVar then
      let ty ← instantiateMVars (← inferType m)
      if ty.isAppOfArity ``Ne 3 then
        let g ← mkFreshExprMVar ty
        return (← keyedNe g.mvarId! hyps) && (← isDefEq m g) && (← keyedFill ms hyps rest)
      for (p, pty) in hyps do
        unless pty.getAppFn == ty.getAppFn && (← keyedQuick pty ty) do continue
        let s ← (Meta.saveState : MetaM _)
        if (← withReducible (isDefEq pty ty)) && (← isDefEq m p) then
          if ← keyedFill ms hyps rest then return true
        s.restore
      return false
    else keyedFill ms hyps rest

/-- `lem` at the step `st` (its argument `MCh.Step _ _ _`) and hypotheses for its other explicit
arguments. -/
def keyedApply (lem : Name) (st : Expr) (hyps : Array (Expr × Expr)) : TacticM (Option Expr) := do
  let s ← saveState
  try
    let c ← mkConstWithFreshMVarLevels lem
    let (ms, bis, _) ← forallMetaTelescopeReducing (← inferType c)
    let mut ex : Array Nat := #[]
    for i in [0:ms.size] do
      if bis[i]! == .default then
        if (← instantiateMVars (← inferType ms[i]!)).isAppOf ``MCh.Step then
          unless ← withReducible (isDefEq ms[i]! st) do
            s.restore
            return none
        else ex := ex.push i
    unless ← keyedFill ms hyps ex.toList do
      s.restore
      return none
    for i in [0:ms.size] do
      if bis[i]! == .instImplicit && (← instantiateMVars ms[i]!).isMVar then
        unless ← isDefEq ms[i]! (← synthInstance (← inferType ms[i]!)) do
          s.restore
          return none
    let e ← instantiateMVars (mkAppN c ms)
    if e.hasMVar then
      s.restore
      return none
    return some e
  catch _ =>
    s.restore
    return none

/-- What `k2l_keyed` knows of a change at its keys: `AtL` (with the keys), and when found, that the
keys are not bound before, and that the change is at them alone; `facts`, the keys it knows are not
bound, for `k2l_det`. -/
structure KeyedFx where
  atP : Expr
  keys : List Expr
  fresh : Option Expr
  only : Option Expr
  facts : Array Expr

/-- A proof of `x = none` among the hypotheses. -/
def keyedNone (x : Expr) (hyps : Array (Expr × Expr)) : MetaM (Option Expr) := do
  for (p, ty) in hyps do
    if let some (_, l, r) := ty.eq? then
      if r.isAppOf ``Option.none && (← withReducible (isDefEq l x)) then return some p
  return none

/-- The keys the change `x` is at, from its step and the match of its rule. -/
def keyedFx (x : Expr) (hyps : Array (Expr × Expr)) : TacticM (Option KeyedFx) := do
  let mut fx : Option KeyedFx := none
  for (st, ty) in hyps do
    unless ty.isAppOf ``MCh.Step do continue
    let as := ty.getAppArgs
    unless ← withReducible (isDefEq as[as.size - 3]! x) do continue
    let L := as[as.size - 2]!
    let mut atP : Option (Expr × List Expr) := none
    let mut only : Option Expr := none
    let mut facts : Array Expr := #[]
    for lem in [``MCh.fx_ins, ``MCh.only_ins, ``MCh.fx_rem, ``MCh.fx_repl, ``MCh.fx_ext, ``MCh.fx_move] do
      let some e ← keyedApply lem st hyps | continue
      for (p, pty) in ← keyedParts e (← inferType e) do
        if pty.isAppOf ``MCh.At then
          if atP.isNone then atP := some (← mkAppM ``MCh.atL_of_at #[p], [pty.getAppArgs.back!])
        else if pty.isAppOf ``MCh.Only then
          if only.isNone then only := some (← mkAppM ``MCh.onlyL_of_only #[p])
        else if pty.isAppOf ``MCh.OnlyL then
          if only.isNone then only := some p
          if atP.isNone then
            if let some (_, ks) := (← instantiateMVars pty.getAppArgs.back!).listLit? then
              atP := some (← mkAppM ``MCh.atL_of_onlyL #[L, p], ks)
        else facts := facts.push p
    if let some (p, ks) := atP then
      -- a change at one key that knows it unbound is fresh at all its keys
      let fresh ← match ks, facts.toList with
        | [_], n :: _ => some <$> mkAppM ``MCh.fresh_one #[n]
        | _, _ => pure none
      fx := some { atP := p, keys := ks, fresh, only, facts }
      break
  return fx

/-- The commutation of `x` at `f₁`'s keys and `y` at `f₂`'s, by what each knows, with the keys told
apart by the hypotheses `kᵢ ≠ kⱼ` of the goal's context. -/
def keyedCompat (f₁ f₂ : KeyedFx) : TacticM Expr := do
  let some k := f₁.keys.head? | throwError "k2l_keyed: a change at no key"
  let kTy ← inferType k
  let hne ← mkFreshExprMVar (← mkAppM ``MCh.KeysNe #[← mkListLit kTy f₁.keys, ← mkListLit kTy f₂.keys])
  let e ← match f₁.fresh, f₂.only, f₂.fresh, f₁.only with
    | some n₁, _, some n₂, _ => mkAppM ``MCh.compat_atL_ff #[hne, f₁.atP, f₂.atP, n₁, n₂]
    | some n₁, _, _, some o₁ => mkAppM ``MCh.compat_atL_fo #[hne, f₁.atP, f₂.atP, n₁, o₁]
    | _, some o₂, some n₂, _ => mkAppM ``MCh.compat_atL_of #[hne, f₁.atP, f₂.atP, o₂, n₂]
    | _, some o₂, _, some o₁ => mkAppM ``MCh.compat_atL_oo #[hne, f₁.atP, f₂.atP, o₂, o₁]
    | _, _, _, _ => throwError "k2l_keyed: a change may read the key of the other"
  let gs ← Tactic.run hne.mvarId! (evalTactic (← `(tactic|
    (intro k₁ h₁ k₂ h₂
     simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h₁ h₂
     (try cases h₁) <;> (try cases h₂) <;> (try subst k₁) <;> (try subst k₂) <;> assumption))))
  unless gs.isEmpty do throwError "k2l_keyed: the keys are not told apart"
  instantiateMVars e

/-- The parts of a conjunction, nested to the right. -/
partial def keyedConj (t : Expr) : List Expr :=
  if t.isAppOfArity ``And 2 then t.appFn!.appArg! :: keyedConj t.appArg! else [t]

/-- A conjunction of the proofs `ps`, nested to the right. -/
def keyedAnd : List Expr → MetaM Expr
  | [] => return mkConst ``True.intro
  | [p] => return p
  | p :: ps => do mkAppM ``And.intro #[p, ← keyedAnd ps]

/-- See above. -/
elab "k2l_keyed " hk:ident : tactic => withMainContext do
  let hkE := (← getLocalDeclFromUserName hk.getId).toExpr
  let hkTy ← instantiateMVars (← inferType hkE)
  unless hkTy.isAppOfArity ``Not 1 do throwError "k2l_keyed: {hk} is not a negation"
  let kTy := hkTy.appArg!
  let some body ← unfoldDefinition? kTy | throwError "k2l_keyed: cannot unfold {kTy}"
  let body := body.headBeta
  let hyps ← keyedHyps
  -- per cell: a proof at once, or the two changes at their keys
  let mut cells : Array (Option Expr × Option (KeyedFx × KeyedFx)) := #[]
  for t in keyedConj body do
    unless t.isAppOf ``MCh.Compat do throwError "k2l_keyed: {t} is not MCh.Compat"
    let as := t.getAppArgs
    let x := as[as.size - 2]!
    let y := as[as.size - 1]!
    -- `MCh.Compat x y` is `x = none ∨ y = none ∨ …`
    let u ← whnfD t
    let (a, b) := (u.appFn!.appArg!, u.appArg!)
    if let some p ← keyedNone x hyps then
      cells := cells.push (some (← mkAppOptM ``Or.inl #[a, b, p]), none)
    else if let some p ← keyedNone y hyps then
      let (b₁, b₂) := (b.appFn!.appArg!, b.appArg!)
      cells := cells.push (some (← mkAppOptM ``Or.inr #[a, b, ← mkAppOptM ``Or.inl #[b₁, b₂, p]]), none)
    else
      let some f₁ ← keyedFx x hyps | throwError "k2l_keyed: no key for {x}"
      let some f₂ ← keyedFx y hyps | throwError "k2l_keyed: no key for {y}"
      cells := cells.push (none, some (f₁, f₂))
  -- the facts that a key is not bound, as hypotheses for `k2l_det`
  let mut g ← getMainGoal
  for (_, f) in cells do
    if let some (f₁, f₂) := f then
      for p in f₁.facts ++ f₂.facts do
        if let some g' ← detAdd g p then g := g'
  let mut left : List MVarId := []
  let mut proofs : Array Expr := #[]
  for (p, f) in cells do
    match p, f with
    | some p, _ => proofs := proofs.push p
    | none, some (f₁, f₂) =>
      for k₁ in f₁.keys do
        for k₂ in f₂.keys do
          let (pos, neg) ← g.withContext do g.byCases (← mkEq k₁ k₂) `k2l_kk
          setGoals [pos.mvarId]
          let kk := mkIdent `k2l_kk
          evalTactic (← `(tactic| (first | (cases $kk:ident) | (subst $kk:ident) | skip); k2l_det))
          left := left ++ (← getGoals)
          g := neg.mvarId
      proofs := proofs.push (← g.withContext (keyedCompat f₁ f₂))
    | none, none => pure ()
  g.withContext do
    let prf ← keyedAnd proofs.toList
    g.assign (← mkAppOptM ``absurd #[kTy, ← g.getType, prf, hkE])
  setGoals left

end KPrelude
