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
  extensionality of canonical maps (`SAL.ext`).
- **Two runs** (`k2lean noninterference`): a relation on pairs of states from which, unless both
  are final, one side can be advanced by any of its steps without leaving the relation
  (`ProductInv`) relates the final states of any two runs from related states.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

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

end MapHook

end KPrelude
