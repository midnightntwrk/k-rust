/-
  EXPERIMENT. Not part of the library and not a test of it: nothing imports this file, it imports
  nothing, and it changes nothing KCore states. Findings: `../../../findings/OD7-blocking.md`.
  Run from the package root: `lake env lean test/experiments/BlockingNoResult.lean`.

  Question. A rewrite rule A matches a configuration, its `requires` is `true`, and its right side
  has no value (or its `ensures` is not true). Does A block a rule B of a larger priority number that
  matches the same configuration?

  - **R-block** (KCore today, `Step.lean`): yes. `NotApplies` reads A's left side and `requires`
    only; Γ's rule axiom carries `⌈rhs⌉` in its premise.
  - **R-skip**: no. A does not apply where its right side has no value, so B fires; the negated
    competitor in B's axiom must then mention A's right side's definedness.

  The model. Three configurations `a`, `b`, `c`. Rule A (priority 10): `a ⇒ b requires Q`, its right
  side defined or not (`Defn.defA`; an undefined right side is a term with no value, e.g. a partial
  function off its domain). Rule B (priority 20, present or not, `Defn.hasB`): `a ⇒ c`. A matching
  logic model of the step axioms is a transition relation `R` (the interpretation of `•`): `x ∈ •ψ`
  iff some successor of `x` is in `ψ`. A pattern is a set of configurations (`Pat`); in KCore's value
  models a term denotes at most one element, and `⌈φ⌉` is the whole carrier or empty (a `Prop`).

  Each reading's theory (`Theory θ d`) has A's axiom `appA ∧ ⌈rhsA⌉ → •rhsA`, B's axiom
  `a ∧ ¬comp → •c` with the reading's negated competitor `comp`, and the step's closure axiom (the
  successors are only those the two axioms give), as Γ and `Γstep` do in the library. Each reading's
  step relation (`Step θ d`) has KCore's shape: A where it matches, its `requires` holds and its right
  side has a value; B where A does not apply (`NotApplies θ d`).

  Section 1: both readings admit a sound and complete step relation, unique. Section 2: what each
  theory asserts beyond the text (kompile's KORE: `\rewrites(L ∧ Q, R)` per rule, priority as an
  attribute only, no competitor). Section 3: which competitor shape each needs. Section 4: N/U
  (no rule applies / a rule applies with no result). Section 5: `ensures`. Section 6: functions,
  where kompile does write the competitor (`[owise]` equation: `¬ ∃ (lhs' ∧ req')`).
-/

set_option autoImplicit false

namespace BlockingNoResult

inductive Cfg where
  | a
  | b
  | c
  deriving DecidableEq

/-- A pattern's denotation in the model: a set of configurations. -/
abbrev Pat := Cfg → Prop

/-- `⌈φ⌉`: φ is not empty (as a pattern, the whole carrier or empty). -/
abbrev Ceil (P : Pat) : Prop := ∃ y, P y

/-- `•ψ` in the model `R`: the configurations with a successor in ψ. -/
abbrev Next (R : Cfg → Cfg → Prop) (P : Pat) : Pat := fun x => ∃ y, P y ∧ R x y

/-- The axiom `φ → •ψ` holds in the model `R`. -/
abbrev Valid (R : Cfg → Cfg → Prop) (φ ψ : Pat) : Prop := ∀ x, φ x → Next R ψ x

/-- The toy definition: A's `requires` at `a`, whether A's right side has a value, whether B is
present. -/
structure Defn where
  q : Bool
  defA : Bool
  hasB : Bool

/-- A's right side: `b` where it has a value, nothing elsewhere. -/
abbrev rhsA (d : Defn) : Pat := fun y => d.defA = true ∧ y = .b

/-- B's right side. -/
abbrev rhsB : Pat := fun y => y = .c

/-- A's left side and `requires`: `a ∧ ⌈Q = true⌉` (kompile's left side of A's `\rewrites`). -/
abbrev appA (d : Defn) : Pat := fun x => x = .a ∧ d.q = true

/-- The premise of A's own axiom: its left side, `requires`, and `⌈rhs⌉`. -/
abbrev premA (d : Defn) : Pat := fun x => appA d x ∧ Ceil (rhsA d)

theorem ceil_rhsA (d : Defn) : Ceil (rhsA d) ↔ d.defA = true :=
  ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨.b, h, rfl⟩⟩

/-- The premise of B's axiom with the negated competitor `C`. -/
abbrev premB (C : Pat) (d : Defn) : Pat := fun x => d.hasB = true ∧ x = .a ∧ ¬ C x

/-- The step's closure axiom: every successor is given by A's or B's axiom. -/
abbrev Closure (C : Pat) (d : Defn) (R : Cfg → Cfg → Prop) : Prop :=
  ∀ x y, R x y → (premA d x ∧ rhsA d y) ∨ (premB C d x ∧ rhsB y)

/-- The theory with competitor `C`: A's axiom, B's axiom, the closure. -/
abbrev TheoryC (C : Pat) (d : Defn) (R : Cfg → Cfg → Prop) : Prop :=
  Valid R (premA d) (rhsA d) ∧ Valid R (premB C d) rhsB ∧ Closure C d R

/-- The step relation of the theory with competitor `C`. -/
inductive StepC (C : Pat) (d : Defn) : Cfg → Cfg → Prop
  | rA (hq : d.q = true) (hd : d.defA = true) : StepC C d .a .b
  | rB (hb : d.hasB = true) (hn : ¬ C .a) : StepC C d .a .c

/-- Every model of the theory has exactly `StepC`'s successors. -/
theorem theoryC_iff {C : Pat} {d : Defn} {R : Cfg → Cfg → Prop} (h : TheoryC C d R) (x y : Cfg) :
    R x y ↔ StepC C d x y := by
  obtain ⟨hA, hB, hcl⟩ := h
  constructor
  · intro hr
    rcases hcl x y hr with ⟨⟨⟨rfl, hq⟩, _⟩, hd, rfl⟩ | ⟨⟨hb, rfl, hn⟩, rfl⟩
    · exact .rA hq hd
    · exact .rB hb hn
  · intro hs
    cases hs with
    | rA hq hd =>
      obtain ⟨_, ⟨_, rfl⟩, hr⟩ := hA .a ⟨⟨rfl, hq⟩, ⟨.b, hd, rfl⟩⟩
      exact hr
    | rB hb hn =>
      obtain ⟨_, rfl, hr⟩ := hB .a ⟨hb, rfl, hn⟩
      exact hr

/-- `StepC` is a model of the theory. -/
theorem theoryC_model (C : Pat) (d : Defn) : TheoryC C d (StepC C d) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨⟨rfl, hq⟩, hc⟩
    exact ⟨.b, ⟨(ceil_rhsA d).mp hc, rfl⟩, .rA hq ((ceil_rhsA d).mp hc)⟩
  · rintro x ⟨hb, rfl, hn⟩
    exact ⟨.c, rfl, .rB hb hn⟩
  · intro x y hs
    cases hs with
    | rA hq hd => exact .inl ⟨⟨⟨rfl, hq⟩, ⟨.b, hd, rfl⟩⟩, hd, rfl⟩
    | rB hb hn => exact .inr ⟨⟨hb, rfl, hn⟩, rfl⟩

/-! ## 1. The two readings: each has a sound and complete step relation -/

inductive Reading where
  | block
  | skip

/-- The negated competitor in B's axiom. R-block: A's left side and `requires` (the left side of
A's `\rewrites`). R-skip: also `⌈rhsA⌉`. -/
abbrev comp : Reading → Defn → Pat
  | .block, d => appA d
  | .skip, d => fun x => appA d x ∧ Ceil (rhsA d)

/-- KCore-style `NotApplies` for A at `a`. R-block reads the `requires` only (A's left side matches
`a`); R-skip reads the right side too. -/
abbrev NotApplies : Reading → Defn → Prop
  | .block, d => d.q ≠ true
  | .skip, d => d.q ≠ true ∨ d.defA ≠ true

/-- KCore-style step: A where it matches, its `requires` evaluates to `true` and its right side has a
value (A has the smallest priority number, so no `hprio`); B where A does not apply. -/
inductive Step (θ : Reading) (d : Defn) : Cfg → Cfg → Prop
  | rA (hq : d.q = true) (hd : d.defA = true) : Step θ d .a .b
  | rB (hb : d.hasB = true) (hn : NotApplies θ d) : Step θ d .a .c

/-- Each reading's theory. -/
abbrev Theory (θ : Reading) (d : Defn) : (Cfg → Cfg → Prop) → Prop := TheoryC (comp θ d) d

theorem notApplies_iff (θ : Reading) (d : Defn) : NotApplies θ d ↔ ¬ comp θ d .a := by
  cases θ <;> rcases d with ⟨q, dA, hb⟩ <;> cases q <;> cases dA <;> simp [NotApplies, comp]

theorem step_iff_stepC (θ : Reading) (d : Defn) (x y : Cfg) :
    Step θ d x y ↔ StepC (comp θ d) d x y := by
  constructor
  · intro h; cases h with
    | rA hq hd => exact .rA hq hd
    | rB hb hn => exact .rB hb ((notApplies_iff θ d).mp hn)
  · intro h; cases h with
    | rA hq hd => exact .rA hq hd
    | rB hb hn => exact .rB hb ((notApplies_iff θ d).mpr hn)

/-- Soundness: every step holds in every model of the theory. -/
def Sound (θ : Reading) (d : Defn) (S : Cfg → Cfg → Prop) : Prop :=
  ∀ x y, S x y → ∀ R, Theory θ d R → R x y

/-- Completeness: every successor in every model is a step. -/
def Complete (θ : Reading) (d : Defn) (S : Cfg → Cfg → Prop) : Prop :=
  ∀ R, Theory θ d R → ∀ x y, R x y → S x y

/-- **Each reading's theory has a model**, for every toy definition. -/
theorem theory_model (θ : Reading) (d : Defn) : ∃ R, Theory θ d R :=
  ⟨_, theoryC_model (comp θ d) d⟩

/-- **Each reading's step is sound and complete for its theory**, for every toy definition. -/
theorem sound_complete (θ : Reading) (d : Defn) : Sound θ d (Step θ d) ∧ Complete θ d (Step θ d) :=
  ⟨fun x y hs _ hR => (theoryC_iff hR x y).mpr ((step_iff_stepC θ d x y).mp hs),
   fun _ hR x y hr => (step_iff_stepC θ d x y).mpr ((theoryC_iff hR x y).mp hr)⟩

/-- … and it is the only one: a sound and complete relation is `Step θ d`. -/
theorem sound_complete_unique (θ : Reading) (d : Defn) (S : Cfg → Cfg → Prop)
    (hs : Sound θ d S) (hc : Complete θ d S) (x y : Cfg) : S x y ↔ Step θ d x y := by
  have hm := theoryC_model (comp θ d) d
  constructor
  · intro h; exact (step_iff_stepC θ d x y).mpr (hs x y h _ hm)
  · intro h; exact hc _ hm x y ((step_iff_stepC θ d x y).mp h)

/-- The configuration in question: A matches with `requires` true and no right side, B present. -/
def d0 : Defn := ⟨true, false, true⟩

/-- **R-block at d0: `a` has no successor in any model** (A blocks B, A gives nothing). -/
theorem block_stuck (R : Cfg → Cfg → Prop) (h : Theory .block d0 R) (y : Cfg) : ¬ R .a y := by
  intro hr
  cases (theoryC_iff h _ _).mp hr with
  | rA _ hd => cases hd
  | rB _ hn => exact absurd (show appA d0 .a from ⟨rfl, rfl⟩) hn

/-- **R-skip at d0: `a`'s only successor is `c`, in every model** (B fires). -/
theorem skip_fires (R : Cfg → Cfg → Prop) (h : Theory .skip d0 R) (y : Cfg) : R .a y ↔ y = .c := by
  rw [theoryC_iff h]
  constructor
  · intro hs; cases hs with
    | rA _ hd => cases hd
    | rB => rfl
  · rintro rfl
    exact .rB rfl (fun ⟨_, hc⟩ => absurd ((ceil_rhsA d0).mp hc) (by decide))

/-- R-block's step is incomplete for R-skip's theory at d0 (it misses `a → c`) … -/
theorem block_step_incomplete_for_skip : ¬ Complete .skip d0 (Step .block d0) := by
  intro hc
  have := hc _ (theoryC_model (comp .skip d0) d0) .a .c
    (.rB rfl (fun ⟨_, hc⟩ => absurd ((ceil_rhsA d0).mp hc) (by decide)))
  cases this with
  | rB _ hn => exact hn rfl

/-- … and R-skip's step is unsound for R-block's theory at d0. -/
theorem skip_step_unsound_for_block : ¬ Sound .block d0 (Step .skip d0) := by
  intro hs
  exact block_stuck _ (theoryC_model (comp .block d0) d0) .c
    (hs .a .c (.rB rfl (.inr (by decide))) _ (theoryC_model (comp .block d0) d0))

/-! ## 2. What each theory asserts beyond the text

The text (kompile's KORE) states A's axiom as `appA → •rhsA` (no `⌈rhs⌉`) and B's as `a → •c` (the
priority is an attribute; no competitor), and no closure axiom. -/

/-- The text's own axioms, read literally. -/
abbrev Text (d : Defn) (R : Cfg → Cfg → Prop) : Prop :=
  Valid R (appA d) (rhsA d) ∧ (d.hasB = true → Valid R (· = .a) rhsB)

/-- **A's axiom without `⌈rhs⌉` has no model** where A matches with `requires` true and its right
side has no value, whatever B's axiom or the competitor: so both readings need `⌈rhs⌉` in A's own
axiom. -/
theorem unguarded_no_model (d : Defn) (hq : d.q = true) (hd : d.defA = false)
    (R : Cfg → Cfg → Prop) : ¬ Valid R (appA d) (rhsA d) := by
  intro h
  obtain ⟨_, ⟨hd', _⟩, _⟩ := h .a ⟨rfl, hq⟩
  rw [hd] at hd'; cases hd'

/-- **The text's literal axioms have no model at such a configuration**: they entail every
statement there, both readings' theories included, so entailment from them decides nothing. -/
theorem text_no_model (d : Defn) (hq : d.q = true) (hd : d.defA = false) : ¬ ∃ R, Text d R :=
  fun ⟨R, h, _⟩ => unguarded_no_model d hq hd R h

/-- The text's axioms with the `⌈rhs⌉` that any model forces, and nothing else. -/
abbrev TextG (d : Defn) (R : Cfg → Cfg → Prop) : Prop :=
  Valid R (premA d) (rhsA d) ∧ (d.hasB = true → Valid R (· = .a) rhsB)

theorem textG_model (d : Defn) : ∃ R, TextG d R :=
  ⟨fun x _ => x = .a,
   fun _ ⟨⟨hx, _⟩, hc⟩ => ⟨.b, ⟨(ceil_rhsA d).mp hc, rfl⟩, hx⟩,
   fun _ _ hx => ⟨.c, rfl, hx⟩⟩

theorem comp_block_a (d : Defn) : comp .block d .a ↔ d.q = true :=
  ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem comp_skip_a (d : Defn) : comp .skip d .a ↔ d.q = true ∧ d.defA = true :=
  ⟨fun ⟨h, hc⟩ => ⟨h.2, (ceil_rhsA d).mp hc⟩, fun ⟨h, hd⟩ => ⟨⟨rfl, h⟩, (ceil_rhsA d).mpr hd⟩⟩

/-- **Each reading's theory entails the text's (guarded) axioms exactly where its competitor does
not hold at `a`** (or B is absent). -/
theorem entails_textG_iff (θ : Reading) (d : Defn) :
    (∀ R, Theory θ d R → TextG d R) ↔ (d.hasB = true → ¬ comp θ d .a) := by
  constructor
  · intro h hb hc
    obtain ⟨_, rfl, hr⟩ := (h _ (theoryC_model (comp θ d) d)).2 hb .a rfl
    cases hr with
    | rB _ hn => exact hn hc
  · intro h R hR
    refine ⟨hR.1, fun hb x hx => ?_⟩
    subst hx
    exact ⟨.c, rfl, (theoryC_iff hR _ _).mpr (.rB hb (h hb))⟩

/-- **… and is consistent with them exactly there.** -/
theorem consistent_textG_iff (θ : Reading) (d : Defn) :
    (∃ R, Theory θ d R ∧ TextG d R) ↔ (d.hasB = true → ¬ comp θ d .a) := by
  constructor
  · rintro ⟨R, hT, hG⟩ hb hc
    obtain ⟨_, rfl, hr⟩ := hG.2 hb .a rfl
    cases (theoryC_iff hT _ _).mp hr with
    | rB _ hn => exact hn hc
  · intro h
    exact ⟨_, theoryC_model (comp θ d) d, (entails_textG_iff θ d).mpr h _ (theoryC_model _ d)⟩

/-- **At d0: R-skip's theory entails the text's guarded axioms; R-block's contradicts them.** -/
theorem d0_textG :
    (∀ R, Theory .skip d0 R → TextG d0 R) ∧ ¬ ∃ R, Theory .block d0 R ∧ TextG d0 R :=
  ⟨(entails_textG_iff .skip d0).mpr fun _ h => absurd ((comp_skip_a d0).mp h).2 (by decide),
   fun h => (consistent_textG_iff .block d0).mp h rfl ((comp_block_a d0).mpr rfl)⟩

/-- Where A has a successor (A matches, `requires` true, right side defined, B present), both
readings contradict the text's guarded axioms: reading the priority as a premise is itself beyond the
text, under either reading. -/
theorem prio_beyond_text (θ : Reading) : ¬ ∃ R, Theory θ ⟨true, true, true⟩ R ∧ TextG ⟨true, true, true⟩ R := by
  intro h
  have := (consistent_textG_iff θ _).mp h rfl
  cases θ
  · exact this ((comp_block_a _).mpr rfl)
  · exact this ((comp_skip_a _).mpr ⟨rfl, rfl⟩)

/-- Neither theory is entailed by the text's guarded axioms (the closure axiom is beyond them). -/
theorem textG_not_entails (θ : Reading) (d : Defn) : ¬ ∀ R, TextG d R → Theory θ d R := by
  intro h
  have hT := h (fun _ _ => True)
    ⟨fun _ ⟨_, hc⟩ => ⟨.b, ⟨(ceil_rhsA d).mp hc, rfl⟩, trivial⟩, fun _ _ _ => ⟨.c, rfl, trivial⟩⟩
  rcases hT.2.2 .b .b trivial with ⟨⟨⟨hx, _⟩, _⟩, _⟩ | ⟨⟨_, hx, _⟩, _⟩ <;> cases hx

/-! ## 3. The competitor each reading needs -/

/-- A competitor that names A's left side and `requires` only (it depends on `d.q`, not on A's right
side). -/
abbrev compQ (P : Bool → Prop) (d : Defn) : Pat := fun x => x = .a ∧ P d.q

/-- **R-block's competitor is A's left side and `requires`** (the left side of A's `\rewrites`). -/
theorem block_comp_lhs_req (d : Defn) : comp .block d = compQ (· = true) d := rfl

/-- **R-skip needs a competitor that mentions A's right side**: no competitor that names A's left
side and `requires` only gives R-skip's successors at every toy definition. -/
theorem skip_needs_rhs :
    ¬ ∃ P : Bool → Prop, ∀ d R, TheoryC (compQ P d) d R → ∀ x y, (R x y ↔ Step .skip d x y) := by
  rintro ⟨P, hP⟩
  have h1 := (hP ⟨true, false, true⟩ _ (theoryC_model _ _) .a .c).mpr (.rB rfl (.inr (by decide)))
  have hnP : ¬ P true := by
    cases h1 with
    | rB _ hn => exact fun hp => hn ⟨rfl, hp⟩
  have h2 := (hP ⟨true, true, true⟩ _ (theoryC_model _ _) .a .c).mp
    (.rB rfl (fun ⟨_, hp⟩ => hnP hp))
  cases h2 with
  | rB _ hn => rcases hn with hn | hn <;> exact hn rfl

/-! ## 4. N (no rule applies) and U (a rule applies, no result) at `a` -/

/-- A applies at `a` (it has the smallest priority number). -/
abbrev AppliesA (θ : Reading) (d : Defn) : Prop := ¬ NotApplies θ d

/-- B applies at `a`: present, matches, and A does not apply. -/
abbrev AppliesB (θ : Reading) (d : Defn) : Prop := d.hasB = true ∧ NotApplies θ d

/-- N: no rule applies (a final configuration). -/
abbrev Final (θ : Reading) (d : Defn) : Prop := ¬ AppliesA θ d ∧ ¬ AppliesB θ d

/-- U: a rule applies and `a` has no successor. -/
abbrev Undef (θ : Reading) (d : Defn) : Prop := (AppliesA θ d ∨ AppliesB θ d) ∧ ∀ y, ¬ Step θ d .a y

/-- **Under R-skip there is no U configuration.** -/
theorem skip_no_U (d : Defn) : ¬ Undef .skip d := by
  rintro ⟨hA | ⟨hb, hn⟩, hno⟩
  · have hq : d.q = true := Classical.byContradiction fun h => hA (.inl h)
    have hd : d.defA = true := Classical.byContradiction fun h => hA (.inr h)
    exact hno .b (.rA hq hd)
  · exact hno .c (.rB hb hn)

/-- **Under R-block, `a` is U exactly where A matches with `requires` true and has no right side**
(with B or without). -/
theorem block_U_iff (d : Defn) : Undef .block d ↔ d.q = true ∧ d.defA = false := by
  constructor
  · rintro ⟨hA | ⟨hb, hn⟩, hno⟩
    · have hq : d.q = true := Classical.byContradiction fun h => hA h
      refine ⟨hq, ?_⟩
      cases hd : d.defA
      · rfl
      · exact absurd (Step.rA hq hd) (hno .b)
    · exact absurd (Step.rB hb hn) (hno .c)
  · rintro ⟨hq, hd⟩
    refine ⟨.inl fun hn => hn hq, fun y hs => ?_⟩
    cases hs with
    | rA _ hd' => rw [hd] at hd'; cases hd'
    | rB _ hn => exact hn hq

/-! ## 5. `ensures`

`rule a => b requires Q ensures E` is written by kompile as `\rewrites(a ∧ (Q = true), b ∧ (E = true))`:
the `ensures` is in the right side. `E = true` is a predicate (the whole carrier or empty), so the
right side is `b` where E is true and empty elsewhere: an undefined right side. -/

/-- A with `ensures e`: its right side defined where it was and `e` holds. -/
def withE (d : Defn) (e : Bool) : Defn := { d with defA := d.defA && e }

/-- The `ensures` read as a conjunct of the `requires`. -/
def conjE (d : Defn) (e : Bool) : Defn := { d with q := d.q && e }

/-- **The right side `rhs ∧ (E = true)` is the undefined-right-side case**: so everything above
applies to `ensures`, with `withE`. -/
theorem rhsE_eq (d : Defn) (e : Bool) : (fun y => rhsA d y ∧ e = true) = rhsA (withE d e) := by
  funext y
  rcases d with ⟨q, dA, hb⟩
  cases dA <;> cases e <;> simp [withE]

/-- The text's ensures axiom, read literally, has no model where the `ensures` is false and the
`requires` true. -/
theorem ensures_text_no_model (d : Defn) (hq : d.q = true) (R : Cfg → Cfg → Prop) :
    ¬ Valid R (appA d) (fun y => rhsA d y ∧ false = true) := by
  rw [rhsE_eq]
  exact unguarded_no_model (withE d false) hq (by simp [withE]) R

theorem step_iff (θ : Reading) (d : Defn) (x y : Cfg) :
    Step θ d x y ↔ x = .a ∧ ((d.q = true ∧ d.defA = true ∧ y = .b) ∨
      (d.hasB = true ∧ NotApplies θ d ∧ y = .c)) := by
  constructor
  · intro h; cases h with
    | rA hq hd => exact ⟨rfl, .inl ⟨hq, hd, rfl⟩⟩
    | rB hb hn => exact ⟨rfl, .inr ⟨hb, hn, rfl⟩⟩
  · rintro ⟨rfl, ⟨hq, hd, rfl⟩ | ⟨hb, hn, rfl⟩⟩
    · exact .rA hq hd
    · exact .rB hb hn

/-- **Under R-skip, the `ensures` in the right side is the `ensures` as a `requires` conjunct**: same
step, same N. -/
theorem ensures_skip_eq_conj (d : Defn) (e : Bool) :
    (∀ x y, Step .skip (withE d e) x y ↔ Step .skip (conjE d e) x y) ∧
    (Final .skip (withE d e) ↔ Final .skip (conjE d e)) := by
  rcases d with ⟨q, dA, hb⟩
  refine ⟨fun x y => ?_, ?_⟩
  · rw [step_iff, step_iff]
    cases q <;> cases dA <;> cases e <;> simp [withE, conjE, NotApplies]
  · cases q <;> cases dA <;> cases e <;> simp [withE, conjE, Final, AppliesA, AppliesB, NotApplies]

/-- **Under R-block they differ beside a rule of a larger priority (c44's shape)**: with the `ensures`
in the right side A blocks B and `a` is U; read as a conjunct, B fires. -/
theorem ensures_block_c44 :
    (∀ y, ¬ Step .block (withE ⟨true, true, true⟩ false) .a y) ∧
    Undef .block (withE ⟨true, true, true⟩ false) ∧
    Step .block (conjE ⟨true, true, true⟩ false) .a .c :=
  ⟨((block_U_iff _).mpr ⟨rfl, rfl⟩).2, (block_U_iff _).mpr ⟨rfl, rfl⟩,
   .rB rfl (by simp [conjE])⟩

/-- **… and alone (c43's shape)**: the same successors (none), but R-block makes `a` U with the
`ensures` in the right side and N with it as a conjunct; R-skip makes it N either way. -/
theorem ensures_c43 :
    Undef .block (withE ⟨true, true, false⟩ false) ∧
    Final .block (conjE ⟨true, true, false⟩ false) ∧
    Final .skip (withE ⟨true, true, false⟩ false) ∧
    (∀ y, ¬ Step .block (withE ⟨true, true, false⟩ false) .a y) ∧
    (∀ y, ¬ Step .block (conjE ⟨true, true, false⟩ false) .a y) := by
  refine ⟨(block_U_iff _).mpr ⟨rfl, rfl⟩, ?_, ?_, ((block_U_iff _).mpr ⟨rfl, rfl⟩).2, ?_⟩
  · simp [conjE, Final, AppliesA, AppliesB, NotApplies]
  · simp [withE, Final, AppliesA, AppliesB, NotApplies]
  · intro y hs
    cases hs with
    | rA hq _ => simp [conjE] at hq
    | rB hb _ => simp [conjE] at hb

/-! ## 6. Functions

A function `f` with clause A `f(a) = rA requires Q` (smaller priority number) and clause B
`f(a) = rB [owise]` (present or not). kompile writes an equation as `\implies(prem, \equals(f(a), rhs))`
and, for the `[owise]` clause, `prem = ¬ ∃ (lhs_A ∧ req_A = true)`: the competitor's argument patterns
and `requires`, not its right side. A model interprets `f(a)` as `F : Option Nat` (`none`: no element);
`\equals(f(a), r)` holds iff both denote the same set, i.e. `F = r` (`den_eq_iff`). -/

structure FDefn where
  q : Bool
  rA : Option Nat
  hasB : Bool
  rB : Option Nat

/-- `\equals` between two terms of at most one element is equality of the options. -/
theorem den_eq_iff (o o' : Option Nat) : (∀ v, o = some v ↔ o' = some v) ↔ o = o' := by
  constructor
  · intro h
    cases o with
    | none => cases o' with
      | none => rfl
      | some v => exact absurd ((h v).mpr rfl) (by simp)
    | some v => exact ((h v).mp rfl).symm
  · rintro rfl _; exact Iff.rfl

/-- The equation `prem → f(a) = r` in the model `F`. -/
abbrev Eqn (prem : Prop) (F r : Option Nat) : Prop := prem → F = r

/-- **The text's function axioms** (kompile's premise: the `[owise]` clause negates A's argument
patterns and `requires`). -/
abbrev FText (fd : FDefn) (F : Option Nat) : Prop :=
  Eqn (fd.q = true) F fd.rA ∧ Eqn (fd.hasB = true ∧ ¬ fd.q = true) F fd.rB

/-- A closure axiom: where no clause applies, no value (not stated by the text; KCore states the
interpretation's value there, `ΓFallback`). -/
abbrev FClosed (fd : FDefn) (F : Option Nat) : Prop :=
  Eqn (¬ fd.q = true ∧ ¬ fd.hasB = true) F none

/-- R-block for functions: the text's axioms and the closure. -/
abbrev FBlock (fd : FDefn) (F : Option Nat) : Prop := FText fd F ∧ FClosed fd F

/-- A clause applies (R-skip): `requires` true and right side defined. -/
abbrev skA (fd : FDefn) : Prop := fd.q = true ∧ fd.rA.isSome = true

/-- R-skip for functions: A's equation guarded by its right side's definedness, B's competitor
mentions it, and the closure. -/
abbrev FSkip (fd : FDefn) (F : Option Nat) : Prop :=
  Eqn (skA fd) F fd.rA ∧ Eqn (fd.hasB = true ∧ ¬ skA fd) F fd.rB ∧ Eqn (¬ skA fd ∧ ¬ fd.hasB = true) F none

def evalBlock (fd : FDefn) : Option Nat := if fd.q then fd.rA else if fd.hasB then fd.rB else none

def evalSkip (fd : FDefn) : Option Nat :=
  if fd.q && fd.rA.isSome then fd.rA else if fd.hasB then fd.rB else none

theorem fblock_iff (fd : FDefn) (F : Option Nat) : FBlock fd F ↔ F = evalBlock fd := by
  rcases fd with ⟨q, rA, hb, rB⟩
  cases q <;> cases hb <;> simp [evalBlock, FBlock, FText, FClosed, Eqn]

theorem fskip_iff (fd : FDefn) (F : Option Nat) : FSkip fd F ↔ F = evalSkip fd := by
  rcases fd with ⟨q, rA, hb, rB⟩
  cases q <;> cases hb <;> cases rA <;> simp [evalSkip, FSkip, skA, Eqn]

/-- KCore's `Eval` cut down to this function: a clause that applies decides, its result possibly
`none` (`Eval.clause`); B where A fails (`Fails`: `requires` not true); undefined where all fail. -/
inductive EvalF (fd : FDefn) : Option Nat → Prop
  | clauseA (hq : fd.q = true) : EvalF fd fd.rA
  | clauseB (hb : fd.hasB = true) (hf : fd.q ≠ true) : EvalF fd fd.rB
  | undef (hf : fd.q ≠ true) (hnb : fd.hasB ≠ true) : EvalF fd none

/-- **KCore's function evaluation is R-block's unique model**: sound and complete for the text's
function axioms with the closure. -/
theorem evalF_sound_complete (fd : FDefn) (r : Option Nat) :
    EvalF fd r ↔ ∀ F, FBlock fd F → F = r := by
  have hiff : EvalF fd r ↔ r = evalBlock fd := by
    rcases fd with ⟨q, rA, hb, rB⟩
    constructor
    · intro h; cases h <;> simp_all [evalBlock]
    · intro h; subst h
      cases q <;> cases hb
      · exact .undef (by simp) (by simp)
      · exact .clauseB rfl (by simp)
      · exact .clauseA rfl
      · exact .clauseA rfl
  rw [hiff]
  constructor
  · intro h F hF; rw [(fblock_iff fd F).mp hF, h]
  · intro h; exact (h _ ((fblock_iff fd _).mpr rfl)).symm

/-- **The text's function axioms are R-block's** (R-block adds only the closure, which agrees with
them), and every R-block model satisfies them. -/
theorem fblock_text (fd : FDefn) (F : Option Nat) : FBlock fd F → FText fd F := And.left

/-- The function configuration in question: A's `requires` true, A's right side no value, B defined. -/
def fd0 : FDefn := ⟨true, none, true, some 2⟩

/-- **At fd0 the text gives `f(a)` no value (A blocks B)**, R-skip gives B's value, and R-skip's
competitor with the text's own (unguarded) A equation has no model; R-skip contradicts the text. -/
theorem f_d0 :
    (∀ F, FText fd0 F → F = none) ∧ evalBlock fd0 = none ∧ evalSkip fd0 = some 2 ∧
    (¬ ∃ F, Eqn (fd0.q = true) F fd0.rA ∧ Eqn (fd0.hasB = true ∧ ¬ skA fd0) F fd0.rB) ∧
    ¬ ∃ F, FSkip fd0 F ∧ FText fd0 F := by
  refine ⟨fun F h => h.1 rfl, rfl, rfl, ?_, ?_⟩
  · rintro ⟨F, h1, h2⟩
    have e1 := h1 rfl
    have e2 := h2 ⟨rfl, by simp [skA, fd0]⟩
    rw [e1] at e2; cases e2
  · rintro ⟨F, hS, hT⟩
    have e1 := hT.1 rfl
    rw [(fskip_iff fd0 F).mp hS] at e1
    cases e1

/-- R-block and R-skip agree on functions wherever A's right side has a value or its `requires` is
not true. -/
theorem f_agree (fd : FDefn) (h : fd.q = true → fd.rA.isSome = true) : evalBlock fd = evalSkip fd := by
  rcases fd with ⟨q, rA, hb, rB⟩
  cases q <;> cases rA <;> simp_all [evalBlock, evalSkip]

#print axioms sound_complete
#print axioms sound_complete_unique
#print axioms block_stuck
#print axioms skip_fires
#print axioms text_no_model
#print axioms d0_textG
#print axioms prio_beyond_text
#print axioms textG_not_entails
#print axioms skip_needs_rhs
#print axioms skip_no_U
#print axioms block_U_iff
#print axioms ensures_skip_eq_conj
#print axioms ensures_block_c44
#print axioms ensures_c43
#print axioms evalF_sound_complete
#print axioms f_d0
#print axioms f_agree

end BlockingNoResult
