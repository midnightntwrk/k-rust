/-
  KCore: noninterference, a theorem kind (ARCHITECTURE.md §3.7).

  **The statement** (`TINI`, frozen). Termination-insensitive noninterference of a definition's
  `Step`, for three relations the property names:
  - `Start x₁ x₂`: the two runs start from configurations an observer cannot tell apart (the
    same program, inputs that agree on what the observer may read);
  - `Fin y`: y is a final configuration;
  - `Obs y₁ y₂`: the observer cannot tell y₁ and y₂ apart.
  Then any two runs from `Start`-related configurations that both reach final configurations end
  in `Obs`-related ones. A run that does not terminate is not constrained (termination-insensitive):
  the observer of a final state learns nothing from a run that has none.

  **The generic theorem** (`tini_of_unwinding`). An unwinding relation R gives `TINI`:
  - `Start ⊆ R`, and R between final configurations gives `Obs`;
  - final configurations have no successor;
  - `Unwinds c R`: a step of the left configuration either keeps R with the right one unmoved
    (a step the observer cannot see), or is matched by a step of the right one into R;
  - the same for the right configuration (`Unwinds c (flip R)`);
  - `Step` is deterministic (the determinism kind's theorem).
  The proof is an induction on the left run, then on the right one: a matched step uses the
  right run's next step, which determinism makes the matching one.

  **Relative to an invariant** (`TINIOn`, `tini_of_unwinding_on`). The statement for runs from
  configurations where `Init` holds, given an invariant `Invariant c Init Inv`. Both runs start
  where `Init` holds, so every configuration of either run is one where `Inv` holds
  (`Invariant.reach`): the unwinding condition (`UnwindsOn`), the observation and the final
  configurations' having no successor are needed only where `Inv` holds at both configurations,
  and determinism only from configurations where `Inv` holds (`DeterministicOn`). Nothing is
  needed of a configuration that is related to one of a run but is not itself one of a run.
  `TINI` and `tini_of_unwinding` are the instance `Init = Inv = fun _ => True`.

  **Determinism up to overlaps** (`deterministicOn_of_except`): the decided determinism up to the
  listed overlapping pairs of rules (with coherence of the clauses of one priority, `CoherentAll`), and
  for each listed pair a refutation on `Inv`
  (`OverlapRefuted`: at no configuration where `Inv` holds do both rules apply), give
  determinism from every configuration where `Inv` holds.

  **The obligations.** `Unwinds c R` splits by rule (`unwinds_of_rules`): `RuleUnwinds c R r` for
  each rule r, the condition at the steps that r makes. The rules a decided condition covers are
  closed by the decision; the others are named obligations, proved by hand or left as premises.
  `RuleUnwindsOn c Inv R r` is the same condition where `Inv` holds at both configurations. The
  split is a `Kind` (Kind.lean) indexed by the rules (`Kind.ofList`), with the decided condition its
  decider: `unwinds_of` and `unwindsOn_of` are its `Kind.of_decided`. A listed overlap refuted where
  `Inv` holds is the determinism kind's obligation at that pair (`joinsOn_of_refuted`).
-/
import KcoreSpec.Cert
import KcoreSpec.Invariant

set_option autoImplicit false

namespace KCore.NI

open KCore.Cert

variable {c : Semantics}

/-! ## The statement -/

/-- **Termination-insensitive noninterference** of `c`'s `Step` for the relations `Start`, `Fin`
and `Obs`. -/
def TINI (c : Semantics) (Start : Config c → Config c → Prop) (Fin : Config c → Prop)
    (Obs : Config c → Config c → Prop) : Prop :=
  ∀ x₁ x₂ y₁ y₂, Start x₁ x₂ → Reach (Step c) x₁ y₁ → Reach (Step c) x₂ y₂ → Fin y₁ → Fin y₂ →
    Obs y₁ y₂

/-- **Termination-insensitive noninterference from initial configurations**: `TINI` for runs from
configurations where `Init` holds. -/
def TINIOn (c : Semantics) (Init : Config c → Prop) (Start : Config c → Config c → Prop)
    (Fin : Config c → Prop) (Obs : Config c → Config c → Prop) : Prop :=
  ∀ x₁ x₂ y₁ y₂, Init x₁ → Init x₂ → Start x₁ x₂ → Reach (Step c) x₁ y₁ → Reach (Step c) x₂ y₂ →
    Fin y₁ → Fin y₂ → Obs y₁ y₂

/-- `TINI` is `TINIOn` from every configuration. -/
theorem tiniOn_true_iff {Start : Config c → Config c → Prop} {Fin : Config c → Prop}
    {Obs : Config c → Config c → Prop} : TINIOn c (fun _ => True) Start Fin Obs ↔ TINI c Start Fin Obs :=
  ⟨fun h x₁ x₂ y₁ y₂ => h x₁ x₂ y₁ y₂ trivial trivial, fun h x₁ x₂ y₁ y₂ _ _ => h x₁ x₂ y₁ y₂⟩

/-! ## Unwinding -/

/-- `Step c` is a function on configurations. -/
def Deterministic (c : Semantics) : Prop := ∀ x y z : Config c, Step c x y → Step c x z → y = z

/-- `Step c` is a function on the configurations where `Inv` holds. -/
def DeterministicOn (c : Semantics) (Inv : Config c → Prop) : Prop :=
  ∀ x y y' : Config c, Inv x → Step c x y → Step c x y' → y = y'

theorem Deterministic.on (h : Deterministic c) (Inv : Config c → Prop) : DeterministicOn c Inv :=
  fun x y y' _ => h x y y'

/-- A step of the left configuration keeps R with the right one unmoved, or the right one makes a
step into R. -/
def Unwinds (c : Semantics) (R : Config c → Config c → Prop) : Prop :=
  ∀ x₁ x₂ y₁, R x₁ x₂ → Step c x₁ y₁ → R y₁ x₂ ∨ ∃ y₂, Step c x₂ y₂ ∧ R y₁ y₂

/-- `Unwinds` where `Inv` holds at both configurations. -/
def UnwindsOn (c : Semantics) (Inv : Config c → Prop) (R : Config c → Config c → Prop) : Prop :=
  ∀ x₁ x₂ y₁, Inv x₁ → Inv x₂ → R x₁ x₂ → Step c x₁ y₁ → R y₁ x₂ ∨ ∃ y₂, Step c x₂ y₂ ∧ R y₁ y₂

theorem Unwinds.on {R : Config c → Config c → Prop} (h : Unwinds c R) (Inv : Config c → Prop) :
    UnwindsOn c Inv R :=
  fun x₁ x₂ y₁ _ _ => h x₁ x₂ y₁

/-- An unwinding relation for `Start`, `Fin` and `Obs`. -/
structure Unwinding (c : Semantics) (Start : Config c → Config c → Prop) (Fin : Config c → Prop)
    (Obs : Config c → Config c → Prop) (R : Config c → Config c → Prop) : Prop where
  start : ∀ x₁ x₂, Start x₁ x₂ → R x₁ x₂
  obs : ∀ y₁ y₂, R y₁ y₂ → Fin y₁ → Fin y₂ → Obs y₁ y₂
  stuck : ∀ y, Fin y → ∀ z, ¬ Step c y z
  left : Unwinds c R
  right : Unwinds c (fun a b => R b a)

/-- An unwinding relation for `Start`, `Fin` and `Obs` from configurations where `Init` holds, with
every condition but `start` needed only where `Inv` holds. -/
structure UnwindingOn (c : Semantics) (Init Inv : Config c → Prop) (Start : Config c → Config c → Prop)
    (Fin : Config c → Prop) (Obs : Config c → Config c → Prop) (R : Config c → Config c → Prop) : Prop where
  start : ∀ x₁ x₂, Init x₁ → Init x₂ → Start x₁ x₂ → R x₁ x₂
  obs : ∀ y₁ y₂, Inv y₁ → Inv y₂ → R y₁ y₂ → Fin y₁ → Fin y₂ → Obs y₁ y₂
  stuck : ∀ y, Inv y → Fin y → ∀ z, ¬ Step c y z
  left : UnwindsOn c Inv R
  right : UnwindsOn c Inv (fun a b => R b a)

theorem Unwinding.on {Start : Config c → Config c → Prop} {Fin : Config c → Prop}
    {Obs R : Config c → Config c → Prop} (h : Unwinding c Start Fin Obs R) (Init Inv : Config c → Prop) :
    UnwindingOn c Init Inv Start Fin Obs R :=
  ⟨fun x₁ x₂ _ _ => h.start x₁ x₂, fun y₁ y₂ _ _ => h.obs y₁ y₂, fun y _ => h.stuck y,
    h.left.on Inv, h.right.on Inv⟩

/-- Every configuration is one where `True` holds, and every step keeps it. -/
theorem invariant_true : Invariant c (fun _ => True) (fun _ => True) := ⟨fun _ h => h, fun _ _ h _ => h⟩

theorem tini_aux_on {Inv Fin : Config c → Prop} {Obs R : Config c → Config c → Prop}
    (hinv : ∀ x y, Inv x → Step c x y → Inv y) (hdet : DeterministicOn c Inv)
    (hobs : ∀ y₁ y₂, Inv y₁ → Inv y₂ → R y₁ y₂ → Fin y₁ → Fin y₂ → Obs y₁ y₂)
    (hstuck : ∀ y, Inv y → Fin y → ∀ z, ¬ Step c y z) (hl : UnwindsOn c Inv R)
    (hr : UnwindsOn c Inv (fun a b => R b a)) :
    ∀ x₁ y₁, Reach (Step c) x₁ y₁ → ∀ x₂ y₂, Reach (Step c) x₂ y₂ → Inv x₁ → Inv x₂ → R x₁ x₂ →
      Fin y₁ → Fin y₂ → Obs y₁ y₂ := by
  intro x₁ y₁ h₁
  induction h₁ with
  | refl x₁ =>
    intro x₂ y₂ h₂
    induction h₂ with
    | refl x₂ => exact fun hi₁ hi₂ hR hf₁ hf₂ => hobs _ _ hi₁ hi₂ hR hf₁ hf₂
    | head hs _ ih =>
      intro hi₁ hi₂ hR hf₁ hf₂
      rcases hr _ _ _ hi₂ hi₁ hR hs with hR' | ⟨z, hz, _⟩
      · exact ih hi₁ (hinv _ _ hi₂ hs) hR' hf₁ hf₂
      · exact absurd hz (hstuck _ hi₁ hf₁ z)
  | head hs _ ih =>
    intro x₂ y₂ h₂ hi₁ hi₂ hR hf₁ hf₂
    rcases hl _ _ _ hi₁ hi₂ hR hs with hR' | ⟨z, hz, hR'⟩
    · exact ih x₂ y₂ h₂ (hinv _ _ hi₁ hs) hi₂ hR' hf₁ hf₂
    · cases h₂ with
      | refl => exact absurd hz (hstuck _ hi₂ hf₂ z)
      | head hs₂ t =>
        rename_i w
        have := hdet _ _ _ hi₂ hs₂ hz
        subst this
        exact ih w y₂ t (hinv _ _ hi₁ hs) (hinv _ _ hi₂ hs₂) hR' hf₁ hf₂

theorem tini_aux {Fin : Config c → Prop} {Obs R : Config c → Config c → Prop}
    (hdet : Deterministic c) (hobs : ∀ y₁ y₂, R y₁ y₂ → Fin y₁ → Fin y₂ → Obs y₁ y₂)
    (hstuck : ∀ y, Fin y → ∀ z, ¬ Step c y z) (hl : Unwinds c R) (hr : Unwinds c (fun a b => R b a)) :
    ∀ x₁ y₁, Reach (Step c) x₁ y₁ → ∀ x₂ y₂, Reach (Step c) x₂ y₂ → R x₁ x₂ → Fin y₁ → Fin y₂ →
      Obs y₁ y₂ := fun x₁ y₁ h₁ x₂ y₂ h₂ =>
  tini_aux_on (Inv := fun _ => True) (fun _ _ h _ => h) (hdet.on _) (fun y₁ y₂ _ _ => hobs y₁ y₂)
    (fun y _ => hstuck y) (hl.on _) (hr.on _) x₁ y₁ h₁ x₂ y₂ h₂ trivial trivial

/-- **The generic theorem, relative to an invariant.** A `Step` deterministic where `Inv` holds,
with an unwinding relation where `Inv` holds, is noninterfering from the configurations where
`Init` holds. -/
theorem tini_of_unwinding_on {Init Inv : Config c → Prop} {Start : Config c → Config c → Prop}
    {Fin : Config c → Prop} {Obs R : Config c → Config c → Prop} (hinv : Invariant c Init Inv)
    (hdet : DeterministicOn c Inv) (hu : UnwindingOn c Init Inv Start Fin Obs R) :
    TINIOn c Init Start Fin Obs := fun x₁ x₂ y₁ y₂ hi₁ hi₂ hs h₁ h₂ hf₁ hf₂ =>
  tini_aux_on hinv.2 hdet hu.obs hu.stuck hu.left hu.right x₁ y₁ h₁ x₂ y₂ h₂ (hinv.1 _ hi₁)
    (hinv.1 _ hi₂) (hu.start _ _ hi₁ hi₂ hs) hf₁ hf₂

/-- **The generic theorem.** A deterministic `Step` with an unwinding relation is noninterfering:
`tini_of_unwinding_on` with `Init = Inv = fun _ => True`. -/
theorem tini_of_unwinding {Start : Config c → Config c → Prop} {Fin : Config c → Prop}
    {Obs R : Config c → Config c → Prop} (hdet : Deterministic c) (hu : Unwinding c Start Fin Obs R) :
    TINI c Start Fin Obs :=
  tiniOn_true_iff.mp (tini_of_unwinding_on invariant_true (hdet.on _) (hu.on _ _))

/-- A symmetric relation's right condition is its left one. -/
theorem Unwinds.flip_of_symm {R : Config c → Config c → Prop} (hsym : ∀ a b, R a b → R b a)
    (h : Unwinds c R) : Unwinds c (fun a b => R b a) := by
  intro x₁ x₂ y₁ hR hs
  rcases h x₁ x₂ y₁ (hsym _ _ hR) hs with h' | ⟨y₂, hy, h'⟩
  · exact Or.inl (hsym _ _ h')
  · exact Or.inr ⟨y₂, hy, hsym _ _ h'⟩

/-- A symmetric relation's right condition is its left one, where `Inv` holds. -/
theorem UnwindsOn.flip_of_symm {Inv : Config c → Prop} {R : Config c → Config c → Prop}
    (hsym : ∀ a b, R a b → R b a) (h : UnwindsOn c Inv R) : UnwindsOn c Inv (fun a b => R b a) := by
  intro x₁ x₂ y₁ hi₁ hi₂ hR hs
  rcases h x₁ x₂ y₁ hi₁ hi₂ (hsym _ _ hR) hs with h' | ⟨y₂, hy, h'⟩
  · exact Or.inl (hsym _ _ h')
  · exact Or.inr ⟨y₂, hy, hsym _ _ h'⟩

/-! ## Determinism up to overlaps, where an invariant holds -/

/-- **The obligation of a listed overlap**: at no configuration where `Inv` holds do rules i and j
both apply. -/
def OverlapRefuted (c : Semantics) (Inv : Config c → Prop) (i j : Nat) : Prop :=
  ∀ rᵢ rⱼ : Rule, c.rules[i]? = some rᵢ → c.rules[j]? = some rⱼ → ∀ x : Config c, Inv x →
    ¬ (Det.Applies c rᵢ x.val ∧ Det.Applies c rⱼ x.val)

/-- A listed overlap refuted where `Inv` holds discharges the determinism kind's obligation at the
pair: where its two rules never both apply, their steps join. -/
theorem joinsOn_of_refuted {Inv : Config c → Prop} {i j : Nat} (h : OverlapRefuted c Inv i j) :
    Det.JoinsOn c Inv i j :=
  fun r r' hr hr' x _ _ hx hb hb' => (h r r' hr hr' x hx ⟨hb.applies, hb'.applies⟩).elim

/-- Determinism up to the overlaps `ovl` (the form of `Det.deterministic_except`), with every
listed overlap refuted where `Inv` holds, is determinism where `Inv` holds. -/
theorem deterministicOn_of_overlaps {Inv : Config c → Prop} {ovl : List (Nat × Nat)}
    (hex : ∀ {x y y' : Config c}, Step c x y → Step c x y' → y = y' ∨ ∃ i j, ((i, j) ∈ ovl ∨ (j, i) ∈ ovl) ∧
      ∃ (hi : i < c.rules.length) (hj : j < c.rules.length),
        Det.Applies c c.rules[i] x.val ∧ Det.Applies c c.rules[j] x.val)
    (hov : ∀ i j, (i, j) ∈ ovl → OverlapRefuted c Inv i j) : DeterministicOn c Inv := by
  intro x y y' hx h h'
  rcases hex h h' with he | ⟨i, j, hm, hi, hj, hai, haj⟩
  · exact he
  · rcases hm with hm | hm
    · exact (hov i j hm _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) x hx ⟨hai, haj⟩).elim
    · exact (hov j i hm _ _ (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hi) x hx ⟨haj, hai⟩).elim

/-- **Determinism where an invariant holds**, from the condition decided up to the listed overlaps
(`Det.detOKExcept`), coherence of the clauses of one priority, and every listed overlap refuted
where `Inv` holds; in a core `okM` accepts. -/
theorem deterministicOn_of_except_okM (hok : c.okM = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hmo : CoherentAll c) {T : Tables} (hT : T = tables c) {ix : Det.DetIndex}
    {ovl : List (Nat × Nat)} (hd : Det.detOKExcept c T ix ovl = true) {Inv : Config c → Prop}
    (hov : ∀ i j, (i, j) ∈ ovl → OverlapRefuted c Inv i j) : DeterministicOn c Inv :=
  deterministicOn_of_overlaps (Det.deterministic_except_okM hok hsr hmr hmo hT hd) hov

/-- **Determinism where an invariant holds, for every interpretation of the parameters**, from the
condition decided once on the data up to the listed overlaps, coherence under each
interpretation, and every listed overlap refuted under H where `Inv` holds; in a core `okM` accepts. -/
theorem deterministicOn_of_except_all_okM (hok : c.okM = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hmo : ∀ H, CoherentAll (c.withHooks H)) {T : Tables}
    (hT : T = tables c) {ix : Det.DetIndex} {ovl : List (Nat × Nat)}
    (hd : Det.detOKExcept c T ix ovl = true) (H : HookParams) {Inv : Config (c.withHooks H) → Prop}
    (hov : ∀ i j, (i, j) ∈ ovl → OverlapRefuted (c.withHooks H) Inv i j) :
    DeterministicOn (c.withHooks H) Inv :=
  deterministicOn_of_overlaps (Det.deterministic_except_all_okM hok hsr hmr hmo hT hd H) hov

/-- **Determinism where an invariant holds**, from the condition decided up to the listed overlaps
(`Det.detOKExcept`), coherence of the clauses of one priority, and every listed overlap refuted
where `Inv` holds. -/
theorem deterministicOn_of_except (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hmo : CoherentAll c) {T : Tables} (hT : T = tables c) {ix : Det.DetIndex}
    {ovl : List (Nat × Nat)} (hd : Det.detOKExcept c T ix ovl = true) {Inv : Config c → Prop}
    (hov : ∀ i j, (i, j) ∈ ovl → OverlapRefuted c Inv i j) : DeterministicOn c Inv :=
  deterministicOn_of_except_okM (Semantics.okM_of_ok hok) hsr hmr hmo hT hd hov

/-- **Determinism where an invariant holds, for every interpretation of the parameters**, from the
condition decided once on the data up to the listed overlaps, coherence under each
interpretation, and every listed overlap refuted under H where `Inv` holds. -/
theorem deterministicOn_of_except_all (hok : c.ok = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hmo : ∀ H, CoherentAll (c.withHooks H)) {T : Tables}
    (hT : T = tables c) {ix : Det.DetIndex} {ovl : List (Nat × Nat)}
    (hd : Det.detOKExcept c T ix ovl = true) (H : HookParams) {Inv : Config (c.withHooks H) → Prop}
    (hov : ∀ i j, (i, j) ∈ ovl → OverlapRefuted (c.withHooks H) Inv i j) :
    DeterministicOn (c.withHooks H) Inv :=
  deterministicOn_of_except_all_okM (Semantics.okM_of_ok hok) hsr hmr hmo hT hd H hov

/-! ## The condition by rule -/

/-- Rule r rewrites x to y: `Step`'s premises for that rule (`Det.StepBy`). -/
abbrev StepBy (c : Semantics) (r : Rule) (x y : GroundTerm) : Prop := Det.StepBy c r x y

/-- `RuleUnwinds c R r`: the unwinding condition at the steps rule r makes. The form of a named
obligation. -/
def RuleUnwinds (c : Semantics) (R : Config c → Config c → Prop) (r : Rule) : Prop :=
  ∀ x₁ x₂ y₁ : Config c, R x₁ x₂ → StepBy c r x₁.val y₁.val → R y₁ x₂ ∨ ∃ y₂, Step c x₂ y₂ ∧ R y₁ y₂

/-- `RuleUnwindsOn c Inv R r`: the unwinding condition at the steps that rule r makes, where `Inv`
holds at both configurations. The form of a named obligation relative to an invariant. -/
def RuleUnwindsOn (c : Semantics) (Inv : Config c → Prop) (R : Config c → Config c → Prop) (r : Rule) : Prop :=
  ∀ x₁ x₂ y₁ : Config c, Inv x₁ → Inv x₂ → R x₁ x₂ → StepBy c r x₁.val y₁.val →
    R y₁ x₂ ∨ ∃ y₂, Step c x₂ y₂ ∧ R y₁ y₂

theorem RuleUnwinds.on {R : Config c → Config c → Prop} {r : Rule} (h : RuleUnwinds c R r)
    (Inv : Config c → Prop) : RuleUnwindsOn c Inv R r :=
  fun x₁ x₂ y₁ _ _ => h x₁ x₂ y₁

theorem RuleUnwindsOn.of_true {R : Config c → Config c → Prop} {r : Rule}
    (h : RuleUnwindsOn c (fun _ => True) R r) : RuleUnwinds c R r :=
  fun x₁ x₂ y₁ => h x₁ x₂ y₁ trivial trivial

theorem stepBy_of_step {x y : Config c} (h : Step c x y) : ∃ r ∈ c.rules, StepBy c r x.val y.val :=
  Det.stepBy_of_step h

theorem step_of_stepBy {r : Rule} (mem : r ∈ c.rules) (hpre : r.pre = .top) (hpost : r.post = .top)
    {x y : Config c} (h : StepBy c r x.val y.val) : Step c x y :=
  Det.step_of_stepBy mem hpre hpost h

/-- A step by a rule of the definition is a step (`StepBy` carries `pre` and `post`). -/
theorem step_of_stepBy_pp {r : Rule} (mem : r ∈ c.rules) {x y : Config c} (h : StepBy c r x.val y.val) :
    Step c x y :=
  Det.step_of_stepBy_pp mem h

/-- The unwinding condition from the rules': one per rule. -/
theorem unwinds_of_rules {R : Config c → Config c → Prop} (h : ∀ r ∈ c.rules, RuleUnwinds c R r) :
    Unwinds c R := by
  intro x₁ x₂ y₁ hR hs
  obtain ⟨r, mem, hb⟩ := stepBy_of_step hs
  exact h r mem x₁ x₂ y₁ hR hb

/-- **Decided rules and named obligations.** If `cond` gives the condition at a rule's steps
(`sound`), every rule not listed in `obl` satisfies `cond` (one decision), and every listed rule is
an obligation proved, the unwinding condition holds. -/
theorem unwinds_of {R : Config c → Config c → Prop} {cond : Rule → Bool}
    (sound : ∀ r ∈ c.rules, cond r = true → RuleUnwinds c R r) {obl : List Nat}
    (h : allExcept cond obl 0 c.rules = true)
    (ho : ∀ i ∈ obl, ∀ r, c.rules[i]? = some r → RuleUnwinds c R r) : Unwinds c R :=
  Kind.of_decided (Kind.ofList c.rules (RuleUnwinds c R) (Unwinds c R) unwinds_of_rules)
    (Kind.listDecider cond sound) obl (decides_of_allExcept h) ho

/-- The unwinding condition where `Inv` holds, from the rules': one per rule. -/
theorem unwindsOn_of_rules {Inv : Config c → Prop} {R : Config c → Config c → Prop}
    (h : ∀ r ∈ c.rules, RuleUnwindsOn c Inv R r) : UnwindsOn c Inv R := by
  intro x₁ x₂ y₁ hi₁ hi₂ hR hs
  obtain ⟨r, mem, hb⟩ := stepBy_of_step hs
  exact h r mem x₁ x₂ y₁ hi₁ hi₂ hR hb

/-- **Decided rules and named obligations, where `Inv` holds**: `unwinds_of` with the condition
and the listed rules' obligations needed only where `Inv` holds. -/
theorem unwindsOn_of {Inv : Config c → Prop} {R : Config c → Config c → Prop} {cond : Rule → Bool}
    (sound : ∀ r ∈ c.rules, cond r = true → RuleUnwindsOn c Inv R r) {obl : List Nat}
    (h : allExcept cond obl 0 c.rules = true)
    (ho : ∀ i ∈ obl, ∀ r, c.rules[i]? = some r → RuleUnwindsOn c Inv R r) : UnwindsOn c Inv R :=
  Kind.of_decided (Kind.ofList c.rules (RuleUnwindsOn c Inv R) (UnwindsOn c Inv R) unwindsOn_of_rules)
    (Kind.listDecider cond sound) obl (decides_of_allExcept h) ho

/-! ## Refutation by runs

A checker that accepts too much is refuted by two concrete runs: from two configurations the
statement relates, the kernel follows each run (`runFirst`, the executable step's first successor
at each point) to final configurations the observer tells apart. `runFirst_reach` makes each run a
chain of `Step`s. -/

open KCore.Exec

/-- The configuration `k` steps of the executable step reach from `x`, following its first
successor (at evaluation fuel `n`); it stops where there is none. -/
def runFirst (c : Semantics) (n : Nat) : Nat → GroundTerm → GroundTerm
  | 0, x => x
  | k + 1, x => match successorsN c n x with
    | y :: _ => runFirst c n k y
    | [] => x

theorem runFirst_reach (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (n : Nat) : ∀ (k : Nat) (x : Config c), ∃ z : Config c, runFirst c n k x.val = z.val ∧ Reach (Step c) x z
  | 0, x => ⟨x, rfl, .refl x⟩
  | k + 1, x => by
    cases hys : successorsN c n x.val with
    | nil => exact ⟨x, by simp [runFirst, hys], .refl x⟩
    | cons y ys =>
      have hl : (successorsN c n x.val).any (same · y) = true := by
        rw [hys]; simp [same_iff]
      obtain ⟨hy, hs⟩ := step_of_listed hok hsr hmr hl
      obtain ⟨z, hz, hr⟩ := runFirst_reach hok hsr hmr n k ⟨y, hy⟩
      exact ⟨z, by simp [runFirst, hys, hz], .head hs hr⟩

end KCore.NI
