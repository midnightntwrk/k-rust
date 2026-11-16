/-
  EXPERIMENT. Not part of the library and not a test of it: nothing imports this file, and it
  changes nothing KCore states. Findings: `../../../findings/UNDEF-vs-undetermined.md`.
  Run from the package root: `lake env lean test/experiments/UndefUndetermined.lean`.

  Question. Where K's text describes an operation on part of its arguments only, the closed reading
  states that the rest has no value (a partial hook gives `some none`; a function where no clause
  applies is undefined, with a closure axiom in Γ). The weaker reading says the
  text does not determine it: no value or any value of the result sort (for a symbol declared
  `total`, some value). The middle design keeps every operation a function of its arguments by
  giving the undescribed part to a parameter `H` (as `HookParams` does for uninterpreted hooks) and
  states the theorems for every `H`; it is the design KCore reads (`HookParams`, `Eval.rest`,
  `Semantics.fnRest`).

  This file is a model of that mechanism, small enough to prove everything about: an operation `d`
  described on part of its arguments, the models of each reading (an interpretation of the
  operation, `none` for ⊥), and a definition with two rules of different priorities whose
  higher-priority `requires` applies the operation (`requires op(arg) ==K w`), as in KCore's
  `Step`/`NotApplies` (Step.lean) and a function's clauses with `Fails` (Evaluation.lean). The
  model's successors (`Succ`) are what Γ's rule axioms and the step's closure axiom (`Γstep`)
  give in a model: the higher rule's successor where its `requires` holds, the lower rule's where it
  does not. Soundness and completeness are KCore's `SoundC`/`CompleteC` cut down to this
  definition: every step holds in every model; every successor in every model is a step.

  The four subjects are instantiated with KCore's own definitions of the described part
  (`KStr.substr`, `KStr.find`, `KStr.ord`) and a user function `half`.
-/
import KcoreSpec

set_option autoImplicit false

namespace UndefExperiment

/-! ## 1. Readings -/

/-- What a text says of an operation at an argument: `some (some v)` the value `v`, `some none` that
it has no value, `none` nothing. -/
abbrev Desc (α β : Type) := α → Option (Option β)

/-- An interpretation of the operation in a model: `none` is ⊥ (no element). -/
abbrev Interp (α β : Type) := α → Option β

variable {α β : Type}

/-- The model agrees with what the text states. -/
def Agrees (d : Desc α β) (m : Interp α β) : Prop := ∀ a r, d a = some r → m a = r

/-- **The closed reading** (a closure axiom, a partial hook's `some none`): where the text says
nothing, ⊥. -/
def Closed (d : Desc α β) (m : Interp α β) : Prop := ∀ a, m a = (d a).join

/-- **The weaker reading**: what the text states, nothing else. -/
def Weak (d : Desc α β) (m : Interp α β) : Prop := Agrees d m

/-- The weaker reading of a symbol declared `total`: also defined everywhere. -/
def WeakTotal (d : Desc α β) (m : Interp α β) : Prop := Agrees d m ∧ ∀ a, (m a).isSome

/-- **The middle design**: the text's value where it states one, the parameter `H`'s elsewhere. -/
def fill (d : Desc α β) (H : Interp α β) : Interp α β := fun a => (d a).getD (H a)

/-- The closed reading is the middle design at the parameter that is ⊥ everywhere
(`HookParams.none`, the interpretation the parsed data carries). -/
theorem fill_none (d : Desc α β) : fill d (fun _ => none) = fun a => (d a).join := by
  funext a; unfold fill; cases d a <;> rfl

/-- **The weaker reading's models are exactly the middle design's, over all parameters.** -/
theorem weak_iff_fill (d : Desc α β) (m : Interp α β) : Weak d m ↔ ∃ H, m = fill d H := by
  constructor
  · intro h
    refine ⟨m, funext fun a => ?_⟩
    unfold fill
    cases hd : d a with
    | none => rfl
    | some r => exact h a r hd
  · rintro ⟨H, rfl⟩ a r hd
    simp [fill, hd]

/-- For a symbol declared `total` whose text never states ⊥: the models of the weaker reading are the
middle design's over the parameters that are defined everywhere (`ParamsTotal`'s condition). -/
theorem weakTotal_iff_fill (d : Desc α β) (hd : ∀ a, d a ≠ some none) (m : Interp α β) :
    WeakTotal d m ↔ ∃ H, (∀ a, (H a).isSome) ∧ m = fill d H := by
  constructor
  · rintro ⟨h, ht⟩
    exact ⟨m, ht, ((weak_iff_fill d m).mp h).elim fun H hH => by
      subst hH; funext a; unfold fill; cases d a <;> simp⟩
  · rintro ⟨H, hH, rfl⟩
    refine ⟨(weak_iff_fill d _).mpr ⟨H, rfl⟩, fun a => ?_⟩
    unfold fill
    cases hda : d a with
    | none => simpa using hH a
    | some r =>
      cases r with
      | none => exact absurd hda (hd a)
      | some v => rfl

/-- **What the weaker reading proves is what the middle design proves for every parameter.** -/
theorem weak_valid_iff (d : Desc α β) (P : Interp α β → Prop) :
    (∀ m, Weak d m → P m) ↔ ∀ H, P (fill d H) := by
  constructor
  · intro h H; exact h _ ((weak_iff_fill d _).mpr ⟨H, rfl⟩)
  · intro h m hm; obtain ⟨H, rfl⟩ := (weak_iff_fill d m).mp hm; exact h H

/-! ## 2. Models -/

theorem closed_model (d : Desc α β) : ∃ m, Closed d m := ⟨fun a => (d a).join, fun _ => rfl⟩

/-- The closure model is a model of the weaker reading (it is one choice among its models). -/
theorem weak_model (d : Desc α β) : ∃ m, Weak d m :=
  ⟨fun a => (d a).join, fun a r h => by simp [h]⟩

/-- The weaker reading of a `total` symbol has a model when the result sort has an element: the
model picks one where the text says nothing (`fill` with a constant parameter). -/
theorem weakTotal_model (d : Desc α β) (hd : ∀ a, d a ≠ some none) (w : β) : ∃ m, WeakTotal d m :=
  ⟨fill d fun _ => some w, (weakTotal_iff_fill d hd _).mpr ⟨fun _ => some w, fun _ => rfl, rfl⟩⟩

/-- … and none when the result sort has no element: a value model (KCore's: a sort's elements are
its values, no G-nonempty) of a `total` symbol into a sort without values does not exist. -/
theorem weakTotal_no_model (d : Desc α β) (hβ : β → False) (a : α) :
    ¬ ∃ m, WeakTotal d m := by
  rintro ⟨m, -, ht⟩
  cases hm : m a with
  | none => have := ht a; rw [hm] at this; cases this
  | some v => exact hβ v

/-- The middle design has exactly one model for each parameter. -/
theorem middle_model (d : Desc α β) (H : Interp α β) : ∃ m, m = fill d H ∧ ∀ m', m' = fill d H → m' = m :=
  ⟨fill d H, rfl, fun _ hm => hm⟩

/-! ## 3. A definition with priorities

Rule 1 (the higher priority): `a ⇒ b requires op(arg) ==K w`. Rule 2: `a ⇒ c`. `==K` is strict:
its result is `true` when `op(arg)` is `w`, `false` at another value, ⊥ when `op(arg)` is ⊥. -/

inductive Cfg where
  | a
  | b
  | c
  deriving DecidableEq

/-- The successors of `a` in a model `m` of Γ with the step's closure: rule 1's where its
`requires` is `true` there, rule 2's where it is not (rule 2's axiom carries rule 1's negated
`applies` pattern; the closure axiom admits no other successor). -/
def Succ (m : Interp α β) (arg : α) (w : β) : Cfg → Cfg → Prop
  | .a, .b => m arg = some w
  | .a, .c => m arg ≠ some w
  | _, _ => False

/-- KCore's `Step` over an evaluation relation `E` of the application (`E arg r`: it evaluates to
`r`; no derivation where evaluation has no result): rule 1 where the `requires` evaluates to `true`,
rule 2 where rule 1 does not apply, i.e. its `requires` evaluates to something else, ⊥ included
(`NotApplies`, `RuleReqFails`). -/
inductive Step (E : α → Option β → Prop) (arg : α) (w : β) : Cfg → Cfg → Prop
  | r1 (h : E arg (some w)) : Step E arg w .a .b
  | r2 (r : Option β) (h : E arg r) (hr : r ≠ some w) (hf : ∀ r', E arg r' → r' ≠ some w) :
      Step E arg w .a .c

/-- Soundness for the theory with the models `T`: every step holds in every model. -/
def Sound (T : Interp α β → Prop) (E : α → Option β → Prop) (arg : α) (w : β) : Prop :=
  ∀ x y, Step E arg w x y → ∀ m, T m → Succ m arg w x y

/-- Completeness for the theory with the models `T`: every successor in every model is a step. -/
def Complete (T : Interp α β → Prop) (E : α → Option β → Prop) (arg : α) (w : β) : Prop :=
  ∀ m, T m → ∀ x y, Succ m arg w x y → Step E arg w x y

/-- The closed reading's evaluation: where the text says nothing, undefined (a hook's `some none`). -/
def EClosed (d : Desc α β) (a : α) (r : Option β) : Prop := r = (d a).join

/-- The evaluation the weaker reading allows: a result only where the text states one. -/
def EWeak (d : Desc α β) (a : α) (r : Option β) : Prop := d a = some r

/-- The middle design's evaluation, at the parameter `H`. -/
def EMid (d : Desc α β) (H : Interp α β) (a : α) (r : Option β) : Prop := r = fill d H a

/-- Over a functional evaluation that the theory's models all agree with, the step is sound and
complete. -/
theorem sound_complete_of_det {T : Interp α β → Prop} {E : α → Option β → Prop} {arg : α} {w : β}
    (v : Option β) (hE : ∀ r, E arg r ↔ r = v) (hT : ∀ m, T m → m arg = v) :
    Sound T E arg w ∧ Complete T E arg w := by
  constructor
  · intro x y hs m hm
    cases hs with
    | r1 h => show m arg = some w; rw [hT m hm, ← (hE _).mp h]
    | r2 r h hr _ => show m arg ≠ some w; rw [hT m hm, ← (hE _).mp h]; exact hr
  · intro m hm x y hs
    cases x <;> cases y <;> simp only [Succ] at hs
    · exact .r1 ((hE _).mpr (by rw [← hT m hm, hs]))
    · exact .r2 v ((hE _).mpr rfl) (by rw [← hT m hm]; exact hs)
        (fun r' h' => by rw [(hE _).mp h', ← hT m hm]; exact hs)

/-- **The closed reading: sound and complete**, at every argument. -/
theorem closed_sound_complete (d : Desc α β) (arg : α) (w : β) :
    Sound (Closed d) (EClosed d) arg w ∧ Complete (Closed d) (EClosed d) arg w :=
  sound_complete_of_det ((d arg).join) (fun _ => Iff.rfl) (fun _ hm => hm arg)

/-- **The middle design: sound and complete for every parameter**, at every argument. -/
theorem middle_sound_complete (d : Desc α β) (H : Interp α β) (arg : α) (w : β) :
    Sound (· = fill d H) (EMid d H) arg w ∧ Complete (· = fill d H) (EMid d H) arg w :=
  sound_complete_of_det (fill d H arg) (fun _ => Iff.rfl) (fun m hm => by rw [hm])

/-- The closed evaluation is the middle design's at the parameter ⊥ everywhere. -/
theorem eClosed_eq (d : Desc α β) : EClosed d = EMid d (fun _ => none) := by
  funext a r; simp only [EClosed, EMid, fill_none]

/-- A step that does not reach the undescribed part is the same for every parameter: what the
executable computes at `HookParams.none` holds for every `H` when no evaluation reaches a point the
text leaves open. -/
theorem middle_step_indep (d : Desc α β) {arg : α} (hd : d arg ≠ none) (H H' : Interp α β) (w : β) (x y : Cfg) :
    Step (EMid d H) arg w x y ↔ Step (EMid d H') arg w x y := by
  have : fill d H arg = fill d H' arg := by
    unfold fill; cases h : d arg with
    | none => exact absurd h hd
    | some r => rfl
  have hE : EMid d H arg = EMid d H' arg := by funext r; simp only [EMid, this]
  constructor <;> intro hs <;> cases hs
  · exact .r1 (by rw [← hE]; assumption)
  · rename_i r h hr hf; exact .r2 r (by rw [← hE]; exact h) hr (fun r' h' => hf r' (by rw [hE]; exact h'))
  · exact .r1 (by rw [hE]; assumption)
  · rename_i r h hr hf; exact .r2 r (by rw [hE]; exact h) hr (fun r' h' => hf r' (by rw [← hE]; exact h'))

/-! ## 4. The weaker reading at an argument the text leaves open -/

/-- **The weaker reading's own evaluation (no result where the text is silent) is sound**, at every
argument (below: and incomplete where the text is silent). -/
theorem weak_weak_sound (d : Desc α β) (arg : α) (w : β) : Sound (Weak d) (EWeak d) arg w := by
  intro x y hs m hm
  cases hs with
  | r1 h => exact hm _ _ h
  | r2 r h hr _ => show m arg ≠ some w; rw [hm _ _ h]; exact hr


section open_arg
variable (d : Desc α β) {arg : α} (hopen : d arg = none) (w : β)
include hopen

/-- **The closed evaluation is unsound for the weaker reading**: it steps by rule 2, and a model of
the weaker reading where `op(arg)` is `w` has only rule 1's successor. -/
theorem weak_closed_unsound : ¬ Sound (Weak d) (EClosed d) arg w := by
  intro hs
  have hstep : Step (EClosed d) arg w .a .c :=
    .r2 none (by simp [EClosed, hopen]) (by simp) (fun r' h' => by simp [EClosed, hopen] at h'; simp [h'])
  have := hs _ _ hstep (fill d fun _ => some w) ((weak_iff_fill d _).mpr ⟨_, rfl⟩)
  exact this (by simp [fill, hopen])

/-- … and incomplete: that model's successor `b` is no step. -/
theorem weak_closed_incomplete : ¬ Complete (Weak d) (EClosed d) arg w := by
  intro hc
  have := hc (fill d fun _ => some w) ((weak_iff_fill d _).mpr ⟨_, rfl⟩) .a .b (by simp [Succ, fill, hopen])
  cases this with
  | r1 h => simp [EClosed, hopen] at h

/-- **The weaker reading's own evaluation is incomplete** here: the closure model (a model of the weaker reading) has the successor
`c`, which the evaluation, having no result, cannot reach. -/
theorem weak_weak_incomplete : ¬ Complete (Weak d) (EWeak d) arg w := by
  intro hc
  have := hc (fun a => (d a).join) (fun a r h => by simp [h]) .a .c (by simp [Succ, hopen])
  cases this with
  | r2 r h _ _ => simp [EWeak, hopen] at h

/-- **No step relation at all is both sound and complete for the weaker reading here**: one model
has only `b` as successor, another only `c`. So no `Step`, however defined, meets both of KCore's
headline statements at such a definition. -/
theorem weak_no_sound_complete :
    ¬ ∃ S : Cfg → Cfg → Prop, (∀ x y, S x y → ∀ m, Weak d m → Succ m arg w x y) ∧
      (∀ m, Weak d m → ∀ x y, Succ m arg w x y → S x y) := by
  rintro ⟨S, hs, hc⟩
  have hb : S .a .b := hc (fill d fun _ => some w) ((weak_iff_fill d _).mpr ⟨_, rfl⟩) .a .b
    (by simp [Succ, fill, hopen])
  have := hs _ _ hb (fun a => (d a).join) (fun a r h => by simp [h])
  simp [Succ, hopen] at this

/-- The same for a symbol declared `total`, when its result sort has two elements. -/
theorem weakTotal_no_sound_complete (hd : ∀ a, d a ≠ some none) {w' : β} (hw : w' ≠ w) :
    ¬ ∃ S : Cfg → Cfg → Prop, (∀ x y, S x y → ∀ m, WeakTotal d m → Succ m arg w x y) ∧
      (∀ m, WeakTotal d m → ∀ x y, Succ m arg w x y → S x y) := by
  rintro ⟨S, hs, hc⟩
  have hb : S .a .b := hc (fill d fun _ => some w)
    ((weakTotal_iff_fill d hd _).mpr ⟨_, fun _ => rfl, rfl⟩) .a .b (by simp [Succ, fill, hopen])
  have := hs _ _ hb (fill d fun _ => some w') ((weakTotal_iff_fill d hd _).mpr ⟨_, fun _ => rfl, rfl⟩)
  simp [Succ, fill, hopen, hw] at this

/-- **The lower rule is neither provably applicable nor provably inapplicable** under the weaker
reading: it applies in one model and not in another. -/
theorem weak_rule2_undetermined :
    ¬ (∀ m, Weak d m → Succ m arg w .a .c) ∧ ¬ (∀ m, Weak d m → ¬ Succ m arg w .a .c) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact h (fill d fun _ => some w) ((weak_iff_fill d _).mpr ⟨_, rfl⟩) (by simp [fill, hopen])
  · exact h (fun a => (d a).join) (fun a r h => by simp [h]) (by simp [Succ, hopen])

end open_arg

/-! ## 5. The subjects -/

open KCore

/-- `substrString(S, A, B)` (declared `total`): the text's value on valid indices, nothing elsewhere
(KCore's `KStr.substr` is the described part). -/
def substrD : Desc (List Char × Int × Int) (List Char) := fun (s, i, j) => (KStr.substr s i j).map some

/-- `findString(S, N, I)` (partial): the text's value when I is a position of S. -/
def findD : Desc (List Char × List Char × Int) Int := fun (s, n, i) => (KStr.find s n i).map some

/-- `ordChar(S)` (partial): the text's value at a string of one code point. -/
def ordD : Desc (List Char) Nat := fun s => (KStr.ord s).map some

/-- A user function `half(X) => X /Int 2 requires X %Int 2 ==Int 0`, no other clause: its clause is
its described part (whether or not it is declared `[total]`). -/
def halfD : Desc Int Int := fun n => if n % 2 = 0 then some (some (n / 2)) else none

/-- KCore's hook is the closure reading of each described part: `hook` gives `some none` exactly
where the text says nothing. -/
example : hook stringSubstr [strV "abc".toList, int 2, int 1] = some none ∧
    hook stringSubstr [strV "abc".toList, int 0, int 2] = some (some (strV "ab".toList)) ∧
    hook stringFind [strV "abc".toList, strV "b".toList, int 7] = some none ∧
    hook stringOrd [strV "ab".toList] = some none ∧
    substrD ("abc".toList, 2, 1) = none ∧ findD ("abc".toList, "b".toList, 7) = none ∧
    ordD "ab".toList = none ∧ halfD 1 = none ∧ halfD 4 = some (some 2) := by decide +kernel

theorem substr_never_bot : ∀ a, substrD a ≠ some none := by
  rintro ⟨s, i, j⟩; simp only [substrD]; cases KStr.substr s i j <;> simp

theorem half_never_bot : ∀ a, halfD a ≠ some none := by
  intro a; simp only [halfD]; split <;> simp

/-- (i) `substrString("abc", 2, 1)` under `requires substrString(…) ==K ""`: KCore's reading is sound
and complete; under the weaker reading of the `total` symbol no step relation is both. -/
theorem substr_subject :
    (Sound (Closed substrD) (EClosed substrD) ("abc".toList, 2, 1) [] ∧
      Complete (Closed substrD) (EClosed substrD) ("abc".toList, 2, 1) []) ∧
    ¬ ∃ S : Cfg → Cfg → Prop,
      (∀ x y, S x y → ∀ m, WeakTotal substrD m → Succ m ("abc".toList, 2, 1) [] x y) ∧
      (∀ m, WeakTotal substrD m → ∀ x y, Succ m ("abc".toList, 2, 1) [] x y → S x y) :=
  ⟨closed_sound_complete _ _ _,
   weakTotal_no_sound_complete substrD (by decide +kernel) [] substr_never_bot (w' := ['z']) (by decide)⟩

/-- (i) `findString("abc", "b", 7)` and `ordChar("ab")` (not declared total): the same, for the weaker
reading with ⊥ among its models. -/
theorem find_ord_subject :
    ¬ (∃ S : Cfg → Cfg → Prop,
      (∀ x y, S x y → ∀ m, Weak findD m → Succ m ("abc".toList, "b".toList, 7) (-1) x y) ∧
      (∀ m, Weak findD m → ∀ x y, Succ m ("abc".toList, "b".toList, 7) (-1) x y → S x y)) ∧
    ¬ (∃ S : Cfg → Cfg → Prop,
      (∀ x y, S x y → ∀ m, Weak ordD m → Succ m "ab".toList 97 x y) ∧
      (∀ m, Weak ordD m → ∀ x y, Succ m "ab".toList 97 x y → S x y)) :=
  ⟨weak_no_sound_complete findD (by decide +kernel) (-1), weak_no_sound_complete ordD (by decide +kernel) 97⟩

/-- (ii) A user function `h` with `h(X) => 1 requires half(X) ==Int 0` and `h(X) => 2 [owise]`, at
`X = 1` (no clause of `half` applies): under KCore's reading `h(1) = 2` in every model; under the
weaker reading, with `half` declared `[total]` or not, the `[owise]` clause is neither provably
applicable nor provably inapplicable, and no evaluation of `h(1)` is sound and complete. -/
theorem half_subject :
    (Sound (Closed halfD) (EClosed halfD) 1 0 ∧ Complete (Closed halfD) (EClosed halfD) 1 0) ∧
    (¬ (∀ m, Weak halfD m → Succ m 1 0 .a .c) ∧ ¬ (∀ m, Weak halfD m → ¬ Succ m 1 0 .a .c)) ∧
    ¬ (∃ S : Cfg → Cfg → Prop, (∀ x y, S x y → ∀ m, WeakTotal halfD m → Succ m 1 0 x y) ∧
      (∀ m, WeakTotal halfD m → ∀ x y, Succ m 1 0 x y → S x y)) :=
  ⟨closed_sound_complete _ _ _, weak_rule2_undetermined halfD (by decide) 0,
   weakTotal_no_sound_complete halfD (by decide) 0 half_never_bot (w' := 7) (by decide)⟩

/-- (ii) Declared `[total]`, `half` has no value at 1 under KCore's reading: the totality FnHyp asks
for is false, so KCore's headline theorems hold of such a definition only vacuously; the middle
design at a parameter defined at 1 meets it. -/
theorem half_total :
    (∀ m, Closed halfD m → m 1 = none) ∧ (fill halfD (fun _ => some 7)) 1 = some 7 :=
  ⟨fun m hm => by rw [hm 1]; decide, by decide⟩

/-- The middle design at the subjects: one model per parameter, sound and complete for each, and its
models over all parameters are the weaker reading's (§1); at `HookParams.none` it is KCore's. -/
theorem middle_subjects (H : Interp (List Char × Int × Int) (List Char)) (H' : Interp Int Int) :
    (Sound (· = fill substrD H) (EMid substrD H) ("abc".toList, 2, 1) [] ∧
      Complete (· = fill substrD H) (EMid substrD H) ("abc".toList, 2, 1) []) ∧
    (Sound (· = fill halfD H') (EMid halfD H') 1 0 ∧ Complete (· = fill halfD H') (EMid halfD H') 1 0) ∧
    EClosed halfD = EMid halfD (fun _ => none) :=
  ⟨middle_sound_complete _ _ _ _, middle_sound_complete _ _ _ _, eClosed_eq _⟩

#print axioms weak_no_sound_complete
#print axioms weakTotal_no_sound_complete
#print axioms middle_sound_complete
#print axioms weak_iff_fill
#print axioms substr_subject
#print axioms half_subject

end UndefExperiment
