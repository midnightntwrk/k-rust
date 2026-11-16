/-
  The facts the course derives on peano (`milestone-1/peano.k`), as theorems over the generated
  package: the first rule's left side as a term, the substitution under which it denotes the
  configuration holding `run(s(s(z)))`, the value of its right side there, the three steps of the
  run from `run(s(s(z)))` and the stuck end `done(z)`, and the instances of soundness and
  completeness at the first step and at the end.

  kompile writes the rule `run(s(N)) => run(pred(s(N)))` with an alias: its left side holds
  `s(N) #as V` (`V` variable 1) and its right side `pred(V)`, so the substitution gives variable 1
  the value `s(s(z))`; the counter cell is variable 2.
-/
import User.Proofs
import Peano.Sound

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Peano

open KCore ML

/-! ## The configurations of the run -/

/-- The configuration with `run(s(s(z)))` in the k cell and the counter at 0. -/
def runSSZ : Config c := ⟨cfg (run (s (s z))) ctr0, sortOf_of_T T_eq (by decide +kernel)⟩
/-- The configuration with `run(s(z))` in the k cell. -/
def runSZ : Config c := ⟨cfg (run (s z)) ctr0, sorted_runSZ⟩
/-- The configuration with `run(z)` in the k cell. -/
def runZ : Config c := ⟨cfg (run z) ctr0, sorted_runZ⟩
/-- The configuration with `done(z)` in the k cell (`z` injected into `Val`). -/
def doneZ : Config c := ⟨cfg (done (natVal z)) ctr0, sorted_doneZ⟩

/-! ## The first rule, its substitution, its two sides -/

/-- The left side of the first rule, `<k> run(s(N) #as V) </k>` in the configuration pattern:
the k cell holds the sequence of `run(s(N) #as V)`, injected from `State` into `KItem`, and
`.K`; N is variable 0, V variable 1, the counter cell variable 2. -/
theorem rule0_lhs : (c.rules[0]'(by rw [rules_length]; decide)).lhs =
    .app topLabel [.app Sym.«<k>» [.app kseq [.inj Srt.«State» KCore.Srt.kitem
      (.app Sym.«run» [.as (.app Sym.«s» [.var 0]) 1]), .app dotk []]], .var 2] :=
  congrArg Rule.lhs (Option.some.inj ((List.getElem?_eq_getElem _).symm.trans rule0))

/-- The right side of the first rule: `run(pred(V))` in the k cell, the counter unchanged. -/
theorem rule0_rhs : (c.rules[0]'(by rw [rules_length]; decide)).rhs =
    .app topLabel [.app Sym.«<k>» [.app kseq [.inj Srt.«State» KCore.Srt.kitem
      (.app Sym.«run» [.app Sym.«pred» [.var 1]]), .app dotk []]], .var 2] :=
  congrArg Rule.rhs (Option.some.inj ((List.getElem?_eq_getElem _).symm.trans rule0))

/-- The substitution of the first step: N ↦ s(z), V ↦ s(s(z)), the counter cell ↦ 0. -/
def σ₁ : Subst := [(0, s z), (1, s (s z)), (2, ctr0)]

/-- The first rule's variables have sorts `Nat`, `Nat` and the counter's, and σ₁ gives each a
value of its sort. -/
theorem σ₁_wellSorted : c.WellSorted [Srt.«Nat», Srt.«Nat», KCore.Srt.counter] σ₁ :=
  Exec.wellSorted_iff.mp (by decide +kernel)

/-- **Matching.** Under σ₁ the first rule's left side denotes the configuration with
`run(s(s(z)))`: `s(N)` denotes `s(s(z))` with N = s(z), the alias gives V that same value, and the
counter cell's variable the counter. -/
theorem match_runSSZ : PatVal c σ₁
    (.app topLabel [.app Sym.«<k>» [.app kseq [.inj Srt.«State» KCore.Srt.kitem
      (.app Sym.«run» [.as (.app Sym.«s» [.var 0]) 1]), .app dotk []]], .var 2])
    (cfg (run (s (s z))) ctr0) :=
  .ctor rfl (.cons (.ctor rfl (.cons (.ctor rfl (.cons
    (.inj (w := run (s (s z))) (.ctor rfl (.cons (.as (.ctor rfl (.cons (.var rfl) .nil)) rfl) .nil)))
    (.cons (.ctor rfl .nil) .nil))) .nil)) (.cons (.var rfl) .nil))

/-- **Evaluation.** Under σ₁ the first rule's right side evaluates to the configuration with
`run(s(z))`: `pred(s(s(z)))` is `s(z)`. -/
theorem eval_rhs_runSSZ : EvalTerm c σ₁
    (.app topLabel [.app Sym.«<k>» [.app kseq [.inj Srt.«State» KCore.Srt.kitem
      (.app Sym.«run» [.app Sym.«pred» [.var 1]]), .app dotk []]], .var 2])
    (some (cfg (run (s z)) ctr0)) :=
  .ctor rfl (.cons (.ctor rfl (.cons (.ctor rfl (.cons
    (.inj (.ctor rfl (.cons (.call (rs := [some (s (s z))]) (by decide +kernel) rfl (.cons .var .nil) rfl
      (pred_succ (s z) (sortOf_of_T T_eq (by decide +kernel))) rfl) .nil)))
    (.cons (.ctor rfl .nil) .nil))) .nil)) (.cons .var .nil))

/-- No rule has a priority below 50, so no rule blocks another. -/
private theorem rule_prios : ∀ r ∈ c.rules, ¬ r.prio < 50 := by decide +kernel

/-! ## The run -/

/-- **A step**: from `run(s(s(z)))` to `run(s(z))`, by the first rule under σ₁ (`match_runSSZ`,
`eval_rhs_runSSZ`). -/
theorem step_runSSZ : Step c runSSZ runSZ :=
  .rule _ (List.mem_of_getElem? rule0) σ₁ σ₁_wellSorted match_runSSZ (fun _ h => nomatch h) .top
    eval_rhs_runSSZ (fun _ h => nomatch h) .top (fun r hr hlt => absurd hlt (rule_prios r hr))

/-- From `run(s(z))` to `run(z)`, by the first rule under N ↦ z, V ↦ s(z). -/
theorem step_runSZ : Step c runSZ runZ :=
  .rule _ (List.mem_of_getElem? rule0) [(0, z), (1, s z), (2, ctr0)]
    (Exec.wellSorted_iff.mp (by decide +kernel))
    (.ctor rfl (.cons (.ctor rfl (.cons (.ctor rfl (.cons
      (.inj (w := run (s z)) (.ctor rfl (.cons (.as (.ctor rfl (.cons (.var rfl) .nil)) rfl) .nil)))
      (.cons (.ctor rfl .nil) .nil))) .nil)) (.cons (.var rfl) .nil)))
    (fun _ h => nomatch h) .top
    (.ctor rfl (.cons (.ctor rfl (.cons (.ctor rfl (.cons
      (.inj (.ctor rfl (.cons (.call (rs := [some (s z)]) (by decide +kernel) rfl (.cons .var .nil) rfl
        (pred_succ z (sortOf_of_T T_eq (by decide +kernel))) rfl) .nil)))
      (.cons (.ctor rfl .nil) .nil))) .nil)) (.cons .var .nil)))
    (fun _ h => nomatch h) .top (fun r hr hlt => absurd hlt (rule_prios r hr))

/-- From `run(z)` to `done(z)`, by the second rule, `run(z #as N) => done(N)`, under N ↦ z. -/
theorem step_runZ : Step c runZ doneZ :=
  .rule _ (List.mem_of_getElem? rule1) [(0, z), (1, ctr0)]
    (Exec.wellSorted_iff.mp (by decide +kernel))
    (.ctor rfl (.cons (.ctor rfl (.cons (.ctor rfl (.cons
      (.inj (w := run z) (.ctor rfl (.cons (.as (.ctor rfl .nil) rfl) .nil)))
      (.cons (.ctor rfl .nil) .nil))) .nil)) (.cons (.var rfl) .nil)))
    (fun _ h => nomatch h) .top
    (.ctor rfl (.cons (.ctor rfl (.cons (.ctor rfl (.cons
      (.inj (.ctor rfl (.cons (.inj .var) .nil)))
      (.cons (.ctor rfl .nil) .nil))) .nil)) (.cons .var .nil)))
    (fun _ h => nomatch h) .top (fun r hr hlt => absurd hlt (rule_prios r hr))

/-- **No step** from `done(z)`: no rule's left side denotes it. -/
theorem stuck_doneZ (y : Config c) : ¬ Step c doneZ y := stuck_of nomatch_doneZ y

/-! ## Soundness at the first step -/

/-- No rule or clause has an open variable or a condition with a binder. -/
theorem readsConfined_course : c.readsConfined = false := by decide +kernel

/-- **Soundness at the first step**: in the theory Γ of peano, the configuration with
`run(s(s(z)))` has the one with `run(s(z))` as a successor, `⟦x⟧ → •⟦y⟧`. -/
theorem sound_runSSZ : Faithful.Γ c ⊧ (den c runSSZ.val ⇒ KoreAML.sNext (den c runSZ.val)) :=
  sound_at_step c coreOK_defn readsConfined_course runSSZ runSZ step_runSSZ

/-! ## Completeness at the first step and at the end

The step function: a configuration's one successor, or none. Peano is deterministic, so it lists
`Step`'s successors (`stepIs_next`). -/

open Classical in
/-- A configuration's successor where it has one (peano is deterministic), else none; `[]` off
the configurations. -/
noncomputable def next : StepFn := fun v =>
  if h : ∃ (hv : c.sortOf v = some topCellSort) (y : Config c), Step c ⟨v, hv⟩ y then
    [(Classical.choose (Classical.choose_spec h)).val] else []

/-- Where x steps to y, `next` at x lists y (peano is deterministic). -/
theorem next_of_step {x y : Config c} (h : Step c x y) : next x.val = [y.val] := by
  have h' : ∃ (hv : c.sortOf x.val = some topCellSort) (y : Config c), Step c ⟨x.val, hv⟩ y :=
    ⟨x.property, y, h⟩
  unfold next
  rw [dite_eq_left_of_eq_true (eq_true h')]
  exact congrArg (fun v => [v])
    (congrArg Subtype.val (deterministic c.hooks (Classical.choose_spec (Classical.choose_spec h')) h))

/-- `next` lists exactly `Step`'s successors. -/
theorem stepIs_next : StepIs c next := by
  intro x y
  constructor
  · intro hy
    unfold next at hy
    split at hy
    · rename_i h
      rw [List.mem_singleton] at hy
      subst hy
      exact ⟨(Classical.choose (Classical.choose_spec h)).property,
        Classical.choose_spec (Classical.choose_spec h)⟩
    · cases hy
  · rintro ⟨_, hs⟩
    rw [next_of_step hs]
    exact List.mem_singleton_self _

/-- **Completeness through `next`**: with the step's closure every successor of x is one `next`
lists (`Peano.complete` at the values `next` lists, `completeC_closed`: every left side binds its
variables). -/
theorem complete_next (x : Config c) : (Faithful.Γ c ∪ Faithful.Γstep c) ⊧
    (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((next x.val).map (den c)))) := by
  have h : (Faithful.Γc c ∪ Faithful.Γstep c) ⊧
      (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((next x.val).map (den c)))) :=
    (completeC_closed c next (Semantics.opens_of_readsConfined readsConfined_course).1).mp
      (Peano.complete _) stepIs_next x
  rw [Faithful.Γc_plain readsConfined_course] at h
  intro M _ I hI
  exact h hI

/-- `next` at the configuration with `run(s(s(z)))` lists the one with `run(s(z))`. -/
theorem next_runSSZ : next runSSZ.val = [runSZ.val] := next_of_step step_runSSZ

/-- `next` at the configuration with `done(z)` lists nothing. -/
theorem next_doneZ : next doneZ.val = [] := by
  unfold next
  rw [dite_eq_right_of_eq_false (eq_false fun ⟨_, y, hs⟩ => stuck_doneZ y hs)]

/-- **Completeness at the first step**: with the step's closure, every successor of the
configuration with `run(s(s(z)))` is the one `next` lists, the configuration with `run(s(z))`:
`⟦x⟧ → ◦ ⋁ [⟦y⟧]`. -/
theorem complete_runSSZ : (Faithful.Γ c ∪ Faithful.Γstep c) ⊧
    (den c runSSZ.val ⇒ KoreAML.allNext (KoreAML.disjList ([runSZ.val].map (den c)))) := by
  have : (Faithful.Γ c ∪ Faithful.Γstep c) ⊧
      (den c runSSZ.val ⇒ KoreAML.allNext (KoreAML.disjList ((next runSSZ.val).map (den c)))) :=
    complete_next runSSZ
  rwa [next_runSSZ] at this

/-- The same, the one-element disjunction read as its element: `⟦x⟧ → ◦⟦y⟧`. -/
theorem complete_runSSZ' : (Faithful.Γ c ∪ Faithful.Γstep c) ⊧
    (den c runSSZ.val ⇒ KoreAML.allNext (den c runSZ.val)) := complete_runSSZ

/-- **Completeness at the end**: with the step's closure, the configuration with `done(z)` has no
successor, `⟦x⟧ → ◦ ⋁ []`. -/
theorem complete_doneZ : (Faithful.Γ c ∪ Faithful.Γstep c) ⊧
    (den c doneZ.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den c)))) := by
  have : (Faithful.Γ c ∪ Faithful.Γstep c) ⊧
      (den c doneZ.val ⇒ KoreAML.allNext (KoreAML.disjList ((next doneZ.val).map (den c)))) :=
    complete_next doneZ
  rwa [next_doneZ] at this

/-- The same, the empty disjunction read as `⊥`: `⟦x⟧ → ◦⊥`. -/
theorem complete_doneZ' : (Faithful.Γ c ∪ Faithful.Γstep c) ⊧
    (den c doneZ.val ⇒ KoreAML.allNext ⊥) := complete_doneZ

#eval show Lean.CoreM Unit from do
  for n in [``rule0_lhs, ``rule0_rhs, ``σ₁_wellSorted, ``match_runSSZ, ``eval_rhs_runSSZ, ``step_runSSZ,
      ``step_runSZ, ``step_runZ, ``stuck_doneZ, ``sound_runSSZ, ``next_of_step, ``stepIs_next, ``next_runSSZ,
      ``next_doneZ, ``complete_runSSZ, ``complete_runSSZ', ``complete_doneZ, ``complete_doneZ'] do
    let axs ← Lean.collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end Peano
