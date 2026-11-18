/-
  KCore. Completeness at one configuration under the hypotheses of `complete_hyp`, and the
  statements a run of the checked executor gives at the configuration it ran.

  - `complete_at_hyp`: `complete_at` (Sound.lean) for a semantics whose functions meet `FnHyp`,
    which makes every configuration `StepDecided` (`stepDecided_of_fnHyp`). `complete_hyp`'s
    statement follows from it (`complete_hyp_of_at`): an outcome function with `OutIs` lists, at
    each configuration, a list holding its outcomes.
  - `CExec.run_exact`: where the executor ran at fuel n and nothing ran out of fuel
    (`outOfFuel c n x = false`), the successors it lists are exactly what the theory entails of x:
    with the step's closure every successor of x is one of them (`complete_at_step`, the
    configuration being `StepDecided` by `CExec.stepDecided_of_fuel`), and each of them is a
    successor of x in every model of `Γ c` (`sound_at_step`), both read where `execReady` makes the
    semantics read no confined sort (`CExec.readsConfined_of_execReady`). Given `FnDet`, which `step_iff_at` and
    `stepDecided_of_fuel` read (a `requires` and a right-hand side have one result).
-/
import KcoreSpec.Sound
import KcoreSpec.CollExecFinal

set_option autoImplicit false

namespace KCore

open ML Faithful

/-- **Completeness at a configuration** of a semantics that `coreOK` accepts and whose functions
meet `FnHyp`, for any list of outcomes holding the successors by the rules whose left side binds
every variable and a family for each unblocked match of the other rules. -/
theorem complete_at_hyp (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (x : Config c)
    (os : List Outcome)
    (hval : ∀ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] → StepBy c r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, Unblocked c r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os) :
    (Γc c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat c)))) :=
  complete_at c h x (stepDecided_of_fnHyp h hf x) os hval hfam hf.2.2.2.2.1.2

/-- `complete_hyp`'s statement follows from `complete_at_hyp`: an outcome function with `OutIs`
lists, at each configuration, a list holding its outcomes. -/
theorem complete_hyp_of_at (c : Semantics) (ref : OutFn) (h : c.coreOK = true) (hf : FnHyp c) :
    CompleteC c ref :=
  fun href x => complete_at_hyp c h hf x (ref x.val)
    (fun y r σ hop hs => ((href x).1 y.val).mpr ⟨y.property, r, σ, hop, hs⟩) (href x).2.2

/-- **Consistency** of a semantics that `coreOK` accepts and whose functions meet `FnHyp`:
`consistent_of`, `FnHyp` giving `FnDet` and `FnSolves` (`fnModel_of_fnHyp`), `ClausePreDecided`
(`clausePreDecided_of_fnHyp`) and `OpenLaws`. -/
theorem consistent_of_fnHyp (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) : Consistent c :=
  consistent_of c h (fnModel_of_fnHyp h hf).1 (fnModel_of_fnHyp h hf).2 (clausePreDecided_of_fnHyp h hf)
    hf.2.2.2.2.2

namespace CExec

variable {c : Semantics}

/-- `execReady`'s conjuncts beside `sortedOK` (which `coreOK` holds) and `srReady`. -/
def execReadyRest (c : Semantics) : Bool :=
  c.matchReadyO &&
  c.allFns.all (fun fn => fn.clauses.all fun cl =>
    readyL c cl.vars cl.pats && binds cl.vars.length (varOccsList cl.pats)) &&
  c.rules.all (fun r => readyL c r.vars [r.lhs] && binds r.vars.length (varOccs r.lhs) &&
    predAtoms r.pre && predAtoms r.post) &&
  c.asideFree &&
  c.fns.all (fun f => f.clauses.all fun cl => cl.pre.isTop)

theorem execReady_of_rest (h : c.coreOK = true) (hsr : c.srReady = true) (hr : execReadyRest c = true) :
    execReady c = true := by
  simp only [execReadyRest, Bool.and_eq_true] at hr
  simp only [execReady, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨(Semantics.coreOK_parts h).1, hsr⟩, hr.1.1.1.1⟩, hr.1.1.1.2⟩, hr.1.1.2⟩, hr.1.2⟩, hr.2⟩

kernel_rfl execReady_withHooks : ∀ (c : Semantics) (H : HookParams), execReady (c.withHooks H) = execReady c

/-- A predicate `predVal` evaluates has no binder. -/
theorem hasBinder_of_predAtoms : ∀ {p : Cond}, predAtoms p = true → p.hasBinder = false
  | .top, _ | .equals .., _ | .mem .., _ => rfl
  | .and p q, h => by
    simp only [predAtoms, Bool.and_eq_true] at h
    simp [Cond.hasBinder, hasBinder_of_predAtoms h.1, hasBinder_of_predAtoms h.2]

/-- A semantics `coreOK` accepts and `execReady` makes ready reads no confined sort: `execReady`
asks every rule's left side and every clause's patterns to bind each of its variables and every
rule's predicates to be conjunctions of atoms, which hold no binder, and `coreOK`'s `sortedOK`
asks every clause's to be `top`. -/
theorem readsConfined_of_execReady (h : c.coreOK = true) (hr : execReady c = true) :
    c.readsConfined = false := by
  have hpreTop := KCore.CExec.clausesPreTop_of_execReady hr
  have hok := (Semantics.coreOK_parts h).1
  have hready := hr
  simp only [execReady, Bool.and_eq_true, List.all_eq_true] at hr
  replace hr := hr.1
  obtain ⟨⟨⟨-, hfn⟩, -⟩, -⟩ := hr
  simp only [Semantics.readsConfined, Bool.or_eq_false_iff, List.any_eq_false]
  refine ⟨fun r hr' => ?_, fun fn hfn' => ?_⟩
  · obtain ⟨hpre, hpost, hb⟩ := rule_atoms_of_execReady hready hr'
    simp [Rule.opens_of_binds hb, hasBinder_of_predAtoms hpre, hasBinder_of_predAtoms hpost]
  · simp only [List.any_eq_true, not_exists, not_and]
    intro cl hcl
    have hpre := Semantics.clausesPreTop_spec hpreTop hfn' hcl
    have hpost := Semantics.sortedOK_clausePost hok hfn' hcl
    have hb := (hfn fn (by simp [Semantics.allFns, hfn']) cl hcl).2
    simp [Clause.opens_of_binds hb, hpre, hpost, Cond.hasBinder]

/-- **A run at a fuel where nothing ran out is exact in matching logic**: with the step's closure,
every successor of x is one `successorsN c n x` lists, and each one it lists is a successor of x in
every model of `Γ c`. Given `FnDet`. -/
theorem run_exact (h : c.coreOK = true) (hr : execReady c = true) (hfd : FnDet c) {n : Nat}
    {x : Config c} (hf : outOfFuel c n x.val = false) :
    ((Γ c ∪ Γstep c) ⊧
        (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((successorsN c n x.val).map (den c))))) ∧
      ∀ y ∈ successorsN c n x.val, Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y)) := by
  have hpreTop := KCore.CExec.clausesPreTop_of_execReady hr
  have hrc := readsConfined_of_execReady h hr
  refine ⟨complete_at_step c h hrc x (stepDecided_of_fuel hr hfd hf) _
    fun y hy => (step_iff_at hr hfd hf).mp hy, fun y hy => ?_⟩
  obtain ⟨hy', hst⟩ := successorsN_step_ready hr hy
  exact sound_at_step c h hrc x ⟨y, hy'⟩ hst

end CExec

end KCore
