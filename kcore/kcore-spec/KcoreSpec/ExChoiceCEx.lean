/-
  KCore. The choice among instances, where a function clause may bind variables by `\exists`: the
  value model at a transition T, for a semantics `coreOKEx` accepts.

  - `stepBy_of_stepMBy_exCEx`: a `StepMBy` step between configurations is a `StepBy` step; every
    configuration is `StepDecided` by `stepDecided_ppCEx`.
  - `stdI_T_modelCEx`: `stdI_T c T` is a model of `Γc` with the step's closure, under `HypModelCore`, `FnSolves`,
    `ClausePreDecided`, `ClausePostDecided` and `OpenLaws`. The functions' equations are
    `AtT.satFnsGoalEx`, which reads the equation of a clause with existential variables, and Bool's
    closure is `boolClosed_modelClT`; neither reads `coreOK`.
  - `stdI_model_exCEx`: the value model `stdI c` is the instance `T := StepM c`.
  - `has_model_choice_exCEx`: `has_model_choice`'s conclusion, the model `stdI_T c (liftT_ex c T)`.
    `HypModelCore`, `ClausePreDecided` and `ClausePostDecided` are read from `coreOKEx` and `FnHyp`.
-/
import KcoreSpec.ExChoice
import KcoreSpec.FnModelCEx
import KcoreSpec.HypModelCoreEx
import KcoreSpec.ModelHasEx

set_option autoImplicit false

namespace KCore

open ML Faithful Faithful.Model

/-- **A `StepMBy` step between configurations is a `StepBy` step**, for a semantics that `coreOKEx`
accepts whose functions terminate, whose rules have `ruleSorted` and `rulePlainEx`. -/
theorem stepBy_of_stepMBy_exCEx {c : Semantics} (h : c.coreOKEx = true) (hft : FnTerminates c)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainEx r' = true)
    {r : Rule} {σ : Subst} {x y : Config c} (hb : StepMBy c r σ x.val y.val) : StepBy c r σ x y := by
  obtain ⟨hr, hst⟩ := hb
  have hd := stepDecided_ppCEx (hypSoundEx_of_coreEx h) hft (fun r' hr' => (hrules r' hr').1) x.val
  exact ⟨hr, hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1, hst.2.2.2.2.2.1, hst.2.2.2.2.2.2.1,
    notApplies_of_stepMAt_ex hd hst⟩

/-- **The value model at a transition T is a model of `Γc` with the step's closure, where a clause
may bind variables by `\exists`**: under `HypModelCore` (whose sortedness of the clauses is
`sortedOKClEx`) and `FnSolves`, with each clause's two predicates decided, for rules with `ruleSorted` and
`rulePlainEx`, where every T step between configurations is a `StepM` step (`hsub`), every `StepMBy`
instance of a rule without existential variables is in T (`hall`), and for a rule with existential
variables some instance that differs from a given one at ē only is (`hsome`). -/
theorem stdI_T_modelCEx (c : Semantics) (hm : HypModelCore c) (hsol : FnSolves c) (hp : ClausePreDecided c)
    (hq : ClausePostDecided c) (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (T : GroundTerm → GroundTerm → Prop)
    (hsub : ∀ x y, c.sortOf x = some topCellSort → c.sortOf y = some topCellSort → T x y → StepM c x y)
    (hall : ∀ r σ x y, StepMBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ r σ x y, StepMBy c r σ x y → r.exs ≠ [] → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepMBy c r σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵP (Γc c ∪ Γstep c) := by
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact AtT.satSigGoal hm φ hφ
    · exact AtT.satConsGoal hm hl φ hφ
    · exact AtT.satDomainsGoal hm φ hφ
    · exact AtT.satCollsGoal hm φ hφ
    · exact AtT.satFnsGoalEx hm hsol (hypModelCore_clsFactsCe hm) hp hq φ hφ
    · exact satRulesGoal_T hm hrules T hall hsome φ hφ
    · exact AtT.satFallbackGoal hm φ hφ
  · obtain ⟨-, hlit, rfl⟩ := hφ
    exact boolClosed_modelClT hm hlit
  · exact satStepGoal_T hm hrules T hsub φ hφ

/-- **The value model is a model of `Γc` with the step's closure, where a clause may bind variables
by `\exists`**: `stdI_T_modelCEx` at `T := StepM c`. -/
theorem stdI_model_exCEx (c : Semantics) (hm : HypModelCore c) (hsol : FnSolves c) (hp : ClausePreDecided c)
    (hq : ClausePostDecided c) (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true) :
    stdI c ⊧ᴵP (Γc c ∪ Γstep c) :=
  stdI_T_modelCEx c hm hsol hp hq hl hrules (StepM c) (fun _ _ _ _ hT => hT)
    (fun r σ _ _ hb _ => (stepM_iff_by c).mpr ⟨r, σ, hb⟩)
    (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, (stepM_iff_by c).mpr ⟨r, σ, hb⟩⟩)

/-- **The choice among instances is free, where a clause may bind variables by `\exists`**:
`has_model_choice`'s conclusion, for a semantics that `coreOKEx` accepts whose functions meet
`FnHyp` and whose rules have `ruleSorted` and `rulePlainEx`. The model is the value model at
`liftT_ex c T`: `hsub` gives its closure, `hall` and `hsome` its rules' axioms, a rule with
existential variables read through `hsome`. -/
theorem has_model_choice_exCEx (c : Semantics) (h : c.coreOKEx = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (T : Config c → Config c → Prop)
    (hsub : ∀ x y, T x y → Step c x y)
    (hall : ∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y') :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  have hfm := fnModel_of_fnHypCEx h hf
  have hfd := hfm.1
  have hm := hypModelCore_of_coreEx h hfm.1
  refine ⟨Elem, inferInstance, stdI_T c (liftT_ex c T),
    stdI_T_modelCEx c hm hfm.2 (clausePreDecided_of_fnHypCEx h hf) (clausePostDecided_of_fnHypCEx h hf)
      hf.2.2.2.2.2 hrules (liftT_ex c T) ?_ ?_ ?_,
    fun x y => (liftT_ex_iff T x y).symm.trans (step_iff_stdI_T c hm _ x y)⟩
  · intro x y hx hy hT
    obtain ⟨r, σ, hb⟩ := step_iff_by.mp (hsub ⟨x, hx⟩ ⟨y, hy⟩ (hT hx hy))
    exact (stepM_iff_by c).mpr ⟨r, σ, stepMBy_of_stepBy_ex hfd hrules hb⟩
  · intro r σ x y hb hex hx hy
    exact hall ⟨x, hx⟩ ⟨y, hy⟩ r σ (stepBy_of_stepMBy_exCEx (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hf.1 hrules hb) hex
  · intro r σ x y hb _
    by_cases hx : c.sortOf x = some topCellSort
    · have hy := rhs_sorted_open hm (hrules r hb.1).1 hb.2.1 hb.2.2.2.2.2.1
      obtain ⟨y', σ', hag, hb', hT⟩ :=
        hsome ⟨x, hx⟩ ⟨y, hy⟩ r σ (stepBy_of_stepMBy_exCEx (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hf.1 hrules hb)
      exact ⟨y'.val, σ', hag, stepMBy_of_stepBy_ex hfd hrules hb', fun _ _ => hT⟩
    · exact ⟨y, σ, fun _ _ => rfl, hb, fun hx' => absurd hx' hx⟩

end KCore
