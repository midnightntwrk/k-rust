/-
  KCore. The choice among instances, for rules with existential variables: the value model at a
  transition T.

  The value model at T (`stdI_T c T`) satisfies every part of `Γc` that does not read the step
  (`model_parts_T`), the rules' axioms where T holds every `StepMBy` instance of a rule without
  existential variables and, for a rule with some, an instance that differs from a given one at ē
  only (`satRulesGoal_T`), and the step's closure where every T step between configurations is a
  `StepM` step (`satStepGoal_T`). So:
  - `stdI_T_model`: `stdI_T c T` is a model of `Γc` with the step's closure under those three;
  - `step_iff_stdI_T`: at configurations its transition is T, for any T;
  - `stdI_model_ex`: the value model `stdI c` is the instance `T := StepM c`;
  - `has_model_choice_ex`: `has_model_choice`'s conclusion, the model `stdI_T c (liftT_ex c T)`.

  `StepM` and `Step` differ in how a competitor of a smaller priority is excluded: `¬ RuleApplies`
  and `NotApplies`. For competitors with `\top` premise predicates where a term has at most one
  result (`FnDet`), `NotApplies` gives `¬ RuleApplies` (`stepMAt_of_notApplies_ex`); where the
  competitors' conditions have results at their matches (`StepDecided`, from `ruleSorted` alone by
  `stepDecided_pp`), `¬ RuleApplies` gives `NotApplies` (`notApplies_of_stepMAt_ex`). Neither asks
  the rule to be one of the definition's.
-/
import KcoreSpec.ExStepT
import KcoreSpec.OpenChoice
import KcoreSpec.HoldsDecided
import KcoreSpec.ModelFnsDecided

set_option autoImplicit false

namespace KCore

open ML Faithful Faithful.Model

/-! ## `StepMAt` and the premises of `Step` -/

/-- **`Step`'s exclusion of competitors gives `StepM`'s**, for a rule not asked to be one of the
definition's, whose competitors have `rulePlainEx` (their premise predicates are `\top`), where a
term has at most one result (`FnDet`). -/
theorem stepMAt_of_notApplies_ex {c : Semantics} (hfd : FnDet c)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainEx r' = true)
    {r : Rule} {σ : Subst} {x y : GroundTerm} (hσ : c.WellSorted r.vars σ) (hm : PatVal c σ r.lhs x)
    (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true) (heval : EvalTerm c σ r.rhs (some y))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x) : StepMAt c r σ x y :=
  ⟨hσ, hm, hreq, hpre, heval, hens, hpost, fun r' hr' hlt =>
    not_ruleApplies_ofChoice hfd (Semantics.rulePlainEx_top (hrules r' hr').2).1 (hprio r' hr' hlt)⟩

/-- **`StepM`'s exclusion of competitors gives `Step`'s**, for a rule not asked to be one of the
definition's, where the competitors' conditions have results at their matches (`StepDecided`). -/
theorem notApplies_of_stepMAt_ex {c : Semantics} {r : Rule} {σ : Subst} {x y : GroundTerm}
    (hd : StepDecided c x) (hst : StepMAt c r σ x y) :
    ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x := fun r' hr' hlt =>
  notApplies_ofChoice (hd r' hr' fun r'' hr'' hlt' => hst.2.2.2.2.2.2.2 r'' hr'' (Nat.lt_trans hlt' hlt)).1
    (hst.2.2.2.2.2.2.2 r' hr' hlt)

/-- **A `StepBy` step is a `StepMBy` step**, for rules with `ruleSorted` and `rulePlainEx`, where a
term has at most one result. -/
theorem stepMBy_of_stepBy_ex {c : Semantics} (hfd : FnDet c)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainEx r' = true)
    {r : Rule} {σ : Subst} {x y : Config c} (hb : StepBy c r σ x y) : StepMBy c r σ x.val y.val :=
  ⟨hb.mem, stepMAt_of_notApplies_ex hfd hrules hb.hσ hb.hmatch hb.hreq hb.hpre hb.heval hb.hens hb.hpost hb.hprio⟩

/-- **A `StepMBy` step between configurations is a `StepBy` step**, for a semantics that `coreOK`
accepts whose functions terminate, whose rules have `ruleSorted` and `rulePlainEx`. -/
theorem stepBy_of_stepMBy_ex {c : Semantics} (h : c.coreOK = true) (hft : FnTerminates c)
    (hrules : ∀ r' ∈ c.rules, c.ruleSorted r' = true ∧ c.rulePlainEx r' = true)
    {r : Rule} {σ : Subst} {x y : Config c} (hb : StepMBy c r σ x.val y.val) : StepBy c r σ x y := by
  obtain ⟨hr, hst⟩ := hb
  have hd := stepDecided_pp (hypSound_of_core h) hft (fun r' hr' => (hrules r' hr').1) x.val
  exact ⟨hr, hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1, hst.2.2.2.2.2.1, hst.2.2.2.2.2.2.1,
    notApplies_of_stepMAt_ex hd hst⟩

/-! ## The value model at T -/

/-- **The value model at a transition T is a model of `Γc` with the step's closure**, for a
semantics that `coreOK` accepts with `HypModelCore`, whose rules have `ruleSorted` and
`rulePlainEx`, where every T step between configurations is a `StepM` step (`hsub`), every `StepMBy`
instance of a rule without existential variables is in T (`hall`), and for a rule with existential
variables some instance that differs from a given one at ē only is (`hsome`). -/
theorem stdI_T_model (c : Semantics) (h : c.coreOK = true) (hm : HypModelCore c) (hp : ClausePreDecided c)
    (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (T : GroundTerm → GroundTerm → Prop)
    (hsub : ∀ x y, c.sortOf x = some topCellSort → c.sortOf y = some topCellSort → T x y → StepM c x y)
    (hall : ∀ r σ x y, StepMBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ r σ x y, StepMBy c r σ x y → r.exs ≠ [] → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepMBy c r σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵP (Γc c ∪ Γstep c) := by
  obtain ⟨hSig, hCons, hDom, hColls, hFns, hFb, hBool⟩ := model_parts_T hm h hl T (AtT.satFnsGoal_decided hm hp)
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact hSig φ hφ
    · exact hCons φ hφ
    · exact hDom φ hφ
    · exact hColls φ hφ
    · exact hFns φ hφ
    · exact satRulesGoal_T hm hrules T hall hsome φ hφ
    · exact hFb φ hφ
  · obtain ⟨-, hl, rfl⟩ := hφ
    exact hBool hl
  · exact satStepGoal_T hm hrules T hsub φ hφ

/-- **At configurations the value model's transition is T**, for any T: x has y's element as a
successor in `stdI_T c T` exactly where `T x y`. -/
theorem step_iff_stdI_T (c : Semantics) (hm : HypModelCore c) (T : GroundTerm → GroundTerm → Prop)
    (x y : Config c) :
    T x.val y.val ↔ ¬ (stdI_T c T ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  constructor
  · intro hT hsat
    have h1 := hsat KoreAML.val0 (.val x.val)
    rw [interpret_impl] at h1
    have h2 := h1 ((den_val_T hm T x.val x.property _ _).mpr rfl)
    rw [interpret_neg] at h2
    exact h2 ((sNext_iff_T T _ _ _).mpr
      ⟨y.val, (den_val_T hm T y.val y.property _ _).mpr rfl, x.property, y.property, hT⟩)
  · intro hn
    simp only [Interpretation.satisfies, Valuation.satifies] at hn
    obtain ⟨e, hn⟩ := Classical.not_forall.mp hn
    obtain ⟨m, hn⟩ := Classical.not_forall.mp hn
    rw [interpret_impl] at hn
    have h1 : (den c x.val).interpret (stdI_T c T) e m :=
      Classical.byContradiction fun hc => hn fun h => absurd h hc
    have h2 : (KoreAML.sNext (den c y.val)).interpret (stdI_T c T) e m :=
      Classical.byContradiction fun hc => hn fun _ => interpret_neg.mpr hc
    rw [(den_val_T hm T x.val x.property e m).mp h1] at h2
    obtain ⟨y', hy', hst⟩ := (sNext_iff_T T _ e x.val).mp h2
    have hyy : Elem.val y' = .val y.val := (den_val_T hm T y.val y.property e _).mp hy'
    cases hyy
    exact hst.2.2

/-- **The value model is a model of `Γc` with the step's closure**, for rules with `ruleSorted` and
`rulePlainEx`: `stdI_T_model` at `T := StepM c`. -/
theorem stdI_model_ex (c : Semantics) (h : c.coreOK = true) (hm : HypModelCore c) (hp : ClausePreDecided c)
    (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true) :
    stdI c ⊧ᴵP (Γc c ∪ Γstep c) :=
  stdI_T_model c h hm hp hl hrules (StepM c) (fun _ _ _ _ hT => hT)
    (fun r σ _ _ hb _ => (stepM_iff_by c).mpr ⟨r, σ, hb⟩)
    (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, (stepM_iff_by c).mpr ⟨r, σ, hb⟩⟩)

/-! ## The choice among instances -/

/-- The transition of the value model for a relation on configurations: x and y are related where
every reading of them as configurations is related by T. At configurations it is T
(`liftT_ex_iff`); off them the value model's `next` does not read it (`StepE_T` asks both to be
configurations). -/
def liftT_ex (c : Semantics) (T : Config c → Config c → Prop) (x y : GroundTerm) : Prop :=
  ∀ (hx : c.sortOf x = some topCellSort) (hy : c.sortOf y = some topCellSort), T ⟨x, hx⟩ ⟨y, hy⟩

theorem liftT_ex_iff {c : Semantics} (T : Config c → Config c → Prop) (x y : Config c) :
    liftT_ex c T x.val y.val ↔ T x y :=
  ⟨fun h' => h' x.property y.property, fun h' _ _ => h'⟩

/-- **The choice among instances is free, for rules with existential variables**:
`has_model_choice`'s conclusion, for a semantics that `coreOK` accepts whose functions meet `FnHyp`
and whose rules have `ruleSorted` and `rulePlainEx`. The model is the value model at `liftT_ex c T`:
`hsub` gives its closure, `hall` and `hsome` its rules' axioms, a rule with existential variables
read through `hsome`. -/
theorem has_model_choice_ex (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (T : Config c → Config c → Prop)
    (hsub : ∀ x y, T x y → Step c x y)
    (hall : ∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y') :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  have hm := hypModel_of_fnHyp h hf
  have hfd := (fnModel_of_fnHyp h hf).1
  refine ⟨Elem, inferInstance, stdI_T c (liftT_ex c T), stdI_T_model c h hm (clausePreDecided_of_fnHyp h hf) hf.2.2.2.2.2 hrules (liftT_ex c T) ?_ ?_ ?_,
    fun x y => (liftT_ex_iff T x y).symm.trans (step_iff_stdI_T c hm _ x y)⟩
  · intro x y hx hy hT
    obtain ⟨r, σ, hb⟩ := step_iff_by.mp (hsub ⟨x, hx⟩ ⟨y, hy⟩ (hT hx hy))
    exact (stepM_iff_by c).mpr ⟨r, σ, stepMBy_of_stepBy_ex hfd hrules hb⟩
  · intro r σ x y hb hex hx hy
    exact hall ⟨x, hx⟩ ⟨y, hy⟩ r σ (stepBy_of_stepMBy_ex (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hf.1 hrules hb) hex
  · intro r σ x y hb _
    by_cases hx : c.sortOf x = some topCellSort
    · have hy := rhs_sorted_open hm (hrules r hb.1).1 hb.2.1 hb.2.2.2.2.2.1
      obtain ⟨y', σ', hag, hb', hT⟩ :=
        hsome ⟨x, hx⟩ ⟨y, hy⟩ r σ (stepBy_of_stepMBy_ex (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hf.1 hrules hb)
      exact ⟨y'.val, σ', hag, stepMBy_of_stepBy_ex hfd hrules hb', fun _ _ => hT⟩
    · exact ⟨y, σ, fun _ _ => rfl, hb, fun hx' => absurd hx' hx⟩

end KCore
