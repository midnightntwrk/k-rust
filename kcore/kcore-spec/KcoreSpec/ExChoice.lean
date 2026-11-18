/-
  KCore. The choice among instances, for rules with existential variables: the step of the value
  model at a transition T.

  At configurations the transition of `stdI_T c T` is T, for any T (`step_iff_stdI_T`);
  `liftT_ex c T` is the relation on values a relation T on configurations gives (`liftT_ex_iff`).

  `StepM` and `Step` differ in how a competitor of a smaller priority is excluded: `¬ RuleApplies`
  and `NotApplies`. For competitors with `\top` premise predicates where a term has at most one
  result (`FnDet`), `NotApplies` gives `¬ RuleApplies` (`stepMAt_of_notApplies_ex`); where the
  competitors' conditions have results at their matches (`StepDecided`, from `ruleSorted` alone by
  `stepDecided_pp`), `¬ RuleApplies` gives `NotApplies` (`notApplies_of_stepMAt_ex`). Neither asks
  the rule to be one of the definition's. So `StepBy` and `StepMBy` agree (`stepMBy_of_stepBy_ex`,
  `stepBy_of_stepMBy_ex`). The model itself (`stdI_T_modelCEx`, `has_model_choice_exCEx`) is
  ExChoiceCEx.lean's.
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

end KCore
