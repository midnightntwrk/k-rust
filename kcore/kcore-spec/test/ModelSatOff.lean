/-
  The value model off some functions (KcoreSpec/ModelSatOff.lean): the statements of `FnSolvesAt`,
  `fnSolves_iff_at`, `Faithful.Model.sat_off` and `AtT.sat_fnEqsEx`, and that `consistent_of_coreEx`
  keeps its statement.
-/
import KcoreSpec.ModelSatOff

open KCore KCore.Faithful KCore.Faithful.Model ML

example (c : Semantics) (fn : Fn) : FnSolvesAt c fn =
    ∀ vs, c.sortsOf vs = some fn.args → ∀ cl ∈ fn.clauses, ∀ σ,
      cl.DecidesAt c fn σ vs → ∀ v, Eval c fn.label vs (some v) ↔
        ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v := rfl

example (c : Semantics) : FnSolves c ↔ ∀ fn ∈ c.fns, FnSolvesAt c fn := fnSolves_iff_at

/-- `sat_off`: every item but the equations of the functions of `D`. -/
example {c : Semantics} {D : List Sym} (h : c.coreOKEx = true) (hd : FnDet c)
    (hs : ∀ fn ∈ c.fns, fn.label ∉ D → FnSolvesAt c fn)
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c) :
    ∀ φ, φ ∈ (Γc c ∪ Γstep c) →
      (∀ fn ∈ c.fns, fn.label ∈ D → ∀ it ∈ kernelItems (fnEquationsK c fn), φ ≠ it.pat) →
      stdI_T c (StepV c) ⊧ᴵ φ := sat_off h hd hs hp hq hl

/-- An item that is no premise of the equations of a function of `D` is concluded. -/
example {c : Semantics} {D : List Sym} (h : c.coreOKEx = true) (hd : FnDet c)
    (hs : ∀ fn ∈ c.fns, fn.label ∉ D → FnSolvesAt c fn)
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c) {φ : KoreAML.P}
    (hφ : φ ∈ (Γc c ∪ Γstep c))
    (hoff : ∀ fn ∈ c.fns, fn.label ∈ D → ¬ KoreAML.itemsPremises (kernelItems (fnEquationsK c fn)) φ) :
    stdI_T c (StepV c) ⊧ᴵ φ :=
  sat_off h hd hs hp hq hl φ hφ fun fn hfn hD it hit he => hoff fn hfn hD (Or.inl ⟨it, hit, he.symm⟩)

/-- At no function, `sat_off` is the model of the whole theory. -/
example {c : Semantics} (h : c.coreOKEx = true) (hd : FnDet c) (hs : FnSolves c)
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c) :
    stdI_T c (StepV c) ⊧ᴵP (Γc c ∪ Γstep c) := sat_off_nil h hd hs hp hq hl

/-- `consistent_of_coreEx` keeps its statement. -/
example {c : Semantics} (h : c.coreOKEx = true) (hd : FnDet c) (hs : FnSolves c)
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c) : Consistent c :=
  Faithful.Model.consistent_of_coreEx h hd hs hp hq hl

#check @AtT.sat_fnEqsEx

/-- info: 'KCore.Faithful.Model.sat_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sat_off
