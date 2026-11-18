/-
  The value model's function equations where a clause may hold existential variables
  (KcoreSpec/ModelFnsExGoal.lean, KcoreSpec/ModelHasEx.lean).

  - The new statements exist at the types the proofs of consistency read.
  - `hcls` follows from `HypModelCore` (`hcls_of_hypModelCore`), whose sortedness `sortedOKClEx`
    admits a clause with existential variables. Where no clause has one (`FnsNoExs`) every
    right-side predicate is `\top`, so `ClausePostDecided` holds (`postDecided_of_hypModelCore`)
    and `consistent_of_modelEx` has the reach of `consistent_ofCl`.
  - The facts of a clause with existential variables that is not asked to be one of the semantics
    give its equation in the value model (`eqn_of_sortedEx`): `eqnFactsEx_of_sorted` supplies what
    `sat_clauseEqEx` reads.
-/
import KcoreSpec.ModelHasEx
import KcoreSpec.ModelFnsCl

set_option autoImplicit false

open KCore KCore.Faithful KCore.Faithful.Model ML

variable {c : Semantics}

#check @ClausePostDecided
#check @clausePostDecided_of_top
#check @clausePostDecided_of_total
#check @eqnFactsEx_of_sorted
#check @eqnFactsPre_of_sorted
#check @eqnFactsPre_sortPred
#check @AtT.satFnsGoalEx
#check @satFnsGoalEx
#check @stdI_V_model_coreEx
#check @consistent_of_modelEx

example (c : Semantics) : ClausePostDecided c =
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, ∀ σ, c.WellSorted cl.vars σ → ∃ b, Holds c cl.vars.length σ cl.post b := rfl

example (c : Semantics) (hm : HypModelCore c)
    (hcls : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.clauseSortedOpen fn (c.fns.map Fn.sig) cl = true ∧
      c.clauseExOK cl = true ∧ (cl.exs = [] → cl.post = .top))
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c) : Consistent c :=
  consistent_of_modelEx c hm hcls hp hq hl

/-- Under `HypModelCore` every clause has `hcls`' facts: `sortedOKClEx` holds `clauseSortedOpen`
and `clausePlainOpenEx` of each clause, which holds `clauseExOK` and `\top` as the right-side
predicate of a clause with no existential variable. -/
theorem hcls_of_hypModelCore (h : HypModelCore c) :
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.clauseSortedOpen fn (c.fns.map Fn.sig) cl = true ∧
      c.clauseExOK cl = true ∧ (cl.exs = [] → cl.post = .top) := fun fn hfn cl hcl =>
  have hp := (Semantics.sortedOKClEx_parts h.hyp.1).2.1 fn hfn cl hcl
  ⟨hp.1, (Semantics.clausePlainOpenEx_parts hp.2).1, (Semantics.clausePlainOpenEx_parts hp.2).2.1⟩

/-- Under `HypModelCore`, where no clause has an existential variable every right-side predicate
is `\top`, so it is decided. -/
theorem postDecided_of_hypModelCore (h : HypModelCore c) (hne : c.FnsNoExs) : ClausePostDecided c :=
  clausePostDecided_of_top fun fn hfn cl hcl => (hcls_of_hypModelCore h fn hfn cl hcl).2.2 (hne fn hfn cl hcl)

/-- `consistent_of_modelEx` gives `Consistent` from `HypModelCore`, `FnsNoExs`, `ClausePreDecided`
and `OpenLaws`. -/
example (c : Semantics) (hm : HypModelCore c) (hne : c.FnsNoExs) (hp : ClausePreDecided c) (hl : OpenLaws c) :
    Consistent c :=
  consistent_of_modelEx c hm (hcls_of_hypModelCore hm) hp (postDecided_of_hypModelCore hm hne) hl

/-- **The equation of a clause with existential variables holds in the value model from the
clause's facts**, the clause not being asked to be one of the semantics: `clauseSortedOpen`,
`clauseExOK`, truth values for its two predicates, and its applying giving the function's values
as the values its instances give. -/
theorem eqn_of_sortedEx {T : GroundTerm → GroundTerm → Prop} (h : HypModelCore c) {fn : Fn}
    (hfn : fn ∈ c.allFns) {cl : Clause} {L : List CtorSig} (hL : HeadsOK c L)
    (hs : c.clauseSortedOpen fn L cl = true) (hx : c.clauseExOK cl = true) (hne : cl.exs ≠ [])
    (hdec : ∀ σ ws, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats ws →
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b)
    (hpostDec : ∀ σ', c.WellSorted cl.vars σ' → ∃ b, Holds c cl.vars.length σ' cl.post b)
    (hsolve : ∀ σ ws, c.sortsOf ws = some fn.args → cl.AppliesAt c σ ws →
      ∀ v, Eval c fn.label ws (some v) ↔
        ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v) :
    ∃ a, clauseEquation c fn cl = .axiom a ∧
      (stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", a⟩).pat) :=
  have F := eqnFactsEx_of_sorted h hfn hL hs hx
  ⟨_, clauseEquation_axEx hne F.exLt, AtT.sat_clauseEqEx h hfn F hdec hpostDec hsolve⟩

#print axioms consistent_of_modelEx
#print axioms eqn_of_sortedEx
