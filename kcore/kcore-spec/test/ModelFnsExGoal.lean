/-
  The value model's function equations where a clause may hold existential variables
  (KcoreSpec/ModelFnsExGoal.lean, KcoreSpec/ModelHasEx.lean).

  - The new statements exist at the types the proofs of consistency read.
  - `HypModelCore` gives every clause of a function of the semantics no existential variable
    (`exs_nil_of_hypModelCore`): the statements below hold of a semantics with such a clause only
    once the sortedness `HypModelCore` holds admits one. Until then `hcls` and `ClausePostDecided`
    follow from `HypModelCore` (`hcls_of_hypModelCore`, `postDecided_of_hypModelCore`), so
    `consistent_of_modelEx` has the reach of `consistent_ofCl`.
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

/-- Under `HypModelCore` no clause of a function of the semantics has an existential variable. -/
theorem exs_nil_of_hypModelCore (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) : cl.exs = [] := clause_exsCl h hfn hcl

/-- Under `HypModelCore` every clause has `hcls`' facts: `clauseExOK` of a clause with no
existential variable and the predicate `\top` is `condOK` of `\top`. -/
theorem hcls_of_hypModelCore (h : HypModelCore c) :
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.clauseSortedOpen fn (c.fns.map Fn.sig) cl = true ∧
      c.clauseExOK cl = true ∧ (cl.exs = [] → cl.post = .top) := by
  intro fn hfn cl hcl
  obtain ⟨hs, hpl⟩ := (Semantics.sortedOKCl_parts h.hyp.1).2.1 fn hfn cl hcl
  obtain ⟨hex, hpost, -, -⟩ := Semantics.clausePlainOpen_partsP hpl
  refine ⟨hs, ?_, fun _ => hpost⟩
  simp [Semantics.clauseExOK, hex, hpost, Semantics.condOK, nodup]

/-- Under `HypModelCore` every right-side predicate is `\top`, so it is decided. -/
theorem postDecided_of_hypModelCore (h : HypModelCore c) : ClausePostDecided c :=
  clausePostDecided_of_top fun fn hfn cl hcl => (hcls_of_hypModelCore h fn hfn cl hcl).2.2
    (exs_nil_of_hypModelCore h (List.mem_append_left _ hfn) hcl)

/-- `consistent_of_modelEx` gives what `HypModelCore`, `ClausePreDecided` and `OpenLaws` give
today. -/
example (c : Semantics) (hm : HypModelCore c) (hp : ClausePreDecided c) (hl : OpenLaws c) : Consistent c :=
  consistent_of_modelEx c hm (hcls_of_hypModelCore hm) hp (postDecided_of_hypModelCore hm) hl

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
