/-
  The heads of the KORE the semantics writes for its functions and rules are Γ's
  (KcoreSpec/TieHeadsKore.lean): the statements, and the axioms their proofs use.
  Run from the package root: `lake env lean -j1 test/TieHeadsKore.lean`.
-/
import KcoreSpec.TieHeadsKore

set_option autoImplicit false

open KCore KCore.Faithful KCore.GHKore

#check @GHKore.term
#check @GHKore.terms
#check @GHKore.cond
#check @GHKore.ctxG_rhsCtx
#check @GHKore.ctxG_patCtxAll
#check @GHKore.clauseG_of_sorted
#check @GHKore.ruleG_of_sorted
#check @GHKore.clauseG_sortPreds
#check @GHKore.prioEquation_ghk
#check @GHKore.prioRuleK_ghk
#check @GHKore.fnG_coreOK
#check @GHKore.ruleG_coreOK
#check @GHKore.prioEquation_coreOK
#check @GHKore.prioRuleK_coreOK

/-- Under `coreOK`, every head of every rule's axiom is one of Γ's. -/
example (c : Semantics) (h : c.coreOK = true) (r : Rule) (hr : r ∈ c.rules) :
    ∀ g ∈ appHeadsOf (prioRuleK c r), g ∈ gammaHeads c :=
  fun _ hg => prioRuleK_coreOK h hr hg

/-- Under `coreOK`, every head of every equation of every function is one of Γ's. -/
example (c : Semantics) (h : c.coreOK = true) (f : Fn) (hf : f ∈ c.allFns) (cl : Clause)
    (hcl : cl ∈ f.clauses) (a : Kore.Axiom) (he : prioEquation c f cl = .axiom a) :
    ∀ g ∈ appHeadsOf a.pattern, g ∈ gammaHeads c := by
  have := prioEquation_coreOK h hf hcl
  rw [he] at this
  exact this

#print axioms GHKore.term
#print axioms GHKore.cond
#print axioms GHKore.clauseG_sortPreds
#print axioms GHKore.prioEquation_coreOK
#print axioms GHKore.prioRuleK_coreOK
