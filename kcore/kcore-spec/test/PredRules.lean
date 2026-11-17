/-
  Rules with predicates, each well sorted, at the conjunct `Semantics.rulePlainPP`.
  Run from the package root: `lake env lean -j1 test/PredRules.lean`. Kernel-checked (`decide +kernel`).

  The semantics is the reader's for `f2-examples/symrule.kompile.kore` (as `test/ExRules.lean`):
  `a(Exp)` and `b()` of sort Exp, over the configuration `cfgE x`
  (`<generatedTop>(<k>(kseq(inj{Exp,KItem}(x), V0)), C)`), V0 of sort K and C of the counter cell's
  sort. The rules:
  - `rNot`: `Z => G` with pre `not (and (mem Z b) (mem Z G))`, Z and G of Exp, G open: the shape of a
    complement on the left side; G is held by the right side under constructors;
  - `rOr`: `b => ?Z` with post `or (mem Z b) (mem Z a(b))`, Z existential: the shape of a connective
    on the right side; Z is held by the right side under constructors;
  - `rBad`: `b => b ensures ?Z ==Int 0`: Z of the unconfined sort Int under the hooked function
    `_==Int_` only, and in no condition: the conjunct is false.
  Each is well sorted (`ruleSorted`); `rNot` and `rOr` have the conjunct, neither has `rulePlainEx`
  (its predicates are not `\top`). `rulePlainPP_of_ex` at the definition's rules, and
  `rulePlainEx_iff_pp` at `rNot`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace PredRules

definition_of defn from "f2-examples/symrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def tA (t : Term) : Term := .app 385 [t]
def tB : Term := .app 386 []
def i (n : Int) : Term := .dv Srt.int (.int n)
/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(x), V0)), C)`. -/
def cfgE (x : Term) : Term := .app 71 [.app 383 [.app 0 [.inj 32 1 x, .var 0]], .var 1]

/-- The sorts of the first two variables of the text's rule: K and the counter cell's. -/
noncomputable def sK : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 1 0
noncomputable def sC : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 2 0

example : c.symName 385 = "Lbla" ∧ c.symName 386 = "Lblb" ∧ c.sortName 32 = "Exp" := by decide +kernel

/-- `Z => G` with pre `not (and (mem Z b) (mem Z G))`. -/
noncomputable def rNot : Rule :=
  { vars := [sK, sC, 32, 32], lhs := cfgE (.var 2), req := none, rhs := cfgE (.var 3), ens := none, prio := 50,
    pre := .not (.and (.mem 32 (.var 2) tB) (.mem 32 (.var 2) (.var 3))) }

/-- `b => ?Z` with post `or (mem Z b) (mem Z a(b))`. -/
noncomputable def rOr : Rule :=
  { vars := [sK, sC, 32], lhs := cfgE tB, req := none, rhs := cfgE (.var 2), ens := none, prio := 50, exs := [2],
    post := .or (.mem 32 (.var 2) tB) (.mem 32 (.var 2) (tA tB)) }

/-- `b => b ensures ?Z ==Int 0`. -/
noncomputable def rBad : Rule :=
  { vars := [sK, sC, Srt.int], lhs := cfgE tB, req := none, rhs := cfgE tB, ens := some (.app intEq [.var 2, i 0]),
    prio := 50, exs := [2] }

/-- `rNot` is well sorted with the conjunct; G (index 3) is its only open variable, held by the
right side under constructors; its pre is not `\top`, so it has no `rulePlainEx`. -/
theorem rNot_pp : c.ruleSorted rNot = true ∧ c.rulePlainPP rNot = true ∧ rNot.opens = [3] ∧
    (ctorOccs c rNot.rhs).contains 3 = true ∧ c.rulePlainEx rNot = false := by
  decide +kernel

/-- `rOr` is well sorted with the conjunct; Z (index 2) is existential and held by the right side
under constructors; its post is not `\top`. -/
theorem rOr_pp : c.ruleSorted rOr = true ∧ c.rulePlainPP rOr = true ∧ rOr.opens = [2] ∧ rOr.exs = [2] ∧
    (ctorOccs c rOr.rhs).contains 2 = true ∧ c.rulePlainEx rOr = false := by
  decide +kernel

/-- `rBad` is well sorted, and the conjunct is false. -/
theorem rBad_pp : c.ruleSorted rBad = true ∧ c.rulePlainPP rBad = false := by
  decide +kernel

/-- `rulePlainEx_iff_pp` at `rNot`: its conjunct holds and its pre is not `\top`. -/
example : ¬ c.rulePlainEx rNot = true := fun h =>
  absurd (Semantics.rulePlainEx_iff_pp.mp h).1 (by decide +kernel)

theorem coreOK : c.coreOK = true := by decide +kernel

/-- `rulePlainPP_of_ex` at the definition's rules. -/
example : ∀ r ∈ c.rules, c.rulePlainPP r = true := fun r hr =>
  Semantics.rulePlainPP_of_ex (Semantics.ruleFactsEx_of_core coreOK r hr).2

/-! ## A predicate under two tables (`KCore.Faithful.tr_condKore_twoT`)

  At `rNot`'s pre (`not`, `and`, `mem`) and at `∃ y:Exp. y ∈ b` over `rNot`'s variables (a binder):
  read through two tables at two valuations that agree at the free variables, the two readings
  denote one set. -/

section TwoTables
open Faithful

variable {M : Type} {I : ML.Interpretation KoreAML.Sym M}

/-- `∃ y:Exp. y ∈ b`, y the variable after `rNot`'s. -/
def pExB : Cond := .ex 32 (.mem 32 (.var 4) tB)

example (hD : KoreAML.DefOK I) {tbl tbl' : KoreAML.VarTable} {e e' : ML.Valuation M}
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c rNot.vars) (srtOf c topCellSort) rNot.pre),
      k ∈ tbl ∧ k ∈ tbl')
    (hf : ∀ i ∈ varOccsCond rNot.vars.length rNot.pre, canonKey c rNot.vars i ∈ tbl ∧ canonKey c rNot.vars i ∈ tbl' ∧
      e.evalEvar (tbl.ev (canonKey c rNot.vars i)) = e'.evalEvar (tbl'.ev (canonKey c rNot.vars i))) (m : M) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c rNot.vars) (srtOf c topCellSort) rNot.pre)).interpret I e m ↔
      (KoreAML.tr ⟨tbl', []⟩ (Cond.kore c (canonVars c rNot.vars) (srtOf c topCellSort) rNot.pre)).interpret I e' m :=
  tr_condKore_twoT hD rNot.pre (by decide +kernel) hk hf m

example (hD : KoreAML.DefOK I) {tbl tbl' : KoreAML.VarTable} {e e' : ML.Valuation M}
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c rNot.vars) (srtOf c topCellSort) pExB), k ∈ tbl ∧ k ∈ tbl')
    (hf : ∀ i ∈ varOccsCond rNot.vars.length pExB, canonKey c rNot.vars i ∈ tbl ∧ canonKey c rNot.vars i ∈ tbl' ∧
      e.evalEvar (tbl.ev (canonKey c rNot.vars i)) = e'.evalEvar (tbl'.ev (canonKey c rNot.vars i))) (m : M) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c rNot.vars) (srtOf c topCellSort) pExB)).interpret I e m ↔
      (KoreAML.tr ⟨tbl', []⟩ (Cond.kore c (canonVars c rNot.vars) (srtOf c topCellSort) pExB)).interpret I e' m :=
  tr_condKore_twoT hD pExB (by decide +kernel) hk hf m

end TwoTables

/-! ## A successor's values for a rule with predicates (`KCore.Faithful.rule_step_values_pp`)

  At `rNot` (its open variable G by arm A, a `pre`), `rOr` (its existential Z by arm A, a `post`)
  and `rC` (`b => b` with pre `Z ∈ 0`, Z:Int open and in `pre` only, the conditions closed: arm C,
  `needsWitness`): in any model of `Γc c`, a valuation with x's element in the left side, the
  conditions and `pre` and y's element in the right side, `ensures` and `post` gives a σ of values
  with every premise of `StepBy` but membership and `hprio`, `Holds` of both predicates included.
  No open variable of the three is of a confined sort, and no predicate holds a binder. -/

/-- `b => b` with pre `Z ∈ 0`, Z:Int open. -/
noncomputable def rC : Rule :=
  { vars := [sK, sC, Srt.int], lhs := cfgE tB, req := none, rhs := cfgE tB, ens := none, prio := 50,
    pre := .mem Srt.int (.var 2) (i 0) }

theorem rC_pp : c.ruleSorted rC = true ∧ c.rulePlainPP rC = true ∧ rC.opens = [2] ∧
    rC.opens.all (rC.armAB c) = false ∧ rC.needsWitness c = true := by
  decide +kernel

theorem stepValues_facts :
    rNot.opens.any (fun i => (rNot.vars[i]?.map c.confined).getD false) = false ∧
    HoldsShape.hasBinder rNot.pre = false ∧ HoldsShape.hasBinder rNot.post = false ∧ rNot.needsWitness c = false ∧
    rNot.opens.all (rNot.armAB c) = true ∧
    rOr.opens.any (fun i => (rOr.vars[i]?.map c.confined).getD false) = false ∧
    HoldsShape.hasBinder rOr.pre = false ∧ HoldsShape.hasBinder rOr.post = false ∧ rOr.needsWitness c = false ∧
    rC.opens.any (fun i => (rC.vars[i]?.map c.confined).getD false) = false ∧
    HoldsShape.hasBinder rC.pre = false ∧ HoldsShape.hasBinder rC.post = false := by
  decide +kernel

section StepValues
open Faithful

variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

/-- Arm A with a `pre`: `rNot`. -/
example (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (tbl : KoreAML.VarTable) (e : ML.Valuation M) :=
  rule_step_values_pp (r := rNot) (tbl := tbl) (e := e) coreOK hft hI hcw rNot_pp.1 rNot_pp.2.1
    (fun h => absurd h (by rw [stepValues_facts.1]; decide))
    (fun h => absurd h (by rw [stepValues_facts.2.1]; decide))
    (fun h => absurd h (by rw [stepValues_facts.2.2.1]; decide))
    (fun h => absurd h (by rw [stepValues_facts.2.2.2.1]; decide))

/-- An existential variable with a `post`: `rOr`. -/
example (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (tbl : KoreAML.VarTable) (e : ML.Valuation M) :=
  rule_step_values_pp (r := rOr) (tbl := tbl) (e := e) coreOK hft hI hcw rOr_pp.1 rOr_pp.2.1
    (fun h => absurd h (by rw [stepValues_facts.2.2.2.2.2.1]; decide))
    (fun h => absurd h (by rw [stepValues_facts.2.2.2.2.2.2.1]; decide))
    (fun h => absurd h (by rw [stepValues_facts.2.2.2.2.2.2.2.1]; decide))
    (fun h => absurd h (by rw [stepValues_facts.2.2.2.2.2.2.2.2.1]; decide))

/-- Arm C, its conditions decided by hypothesis: `rC`. -/
example (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (hw : rC.needsWitness c = true → rC.CondDecided c) (tbl : KoreAML.VarTable) (e : ML.Valuation M) :=
  rule_step_values_pp (r := rC) (tbl := tbl) (e := e) coreOK hft hI hcw rC_pp.1 rC_pp.2.1
    (fun h => absurd h (by rw [stepValues_facts.2.2.2.2.2.2.2.2.2.1]; decide))
    (fun h => absurd h (by rw [stepValues_facts.2.2.2.2.2.2.2.2.2.2.1]; decide))
    (fun h => absurd h (by rw [stepValues_facts.2.2.2.2.2.2.2.2.2.2.2]; decide)) hw

end StepValues

/-! ## Numbered sorts of a condition (`KCore.Semantics.condOK`, `KCore.Faithful.Model.rule_vars_numCN`)

  `condOK` refuses an atom at a sort the definition does not have: `⌈Z⌉` at the sort 999, Z of
  that sort, is well sorted as a term and refused. At `rNot`, `rOr` and `rC` (a variable held by
  `pre` only, or by `post` only) every variable has a numbered sort. -/

theorem condOK_unnumbered : c.condOK [999] (.ceil 999 (.var 0)) = false ∧
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [999] (.var 0) = some 999 ∧
    ¬ (999 < nRegSorts + c.sortNames.length) := by
  decide +kernel

example (h : Faithful.Model.HypModelCore c) :
    (∀ i < rNot.vars.length, rNot.vars.getD i 0 < nRegSorts + c.sortNames.length) ∧
    (∀ i < rOr.vars.length, rOr.vars.getD i 0 < nRegSorts + c.sortNames.length) ∧
    (∀ i < rC.vars.length, rC.vars.getD i 0 < nRegSorts + c.sortNames.length) :=
  ⟨Faithful.Model.rule_vars_numCN h rNot_pp.1, Faithful.Model.rule_vars_numCN h rOr_pp.1,
    Faithful.Model.rule_vars_numCN h rC_pp.1⟩

/-! ## The value model's truth of a condition (`KCore.TrueV`, `KCore.Faithful.trueV_stdI`)

  At `rNot`'s pre (`not`, `and`, `mem`), in the value model at any T, with no hypothesis that the
  condition has a truth value: an element of the predicate sort is in the condition exactly where
  `TrueV` holds, and `TrueV` reads the values of the terms. -/

section TrueValue
open Faithful Faithful.Model

example (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop) {P : Nat → Prop} {σ : Subst}
    {tbl : KoreAML.VarTable} {e : ML.Valuation Elem}
    (hP : ∀ i ∈ varOccsCond rNot.vars.length rNot.pre, i < rNot.vars.length → P i) (hr : ReadsT c rNot.vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c rNot.vars) (srtOf c topCellSort) rNot.pre), k ∈ tbl)
    (hS : topCellSort < nRegSorts + c.sortNames.length) (a : Elem) (ha : InSort c topCellSort a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c rNot.vars) (srtOf c topCellSort) rNot.pre)).interpret
        (stdI_T c T) e a ↔
      ¬ ((∃ v, EvalTerm c σ (.var 2) (some v) ∧ EvalTerm c σ tB (some v)) ∧
        ∃ v, EvalTerm c σ (.var 2) (some v) ∧ EvalTerm c σ (.var 3) (some v)) :=
  trueV_stdI h T rNot.pre (by decide +kernel) (by decide +kernel) hP hr hk hS a ha

/-- `applies_iff_T_pp` at `rNot`: a configuration is in `rNot`'s `applies` exactly where
`RuleAppliesV`, no truth value of its pre asked for. -/
example (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop) {tbl : KoreAML.VarTable}
    (hkeys : ∀ i < rNot.vars.length, i ∈ rNot.leftVars → canonKey c rNot.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c rNot.vars) (srtOf c topCellSort) rNot.pre), k ∈ tbl)
    (e : ML.Valuation Elem) {x : GroundTerm} (hx : c.sortOf x = some topCellSort) :
    (KoreAML.tr ⟨tbl, []⟩ (applies c rNot (canonRulePres rNot))).interpret (stdI_T c T) e (.val x) ↔
      RuleAppliesV c rNot x :=
  applies_iff_T_pp h rNot_pp.1 hkeys hkP e hx

end TrueValue

/-! ## A rule's axiom in the value model (`KCore.Faithful.Model.sat_rule_pp`, `satRulesGoal_pp`)

  At `rNot` (a pre) and `rOr` (an existential variable and a post), among the definition's rules:
  the axiom holds in the value model at T wherever T holds the rule's `StepVAt` instances (for
  `rOr`, some instance differing at its existential variable), with no hypothesis that a predicate
  has a truth value. -/

section SatRule
open Faithful Faithful.Model

theorem rules_pp : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainPP r = true := fun r hr =>
  ⟨(Semantics.ruleFactsEx_of_core coreOK r hr).1,
    Semantics.rulePlainPP_of_ex (Semantics.ruleFactsEx_of_core coreOK r hr).2⟩

example (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop)
    (hall : ∀ σ x y, StepVAt c rNot σ x y → T x y) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [], pattern := prioRuleK c rNot, attributes := [] }⟩).pat :=
  sat_rule_pp h rules_pp rNot_pp.1 rNot_pp.2.1 T (fun σ x y hst _ => hall σ x y hst)
    (fun _ _ _ _ hex => absurd rfl hex)

example (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop)
    (hsome : ∀ σ x y, StepVAt c rOr σ x y → ∃ y' σ',
      (∀ i, ¬ i ∈ rOr.exs → σ'.lookup i = σ.lookup i) ∧ StepVAt c rOr σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [], pattern := prioRuleK c rOr, attributes := [] }⟩).pat :=
  sat_rule_pp h rules_pp rOr_pp.1 rOr_pp.2.1 T
    (fun _ _ _ _ hex => absurd (rOr_pp.2.2.2.1.symm.trans hex) (List.cons_ne_nil _ _))
    (fun σ x y hst _ => hsome σ x y hst)

/-- The definition's rules at T, through `StepVBy`. -/
example (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop)
    (hall : ∀ r σ x y, StepVBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ r σ x y, StepVBy c r σ x y → r.exs ≠ [] → ∃ y' σ',
      (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepVBy c r σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵP ΓRules c :=
  satRulesGoal_pp h rules_pp T hall hsome

end SatRule

/-! ## The closure, the model and the choice (`KCore.Faithful.Model.satStepGoal_pp`,
  `KCore.consistent_pp`, `KCore.has_model_choice_pp`)

  At the definition (rules with a pre, a post and an existential variable): the closure holds at T
  wherever T steps are `StepV` steps, the theory has a model under `FnDet` and `FnSolves` alone,
  and the choice among instances is free under `FnHyp`. -/

section ModelChoice
open Faithful Faithful.Model

example (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop)
    (hsub : ∀ x y, c.sortOf x = some topCellSort → c.sortOf y = some topCellSort → T x y → StepV c x y) :
    stdI_T c T ⊧ᴵP Γstep c :=
  satStepGoal_pp h rules_pp T hsub

example : ∀ r' ∈ c.rules, ∀ {k}, k ∈ KoreAML.freeOf [] (applies c r' (canonRulePres r')) → False :=
  fun r' hr' _ hk => freeOf_appliesPP (rules_pp r' hr').1 hk

example (hd : FnDet c) (hs : FnSolves c) : Consistent c := consistent_pp c coreOK hd hs rules_pp

example (hf : FnHyp c) (T : Config c → Config c → Prop) (hsub : ∀ x y, T x y → Step c x y)
    (hall : ∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y') :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M), (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  has_model_choice_pp c coreOK hf rules_pp T hsub hall hsome

end ModelChoice

end PredRules
