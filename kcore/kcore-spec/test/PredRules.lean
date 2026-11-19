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
  (its predicates are not `\top`). `rulePlainPP` of the definition's rules, decided, with `ruleSorted`
  from `coreOK` (`Semantics.ruleFactsPP_of_coreAll`), `rulePlainEx_iff_pp` at `rNot`, and the definition's semantics
  with `rNot` among its rules has `rulesPlain`, `okAll`, `sortedOK` and `coreOK` (`cP_core`).
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

theorem coreOK : c.coreOK = true := by decide_cheap

/-- `rulePlainPP` of the definition's rules, decided. -/
example : ∀ r ∈ c.rules, c.rulePlainPP r = true := fun r hr =>
  (Semantics.ruleFactsPP_of_coreAll coreOK (by decide +kernel) r hr).2

/-- The definition's semantics with `rNot`, a rule with a predicate, among its rules. -/
noncomputable abbrev cP : Semantics := { c with rules := c.rules ++ [rNot] }

/-- A semantics with a rule that has a predicate has `rulesPlain`, `okAll`, `sortedOK` and
`coreOK`. -/
theorem cP_core : rNot.pre.isTop = false ∧ cP.rulesPlain = true ∧ cP.okAll = true ∧ cP.sortedOK = true ∧
    cP.coreOK = true := by decide_cheap

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

/-! ## The facts of the rules with predicates

  `rNot` (its open variable G by arm A, a `pre`), `rOr` (its existential Z by arm A, a `post`) and
  `rC` (`b => b` with pre `Z ∈ 0`, Z:Int open and in `pre` only, the conditions closed: arm C,
  `needsWitness`). No open variable of the three is of a confined sort, and no predicate holds a
  binder (`stepValues_facts`). -/

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

theorem rules_pp : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainPP r = true :=
  Semantics.ruleFactsPP_of_coreAll coreOK (by decide +kernel)

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

/-! ## The closure, the model and the choice (`KCore.Faithful.Model.satStepGoal_pp`)

  At the definition (rules with a pre, a post and an existential variable): the closure holds at T
  wherever T steps are `StepV` steps, and no rule's `applies` pattern has a free variable. -/

section ModelChoice
open Faithful Faithful.Model

example (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop)
    (hsub : ∀ x y, c.sortOf x = some topCellSort → c.sortOf y = some topCellSort → T x y → StepV c x y) :
    stdI_T c T ⊧ᴵP Γstep c :=
  satStepGoal_pp h rules_pp T hsub

example : ∀ r' ∈ c.rules, ∀ {k}, k ∈ KoreAML.freeOf [] (applies c r' (canonRulePres r')) → False :=
  fun r' hr' _ hk => freeOf_appliesPP (rules_pp r' hr').1 hk

end ModelChoice

/-! ## The instances of a step by a rule with a `post` (`KCore.famEx_closed_postCEx`)

  `rPost`: `Z => a(Z)` with post `Z ∈ b`, no existential variable. It is well sorted and its
  `post` is not `\top`: `famEx_denPPCEx` gives, in every model of `Γc`, that the instances of a step
  by it at σ are its successor, from `Holds … post true` at σ; `famEx_closed_postCEx` at the
  definition. -/

section FamExPost
open Faithful

variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

/-- `Z => a(Z)` with post `Z ∈ b`. -/
noncomputable def rPost : Rule :=
  { vars := [sK, sC, 32], lhs := cfgE (.var 2), req := none, rhs := cfgE (tA (.var 2)), ens := none, prio := 50,
    post := .mem 32 (.var 2) tB }

theorem rPost_facts : c.ruleSorted rPost = true ∧ rPost.exs = [] ∧ rPost.post.isTop = false ∧
    HoldsShape.hasBinder rPost.post = false := by
  decide +kernel

example (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {σ : Subst} (hσ : c.WellSorted rPost.vars σ) {y : Config c}
    (heval : EvalTerm c σ rPost.rhs (some y.val)) (hpost : Holds c rPost.vars.length σ rPost.post true)
    (e : ML.Valuation M) (m : M) :
    (famEx c rPost σ).interpret I e m ↔ (den c y.val).interpret I e m :=
  famEx_denPPCEx (Semantics.coreOK_iff_ex.mp coreOK) rPost_facts.1 rPost_facts.2.1 (fun h => absurd h (by rw [rPost_facts.2.2.2]; decide))
    hσ heval (fun t ht => by cases ht) hpost hI hcw e m

example {x y : Config c} {r : Rule} {σ : Subst} (hs : StepBy c r σ x y) (hex : r.exs = [])
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    Γc c ⊧ (famEx c r σ ≡ den c y.val) :=
  famEx_closed_postCEx c (Semantics.coreOK_iff_ex.mp coreOK) hs hex hcw

end FamExPost

/-! ## A competitor with a `pre` in a model of `Γc`: `rNot` -/

section Compete
open Faithful

variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

/-- `rNot`'s conditions need no witness, its `pre` has no binder, and its open variable G is of a
sort that is not confined. -/
theorem compete_facts : rNot.needsWitness c = false ∧ HoldsShape.hasBinder rNot.pre = false ∧
    (rNot.opens.any fun i => (rNot.vars[i]?.map c.confined).getD false) = false := by
  decide +kernel

/-- `applies_of_values_ppCEx` at `rNot`: no rule of a larger priority is read. -/
example (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {x : Config c}
    {σ : Subst} (hσ : c.WellSortedAt rNot.vars rNot.leftVars σ) (hpv : PatVal c σ rNot.lhs x.val)
    (hpre : Holds c rNot.vars.length σ rNot.pre true)
    {tbl : KoreAML.VarTable} (hkeys : ∀ i < rNot.vars.length, i ∈ rNot.leftVars → canonKey c rNot.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c rNot.vars) (srtOf c topCellSort) rNot.pre), k ∈ tbl)
    (e : ML.Valuation M) :
    (KoreAML.tr ⟨tbl, []⟩ (applies c rNot (canonRulePres rNot))).interpret I e (elemOf c I x.val) :=
  applies_of_values_ppCEx (Semantics.coreOK_iff_ex.mp coreOK) hI hcw rNot_pp.1 (fun h => absurd h (by rw [compete_facts.2.1]; decide)) hσ hpv
    (fun t ht => nomatch (show (none : Option Term) = some t from ht)) hpre hkeys hkP e

end Compete

/-! ## A condition is a predicate (`KCore.Faithful.cond_pred_transfer_top`)

  At `rNot`'s pre (a complement of a conjunction of memberships) and at `pExB` (a binder over a
  membership): in any model of `Γ c`, through a table holding the pattern's keys and at a valuation
  that gives each free variable an element of its sort, the conjuncts hold at one element of the
  configuration sort iff at any other. -/

section CondPred
open Faithful

variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

example (hI : I ⊧ᴵP Γ c) (tbl : KoreAML.VarTable) (e : ML.Valuation M) (a a' : M)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c rNot.vars) (srtOf c topCellSort) rNot.pre), k ∈ tbl)
    (hf : ∀ i ∈ varOccsCond rNot.vars.length rNot.pre, canonKey c rNot.vars i ∈ tbl ∧
      InS I (c.sortName (rNot.vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c rNot.vars i))))
    (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a)
    (ha' : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a')
    (hpre : ∀ φ ∈ Cond.conj c (canonVars c rNot.vars) (srtOf c topCellSort) rNot.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) :
    ∀ φ ∈ Cond.conj c (canonVars c rNot.vars) (srtOf c topCellSort) rNot.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a' :=
  cond_pred_transfer_top coreOK hI (by decide +kernel) tbl e a a' hk hf ha ha' hpre

example (hI : I ⊧ᴵP Γ c) (tbl : KoreAML.VarTable) (e : ML.Valuation M) (a a' : M)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c rNot.vars) (srtOf c topCellSort) pExB), k ∈ tbl)
    (hf : ∀ i ∈ varOccsCond rNot.vars.length pExB, canonKey c rNot.vars i ∈ tbl ∧
      InS I (c.sortName (rNot.vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c rNot.vars i))))
    (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a)
    (ha' : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a')
    (hp : ∀ φ ∈ Cond.conj c (canonVars c rNot.vars) (srtOf c topCellSort) pExB,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) :
    ∀ φ ∈ Cond.conj c (canonVars c rNot.vars) (srtOf c topCellSort) pExB,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a' :=
  cond_pred_transfer_top coreOK hI (by decide +kernel) tbl e a a' hk hf ha ha' hp

end CondPred

/-! ## A value in the instances of an application

  At `rOr` (`b => ?Z` with post `or (mem Z b) (mem Z a(b))`, Z existential, a `post` that is not
  `\top`): the facts of the rule that the values in `famEx c rOr σ` read (`famExValues_facts`). -/

section FamExValues
open Faithful

variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

/-- `rOr`'s existential variable Z is of a sort that is not confined, and its `post` is not `\top`
and holds no binder. -/
theorem famExValues_facts : (rOr.exs.any fun i => (rOr.vars[i]?.map c.confined).getD false) = false ∧
    HoldsShape.hasBinder rOr.post = false ∧ rOr.post.isTop = false := by
  decide +kernel

end FamExValues

/-! ## Completeness at a configuration (`KCore.Faithful.successor_split_ppCEx`, `step_successor_axiomPP`)

  At `rNot` (a `pre` that is not `\top`, without a binder): the left part of its axiom
  (`rule_parts_pp`) and the two cases of a successor its axiom gives where the step is decided
  (`successor_split_ppCEx`, the hypotheses on the table, the valuation and the elements left as
  arguments). At the definition: the rule a successor comes from. -/

section CompletePP
open Faithful

variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

example := rule_parts_pp (c := c) (I := I) rNot_pp.1

example (x : Config c) (hd : StepDecided c x.val) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :=
  successor_split_ppCEx (r := rNot) (Semantics.coreOK_iff_ex.mp coreOK) (fun r hr => (rules_pp r hr).1) x hd hI hcw rNot_pp.1
    (fun h => absurd h (by rw [stepValues_facts.2.1]; decide))
    (fun h => absurd h (by rw [stepValues_facts.2.2.1]; decide))

example (x : Config c) (hI : I ⊧ᴵP (Γc c ∪ Γstep c)) (e : ML.Valuation M) (ψ : KoreAML.P)
    (hs : (KoreAML.sNext ψ).interpret I e (elemOf c I x.val)) :=
  step_successor_axiomPP (fun r hr => (rules_pp r hr).1) x hI e ψ hs

end CompletePP

/-! ## The outcomes of a match (`KCore.Faithful.famOpen_stepPPCEx`, `KCore.famOpen_values_ppCEx`)

  `rOpenB`: `b => b` with pre `not (mem Z true)`, Z of Bool, open and in `pre` only. Bool is
  confined, so every open variable of the rule is of a confined sort, and its `pre` is not `\top`:
  in any model of `Γc c`, an element of `famOpen c rOpenB σ` at a match σ is in the pattern of a
  configuration y, with a σ' that is σ on the left side and every premise of a step by the rule to y
  but membership and the competitors, `Holds … pre true` included. `rOpenB` is not a rule of the
  definition, so `readsConfined` (asked for a confined open variable) is a hypothesis. At the
  definition: `famOpen_values`'s statement from `ruleSorted` of the rule. -/

section FamOpenValues
open Faithful

variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

/-- `b => b` with pre `not (mem Z true)`, Z:Bool open. -/
noncomputable def rOpenB : Rule :=
  { vars := [sK, sC, Srt.bool], lhs := cfgE tB, req := none, rhs := cfgE tB, ens := none, prio := 50,
    pre := .not (.mem Srt.bool (.var 2) (.dv Srt.bool (.bool true))) }

theorem rOpenB_facts : c.ruleSorted rOpenB = true ∧ rOpenB.opens = [2] ∧ rOpenB.pre.isTop = false ∧
    HoldsShape.hasBinder rOpenB.pre = false ∧ HoldsShape.hasBinder rOpenB.post = false ∧
    (rOpenB.opens.all fun i => (rOpenB.vars[i]?.map c.confined).getD false) = true := by
  decide +kernel

example (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (hrc : c.readsConfined = true)
    {x : Config c} {σ : Subst} (hσ : c.WellSortedAt rOpenB.vars (varOccs rOpenB.lhs) σ)
    (hmatch : PatVal c σ rOpenB.lhs x.val)
    (e : ML.Valuation M) (m : M) (hm : (famOpen c rOpenB σ).interpret I e m) :
    ∃ (y : Config c) (σ' : Subst), (∀ i ∈ varOccs rOpenB.lhs, σ'.lookup i = σ.lookup i) ∧
      c.WellSorted rOpenB.vars σ' ∧ PatVal c σ' rOpenB.lhs x.val ∧
      (∀ t, rOpenB.req = some t → EvalTerm c σ' t (some (bool true))) ∧
      Holds c rOpenB.vars.length σ' rOpenB.pre true ∧ EvalTerm c σ' rOpenB.rhs (some y.val) ∧
      (∀ t, rOpenB.ens = some t → EvalTerm c σ' t (some (bool true))) ∧
      Holds c rOpenB.vars.length σ' rOpenB.post true ∧ (den c y.val).interpret I e m :=
  famOpen_stepPPCEx (Semantics.coreOK_iff_ex.mp coreOK) hft hI hcw rOpenB_facts.1 (List.all_eq_true.mp rOpenB_facts.2.2.2.2.2) (fun _ => hrc)
    (fun h => absurd h (by rw [rOpenB_facts.2.2.2.1]; decide))
    (fun h => absurd h (by rw [rOpenB_facts.2.2.2.2.1]; decide)) hσ hmatch e m hm

/-- The pinned type of `famOpen_values` (`test/Pins.lean`), from `ruleSorted` of the rule. -/
example : ∀ (hf : FnHyp c)
    (x : Config c) (r : Rule) (hr : r ∈ c.rules) (σ : Subst) (hu : Unblocked c r σ x.val)
    (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (ys : List GroundTerm)
    (hys : ∀ y : Config c, (∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y) →
      y.val ∈ ys),
    Γc c ⊧ (famOpen c r σ ⇒ KoreAML.disjList (ys.map (den c))) :=
  fun hf x r hr => famOpen_values_ppCEx c (Semantics.coreOK_iff_ex.mp coreOK) hf x r hr (rules_pp r hr).1

end FamOpenValues

/-! ## Soundness at a step (`KCore.Faithful.applies_match_pp`, `famEx_mem_ppCEx`)

  At `rNot` (a `pre` that is not `\top`): x's element in its `applies` gives a match of its left
  side at x. At `rOr` (an existential variable and a `post` that is not `\top`): the successor of a
  step is among its instances (`famEx_mem_ppCEx`). -/

section SoundPP
open Faithful

variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

example (hI : I ⊧ᴵP Γ c) {x : Config c} {tbl : KoreAML.VarTable}
    (hkeys : ∀ i < rNot.vars.length, i ∈ rNot.leftVars → canonKey c rNot.vars i ∈ tbl) (e : ML.Valuation M)
    (hm : (KoreAML.tr ⟨tbl, []⟩ (applies c rNot (canonRulePres rNot))).interpret I e (elemOf c I x.val)) :
    ∃ σ', PatVal c σ' rNot.lhs x.val :=
  applies_match_pp coreOK hI rNot_pp.1 hkeys e hm

example (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {σ : Subst} (hσ : c.WellSorted rOr.vars σ) {y : Config c}
    (heval : EvalTerm c σ rOr.rhs (some y.val)) (hpost : Holds c rOr.vars.length σ rOr.post true)
    (e : ML.Valuation M) : (famEx c rOr σ).interpret I e (elemOf c I y.val) :=
  famEx_mem_ppCEx (Semantics.coreOK_iff_ex.mp coreOK) rOr_pp.1 (fun h => absurd h (by rw [famExValues_facts.2.1]; decide)) hσ heval
    (fun t ht => nomatch (show (none : Option Term) = some t from ht)) hpost hI hcw e

end SoundPP

end PredRules
