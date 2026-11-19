/-
  Rules with existential variables, each well sorted, at the conjunct `Semantics.rulePlainEx`.
  Run from the package root: `lake env lean -j1 test/ExRules.lean`. Kernel-checked (`decide +kernel`).

  The semantics is the reader's for `f2-examples/symrule.kompile.kore`, over the configuration
  `cfg t` (`<generatedTop>(<k>(kseq(inj{Exp,KItem}(b), V0)), t)`) of `test/OpenRules.lean`, V0 of
  sort K and V1 of the counter cell's sort; `b(X)` stands as `<generatedCounter>(X)`, the counter
  cell's constructor. The rules (each variable from index 2 on is existential):
  - `exA`: `a() => b(?X:Int)`: X held under a constructor (arm A), Int unconfined;
  - `exB`: `a() => a() ensures ?B:Bool`: B under no constructor, of the confined sort Bool (arm B);
  - `exTwo`: `a() => b(?X:Int) ensures ?B:Bool`: two existential variables, X by arm A, B by arm B;
  - `exUnsat`: `a() => b(?Z:Int) ensures ?Z *Int 2 ==Int 1`: Z by arm A; the conjunct holds
    although no Int satisfies the `ensures`;
  - `exBad`: `a() => a() ensures ?Z ==Int 0`: Z under the hooked function `_==Int_` only, of the
    unconfined sort Int and in no condition: no arm holds it, the conjunct is false.
  Each is well sorted (`ruleSorted`: an existential variable is open and in no condition), and none
  has `rulePlainOpen` (that conjunct asks for no existential variable).

  The value model at a transition T (`Faithful.Model.sat_rule_T`, `satRulesGoal_T`): under `FnDet`
  and `FnSolves`, the axiom of each admitted rule holds at the transition that relates x and y where
  some `StepMAt` instance of the rule does (the rule need not be one of the definition's); `satRulesGoal_T` at the definition's rules; and the landed
  `satRulesGoal_open` is `satRulesGoal_T` at `T := StepM c`. The step's closure
  (`Faithful.Model.closureDisjunct_T`, `satStepGoal_T`): a `StepMAt` step by each admitted rule lies
  in the rule's disjunct of the closure at any T; `satStepGoal_T` at `StepM`; and the landed
  `satStepGoal_open` is `satStepGoal_T` at `T := StepM c`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- `ClausePostDecided` from the decided check that every clause's right-side predicate is `\top`. -/
theorem clausePostDecided_of_isTop_exr {c : Semantics}
    (h : (c.fns.all fun f => f.clauses.all fun cl => cl.post.isTop) = true) : ClausePostDecided c :=
  clausePostDecided_of_top fun fn hfn cl hcl =>
    Cond.eq_top_of_isTop (List.all_eq_true.mp (List.all_eq_true.mp h fn hfn) cl hcl)

namespace ExRules

definition_of defn from "f2-examples/symrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def i (n : Int) : Term := .dv Srt.int (.int n)
/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(b), V0)), cnt)`. -/
def cfg (cnt : Term) : Term :=
  .app 71 [.app 383 [.app 0 [.inj 32 1 (.app 386 []), .var 0]], cnt]

/-- The symbols `cfg` and the rules name. -/
example : c.symName 71 = "Lbl'-LT-'generatedTop'-GT-'" ∧ c.symName 383 = "Lbl'-LT-'k'-GT-'" ∧
    c.symName 0 = "kseq" ∧ c.symName 386 = "Lblb" ∧ c.symName 73 = "Lbl'-LT-'generatedCounter'-GT-'" ∧
    c.sortName 32 = "Exp" ∧ c.sortName 1 = "KItem" := by
  decide +kernel

/-- The sorts of the first two variables of the text's rule: K and the counter cell's. -/
noncomputable def sK : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 1 0
noncomputable def sC : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 2 0

/-- A rule over `cfg` with the existential variables `exs`. -/
noncomputable def mkEx (vars : List Srt) (rhs : Term) (ens : Option Term) (exs : List Nat) : Rule :=
  { vars := vars, lhs := cfg (.var 1), req := none, rhs := rhs, ens := ens, prio := 50, exs := exs }

/-- `a() => b(?X:Int)` -/
noncomputable def exA : Rule := mkEx [sK, sC, Srt.int] (cfg (.app 73 [.var 2])) none [2]
/-- `a() => a() ensures ?B:Bool` -/
noncomputable def exB : Rule := mkEx [sK, sC, Srt.bool] (cfg (.var 1)) (some (.var 2)) [2]
/-- `a() => b(?X:Int) ensures ?B:Bool` -/
noncomputable def exTwo : Rule :=
  mkEx [sK, sC, Srt.int, Srt.bool] (cfg (.app 73 [.var 2])) (some (.var 3)) [2, 3]
/-- `a() => b(?Z:Int) ensures ?Z *Int 2 ==Int 1` -/
noncomputable def exUnsat : Rule :=
  mkEx [sK, sC, Srt.int] (cfg (.app 73 [.var 2])) (some (.app intEq [.app intMul [.var 2, i 2], i 1])) [2]
/-- `a() => a() ensures ?Z ==Int 0` -/
noncomputable def exBad : Rule := mkEx [sK, sC, Srt.int] (cfg (.var 1)) (some (.app intEq [.var 2, i 0])) [2]

/-! ## Arm A: an existential variable under a constructor -/

/-- `exA` is well sorted with the conjunct; X (index 2) is its only open variable, existential,
held under constructors, of the unconfined sort Int. -/
theorem exA_ex : c.ruleSorted exA = true ∧ c.rulePlainEx exA = true ∧ exA.opens = [2] ∧ exA.exs = [2] ∧
    (ctorOccs c exA.rhs).contains 2 = true ∧ c.confined Srt.int = false := by
  decide +kernel

/-! ## Arm B: an existential variable of a confined sort -/

/-- `exB` is well sorted with the conjunct; B (index 2) is under no constructor, so it passes by
its sort, Bool, being confined. -/
theorem exB_ex : c.ruleSorted exB = true ∧ c.rulePlainEx exB = true ∧ exB.opens = [2] ∧ exB.exs = [2] ∧
    (ctorOccs c exB.rhs).contains 2 = false ∧ c.confined Srt.bool = true := by
  decide +kernel

/-! ## Two existential variables -/

/-- `exTwo` is well sorted with the conjunct; X (index 2) passes by arm A, B (index 3) by arm B. -/
theorem exTwo_ex : c.ruleSorted exTwo = true ∧ c.rulePlainEx exTwo = true ∧ exTwo.opens = [2, 3] ∧
    exTwo.exs = [2, 3] ∧ (ctorOccs c exTwo.rhs).contains 2 = true ∧
    (ctorOccs c exTwo.rhs).contains 3 = false := by
  decide +kernel

/-! ## An `ensures` no value satisfies: admitted -/

/-- `exUnsat` is well sorted with the conjunct: Z (index 2) is held under a constructor, and the
conjunct does not read the `ensures`' truth. -/
theorem exUnsat_ex : c.ruleSorted exUnsat = true ∧ c.rulePlainEx exUnsat = true ∧ exUnsat.opens = [2] ∧
    exUnsat.exs = [2] ∧ (ctorOccs c exUnsat.rhs).contains 2 = true := by
  decide +kernel

/-! ## A variable held by no arm: the conjunct false -/

/-- `exBad` is well sorted, and the conjunct is false: Z (index 2) is under `_==Int_` only, Int is
unconfined, and Z is in no condition. -/
theorem exBad_ex : c.ruleSorted exBad = true ∧ c.rulePlainEx exBad = false ∧ exBad.opens = [2] ∧
    (ctorOccs c exBad.rhs).contains 2 = false ∧ c.confined Srt.int = false ∧ exBad.condVars = [] := by
  decide +kernel

/-! ## None has `rulePlainOpen`; the admitted ones have `\top` predicates -/

/-- `rulePlainOpen_iff_ex` at the four admitted rules: each fails `rulePlainOpen` by its existential
variables alone; `rulePlainEx_top` at each. -/
example : c.rulePlainOpen exA = false ∧ c.rulePlainOpen exB = false ∧ c.rulePlainOpen exTwo = false ∧
    c.rulePlainOpen exUnsat = false ∧ c.rulePlainOpen exBad = false := by
  decide +kernel

example : exA.pre = .top ∧ exB.post = .top ∧ exTwo.pre = .top ∧ exUnsat.post = .top :=
  ⟨(Semantics.rulePlainEx_top exA_ex.2.1).1, (Semantics.rulePlainEx_top exB_ex.2.1).2,
   (Semantics.rulePlainEx_top exTwo_ex.2.1).1, (Semantics.rulePlainEx_top exUnsat_ex.2.1).2⟩

example : c.rulePlainOpen exTwo ≠ true :=
  fun h => absurd (Semantics.rulePlainOpen_iff_ex.mp h).2 (by decide +kernel)

/-! ## The value model at a transition T satisfies the axiom of each admitted rule -/

section AtT
open Faithful Faithful.Model

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The rules of the definition have `ruleSorted` and `rulePlainEx`. -/
theorem hrulesC : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true :=
  Semantics.ruleFactsEx_of_coreAll coreOK (by decide +kernel)

/-- The transition of a rule's own instances. -/
def ownT (r : Rule) (x y : GroundTerm) : Prop := ∃ σ, StepMAt c r σ x y

/-- `sat_rule_T` at a rule with existential variables and the transition of its own instances:
`hall` is not asked, `hsome` holds with the instance itself. -/
theorem sat_own (hd : FnDet c) (hs : FnSolves c) {r : Rule} (hsr : c.ruleSorted r = true)
    (hpr : c.rulePlainEx r = true) (hne : r.exs ≠ []) :
    stdI_T c (ownT r) ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩).pat :=
  sat_rule_T (hypModel_of_fn coreOK hd hs) hrulesC hsr hpr (ownT r)
    (fun _ _ _ _ he => absurd he hne) (fun σ _ y hst _ => ⟨y, σ, fun _ _ => rfl, hst, σ, hst⟩)

example (hd : FnDet c) (hs : FnSolves c) :
    (stdI_T c (ownT exA) ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [], pattern := prioRuleK c exA, attributes := [] }⟩).pat) ∧
    (stdI_T c (ownT exB) ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [], pattern := prioRuleK c exB, attributes := [] }⟩).pat) ∧
    (stdI_T c (ownT exTwo) ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [], pattern := prioRuleK c exTwo, attributes := [] }⟩).pat) ∧
    (stdI_T c (ownT exUnsat) ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [], pattern := prioRuleK c exUnsat, attributes := [] }⟩).pat) :=
  ⟨sat_own hd hs exA_ex.1 exA_ex.2.1 (by rw [exA_ex.2.2.2.1]; exact List.cons_ne_nil _ _),
   sat_own hd hs exB_ex.1 exB_ex.2.1 (by rw [exB_ex.2.2.2.1]; exact List.cons_ne_nil _ _),
   sat_own hd hs exTwo_ex.1 exTwo_ex.2.1 (by rw [exTwo_ex.2.2.2.1]; exact List.cons_ne_nil _ _),
   sat_own hd hs exUnsat_ex.1 exUnsat_ex.2.1 (by rw [exUnsat_ex.2.2.2.1]; exact List.cons_ne_nil _ _)⟩

/-- `satRulesGoal_T` at the definition's rules at `StepM`. `c`'s rules
have no existential variable, so `hsome` is not read here; the instances with existential variables
are `sat_rule_T`'s above, and `satRulesGoal_T` at `cX` (end of file). -/
example (hd : FnDet c) (hs : FnSolves c) :
    (stdI_T c (StepM c) ⊧ᴵP ΓRules c) := by
  exact satRulesGoal_T (hypModel_of_fn coreOK hd hs) hrulesC (StepM c)
    (fun r σ _ _ hb _ => (stepM_iff_by c).mpr ⟨r, σ, hb⟩)
    (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, (stepM_iff_by c).mpr ⟨r, σ, hb⟩⟩)

/-- `closureDisjunct_T` at a rule, the closure's variable placed after the rule's table. -/
theorem disj_own (hd : FnDet c) (hs : FnSolves c) {r : Rule} (hsr : c.ruleSorted r = true)
    (hpr : c.rulePlainEx r = true) (T : GroundTerm → GroundTerm → Prop) {σ : Subst} {x y : GroundTerm}
    (hst : StepMAt c r σ x y) (hx : c.sortOf x = some topCellSort) (e1 : ML.Valuation Elem)
    (he1 : e1.evalEvar ⟨(KoreAML.tableOf [] (prioRuleK c r)).length + 1⟩ = .val y) :
    (KoreAML.closureDisjunct [] 0 ⟨(KoreAML.tableOf [] (prioRuleK c r)).length + 1⟩ (prioRuleK c r)).2.interpret
      (stdI_T c T) e1 (.val x) :=
  closureDisjunct_T (hypModel_of_fn coreOK hd hs) hrulesC hsr hpr hst hx 0 _
    (fun k hk he => by have h1 := index_le hk; rw [← he] at h1; simp at h1; omega) e1 he1

example (hd : FnDet c) (hs : FnSolves c) (T : GroundTerm → GroundTerm → Prop) (σ : Subst) (x y : GroundTerm)
    (hx : c.sortOf x = some topCellSort) (e1 : ML.Valuation Elem) :
    (StepMAt c exA σ x y → e1.evalEvar ⟨(KoreAML.tableOf [] (prioRuleK c exA)).length + 1⟩ = .val y →
      (KoreAML.closureDisjunct [] 0 ⟨(KoreAML.tableOf [] (prioRuleK c exA)).length + 1⟩ (prioRuleK c exA)).2.interpret
        (stdI_T c T) e1 (.val x)) ∧
    (StepMAt c exB σ x y → e1.evalEvar ⟨(KoreAML.tableOf [] (prioRuleK c exB)).length + 1⟩ = .val y →
      (KoreAML.closureDisjunct [] 0 ⟨(KoreAML.tableOf [] (prioRuleK c exB)).length + 1⟩ (prioRuleK c exB)).2.interpret
        (stdI_T c T) e1 (.val x)) ∧
    (StepMAt c exTwo σ x y → e1.evalEvar ⟨(KoreAML.tableOf [] (prioRuleK c exTwo)).length + 1⟩ = .val y →
      (KoreAML.closureDisjunct [] 0 ⟨(KoreAML.tableOf [] (prioRuleK c exTwo)).length + 1⟩ (prioRuleK c exTwo)).2.interpret
        (stdI_T c T) e1 (.val x)) ∧
    (StepMAt c exUnsat σ x y → e1.evalEvar ⟨(KoreAML.tableOf [] (prioRuleK c exUnsat)).length + 1⟩ = .val y →
      (KoreAML.closureDisjunct [] 0 ⟨(KoreAML.tableOf [] (prioRuleK c exUnsat)).length + 1⟩
        (prioRuleK c exUnsat)).2.interpret (stdI_T c T) e1 (.val x)) :=
  ⟨fun hst he1 => disj_own hd hs exA_ex.1 exA_ex.2.1 T hst hx e1 he1,
   fun hst he1 => disj_own hd hs exB_ex.1 exB_ex.2.1 T hst hx e1 he1,
   fun hst he1 => disj_own hd hs exTwo_ex.1 exTwo_ex.2.1 T hst hx e1 he1,
   fun hst he1 => disj_own hd hs exUnsat_ex.1 exUnsat_ex.2.1 T hst hx e1 he1⟩

/-- `satStepGoal_T` at the definition's rules at `StepM`. -/
example (hd : FnDet c) (hs : FnSolves c) : stdI_T c (StepM c) ⊧ᴵP Γstep c :=
  satStepGoal_T (hypModel_of_fn coreOK hd hs) hrulesC (StepM c) (fun _ _ _ _ h => h)

end AtT

/-- The landed `satRulesGoal_open` is `satRulesGoal_T` at `T := StepM c`. -/
example : type_of% @Faithful.Model.satRulesGoal_open := @fun c h hrules =>
  Faithful.Model.satRulesGoal_T h
    (fun r hr => ⟨(hrules r hr).1, (Semantics.rulePlainOpen_iff_ex.mp (hrules r hr).2).1⟩) (Faithful.Model.StepM c)
    (fun r σ _ _ hb _ => (Faithful.Model.stepM_iff_by c).mpr ⟨r, σ, hb⟩)
    (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, (Faithful.Model.stepM_iff_by c).mpr ⟨r, σ, hb⟩⟩)

/-- The landed `satStepGoal_open` is `satStepGoal_T` at `T := StepM c`. -/
example : type_of% @Faithful.Model.satStepGoal_open := @fun c h hrules =>
  Faithful.Model.satStepGoal_T h
    (fun r hr => ⟨(hrules r hr).1, (Semantics.rulePlainOpen_iff_ex.mp (hrules r hr).2).1⟩) (Faithful.Model.StepM c)
    (fun _ _ _ _ h' => h')

end ExRules

/-! # The choice among instances (`KCore.has_model_choice_exCEx`, `KCore.ExChoice`)

  - `stepMAt_of_notApplies_ex` and `notApplies_of_stepMAt_ex` at `exA`, `exB`, `exTwo`, `exUnsat`:
    `Step`'s and `StepM`'s exclusions of competitors agree for a rule with existential variables,
    the rule not one of the definition's;
  - `step_iff_stdI_T` at the transition of `exA`'s own instances (`ownT`), not `StepM`;
  - `stdI_T_modelCEx`, `stdI_model_exCEx` and `has_model_choice_exCEx` at the definition's rules.
    `c`'s rules have no existential variable, so there `hsome` is read at no rule; their instances
    at a definition with one are at `cX` (end of file);
  - the pinned `has_model_choice` as a term over `has_model_choice_exCEx` (`type_of%`). -/

namespace ExRules

section Choice
open Faithful Faithful.Model

/-! ## The two exclusions of competitors agree, at rules with existential variables -/

/-- `stepMAt_of_notApplies_ex` and `notApplies_of_stepMAt_ex` at a rule. -/
theorem excl_own (h : FnHyp c) {r : Rule} {σ : Subst} {x y : GroundTerm} :
    (c.WellSorted r.vars σ → PatVal c σ r.lhs x → (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) →
      Holds c r.vars.length σ r.pre true →
      EvalTerm c σ r.rhs (some y) → (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) →
      Holds c r.vars.length σ r.post true →
      (∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x) → StepMAt c r σ x y) ∧
    (StepMAt c r σ x y → ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x) :=
  ⟨fun hσ hm hq hpr he hn hpo hp =>
    stepMAt_of_notApplies_ex (fnModel_of_fnHyp coreOK h).1 hrulesC hσ hm hq hpr he hn hpo hp,
   notApplies_of_stepMAt_ex (stepDecided_pp (hypSound_of_core coreOK) h.1
     (fun r' hr' => (hrulesC r' hr').1) x)⟩

example (h : FnHyp c) (σ : Subst) (x y : GroundTerm) :
    (StepMAt c exA σ x y → ∀ r' ∈ c.rules, r'.prio < exA.prio → NotApplies c r' x) ∧
    (StepMAt c exB σ x y → ∀ r' ∈ c.rules, r'.prio < exB.prio → NotApplies c r' x) ∧
    (StepMAt c exTwo σ x y → ∀ r' ∈ c.rules, r'.prio < exTwo.prio → NotApplies c r' x) ∧
    (StepMAt c exUnsat σ x y → ∀ r' ∈ c.rules, r'.prio < exUnsat.prio → NotApplies c r' x) :=
  ⟨(excl_own h).2, (excl_own h).2, (excl_own h).2, (excl_own h).2⟩

example (h : FnHyp c) (σ : Subst) (x y : GroundTerm) (hσ : c.WellSorted exTwo.vars σ)
    (hm : PatVal c σ exTwo.lhs x) (he : EvalTerm c σ exTwo.rhs (some y))
    (hn : ∀ t, exTwo.ens = some t → EvalTerm c σ t (some (bool true)))
    (hp : ∀ r' ∈ c.rules, r'.prio < exTwo.prio → NotApplies c r' x) : StepMAt c exTwo σ x y :=
  (excl_own h).1 hσ hm (fun t ht => by simp [exTwo, mkEx] at ht) ((Semantics.rulePlainEx_top exTwo_ex.2.1).1 ▸ .top)
    he hn ((Semantics.rulePlainEx_top exTwo_ex.2.1).2 ▸ .top) hp

example (h : FnHyp c) (σ : Subst) (x y : GroundTerm) (hσ : c.WellSorted exA.vars σ)
    (hm : PatVal c σ exA.lhs x) (he : EvalTerm c σ exA.rhs (some y))
    (hp : ∀ r' ∈ c.rules, r'.prio < exA.prio → NotApplies c r' x) : StepMAt c exA σ x y :=
  (excl_own h).1 hσ hm (fun t ht => by simp [exA, mkEx] at ht) ((Semantics.rulePlainEx_top exA_ex.2.1).1 ▸ .top)
    he (fun t ht => by simp [exA, mkEx] at ht) ((Semantics.rulePlainEx_top exA_ex.2.1).2 ▸ .top) hp

/-! ## At configurations the value model's transition is T -/

/-- `step_iff_stdI_T` at the transition of `exA`'s own instances. -/
example (hd : FnDet c) (hs : FnSolves c) (x y : Config c) :
    ownT exA x.val y.val ↔
      ¬ (stdI_T c (ownT exA) ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  step_iff_stdI_T c (hypModel_of_fn coreOK hd hs) (ownT exA) x y

/-! ## The models, at the definition's rules -/

example (hd : FnDet c) (hs : FnSolves c) : stdI_T c (StepM c) ⊧ᴵP (Γc c ∪ Γstep c) :=
  stdI_T_modelCEx c (hypModel_of_fn coreOK hd hs) (clausePreDecided_of_isTop (by decide +kernel)) (clausePostDecided_of_isTop_exr (by decide +kernel)) (openLaws_of_plain (by decide +kernel)) hrulesC (StepM c) (fun _ _ _ _ hT => hT)
    (fun r σ _ _ hb _ => (stepM_iff_by c).mpr ⟨r, σ, hb⟩)
    (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, (stepM_iff_by c).mpr ⟨r, σ, hb⟩⟩)

example (hd : FnDet c) (hs : FnSolves c) : stdI c ⊧ᴵP (Γc c ∪ Γstep c) :=
  stdI_model_exCEx c (hypModel_of_fn coreOK hd hs) (clausePreDecided_of_isTop (by decide +kernel)) (clausePostDecided_of_isTop_exr (by decide +kernel)) (openLaws_of_plain (by decide +kernel)) hrulesC

/-- `has_model_choice_exCEx` at `T := Step c`. -/
example (hf : FnHyp c) : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  has_model_choice_exCEx c (Semantics.coreOK_iff_ex.mp coreOK) hf hrulesC (Step c) (fun _ _ hst => hst)
    (fun _ _ r σ hb _ => step_iff_by.mpr ⟨r, σ, hb⟩)
    (fun _ y r σ hb => ⟨y, σ, fun _ _ => rfl, hb, step_iff_by.mpr ⟨r, σ, hb⟩⟩)

end Choice

end ExRules

/-! ## The landed and pinned statements, as terms over the new ones

  A pinned statement is a term over the `CEx` statement where the rules have `rulePlainEx`
  (`hex`), with `ruleSorted` from `coreOK`. -/

namespace ExRules

theorem hrulesEx_of_openC {c : Semantics}
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true :=
  fun r hr => ⟨(hrules r hr).1, (Semantics.rulePlainOpen_iff_ex.mp (hrules r hr).2).1⟩

/-- The rules' facts of a semantics `coreOK` accepts whose rules have `rulePlainEx`. -/
theorem hrulesEx_of_coreC {c : Semantics} (h : c.coreOK = true)
    (hex : c.rules.all c.rulePlainEx = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true :=
  Semantics.ruleFactsEx_of_coreAll h hex

example (c : Semantics) (hex : c.rules.all c.rulePlainEx = true) : type_of% (@has_model_choice c) := fun h hf => has_model_choice_exCEx c (Semantics.coreOK_iff_ex.mp h) hf (hrulesEx_of_coreC h hex)

end ExRules

/-! # A value among the instances of an application

  `cR`: the text's semantics with the rule `openB` (`a() => a() ensures B`, B:Bool, open, no
  existential variable), so that it has `coreOK` and reads a confined sort (`readsConfined`), both
  decided. In any model of `Γc cR`, a configuration whose element is in `famEx cR r σ` is the right
  side at a σ' that differs from σ at r's existential variables only: at `exA` (arm A: X under a
  constructor; `hrc` is not read, X's sort Int is unconfined), `exB` (arm B: B of the confined sort
  Bool, `hrc` read) and `exTwo` (both). The rules are not `cR`'s. -/

namespace ExRules

/-- `a() => a() ensures B`, B open. -/
noncomputable def openB : Rule := mkEx [sK, sC, Srt.bool] (cfg (.var 1)) (some (.var 2)) []

/-- The text's semantics with `openB`. -/
noncomputable abbrev cR : Semantics := { c with rules := c.rules ++ [openB] }

theorem coreR : cR.coreOK = true ∧ cR.readsConfined = true ∧
    (cR.ruleSorted exA = true ∧ cR.rulePlainEx exA = true) ∧
    (cR.ruleSorted exB = true ∧ cR.rulePlainEx exB = true) ∧
    (cR.ruleSorted exTwo = true ∧ cR.rulePlainEx exTwo = true) ∧
    exA.exs.any (fun i => (exA.vars[i]?.map cR.confined).getD false) = false ∧
    exB.exs.any (fun i => (exB.vars[i]?.map cR.confined).getD false) = true ∧
    exTwo.exs.any (fun i => (exTwo.vars[i]?.map cR.confined).getD false) = true := by
  decide_cheap

/-! ## The outcomes of a match

  `exB`'s one open variable is its existential one, of the confined sort Bool (`exB_confOpens`);
  `exB` is not one of `cR`'s rules. -/

/-- The open variables of `exB` are of confined sorts. -/
theorem exB_confOpens : ∀ i ∈ exB.opens, (exB.vars[i]?.map cR.confined).getD false = true := by
  decide +kernel

end ExRules

/-! # Soundness at a step by a rule with existential variables

  In any model of `Γc c`, at `exA`, `exB` and `exTwo` (not the definition's rules): a step's
  successor is among the instances of its application; an element of the right side at a valuation
  of σ is among them (`famEx_of_right_ex`); the right side's elements are in the configuration sort
  (`ruleRight_sort_ex`), its `ceil` holds (`ceil_right_ex`), y is in it; the axiom gives a successor
  among the instances. At `exUnsat`, whose `ensures` is true under no σ, the lemmas that do not read
  a true `ensures` (`famEx_of_right_ex`, `ruleRight_sort_ex`, `ceil_right_ex`, the `dropExs` facts);
  the others would hold there only vacuously. A competitor's `NotApplies`, `ruleSorted` and
  `rulePlainOpen` with its existential variables read as ordinary ones, at `exA`, `exB`, `exTwo`. -/

namespace ExRules

section SoundEx
open Faithful

variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γc c)
include hI

example := @famEx_of_right_ex c M _ I coreOK hI exA exA_ex.1 exA_ex.2.1
example := @famEx_of_right_ex c M _ I coreOK hI exB exB_ex.1 exB_ex.2.1
example := @famEx_of_right_ex c M _ I coreOK hI exTwo exTwo_ex.1 exTwo_ex.2.1
example := @famEx_of_right_ex c M _ I coreOK hI exUnsat exUnsat_ex.1 exUnsat_ex.2.1

example := @ruleRight_sort_ex c M _ I coreOK (fun φ hφ => hI φ (Or.inl hφ)) exA exA_ex.1 exA_ex.2.1
example := @ruleRight_sort_ex c M _ I coreOK (fun φ hφ => hI φ (Or.inl hφ)) exB exB_ex.1 exB_ex.2.1
example := @ruleRight_sort_ex c M _ I coreOK (fun φ hφ => hI φ (Or.inl hφ)) exTwo exTwo_ex.1 exTwo_ex.2.1
example := @ruleRight_sort_ex c M _ I coreOK (fun φ hφ => hI φ (Or.inl hφ)) exUnsat exUnsat_ex.1 exUnsat_ex.2.1

example := @ceil_right_ex c M _ I coreOK (fun φ hφ => hI φ (Or.inl hφ)) exA exA_ex.1 exA_ex.2.1
example := @ceil_right_ex c M _ I coreOK (fun φ hφ => hI φ (Or.inl hφ)) exB exB_ex.1 exB_ex.2.1
example := @ceil_right_ex c M _ I coreOK (fun φ hφ => hI φ (Or.inl hφ)) exTwo exTwo_ex.1 exTwo_ex.2.1
example := @ceil_right_ex c M _ I coreOK (fun φ hφ => hI φ (Or.inl hφ)) exUnsat exUnsat_ex.1 exUnsat_ex.2.1

end SoundEx

example : c.ruleSorted (Faithful.ruleDropExs exA) = true ∧ c.rulePlainOpen (Faithful.ruleDropExs exA) = true ∧
    c.ruleSorted (Faithful.ruleDropExs exB) = true ∧ c.rulePlainOpen (Faithful.ruleDropExs exB) = true ∧
    c.ruleSorted (Faithful.ruleDropExs exTwo) = true ∧ c.rulePlainOpen (Faithful.ruleDropExs exTwo) = true :=
  ⟨Faithful.ruleSorted_dropExs exA_ex.1, Faithful.rulePlainOpen_dropExs exA_ex.2.1,
   Faithful.ruleSorted_dropExs exB_ex.1, Faithful.rulePlainOpen_dropExs exB_ex.2.1,
   Faithful.ruleSorted_dropExs exTwo_ex.1, Faithful.rulePlainOpen_dropExs exTwo_ex.2.1⟩

example : c.ruleSorted (Faithful.ruleDropExs exUnsat) = true ∧ c.rulePlainOpen (Faithful.ruleDropExs exUnsat) = true ∧
    ∀ x, NotApplies c exUnsat x → NotApplies c (Faithful.ruleDropExs exUnsat) x :=
  ⟨Faithful.ruleSorted_dropExs exUnsat_ex.1, Faithful.rulePlainOpen_dropExs exUnsat_ex.2.1,
   fun _ => Faithful.notApplies_dropExs⟩

example (x : GroundTerm) : (NotApplies c exA x → NotApplies c (Faithful.ruleDropExs exA) x) ∧
    (NotApplies c exTwo x → NotApplies c (Faithful.ruleDropExs exTwo) x) :=
  ⟨Faithful.notApplies_dropExs, Faithful.notApplies_dropExs⟩

end ExRules

/-! # Completeness with rules with existential variables

  In any model of `Γc c`, at `exA`, `exB` and `exTwo` (not the definition's rules): the axiom's left
  part read (`rule_partsEx`), `famOpen`'s pattern (`famOpen_eqEx`, `famOpen_keysEx`), the valuation
  copied at the variables other than the existential ones (`copyVEx_at`, `copyVEx_off`), and the two
  cases of a successor the axiom gives. `cA`: the text's semantics with `exA` and `exTwo` among its
  rules, each rule with `ruleSorted` and `rulePlainEx` (decided; `cA` is not asked to be `coreOK`):
  in any model of `Γc cA` with the step's closure, a successor is given by a rule's axiom
  (`step_successor_axiomEx`). A competitor's `NotApplies` back from its existential variables read
  as ordinary ones (`notApplies_ofDropExs`). -/

namespace ExRules

section CompleteEx
open Faithful

variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

example := @rule_partsEx c M I hrulesC exA exA_ex.1 exA_ex.2.1
example := @rule_partsEx c M I hrulesC exB exB_ex.1 exB_ex.2.1
example := @rule_partsEx c M I hrulesC exTwo exTwo_ex.1 exTwo_ex.2.1

example (σ : Subst) : famOpen c exA σ = KoreAML.denB (famOpenPatEx c exA σ) :=
  famOpen_eqEx (Semantics.rulePlainEx_top exA_ex.2.1).1 (Semantics.rulePlainEx_top exA_ex.2.1).2
    (fun i hi => (Model.ruleSorted_partsEx exA_ex.1 exA_ex.2.1).2.2.2.2.2.2 i hi |>.1) σ
example (σ : Subst) : famOpen c exB σ = KoreAML.denB (famOpenPatEx c exB σ) :=
  famOpen_eqEx (Semantics.rulePlainEx_top exB_ex.2.1).1 (Semantics.rulePlainEx_top exB_ex.2.1).2
    (fun i hi => (Model.ruleSorted_partsEx exB_ex.1 exB_ex.2.1).2.2.2.2.2.2 i hi |>.1) σ
example (σ : Subst) : famOpen c exTwo σ = KoreAML.denB (famOpenPatEx c exTwo σ) :=
  famOpen_eqEx (Semantics.rulePlainEx_top exTwo_ex.2.1).1 (Semantics.rulePlainEx_top exTwo_ex.2.1).2
    (fun i hi => (Model.ruleSorted_partsEx exTwo_ex.1 exTwo_ex.2.1).2.2.2.2.2.2 i hi |>.1) σ

example (σ : Subst) := @famOpen_keysEx c exTwo σ

/-- The copy at `exTwo`'s variables other than the existential ones, into `famOpen`'s table: X
(index 2) is not copied, V1 (index 1) is. -/
example (σ : Subst) (tbl : KoreAML.VarTable) (src base : ML.Valuation M) :
    (copyVEx c tbl (KoreAML.tableOf [] (famOpenPatEx c exTwo σ)) exTwo.vars [0, 1] src base).evalEvar
        ((KoreAML.tableOf [] (famOpenPatEx c exTwo σ)).ev (canonKey c exTwo.vars 1)) =
      src.evalEvar (tbl.ev (canonKey c exTwo.vars 1)) :=
  copyVEx_at famOpen_keysEx (by simp [exTwo, mkEx]) (by simp)

example (tbl tbl' : KoreAML.VarTable) (src base : ML.Valuation M) (z : ML.EVar)
    (hz : ∀ i < exTwo.vars.length, i ∈ [0, 1] → z ≠ tbl'.ev (canonKey c exTwo.vars i)) :
    (copyVEx c tbl tbl' exTwo.vars [0, 1] src base).evalEvar z = base.evalEvar z :=
  copyVEx_off hz

example (x : GroundTerm) : (NotApplies c (ruleDropExs exA) x → NotApplies c exA x) ∧
    (NotApplies c (ruleDropExs exTwo) x → NotApplies c exTwo x) :=
  ⟨notApplies_ofDropExs, notApplies_ofDropExs⟩

end CompleteEx

/-- The text's semantics with `exA` and `exTwo` among its rules. -/
noncomputable abbrev cA : Semantics := { c with rules := c.rules ++ [exA, exTwo] }

theorem hrulesA : ∀ r ∈ cA.rules, cA.ruleSorted r = true ∧ cA.rulePlainEx r = true := by
  decide +kernel

/-- `cA` has rules with existential variables. -/
example : exA ∈ cA.rules ∧ exA.exs ≠ [] ∧ exTwo ∈ cA.rules ∧ exTwo.exs ≠ [] :=
  ⟨List.mem_append_right _ (List.mem_cons_self ..), by rw [exA_ex.2.2.2.1]; exact List.cons_ne_nil _ _,
   List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
   by rw [exTwo_ex.2.2.2.1]; exact List.cons_ne_nil _ _⟩

open Faithful in
/-- `step_successor_axiomEx` at `cA`, whose rules `exA` and `exTwo` have existential variables. -/
example {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} :=
  @step_successor_axiomEx cA M _ I hrulesA

example (hf : FnHyp c) (x : GroundTerm) : StepDecided c x :=
  stepDecided_of_rules_ex (hypSound_of_core coreOK) hf.1 hrulesC x

example : type_of% @Faithful.stepDecided_of_rules := @fun _ h hft hr x =>
  stepDecided_of_rules_ex h hft (hrulesEx_of_openC hr) x

end ExRules

/-! # Exactness with rules with existential variables

  In any model of `Γc cR`, at `exA` (arm A), `exB` (arm B, Bool confined) and `exTwo` (both), not
  `cR`'s rules: a successor in the right side `∃ē. (rhs ∧ ens)` gives the step's values
  (`stepVals_of_right_exSSx`); neither rule needs a witness. `step_of_successor_exCEx`
  reads every rule's facts, so it stands at the definition's rules (`c`, `cR`, which have no
  existential variable; `exact_hyp` at `cX`, end of file). -/

namespace ExRules

theorem noWitR : exA.needsWitness cR = false ∧ exB.needsWitness cR = false ∧ exTwo.needsWitness cR = false := by
  decide +kernel

section ExactEx
open Faithful

variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

example (hft : FnTerminates cR) (hI : I ⊧ᴵP Γc cR) := fun hcw =>
  @stepVals_of_right_exSSx cR M _ I (Semantics.coreOK_iff_ex.mp coreR.1) hft hI hcw exA coreR.2.2.1.1 coreR.2.2.1.2 (fun _ => coreR.2.1)
    (fun hn => absurd hn (by rw [noWitR.1]; decide))
example (hft : FnTerminates cR) (hI : I ⊧ᴵP Γc cR) := fun hcw =>
  @stepVals_of_right_exSSx cR M _ I (Semantics.coreOK_iff_ex.mp coreR.1) hft hI hcw exB coreR.2.2.2.1.1 coreR.2.2.2.1.2 (fun _ => coreR.2.1)
    (fun hn => absurd hn (by rw [noWitR.2.1]; decide))
example (hft : FnTerminates cR) (hI : I ⊧ᴵP Γc cR) := fun hcw =>
  @stepVals_of_right_exSSx cR M _ I (Semantics.coreOK_iff_ex.mp coreR.1) hft hI hcw exTwo coreR.2.2.2.2.1.1 coreR.2.2.2.2.1.2 (fun _ => coreR.2.1)
    (fun hn => absurd hn (by rw [noWitR.2.2]; decide))

end ExactEx

example (hf : FnHyp c) {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} :=
  @step_of_successor_exCEx c (Semantics.coreOK_iff_ex.mp coreOK) hf hrulesC M _ I
example (hf : FnHyp cR) {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} :=
  @step_of_successor_exCEx cR (Semantics.coreOK_iff_ex.mp coreR.1) hf (hrulesEx_of_coreC coreR.1 (by decide +kernel)) M _ I

end ExRules

/-! # After the flip: a definition `coreOK` accepts with a rule with existential variables

  `rulesPlain` asks `rulePlainHO2` of each rule (`Semantics.rulesPlain_iff_memHeld`), not
  `r.exs = []`. `cX`, the text's semantics with `exTwo` (`a() => b(?X:Int) ensures ?B:Bool`: X by
  arm A, B by arm B), has `coreOK` and `rulesPlain` (`coreX`), and `exTwo` is one of its rules.
  `FnDet`, `FnSolves`, `FnHyp` and the witnesses are hypotheses, as above. -/

namespace ExRules

/-- The text's semantics with `exTwo`. -/
noncomputable abbrev cX : Semantics := { c with rules := c.rules ++ [exTwo] }

theorem coreX : cX.coreOK = true ∧ cX.rulesPlain = true ∧ exTwo.exs = [2, 3] := by
  decide_cheap

theorem exTwo_memX : exTwo ∈ cX.rules := List.mem_append_right _ (List.mem_singleton_self _)

/-- `cX` has a rule with existential variables: the instances below read `hsome` there. -/
theorem exs_someX : ∃ r ∈ cX.rules, r.exs ≠ [] :=
  ⟨exTwo, exTwo_memX, by rw [coreX.2.2]; exact List.cons_ne_nil _ _⟩

/-- The rules' facts at `cX`, from `coreOK` and the rules' `rulePlainEx`, decided. -/
theorem hrulesX : ∀ r ∈ cX.rules, cX.ruleSorted r = true ∧ cX.rulePlainEx r = true :=
  Semantics.ruleFactsEx_of_coreAll coreX.1 (by decide +kernel)

section FlipX
open Faithful Faithful.Model

/-- `satRulesGoal_T` at `cX`'s rules at `StepM`: `hsome` read at `exTwo`. -/
example (hd : FnDet cX) (hs : FnSolves cX) : stdI_T cX (StepM cX) ⊧ᴵP ΓRules cX :=
  satRulesGoal_T (hypModel_of_fn coreX.1 hd hs) hrulesX (StepM cX)
    (fun r σ _ _ hb _ => (stepM_iff_by cX).mpr ⟨r, σ, hb⟩)
    (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, (stepM_iff_by cX).mpr ⟨r, σ, hb⟩⟩)

/-- `satStepGoal_T` at `cX`'s rules at `StepM`. -/
example (hd : FnDet cX) (hs : FnSolves cX) : stdI_T cX (StepM cX) ⊧ᴵP Γstep cX :=
  satStepGoal_T (hypModel_of_fn coreX.1 hd hs) hrulesX (StepM cX) (fun _ _ _ _ hT => hT)

/-- `stdI_T_modelCEx` at `cX`'s rules at `StepM`: `hsome` read at `exTwo`. -/
example (hd : FnDet cX) (hs : FnSolves cX) : stdI_T cX (StepM cX) ⊧ᴵP (Γc cX ∪ Γstep cX) :=
  stdI_T_modelCEx cX (hypModel_of_fn coreX.1 hd hs) (clausePreDecided_of_isTop (by decide +kernel)) (clausePostDecided_of_isTop_exr (by decide +kernel)) (openLaws_of_plain (by decide +kernel)) hrulesX (StepM cX) (fun _ _ _ _ hT => hT)
    (fun r σ _ _ hb _ => (stepM_iff_by cX).mpr ⟨r, σ, hb⟩)
    (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, (stepM_iff_by cX).mpr ⟨r, σ, hb⟩⟩)

example (hd : FnDet cX) (hs : FnSolves cX) : stdI cX ⊧ᴵP (Γc cX ∪ Γstep cX) :=
  stdI_model_exCEx cX (hypModel_of_fn coreX.1 hd hs) (clausePreDecided_of_isTop (by decide +kernel)) (clausePostDecided_of_isTop_exr (by decide +kernel)) (openLaws_of_plain (by decide +kernel)) hrulesX

/-- The pinned `consistent_of` at `cX`. -/
example (hd : FnDet cX) (hs : FnSolves cX) (hp : ClausePreDecided cX) (hl : OpenLaws cX) : Consistent cX :=
  consistent_of cX coreX.1 hd hs hp (clausePostDecided_of_isTop_exr (by decide +kernel)) hl

/-- `has_model_choice_exCEx` and the pinned `has_model_choice` at `T := Step cX`: `hsome` read at
`exTwo`'s steps. -/
example (hf : FnHyp cX) : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc cX ∪ Γstep cX)) ∧
      ∀ x y : Config cX, Step cX x y ↔ ¬ (I ⊧ᴵ (den cX x.val ⇒ ∼ KoreAML.sNext (den cX y.val))) :=
  has_model_choice_exCEx cX (Semantics.coreOK_iff_ex.mp coreX.1) hf hrulesX (Step cX) (fun _ _ hst => hst)
    (fun _ _ r σ hb _ => step_iff_by.mpr ⟨r, σ, hb⟩)
    (fun _ y r σ hb => ⟨y, σ, fun _ _ => rfl, hb, step_iff_by.mpr ⟨r, σ, hb⟩⟩)

example (hf : FnHyp cX) : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc cX ∪ Γstep cX)) ∧
      ∀ x y : Config cX, Step cX x y ↔ ¬ (I ⊧ᴵ (den cX x.val ⇒ ∼ KoreAML.sNext (den cX y.val))) :=
  has_model_choice cX coreX.1 hf (Step cX) (fun _ _ hst => hst)
    (fun _ _ r σ hb _ => step_iff_by.mpr ⟨r, σ, hb⟩)
    (fun _ y r σ hb => ⟨y, σ, fun _ _ => rfl, hb, step_iff_by.mpr ⟨r, σ, hb⟩⟩)

/-- `stepMBy_of_stepBy_ex` and `stepBy_of_stepMBy_ex` at a step by `exTwo`. -/
example (hd : FnDet cX) {σ : Subst} {x y : Config cX} (hb : StepBy cX exTwo σ x y) :
    StepMBy cX exTwo σ x.val y.val :=
  stepMBy_of_stepBy_ex hd hrulesX hb

example (hft : FnTerminates cX) {σ : Subst} {x y : Config cX} (hb : StepMBy cX exTwo σ x.val y.val) :
    StepBy cX exTwo σ x y :=
  stepBy_of_stepMBy_ex coreX.1 hft hrulesX hb

example (hf : FnHyp cX) (x y : Config cX) (σ : Subst) (hs : ∃ y₀, StepBy cX exTwo σ x y₀)
    (hy : Γc cX ⊧ (den cX y.val ⇒ famEx cX exTwo σ)) :
    ∃ σ', (∀ i, ¬ i ∈ exTwo.exs → σ'.lookup i = σ.lookup i) ∧ StepBy cX exTwo σ' x y :=
  famEx_values cX coreX.1 hf x y exTwo σ hs hy

example (x y : Config cX) (σ : Subst) (hs : StepBy cX exTwo σ x y)
    (hw : ∀ r' ∈ cX.rules, r'.prio < exTwo.prio → r'.needsWitness cX = true →
      (∃ σ', PatVal cX σ' r'.lhs x.val) → r'.CondDecided cX)
    (hc : ∀ fn ∈ cX.fns, ∀ cl ∈ fn.clauses, cl.needsWitness cX = true → cl.CondDecided cX) :
    (Γc cX ⊧ (den cX x.val ⇒ KoreAML.sNext (famEx cX exTwo σ))) ∧ (Γc cX ⊧ (den cX y.val ⇒ famEx cX exTwo σ)) :=
  sound_at cX coreX.1 x y exTwo σ hs hw hc

example (hf : FnHyp cX) (x : Config cX) (os : List Outcome)
    (hval : ∀ (y : Config cX) (r : Rule) (σ : Subst), r.opens = [] → StepBy cX r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ cX.rules, r.opens ≠ [] → ∀ σ, Unblocked cX r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os) :
    (Γc cX ∪ Γstep cX) ⊧ (den cX x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat cX)))) :=
  complete_at cX coreX.1 x (stepDecided_of_fnHyp coreX.1 hf x) os hval hfam hf.2.2.2.2.1.2

/-- The pinned `exact_hyp` at `cX`. -/
example (hf : FnHyp cX) : ExactC cX := exact_hyp cX coreX.1 hf

end FlipX

end ExRules
