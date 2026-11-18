/-
  The fixture e3-vars-ens-unsat (CN-4 §4.8, R2 fixture table, row 3), read from K 7.1.337 kompile's
  KORE: a rule with an existential variable whose `ensures` no value satisfies. Run from the
  package root: `lake env lean -j1 test/ExFixturesEnsUnsat.lean`. Beside `test/ExFixtures.lean`.

  The text (`test/constructs/fixtures/e3-vars-ens-unsat`, copied to
  `f2-examples/exensunsat.kompile.kore`): `rule <k> c() => d(?Z:Int) </k> ensures ?Z *Int 2 ==Int 1`,
  the right side and the `ensures` under the one binder. The rule is admitted as e3-vars' is (Z under
  the constructor d, arm A) and the text has `coreOK` (`facts`, `coreOK`). At no Int value of Z is
  the `ensures` true (`ens_not_true`: `i * 2` is not 1), so `<k> c() </k>` has no successor
  (`no_step`); the value model is a model of the theory (`value_model`), in which the rule's right
  side under its binder is empty (`right_empty`), so its premise `⌈∃Z. (rhs ∧ ens)⌉` is false there.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace ExFixtures

namespace EnsUnsat

definition_of defn from "f2-examples/exensunsat.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def sExp : Srt := 32
def kCell : Sym := 383
def symC : Sym := 385
def symD : Sym := 386

theorem names_ok : c.sortName sExp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symC = "Lblc" ∧ c.symName symD = "Lbld" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem r0_mem : r0 ∈ c.rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rules_one {r : Rule} (h : r ∈ c.rules) : r = r0 := by
  have hl : c.rules.length = 1 := by decide +kernel
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hl
  have h0 : r0 = a := by unfold r0; simp only [ha, List.getElem_cons_zero]
  rw [ha, List.mem_singleton] at h
  rw [h, h0]

/-- `Z *Int 2 ==Int 1`, Z the rule's variable 1. -/
def ensT : Term := .app intEq [.app intMul [.var 1, .dv Srt.int (.int 2)], .dv Srt.int (.int 1)]

theorem r0_vars : r0.vars = [Srt.counter, Srt.int] := by decide +kernel
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symC []),
    .app dotk []]], .var 0] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symD [.var 1]),
    .app dotk []]], .var 0] := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = some ensT ∧ r0.pre = .top ∧ r0.post = .top ∧ r0.exs = [1] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `c() => d(?Z:Int) ensures ?Z *Int 2 ==Int 1` is admitted: Z (variable 1) is existential and
held by the constructor d (arm A), `ruleSorted` and `rulePlainEx` hold; the text declares no
function and no parameter symbol. -/
theorem facts : c.ruleSorted r0 = true ∧ c.rulePlainEx r0 = true ∧ (ctorOccs c r0.rhs).contains 1 = true ∧
    c.fns = [] ∧ c.params = [] := by
  decide +kernel

/-- `<k> c() ~> . </k>` with the counter 0. -/
def X : Config c :=
  ⟨.ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symC []), .ctor dotk []]],
    .ctor counterLabel [int 0]], by decide +kernel⟩

/-! ### No value of Z satisfies the `ensures` -/

theorem int2_at (x y : Int) (f : Int → Int → Option GroundTerm) : int2 [int x, int y] f = f x y := by
  simp [int2, asInt, int]

theorem hook_mul (vs : List GroundTerm) : hook intMul vs = some (int2 vs fun x y => some (int (x * y))) := rfl

/-- **At no Int value of Z is `Z *Int 2 ==Int 1` true**: the product is `i * 2`, which is not 1. -/
theorem ens_not_true {σ : Subst} (hσ : c.WellSorted r0.vars σ) : ¬ EvalTerm c σ ensT (some (bool true)) := by
  intro he
  obtain ⟨v, hv, hsv⟩ := hσ 1 Srt.int (by rw [r0_vars]; rfl)
  obtain ⟨i, rfl⟩ := shape_int (c := c) (by decide +kernel) hsv
  obtain ⟨rs, hts, hh, -⟩ := (EvalTerm.hook_iff (by decide +kernel) rfl).mp he
  obtain ⟨r1, rs1, rfl, h1, hts1⟩ := hts.cons_inv
  obtain ⟨r2, rs2, rfl, h2, hts2⟩ := hts1.cons_inv
  cases hts2.nil_inv
  cases h2.dv_inv
  obtain ⟨ps, hps, hm, -⟩ := (EvalTerm.hook_iff (by decide +kernel) rfl).mp h1
  obtain ⟨p1, ps1, rfl, hp1, hps1⟩ := hps.cons_inv
  obtain ⟨p2, ps2, rfl, hp2, hps2⟩ := hps1.cons_inv
  cases hps2.nil_inv
  cases hp2.dv_inv
  rw [hp1.var_inv, hv] at hm
  have hmul : c.hookRes intMul [int i, int 2] = some (some (int (i * 2))) :=
    Semantics.hookRes_of_value (by rw [hook_mul, int2_at])
  have hr1 := (hm _ rfl).symm.trans hmul
  cases hr1
  have heq : c.hookRes intEq [int (i * 2), int 1] = some (some (KCore.bool (decide (i * 2 = 1)))) :=
    Semantics.hookRes_of_value (by rw [Det.hook_intEq, int2_at])
  have hb := (hh _ rfl).symm.trans heq
  simp only [Option.some.injEq, KCore.bool, GroundTerm.dv.injEq, Lit.bool.injEq, true_and] at hb
  have : i * 2 = 1 := of_decide_eq_true hb.symm
  omega

/-- **`<k> c() </k>` has no successor**: the one rule gives a step only at a value of Z with a true
`ensures`. -/
theorem no_step : ∀ y, ¬ Step c X y := by
  intro y h
  obtain ⟨r, σ, hb⟩ := step_iff_by.mp h
  cases rules_one hb.mem
  exact ens_not_true hb.hσ (hb.hens _ r0_shape.2.1)

/-! ### The value model

The rule is read with the premise `⌈∃Z. (rhs ∧ ens)⌉`. In the value model the right side under its
binder is empty at every valuation that reads the counter variable as a value (`right_empty`), so
the premise is false there and the rule's axiom holds; the value model is a model of the theory
(`value_model`). -/

theorem fnHyp : FnHyp c :=
  fnHyp_of_core (t := defn.cert) coreOK (Semantics.rightHeld_of_valued (by decide +kernel))
    ⟨fun f hf => (by
        rw [show c.orderObligations ++ defn.cert.obligations c = [] by decide +kernel] at hf; cases hf),
      fun f hf => (by rw [show c.totalObligations = [] by decide +kernel] at hf; cases hf),
      fun f hf => (by rw [show c.agreeObligations = [] by decide +kernel] at hf; cases hf),
      fun p hp => (by rw [show c.matchObligations = [] by decide +kernel] at hp; cases hp),
      fun o ho => (by rw [show c.lazyObligations = [] by decide +kernel] at ho; cases ho),
      openDecided_of_plain (fun r hr => (by cases rules_one hr; decide +kernel))
        (fun fn hfn => (by rw [facts.2.2.2.1] at hfn; cases hfn)),
      openLaws_of_plain (fun k hk => (by rw [facts.2.2.2.2] at hk; cases hk))⟩

/-- **The value model is a model of the theory** (`Γc` with the step's closure). -/
theorem value_model : Faithful.Model.stdI c ⊧ᴵP (Γc c ∪ Γstep c) :=
  stdI_model_exCEx c (hypModel_of_fnHyp coreOK fnHyp) (clausePreDecided_of_fnHyp coreOK fnHyp)
    (clausePostDecided_of_fnHypCEx (Semantics.coreOKEx_of_coreOK coreOK) fnHyp)
    (openLaws_of_plain (fun k hk => (by rw [facts.2.2.2.2] at hk; cases hk)))
    (Semantics.ruleFactsEx_of_coreAll coreOK (by decide +kernel))

open Faithful.Model in
/-- **`∃Z. (rhs ∧ ens)` is empty in the value model**, at every valuation that reads the counter
variable as a value of its sort: no element is the right side at a value of Z with a true
`ensures`. -/
theorem right_empty {tbl : KoreAML.VarTable} (hkeys : ∀ i < r0.vars.length, canonKey c r0.vars i ∈ tbl)
    {e : Valuation Elem} {σ : Subst}
    (hσ : ∀ i < r0.vars.length, i ∉ r0.exs → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r0.vars.getD i 0))
    (hvar : ∀ i < r0.vars.length, i ∉ r0.exs → ∀ m,
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c r0.vars) i)).interpret (stdI c) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v) (m : Elem) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r0)).interpret (stdI c) e m := by
  intro hm
  obtain ⟨σ', y, -, hσ', -, hens, -⟩ :=
    (ruleRight_read_T (hypModel_of_fnHyp coreOK fnHyp) facts.1 facts.2.1 (T := StepM c) hkeys hσ hvar m).mp hm
  exact ens_not_true hσ' (hens _ r0_shape.2.1)

/-- info: 'ExFixtures.EnsUnsat.no_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_step
/-- info: 'ExFixtures.EnsUnsat.value_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms value_model
/-- info: 'ExFixtures.EnsUnsat.right_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms right_empty

end EnsUnsat

end ExFixtures
