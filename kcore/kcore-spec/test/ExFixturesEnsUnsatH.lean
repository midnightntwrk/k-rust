/-
  The fixture e3-vars-ens-unsat of test/ExFixturesEnsUnsat.lean, under every interpretation of the
  parameters: K 7.1.337 kompile's text (`f2-examples/exensunsat.kompile.kore`, the fixture's text up
  to the Source and Location attributes) of
  `rule <k> c() => d(?Z:Int) </k> ensures ?Z *Int 2 ==Int 1`, read by the reader, each statement
  over `c0.withHooks H` for every `H : HookParams`, `c0` the reading.
  Run from the package root: `lake env lean -j1 test/ExFixturesEnsUnsatH.lean`.

  ## Why no statement depends on H
  An interpretation enters evaluation in three places: a parameter symbol without a registry hook
  (`Semantics.paramVal`), an interpreted symbol at a silent point where the registry gives no value
  (`Semantics.hookRes`), and the sort of an open generator's application (`Semantics.sortOf`). The
  text declares no function and no parameter symbol (`fns_nil`, `params_nil`), so every value has
  the sort the parsed data gives it (`sortOf_eq`). The `ensures` applies two interpreted hooked
  symbols, `_*Int_` and `_==Int_`, at Int values only: `i * 2` and 1. There the registry gives a
  value, and a value of the registry is the result under every interpretation
  (`Semantics.hookRes_of_value`); the statements read neither symbol at a point where the registry
  gives none.

  The rule's item in Γ is a consequence of its text sentence 154 (W1), on the same text:
  test/TieE3VarsEnsUnsat.lean `rule0_from_text`.

  - `ens_not_true`: at no Int value of Z is the `ensures` true (`i * 2` is not 1).
  - `no_step H`: `<k> c() </k>` (`X H`) has no successor; `no_succ H`: by `ExactC`, no value is its
    successor in any model of `Γc` with the step's closure.
  - `value_model H`: the value model is a model of `Γc` with the step's closure.
  - `right_empty H`: in it, the rule's right side under its binder, `∃Z. (rhs ∧ ens)`, is empty at
    every valuation that reads the counter variable as a value, so the rule's premise
    `⌈∃Z. (rhs ∧ ens)⌉` is false there.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace ExFixturesH

namespace EnsUnsat

/-! The conditions of the parsed data that the proofs read do not read the interpretation. -/
theorem isCtor_wh_exu (c : Semantics) (H : HookParams) (f : Sym) : (c.withHooks H).isCtor f = c.isCtor f := rfl
theorem rules_wh_exu (c : Semantics) (H : HookParams) : (c.withHooks H).rules = c.rules := rfl
theorem fns_wh_exu (c : Semantics) (H : HookParams) : (c.withHooks H).fns = c.fns := rfl
theorem params_wh_exu (c : Semantics) (H : HookParams) : (c.withHooks H).params = c.params := rfl
theorem shapesOK_wh_exu (c : Semantics) (H : HookParams) : (c.withHooks H).shapesOK = c.shapesOK := rfl
kernel_rfl rulePlainEx_wh_exu : ∀ (c : Semantics) (H : HookParams) (r : Rule),
  (c.withHooks H).rulePlainEx r = c.rulePlainEx r

definition_of defn from "f2-examples/exensunsat.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

theorem coreOK0 : c0.coreOK = true := by decide_cheap
theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel

variable {H : HookParams}

/-- A value has the sort the parsed data gives it, under every interpretation: no parameter is an
open generator. -/
theorem sortOf_eq : (c0.withHooks H).sortOf = c0.sortOf := Semantics.sortOf_withHooks c0 H noRaw0

/-- Decides a condition of the parsed data stated of `c0.withHooks H`: the condition does not read
the interpretation, so it is rewritten to `c0`'s and decided there. -/
local macro "whd" : tactic => `(tactic| first | decide +kernel | (rw [sortOf_eq]; decide +kernel) |
  (simp only [isCtor_wh_exu, rules_wh_exu, fns_wh_exu, params_wh_exu, shapesOK_wh_exu];
    decide +kernel))

def sExp : Srt := 32
def kCell : Sym := 383
def symC : Sym := 385
def symD : Sym := 386

theorem names_ok : c0.sortName sExp = "Exp" ∧ c0.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c0.symName symC = "Lblc" ∧ c0.symName symD = "Lbld" := by
  decide +kernel

theorem coreOK : (c0.withHooks H).coreOK = true := (Semantics.coreOK_withHooks c0 H).trans coreOK0

noncomputable def r0 : Rule := c0.rules[0]'(by decide +kernel)

theorem r0_mem : r0 ∈ (c0.withHooks H).rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rules_one {r : Rule} (h : r ∈ (c0.withHooks H).rules) : r = r0 := by
  rw [rules_wh_exu] at h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  have h1 : c0.rules.length = 1 := by decide +kernel
  have : i = 0 := by omega
  subst this
  rfl

/-- `Z *Int 2 ==Int 1`, Z the rule's variable 1. -/
def ensT : Term := .app intEq [.app intMul [.var 1, .dv Srt.int (.int 2)], .dv Srt.int (.int 1)]

theorem r0_vars : r0.vars = [Srt.counter, Srt.int] := by decide +kernel
theorem r0_shape : r0.req = none ∧ r0.ens = some ensT ∧ r0.pre = .top ∧ r0.post = .top ∧ r0.exs = [1] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The text declares no function and no parameter symbol. -/
theorem fns_nil : (c0.withHooks H).fns = [] := by whd
theorem params_nil : (c0.withHooks H).params = [] := by whd
theorem shapesOK : (c0.withHooks H).shapesOK = true := by whd

/-- `c() => d(?Z:Int) ensures ?Z *Int 2 ==Int 1` is admitted under every interpretation:
`ruleSorted` and `rulePlainEx` hold of each rule of the text. -/
theorem ruleFacts : ∀ r ∈ (c0.withHooks H).rules,
    (c0.withHooks H).ruleSorted r = true ∧ (c0.withHooks H).rulePlainEx r = true :=
  have h0 : c0.rules.all c0.rulePlainEx = true := by decide +kernel
  Semantics.ruleFactsEx_of_coreAll coreOK (List.all_eq_true.mpr fun r hr => by
    rw [rulePlainEx_wh_exu]; exact List.all_eq_true.mp h0 r hr)

theorem noWitness : ∀ r ∈ (c0.withHooks H).rules, r.needsWitness (c0.withHooks H) = false := by
  intro r hr
  rw [rules_one hr]
  have h : r0.reqOpen = false := by decide +kernel
  simp only [Rule.needsWitness, h, Bool.false_and]

/-- The hypothesis on the functions holds: the text declares none, no rule needs a witness and it
has no parameter symbol. -/
theorem fnHyp : FnHyp (c0.withHooks H) :=
  have hn : ∀ fn, fn ∈ (c0.withHooks H).fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain (fun k hk => by rw [params_nil] at hk; cases hk)⟩

/-- `<k> c() ~> . </k>` with the counter 0. -/
def X (H : HookParams) : Config (c0.withHooks H) :=
  ⟨.ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symC []), .ctor dotk []]],
    .ctor counterLabel [int 0]], by whd⟩

/-! ### No value of Z satisfies the `ensures` -/

theorem int2_at (x y : Int) (f : Int → Int → Option GroundTerm) : int2 [int x, int y] f = f x y := by
  simp [int2, asInt, int]

theorem hook_mul (vs : List GroundTerm) : hook intMul vs = some (int2 vs fun x y => some (int (x * y))) := rfl

/-- **At no Int value of Z is `Z *Int 2 ==Int 1` true**, under every interpretation: the product is
the registry's value `i * 2`, which is not 1. -/
theorem ens_not_true {σ : Subst} (hσ : (c0.withHooks H).WellSorted r0.vars σ) :
    ¬ EvalTerm (c0.withHooks H) σ ensT (some (bool true)) := by
  intro he
  obtain ⟨v, hv, hsv⟩ := hσ 1 Srt.int (by rw [r0_vars]; rfl)
  obtain ⟨i, rfl⟩ := shape_int (shapesOK (H := H)) hsv
  obtain ⟨rs, hts, hh, -⟩ := (EvalTerm.hook_iff (by whd) rfl).mp he
  obtain ⟨r1, rs1, rfl, h1, hts1⟩ := hts.cons_inv
  obtain ⟨r2, rs2, rfl, h2, hts2⟩ := hts1.cons_inv
  cases hts2.nil_inv
  cases h2.dv_inv
  obtain ⟨ps, hps, hm, -⟩ := (EvalTerm.hook_iff (by whd) rfl).mp h1
  obtain ⟨p1, ps1, rfl, hp1, hps1⟩ := hps.cons_inv
  obtain ⟨p2, ps2, rfl, hp2, hps2⟩ := hps1.cons_inv
  cases hps2.nil_inv
  cases hp2.dv_inv
  rw [hp1.var_inv, hv] at hm
  have hmul : (c0.withHooks H).hookRes intMul [int i, int 2] = some (some (int (i * 2))) :=
    Semantics.hookRes_of_value (by rw [hook_mul, int2_at])
  have hr1 := (hm _ rfl).symm.trans hmul
  cases hr1
  have heq : (c0.withHooks H).hookRes intEq [int (i * 2), int 1] = some (some (KCore.bool (decide (i * 2 = 1)))) :=
    Semantics.hookRes_of_value (by rw [Det.hook_intEq, int2_at])
  have hb := (hh _ rfl).symm.trans heq
  simp only [Option.some.injEq, KCore.bool, GroundTerm.dv.injEq, Lit.bool.injEq, true_and] at hb
  have : i * 2 = 1 := of_decide_eq_true hb.symm
  omega

/-- **`<k> c() </k>` has no successor**, under every interpretation: the one rule gives a step only
at a value of Z with a true `ensures`. -/
theorem no_step (H : HookParams) : ∀ y, ¬ Step (c0.withHooks H) (X H) y := by
  intro y h
  obtain ⟨r, σ, hb⟩ := step_iff_by.mp h
  cases rules_one hb.mem
  exact ens_not_true hb.hσ (hb.hens _ r0_shape.2.1)

/-- **By `ExactC`, no value is a successor of `<k> c() </k>` in any model of `Γc` with the step's
closure**, under every interpretation. -/
theorem no_succ (H : HookParams) (y : Config (c0.withHooks H)) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (c0.withHooks H) ∪ Γstep (c0.withHooks H))) ∧
      ¬ (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) y.val))) := by
  rw [← exact_hyp (c0.withHooks H) coreOK fnHyp (X H) y]
  exact no_step H y

/-! ### The value model

The rule is read with the premise `⌈∃Z. (rhs ∧ ens)⌉`. In the value model the right side under its
binder is empty at every valuation that reads the counter variable as a value (`right_empty`), so
the premise is false there and the rule's axiom holds; the value model is a model of the theory
(`value_model`). -/

/-- **The value model is a model of the theory** (`Γc` with the step's closure), under every
interpretation. -/
theorem value_model (H : HookParams) :
    Faithful.Model.stdI (c0.withHooks H) ⊧ᴵP (Γc (c0.withHooks H) ∪ Γstep (c0.withHooks H)) :=
  stdI_model_exCEx (c0.withHooks H) (hypModel_of_fnHyp coreOK fnHyp) (clausePreDecided_of_fnHyp coreOK fnHyp)
    (clausePostDecided_of_fnHypCEx (Semantics.coreOK_iff_ex.mp coreOK) fnHyp)
    (openLaws_of_plain (fun k hk => by rw [params_nil] at hk; cases hk))
    ruleFacts

open Faithful.Model in
/-- **`∃Z. (rhs ∧ ens)` is empty in the value model**, under every interpretation, at every
valuation that reads the counter variable as a value of its sort: no element is the right side at
a value of Z with a true `ensures`. -/
theorem right_empty (H : HookParams) {tbl : KoreAML.VarTable}
    (hkeys : ∀ i < r0.vars.length, canonKey (c0.withHooks H) r0.vars i ∈ tbl)
    {e : Valuation Elem} {σ : Subst}
    (hσ : ∀ i < r0.vars.length, i ∉ r0.exs →
      ∃ v, σ.lookup i = some v ∧ (c0.withHooks H).sortOf v = some (r0.vars.getD i 0))
    (hvar : ∀ i < r0.vars.length, i ∉ r0.exs → ∀ m,
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars (c0.withHooks H) r0.vars) i)).interpret
          (stdI (c0.withHooks H)) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v) (m : Elem) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (ruleRight (c0.withHooks H) r0)).interpret (stdI (c0.withHooks H)) e m := by
  intro hm
  obtain ⟨σ', y, -, hσ', -, hens, -⟩ :=
    (ruleRight_read_T (hypModel_of_fnHyp coreOK fnHyp) (ruleFacts r0 r0_mem).1 (ruleFacts r0 r0_mem).2
      (T := StepM (c0.withHooks H)) hkeys hσ hvar m).mp hm
  exact ens_not_true hσ' (hens _ r0_shape.2.1)

/-- info: 'ExFixturesH.EnsUnsat.no_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_step
/-- info: 'ExFixturesH.EnsUnsat.no_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_succ
/-- info: 'ExFixturesH.EnsUnsat.value_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms value_model
/-- info: 'ExFixturesH.EnsUnsat.right_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms right_empty

end EnsUnsat

end ExFixturesH

#check @ExFixturesH.EnsUnsat.no_step
#check @ExFixturesH.EnsUnsat.no_succ
#check @ExFixturesH.EnsUnsat.value_model
#check @ExFixturesH.EnsUnsat.right_empty
