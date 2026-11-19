/-
  Rules with variables their left side does not bind, at the lemmas that read them. Run from the
  package root: `lake env lean test/OpenRules.lean`. Kernel-checked (`decide +kernel`).

  The semantics is the reader's for `f2-examples/symrule.kompile.kore`; the rules are those of
  `test/RulesPlainArmC.lean`, over its configuration `cfg t`
  (`<generatedTop>(<k>(kseq(inj{Exp,KItem}(b), V0)), t)`), V0 of sort K and V1 of the counter
  cell's sort:
  - `ok1`: `a() => b(X)`, X:Int (vars V0, V1, X);
  - `ok2`: `a() => a() requires H ==Int 0`, H:Int (vars V0, V1, H);
  - `ok4`: `a() => b(X) requires H ==Int 0`, X, H:Int (vars V0, V1, X, H).
  `b(X)` stands as `<generatedCounter>(X)`, the counter cell's constructor.

  - `ctorOccs_witnessed` (arm A, an open variable held by the right side under constructors): at
    `ok1` and `ok4` the right side has the configuration sort in the right side's context and holds
    the open variable X (index 2) under constructors only.
  - `Rule.decided_of_fnHyp` (a rule whose left side does not bind every variable): `ok1` (arm A),
    `ok2` (arm C: H held by a closed condition only) and `ok4` (arms A and C) are well sorted, have
    `rulePlainOpen` and an open variable, and the semantics has `coreOK`; so for every `FnHyp` the
    lemma gives each its two conjuncts of `StepDecided`.
  - `rule_witnessed`, `rule_subst_AB` (a successor's valuation at values, arms A and B): `ok1`
    (arm A) and `okB` (`a() => a() ensures B`, B:Bool held by the `ensures` only: arm B, Bool
    confined) are well sorted, have `rulePlainOpen`, and each open variable passes arm A or B.
  - `rule_step_valuesSSx` (every arm) and `rule_step_CSSx` (arm C): `ok2` (H by arm C only) and `ok4`
    (X by arm A, H by arm C only) are well sorted, have `rulePlainOpen`, an open variable failing
    arms A and B, `needsWitness`, and conditions whose variables the left side, the right side and
    the `ensures` do not hold; the lemma instantiated at `ok1`, `okB`, `ok2` and `ok4`.
  - `notApplies_of_not_appliesSSx` (a competitor): in `c2`, the text's semantics with `plain`
    (`a() => a()` at priority 200) added, which has `coreOK`, the competitors `ok1` (no open
    condition variable), `okBc` (`a() => a() requires B`, B:Bool: open condition variables of
    confined sorts) and `ok2` (closed conditions, `needsWitness`), each with a larger rule
    (`competitors`); the lemma instantiated at `ok2`.
  - `applies_iff_open`, `rule_premise_open` (the value model, no arm read): at `ok1`, `okB`, `ok2`
    and `ok4` in the value model of the text's semantics; `rule_premise_open` also at `ok1hi`
    (`ok1` at priority 300 in `c2`, whose two rules are its competitors). `sat_rule_open` asks the
    rule to be one of the definition's: it is instantiated at the open rules of
    `test/OpenRulesCore.lean`'s `cO`.
  - `freeOf_prioOpen` (the axiom's free variables are the rule's): at `ok1`, `okB`, `ok2`, `ok4`.
  - `famOpen_congrOpen` (`famOpen` reads the match at the left side's variables only): at `ok1`,
    whose open variable X the left side does not hold.
  - `not_ruleApplies_ofChoice`, `notApplies_ofChoice` (a competitor at values, either way): at
    `ok4`; `step_iff_stdIChoice` (the value model): at the text's semantics and `c2`, whose rules
    are closed.
  - `Parse.owedCondDecided` (the rules whose `CondDecided` the account lists as owed): none at the
    text's semantics; `ok2` once added to it.
  - `Semantics.rulePlainEx` (`rulePlainOpen` less `r.exs.isEmpty`): true at `exA` (`ok1` with X
    existential, held under a constructor), false at `exBad` (`a() => a() ensures ?Z ==Int 0`, Z
    under a function only); `rulePlainOpen_iff_ex` at `ok1` (both true) and `exA` (`rulePlainOpen`
    false); `rulePlainEx_top` at `exA`.
  - `heldOccs` (HO-1's occurrence test: constructors, injections and the collection symbols
    `Semantics.holds` names): a variable under a map entry is held and not in `ctorOccs`; one under
    the hooked function `_==Int_` is in neither; `ctorOccs_subset_heldOccs` at `ok4`'s right side.
  - `rulePattern_noExs` (the emitted rule without existential variables): at `ok1`; at `exA` the
    emitted right side is an `\exists` over X's name.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OpenRules

definition_of defn from "f2-examples/symrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def i (n : Int) : Term := .dv Srt.int (.int n)
/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(b), V0)), cnt)`. -/
def cfg (cnt : Term) : Term :=
  .app 71 [.app 383 [.app 0 [.inj 32 1 (.app 386 []), .var 0]], cnt]

/-- The symbols and sorts `cfg` and the rules name. -/
example : c.symName 71 = "Lbl'-LT-'generatedTop'-GT-'" ∧ c.symName 383 = "Lbl'-LT-'k'-GT-'" ∧
    c.symName 0 = "kseq" ∧ c.symName 386 = "Lblb" ∧ c.symName 73 = "Lbl'-LT-'generatedCounter'-GT-'" ∧
    c.sortName 32 = "Exp" ∧ c.sortName 1 = "KItem" := by
  decide +kernel

/-- The sorts of the first two variables of the text's rule: K and the counter cell's. -/
noncomputable def sK : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 1 0
noncomputable def sC : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 2 0

noncomputable def mk (vars : List Srt) (rhs : Term) (req ens : Option Term) (prio : Nat) : Rule :=
  { vars := vars, lhs := cfg (.var 1), req := req, rhs := rhs, ens := ens, prio := prio }

/-- `a() => b(X)` -/
noncomputable def ok1 : Rule := mk [sK, sC, Srt.int] (cfg (.app 73 [.var 2])) none none 50
/-- `a() => a() requires H ==Int 0` -/
noncomputable def ok2 : Rule := mk [sK, sC, Srt.int] (cfg (.var 1)) (some (.app intEq [.var 2, i 0])) none 50
/-- `a() => b(X) requires H ==Int 0` -/
noncomputable def ok4 : Rule := mk [sK, sC, Srt.int, Srt.int] (cfg (.app 73 [.var 2])) (some (.app intEq [.var 3, i 0])) none 50

/-! ## Arm A: `ctorOccs_witnessed` -/

/-- `ok1`'s right side is a configuration over the right side's context, and holds its open
variable X under constructors only. -/
example : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) ok1.vars ok1.rhs = some topCellSort ∧
    ok1.opens = [2] ∧ (ctorOccs c ok1.rhs).contains 2 = true := by
  decide +kernel

/-- `ok4`'s likewise, for X (index 2); its other open variable H (index 3) is held by the
condition only. -/
example : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) ok4.vars ok4.rhs = some topCellSort ∧
    ok4.opens = [2, 3] ∧ (ctorOccs c ok4.rhs).contains 2 = true ∧ (ctorOccs c ok4.rhs).contains 3 = false := by
  decide +kernel

/-- `a() => a() ensures B` -/
noncomputable def okB : Rule := mk [sK, sC, Srt.bool] (cfg (.var 1)) none (some (.var 2)) 50

/-! ## Arms A and C: `Rule.decided_of_fnHyp` -/

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The text's semantics reads no confined sort, so each clause's conditions are decided where
`needsWitness` holds (`openDecided_of_readsConfined`): the clause-side hypothesis of the lemmas
below. -/
theorem hcT : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c :=
  (openDecided_of_readsConfined (by decide +kernel)).2

theorem ok1_open : c.ruleSorted ok1 = true ∧ c.rulePlainOpen ok1 = true ∧ ok1.opens = [2] ∧ ok1.condVars = [] := by
  decide +kernel
theorem ok2_open : c.ruleSorted ok2 = true ∧ c.rulePlainOpen ok2 = true ∧ ok2.opens = [2] ∧ ok2.condVars = [2] ∧
    ok2.reqClosed = true := by
  decide +kernel
theorem ok4_open : c.ruleSorted ok4 = true ∧ c.rulePlainOpen ok4 = true ∧ ok4.opens = [2, 3] ∧ ok4.condVars = [3] ∧
    ok4.reqClosed = true := by
  decide +kernel

/-- The lemma at each of the three rules, for every `FnHyp`. -/
example (hf : FnHyp c) (x : GroundTerm) :
    (∀ σ, c.WellSortedAt ok1.vars ok1.leftVars σ → PatVal c σ ok1.lhs x →
      (∀ t, ok1.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c ok1.vars.length σ ok1.pre b) ∧
    (∀ σ, c.WellSortedAt ok2.vars ok2.leftVars σ → PatVal c σ ok2.lhs x →
      (∀ t, ok2.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c ok2.vars.length σ ok2.pre b) ∧
    (∀ σ, c.WellSortedAt ok4.vars ok4.leftVars σ → PatVal c σ ok4.lhs x →
      (∀ t, ok4.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c ok4.vars.length σ ok4.pre b) :=
  ⟨(Rule.decided_of_fnHyp coreOK hf ok1_open.1 ok1_open.2.1 x).1,
   (Rule.decided_of_fnHyp coreOK hf ok2_open.1 ok2_open.2.1 x).1,
   (Rule.decided_of_fnHyp coreOK hf ok4_open.1 ok4_open.2.1 x).1⟩

/-- info: 'OpenRules.ok4_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ok4_open

/-! ## Arms A and B: `rule_subst_AB` -/

example : c.ruleSorted ok1 = true ∧ c.rulePlainOpen ok1 = true ∧ ok1.opens.all (ok1.armAB c) = true := by
  decide +kernel
example : c.ruleSorted okB = true ∧ c.rulePlainOpen okB = true ∧ okB.opens = [2] ∧
    okB.opens.all (okB.armAB c) = true ∧ (ctorOccs c okB.rhs).contains 2 = false ∧ c.confined Srt.bool = true := by
  decide +kernel

/-! ## Arm C: `rule_step_CSSx`, `rule_step_valuesSSx` -/

theorem ok2_C : c.ruleSorted ok2 = true ∧ c.rulePlainOpen ok2 = true ∧ ok2.opens.all (ok2.armAB c) = false ∧
    ok2.needsWitness c = true ∧ ok2.condVars.all (fun j => !(varOccs ok2.lhs).contains j &&
      !(varOccs ok2.rhs).contains j && ok2.ens.isNone) = true := by
  decide +kernel
theorem ok4_C : c.ruleSorted ok4 = true ∧ c.rulePlainOpen ok4 = true ∧ ok4.opens.all (ok4.armAB c) = false ∧
    ok4.armAB c 2 = true ∧ ok4.armAB c 3 = false ∧ ok4.needsWitness c = true ∧
    ok4.condVars.all (fun j => !(varOccs ok4.lhs).contains j && !(varOccs ok4.rhs).contains j && ok4.ens.isNone) = true := by
  decide +kernel
theorem okB_open : c.ruleSorted okB = true ∧ c.rulePlainOpen okB = true := by
  decide +kernel

/-- No open variable of `ok1`, `ok2`, `ok4` is of a confined sort; `okB`'s is. -/
theorem conf_open : ok1.opens.any (fun i => (ok1.vars[i]?.map c.confined).getD false) = false ∧
    ok2.opens.any (fun i => (ok2.vars[i]?.map c.confined).getD false) = false ∧
    ok4.opens.any (fun i => (ok4.vars[i]?.map c.confined).getD false) = false ∧
    okB.opens.any (fun i => (okB.vars[i]?.map c.confined).getD false) = true := by
  decide +kernel

/-- The lemma at each of the four rules: its hypotheses on the rule are met; that the definition
reads a confined sort is asked only at `okB`, whose open variable is of a confined sort. -/
example (hft : FnTerminates c) {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γc c)
    (hrc : c.readsConfined = true) : True := by
  have := @Faithful.rule_step_valuesSSx c M _ I (Semantics.coreOK_iff_ex.mp coreOK) hft hI hcT ok1 ok1_open.1 ok1_open.2.1
    (fun h' => by rw [conf_open.1] at h'; cases h')
  have := @Faithful.rule_step_valuesSSx c M _ I (Semantics.coreOK_iff_ex.mp coreOK) hft hI hcT okB okB_open.1 okB_open.2 (fun _ => hrc)
  have := @Faithful.rule_step_valuesSSx c M _ I (Semantics.coreOK_iff_ex.mp coreOK) hft hI hcT ok2 ok2_C.1 ok2_C.2.1
    (fun h' => by rw [conf_open.2.1] at h'; cases h')
  have := @Faithful.rule_step_valuesSSx c M _ I (Semantics.coreOK_iff_ex.mp coreOK) hft hI hcT ok4 ok4_C.1 ok4_C.2.1
    (fun h' => by rw [conf_open.2.2.1] at h'; cases h')
  trivial

/-- info: 'OpenRules.ok4_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ok4_C

/-! ## Competitors: `notApplies_of_not_appliesSSx` -/

/-- `a() => a()` at priority 200: a larger rule. -/
noncomputable def plain : Rule := mk [sK, sC] (cfg (.var 1)) none none 200
/-- `a() => a() requires B`, B:Bool held by the condition only. -/
noncomputable def okBc : Rule := mk [sK, sC, Srt.bool] (cfg (.var 1)) (some (.var 2)) none 50
/-- The text's semantics with the larger rule. -/
noncomputable abbrev c2 : Semantics := { c with rules := c.rules ++ [plain] }

theorem coreOK2 : c2.coreOK = true := by decide_cheap

/-- `hcT` at `c2`. -/
theorem hcT2 : ∀ fn ∈ c2.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c2 = true → cl.CondDecided c2 :=
  (openDecided_of_readsConfined (by decide +kernel)).2

/-- One competitor per disjunct of the competition conjunct, each beside the larger rule: `ok1` (no
open condition variable), `okBc` (its open condition variable of a confined sort), `ok2` (closed
conditions, `needsWitness`). -/
theorem competitors :
    (c2.ruleSorted ok1 = true ∧ c2.rulePlainOpen ok1 = true ∧ c2.rules.any (fun r => ok1.prio < r.prio) = true ∧
      ok1.reqOpen = false) ∧
    (c2.ruleSorted okBc = true ∧ c2.rulePlainOpen okBc = true ∧ c2.rules.any (fun r => okBc.prio < r.prio) = true ∧
      okBc.reqOpen = true ∧ okBc.openCondVars.all (fun i => (okBc.vars[i]?.map c2.confined).getD false) = true ∧
      okBc.needsWitness c2 = false) ∧
    (c2.ruleSorted ok2 = true ∧ c2.rulePlainOpen ok2 = true ∧ c2.rules.any (fun r => ok2.prio < r.prio) = true ∧
      ok2.reqOpen = true ∧ ok2.needsWitness c2 = true) := by
  decide +kernel

/-- No open variable of `ok1`, `ok2` is of a confined sort; `okBc`'s is. -/
theorem conf_open2 : ok1.opens.any (fun i => (ok1.vars[i]?.map c2.confined).getD false) = false ∧
    ok2.opens.any (fun i => (ok2.vars[i]?.map c2.confined).getD false) = false ∧
    okBc.opens.any (fun i => (okBc.vars[i]?.map c2.confined).getD false) = true := by
  decide +kernel

/-- The lemma at the competitor `ok2`. -/
example {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γc c2) : True := by
  have := @Faithful.notApplies_of_not_appliesSSx c2 M _ I (Semantics.coreOK_iff_ex.mp coreOK2) hI hcT2 ok2
    competitors.2.2.1 competitors.2.2.2.1
  trivial

/-- Neither semantics reads a confined sort: its rules have no open variable. -/
example : c.readsConfined = false ∧ c2.readsConfined = false := by decide +kernel

/-! ## The value model: `applies_iff_open`, `rule_premise_open` -/

/-- The lemmas at each of the four rules, in the value model of the text's semantics, for every
`FnDet` and `FnSolves`: a configuration is in a rule's `applies` pattern exactly where the rule
applies, and the left part of the rule's axiom holds exactly at `StepM`'s premises for it. -/
example (hd : FnDet c) (hs : FnSolves c) : True := by
  have h := hypModel_of_fn coreOK hd hs
  have := @Faithful.Model.applies_iff_open c h ok1 ok1_open.1 ok1_open.2.1
  have := @Faithful.Model.applies_iff_open c h okB okB_open.1 okB_open.2
  have := @Faithful.Model.applies_iff_open c h ok2 ok2_open.1 ok2_open.2.1
  have := @Faithful.Model.applies_iff_open c h ok4 ok4_open.1 ok4_open.2.1
  have := Faithful.Model.rule_premise_open h ok1_open.1 ok1_open.2.1 (h.ruleFactsEx_of_all (by decide +kernel))
  have := Faithful.Model.rule_premise_open h okB_open.1 okB_open.2 (h.ruleFactsEx_of_all (by decide +kernel))
  have := Faithful.Model.rule_premise_open h ok2_open.1 ok2_open.2.1 (h.ruleFactsEx_of_all (by decide +kernel))
  have := Faithful.Model.rule_premise_open h ok4_open.1 ok4_open.2.1 (h.ruleFactsEx_of_all (by decide +kernel))
  trivial

/-- `freeOf_prioOpen` at each of the four rules: the free variables of the rule's axiom are its own. -/
example (hd : FnDet c) (hs : FnSolves c) : True := by
  have h := hypModel_of_fn coreOK hd hs
  have := @Faithful.Model.freeOf_prioOpen c h ok1 ok1_open.1 ok1_open.2.1 (h.ruleFactsEx_of_all (by decide +kernel))
  have := @Faithful.Model.freeOf_prioOpen c h okB okB_open.1 okB_open.2 (h.ruleFactsEx_of_all (by decide +kernel))
  have := @Faithful.Model.freeOf_prioOpen c h ok2 ok2_open.1 ok2_open.2.1 (h.ruleFactsEx_of_all (by decide +kernel))
  have := @Faithful.Model.freeOf_prioOpen c h ok4 ok4_open.1 ok4_open.2.1 (h.ruleFactsEx_of_all (by decide +kernel))
  trivial

/-- `ok1` at priority 300 in `c2`: both rules of `c2` are its competitors, so its axiom's left part
holds the negation of their `applies`, which `rule_premise_open` reads. -/
noncomputable def ok1hi : Rule := { ok1 with prio := 300 }

theorem ok1hi_open : c2.ruleSorted ok1hi = true ∧ c2.rulePlainOpen ok1hi = true ∧ ok1hi.opens = [2] ∧
    (c2.rules.filter (·.prio < ok1hi.prio)).length = 2 := by
  decide +kernel

example (hd : FnDet c2) (hs : FnSolves c2) : True := by
  have := Faithful.Model.rule_premise_open (hypModel_of_fn coreOK2 hd hs) ok1hi_open.1 ok1hi_open.2.1
    ((hypModel_of_fn coreOK2 hd hs).ruleFactsEx_of_all (by decide +kernel))
  trivial

/-! ## The rules' facts at the text's semantics and at `c2` -/

/-- The rules of the text's semantics and of `c2` have `ruleSorted` and `rulePlainOpen`. -/
theorem rules_open : c.rules.all (fun r => c.ruleSorted r && c.rulePlainOpen r) = true ∧
    c2.rules.all (fun r => c2.ruleSorted r && c2.rulePlainOpen r) = true := by
  decide +kernel

theorem hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true := fun r hr => by
  simpa using List.all_eq_true.mp rules_open.1 r hr
theorem hrules2 : ∀ r ∈ c2.rules, c2.ruleSorted r = true ∧ c2.rulePlainOpen r = true := fun r hr => by
  simpa using List.all_eq_true.mp rules_open.2 r hr

/-- Each of the four rules has an open variable. -/
example : ok1.opens ≠ [] ∧ okB.opens ≠ [] ∧ ok2.opens ≠ [] ∧ ok4.opens ≠ [] := by decide +kernel

/-! ## The outcomes of a match -/

/-- `okB`'s open variable is of a confined sort (Bool). -/
theorem okB_conf : okB.opens.all (fun i => (okB.vars[i]?.map c.confined).getD false) = true := by
  decide +kernel

/-! ## Soundness at a step: `applies_matchOpen` -/

/-- At each of the four rules, in a model of `Γc` of the text's semantics: a rule whose `applies`
holds matches (`applies_matchOpen`). -/
example {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γc c) : True := by
  have hIΓ : I ⊧ᴵP Faithful.Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have := @Faithful.applies_matchOpen c M _ I coreOK hIΓ ok1 ok1_open.1 ok1_open.2.1
  have := @Faithful.applies_matchOpen c M _ I coreOK hIΓ okB okB_open.1 okB_open.2
  have := @Faithful.applies_matchOpen c M _ I coreOK hIΓ ok2 ok2_C.1 ok2_C.2.1
  have := @Faithful.applies_matchOpen c M _ I coreOK hIΓ ok4 ok4_C.1 ok4_C.2.1
  trivial

/-! ## The outcomes of a match read its left side's variables: `famOpen_congrOpen` -/

/-- `ok1`'s left side does not hold its open variable X (index 2): two matches that differ at X
give one `famOpen`. -/
example : (varOccs ok1.lhs).contains 2 = false := by decide +kernel

example (σ σ' : Subst) (h : ∀ i ∈ varOccs ok1.lhs, σ'.lookup i = σ.lookup i) :
    Faithful.famOpen c ok1 σ' = Faithful.famOpen c ok1 σ :=
  Faithful.famOpen_congrOpen c ok1 h

/-! ## The choice among instances: `not_ruleApplies_ofChoice`, `notApplies_ofChoice`,
`step_iff_stdIChoice` -/

/-- `NotApplies` and `¬ RuleApplies` at `ok4` (arms A and C: open variables X and H, H in its
`requires`), for every `FnHyp`: one from the other, the conditions' results by
`Rule.decided_of_fnHyp`. -/
example (hf : FnHyp c) (x : GroundTerm) : NotApplies c ok4 x ↔ ¬ RuleApplies c ok4 x :=
  ⟨not_ruleApplies_ofChoice (fnModel_of_fnHyp coreOK hf).1 (Semantics.rulePlainOpen_top ok4_open.2.1).2.1,
   notApplies_ofChoice (Rule.decided_of_fnHyp coreOK hf ok4_open.1 ok4_open.2.1 x).1⟩

/-- `step_iff_stdIChoice` at the text's semantics and at `c2`, the rules'
facts by `rules_open`; their rules are closed, see `test/OpenRulesCore.lean` for a definition with open rules. -/
example (hf : FnHyp c) (hf2 : FnHyp c2) (x y : Config c) (x2 y2 : Config c2) : True := by
  have := step_iff_stdIChoice c coreOK hf hrules x y
  have := step_iff_stdIChoice c2 coreOK2 hf2 hrules2 x2 y2
  trivial

/-! ## A rule's conjunct with existential variables: `Semantics.rulePlainEx` -/

/-- `a() => b(?X:Int)`: `ok1` with its open variable X existential. -/
noncomputable def exA : Rule := { ok1 with exs := [2] }
/-- `a() => a() ensures ?Z ==Int 0` -/
noncomputable def exBad : Rule :=
  { mk [sK, sC, Srt.int] (cfg (.var 1)) none (some (.app intEq [.var 2, i 0])) 50 with exs := [2] }

/-- An existential variable held under a constructor passes arm A; one under a function only, of
the unconfined sort Int and in no condition, passes no arm. -/
example : c.rulePlainEx exA = true ∧ c.rulePlainOpen exA = false ∧ exA.exs ≠ [] ∧
    c.rulePlainEx exBad = false := by
  decide +kernel

/-- `rulePlainOpen_iff_ex` both ways: at `ok1` from `rulePlainEx` and `exs = []`; at `exA`
`rulePlainOpen` fails by its existential variable alone. `rulePlainEx_top` at `exA`. -/
example : c.rulePlainOpen ok1 = true ∧ c.rulePlainOpen exA ≠ true ∧ exA.pre = .top ∧ exA.post = .top :=
  ⟨Semantics.rulePlainOpen_iff_ex.mpr ⟨by decide +kernel, rfl⟩,
   fun h => absurd (Semantics.rulePlainOpen_iff_ex.mp h).2 (by decide +kernel),
   Semantics.rulePlainEx_top (by decide +kernel : c.rulePlainEx exA = true)⟩

/-! ## The held occurrences: `heldOccs`, `Semantics.holds`, `ctorOccs_subset_heldOccs` -/

/-- Under a map entry `K |-> V`, both variables are held, and neither is under constructors only;
under `_==Int_`, a hooked function, neither is held. -/
example : c.holds mapElem = true ∧ c.isCtor mapElem = false ∧
    heldOccs c (.app mapElem [.var 0, .var 1]) = [0, 1] ∧ ctorOccs c (.app mapElem [.var 0, .var 1]) = [] ∧
    c.holds intEq = false ∧ heldOccs c (.app intEq [.var 0, i 0]) = [] ∧
    ctorOccs c (.app intEq [.var 0, i 0]) = [] := by
  decide +kernel

/-- `ok4`'s right side holds X (index 2) under constructors, so `heldOccs` holds it. -/
example : 2 ∈ heldOccs c ok4.rhs :=
  ctorOccs_subset_heldOccs c ok4.rhs 2 (List.contains_iff_mem.mp (by decide +kernel))

/-! ## The account's owed facts: `Parse.owedCondDecided` -/

/-- The text's semantics owes no `CondDecided`; with `ok2` added (its `requires` closed over H, of
the unconfined sort Int), `ok2`'s is owed, over H (index 2). -/
example : Parse.owedCondDecided c = [] ∧
    Parse.owedCondDecided { c with rules := c.rules ++ [ok2] } = [(c.rules.length, [2])] := by
  decide +kernel

/-! ## The emitted rule: `rulePattern_noExs` -/

/-- `ok1` has no existential variable and its predicates are `\top`: its emitted pattern is
`\rewrites(\and(lhs, req), \and(rhs, ens))`, under any names. At `exA` (X, index 2, existential)
the right side is emitted under `\exists` binding X's name. -/
example (vs : List KoreAML.Var) :
    rulePattern c vs ok1 =
      .rewrites (srtOf c topCellSort)
        (.and (srtOf c topCellSort) [Term.kore c vs ok1.lhs, reqPat (srtOf c topCellSort) (ok1.req.map (Term.kore c vs))])
        (.and (srtOf c topCellSort) [Term.kore c vs ok1.rhs, reqPat (srtOf c topCellSort) (ok1.ens.map (Term.kore c vs))]) := by
  rw [rulePattern_noExs c vs ok1 rfl, rulePredPat_top (p := ok1.pre) rfl, rulePredPat_top (p := ok1.post) rfl]

example (v0 v1 v2 : KoreAML.Var) :
    (match rulePattern c [v0, v1, v2] exA with
     | .rewrites _ _ (.exist _ v _) => v = v2.kore
     | _ => False) := rfl

end OpenRules
