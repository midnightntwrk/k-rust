/-
  The tie (C14) of the fixture c3-rule-req-prio-comp (the pair rule `requires` x rule `priority`, with a competitor):
  `rule <k> a(X) => b(X) </k> requires X >Int 0 [priority(40)]` beside `rule <k> a(_) => c() </k>` of the default priority.
  The text is `f2-examples/c3-rule-req-prio-comp.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-rule-req-prio-comp/kompile.txt` records (sha256 86851869…), with its paths restored.
  Run from the package root: `lake env lean -j1 test/C3RuleReqPrioComp.lean`. Every statement is on the literal
  `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree`: the attributes of the text agree with
  `defn`, each rule's priority and `owise` with the `Rule`'s `prio` (`rule_prios`); `account`: the
  function equations, the constructor sentences and the rule sentences are sentences of the user
  module, apart, with the count of the rest.

  Layer 2.
  - Function equations (`fnText`, the sort predicates'): each of Γ's items is the translation of its
    sentence (`shape`), so Γ entails each (`fns_entailed`) and each item is a consequence of its
    sentence (`fns_from_text`).
  - Constructor sentences (`consText`): entailed by Γ (`cons_entailed`).
  - The rule sentences (`ruleText`, in the order of `c.rules`): Γ's axiom of each rule
    (`prioRuleK`) is its sentence with conjuncts more on the left side, the definedness of the right
    side with its `ensures` and, beside a rule of a smaller priority, the negation of that rule's
    left side and `requires` (`rules_tie`, kernel, `TieRulePair.ruleTextB`). So each of Γ's rule
    items is a consequence of its sentence (`rules_from_text`, W1), and in a model of Γ each sentence
    holds at each valuation where those conjuncts hold of every element the sentence's left side and
    `requires` hold (`rules_w2`, W2 with the guard `TieRulePair.RuleGuard`).
  - `consistent`: Γ with the step's closure has a model, for every H.

  The expectations (C7 form (a)); `Pre H` (the function sentences as written, Γ's rule items, the
  families) has a model with the step's closure (`pre_model`):
  - `a5_step`: `a(5)` steps to `b(5)`, from the sentence of the rule of priority 40. From sentences: `PreS` (the function sentences and the rule sentences as written, and
    the families), by W1 (`rules_from_text`) and the cut (`TieRulePair.cutS`).
  - `a5_succs`: `b(5)` is `a(5)`'s only successor: the rule of priority 40 applies at 5, so the other one does not (the text's sentence 159 alone states the step to `c()` there too). Through the reading, from `Pre H` with the step's closure: the priority premise (prioRuleK: Γ's item of a rule holds only where no rule of a smaller priority applies); the step's closure (Γstep: every successor is one Step gives).
  - `an1_step`: `a(-1)` steps to `c()`, from the sentence of the rule of default priority. From sentences: `PreS` (the function sentences and the rule sentences as written, and
    the families), by W1 (`rules_from_text`) and the cut (`TieRulePair.cutS`).
  - `an1_succs`: `c()` is `a(-1)`'s only successor: the rule of priority 40 does not apply at -1 (its `requires` is not true). Through the reading, from `Pre H` with the step's closure: the priority premise (prioRuleK: Γ's item of a rule holds only where no rule of a smaller priority applies); the step's closure (Γstep: every successor is one Step gives).

  W2 at an instance: `stepBy_an1` (the step from `a(-1)` to `c()` by the rule of default priority at
  its listed match σ1, `Cert.stepBy_of_checkStep`); `guard_an1` (the guard `RuleGuard` of that rule's
  axiom at the valuation of σ1: the rule of priority 40 does not apply at `a(-1)` and the right side
  is defined, `TieRulePair.ruleGuard_of_stepBy`); `w2_an1` (the sentence 159 as written holds there
  in every model of Γ).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3RuleReqPrioComp

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-rule-req-prio-comp.kompile.kore"
definition_of defn from "f2-examples/c3-rule-req-prio-comp.kompile.kore"
user_axioms U from "f2-examples/c3-rule-req-prio-comp.kompile.kore" module "C3-RULE-REQ-PRIO-COMP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The attributes of the text agree with `defn` (`attrsAgree`): constructors, functions, hooks,
collection symbols, the priorities and `owise` of rules and equations. -/
theorem defs_attrsAgree : attrsAgree kore defn = true := by decide +kernel

/-! ## The function equations (the sort predicates') -/

noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

theorem fnText_index : fnText.map (·.index) = [232, 240, 239, 238, 237, 244, 243, 246, 245, 242, 241, 219, 218, 231, 230, 227, 226, 229, 228, 234, 233, 236, 235, 223, 222, 225, 224, 221, 220] := by decide +kernel

noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for the function equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat :=
  fun _ had => TiePair.entailed (shapeH H) _ (List.mem_map_of_mem had)

/-- **The converse for `fnItems`**: each item is a consequence of a text sentence. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  unfold textPats at ht
  rw [List.getElem?_map] at ht
  cases hf : fnText[j]? with
  | none => rw [hf] at ht; cases ht
  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-! ## The constructor sentences -/

noncomputable def consText : List AxiomDecl := U.all.filter fun ad => tieConsB c ad.ax

theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **E for the constructor sentences**: Γ entails each, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.mem_filter.mp had).2) ad.index ad.module hI

/-! ## The rule sentences -/

/-- The rule sentences, in the order of `c.rules`. -/
noncomputable def ruleText : List AxiomDecl := [U.ax158, U.ax159]

noncomputable def rulePats : List P := ruleText.map (trS · |>.pat)

/-- The rules' priorities (the text's `priority` and `owise` attributes, `defs_attrsAgree`) and
their sentences' indices. -/
theorem rule_prios : c.rules.map (·.prio) = [40, 50] ∧ ruleText.map (·.index) = [158, 159] := by
  decide +kernel

/-- **Γ's axiom of each rule is its sentence with conjuncts more on the left side** (kernel). -/
theorem rules_tie : TieRulePair.rulesTieB c rulePats = true := by decide +kernel

theorem rules_tieH (H : HookParams) : TieRulePair.rulesTieB (cH H) rulePats = true :=
  (TieRulePair.rulesTieB_withHooks c H rulePats).trans rules_tie

/-- **W1 for the rules**: each of Γ's rule items is a consequence of its sentence, for every H. -/
theorem rules_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (ruleItems (cH H))[j]? = some it →
      ∃ ad, ruleText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  obtain ⟨t, ht, hent⟩ := TieRulePair.rules_from_text (rules_tieH H) j it hj
  unfold rulePats at ht
  rw [List.getElem?_map] at ht
  cases hf : ruleText[j]? with
  | none => rw [hf] at ht; cases ht
  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-- **W2 for the rules, with the guard**: in a model of Γ, for every H, each rule's sentence holds
at each valuation at which the conjuncts Γ's axiom of the rule adds (the definedness of the right
side with its `ensures`, the negation of the rules of a smaller priority) hold of every element the
sentence's left side and `requires` hold. -/
theorem rules_w2 (H : HookParams) {j : Nat} {r : Rule} {ad : AxiomDecl} (hr : (cH H).rules[j]? = some r)
    (had : ruleText[j]? = some ad) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (hx : TieRulePair.RuleGuard (prioRuleK (cH H) r) I e) (m : M) :
    (trS ad).pat.interpret I e m :=
  TieRulePair.rules_w2 (rules_tieH H) hr (by unfold rulePats; rw [List.getElem?_map, had]; rfl) hI e hx m

/-! ## The account -/

noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ consText.map (·.index) ++ ruleText.map (·.index)

/-- **The account**: the function equations, the constructor sentences and the rule sentences are
sentences of the user module, each once and none in two classes; the sizes of the classes and of the
rest (library sentences, hooked symbols' `functional` sentences, collection laws, no junk, the
projections and initializers: not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length, consText.length, ruleText.length, U.all.length - tiedIdx.length) = (29, 33, 2, 202) := by
  decide +kernel

/-! ## The facts the deciders leave -/

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem readsConfined_c : c.readsConfined = false := by decide +kernel
theorem readsConfinedH (H : HookParams) : (cH H).readsConfined = false :=
  (Semantics.readsConfined_withHooks c H).trans readsConfined_c

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H** (C14 closure (a)). -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-- The clauses of one priority are coherent, for every H (no agreement is owed). -/
theorem coherentH (H : HookParams) : CoherentAll (cH H) :=
  Det.coherentAll_of_nil (hokH H) ((Semantics.srReady_withHooks c H).trans hsr)
    ((Semantics.matchReady_withHooks c H).trans hmr) ((TiePair.clausesFixed_withHooks c H).trans (by decide +kernel))
    ((Semantics.agreeObligations_withHooks c H).trans (by decide +kernel))

/-! ## The expectations (C7 form (a)) -/

/-- The premises of the derivations through the reading: the function sentences as written, Γ's
rule items, and the families (the parts of Γ no sentence states). -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

/-- The premises of the derivations from sentences: the function sentences and the rule sentences
as written, and the families. -/
noncomputable abbrev PreS (H : HookParams) : Premises KoreAML.Sym := TieRulePair.PreS (cH H) textPats rulePats

def kCell : Sym := 383
def a_ : Sym := 385
def b_ : Sym := 386
def c_ : Sym := 387
def cmd : Srt := 32

theorem names : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName a_ = "Lbla" ∧
    c.symName b_ = "Lblb" ∧ c.symName c_ = "Lblc" ∧ c.sortName cmd = "Cmd" := by
  decide +kernel

/-- The configuration with `it` in the k cell and the counter at 0. -/
def cfg (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmd Srt.kitem it, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

/-- A configuration of the data under the interpretation H. -/
noncomputable abbrev XH (x : Config c) (H : HookParams) : Config (cH H) := TieRulePair.cfgH noRaw x H
noncomputable def A5 : Config c := ⟨cfg (.ctor a_ [int (5)]), by decide +kernel⟩
noncomputable def B5 : Config c := ⟨cfg (.ctor b_ [int (5)]), by decide +kernel⟩
noncomputable def An1 : Config c := ⟨cfg (.ctor a_ [int (-1)]), by decide +kernel⟩
noncomputable def Cc : Config c := ⟨cfg (.ctor c_ []), by decide +kernel⟩

/-- **`a(5)` steps to `b(5)`, from the sentence of the rule of priority 40**, for every H: derived from `PreS`, the sentences as written. -/
theorem a5_step (H : HookParams) :
    PreS H ⊧ (den (cH H) (XH A5 H).val ⇒ KoreAML.sNext (den (cH H) (XH B5 H).val)) :=
  TieRulePair.cutS (shapeH H) (rules_tieH H)
    (sound_at_step (cH H) (coreOKH H) (readsConfinedH H) _ _
      (TieRulePair.step_withHooks hok hsr hmr noRaw (n := 100) (by decide +kernel) H))

/-- **`b(5)` is `a(5)`'s only successor: the rule of priority 40 applies at 5, so the other one does not (the text's sentence 159 alone states the step to `c()` there too)**, for every H: derived from `Pre` with the step's closure. -/
theorem a5_succs (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) (XH A5 H).val ⇒
      KoreAML.allNext (KoreAML.disjList (([B5.val] : List GroundTerm).map (den (cH H))))) :=
  TiePair.cutStep (shapeH H)
    (complete_at_step (cH H) (coreOKH H) (readsConfinedH H) _
      (stepDecided_of_fnHyp (coreOKH H) (fnHypH H) _) _
      (TieRulePair.listed_sound hok hsr hmr H (coherentH H) (x := A5) (n := 100) (by decide +kernel)
        (by decide +kernel) noRaw))

/-- **`a(-1)` steps to `c()`, from the sentence of the rule of default priority**, for every H: derived from `PreS`, the sentences as written. -/
theorem an1_step (H : HookParams) :
    PreS H ⊧ (den (cH H) (XH An1 H).val ⇒ KoreAML.sNext (den (cH H) (XH Cc H).val)) :=
  TieRulePair.cutS (shapeH H) (rules_tieH H)
    (sound_at_step (cH H) (coreOKH H) (readsConfinedH H) _ _
      (TieRulePair.step_withHooks hok hsr hmr noRaw (n := 100) (by decide +kernel) H))

/-- **`c()` is `a(-1)`'s only successor: the rule of priority 40 does not apply at -1 (its `requires` is not true)**, for every H: derived from `Pre` with the step's closure. -/
theorem an1_succs (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) (XH An1 H).val ⇒
      KoreAML.allNext (KoreAML.disjList (([Cc.val] : List GroundTerm).map (den (cH H))))) :=
  TiePair.cutStep (shapeH H)
    (complete_at_step (cH H) (coreOKH H) (readsConfinedH H) _
      (stepDecided_of_fnHyp (coreOKH H) (fnHypH H) _) _
      (TieRulePair.listed_sound hok hsr hmr H (coherentH H) (x := An1) (n := 100) (by decide +kernel)
        (by decide +kernel) noRaw))

/-! ## W2 at an instance -/

/-- The rule of the default priority, `a(_) => c()`, the second of `c.rules` (sentence 159). -/
noncomputable abbrev r1 : Rule := c.rules[1]'(by decide +kernel)

/-- The match of that rule at `a(-1)` that the matcher lists. -/
noncomputable def σ1 : Subst := ((Exec.ruleMatches c 100 r1 An1.val).headD ([], none)).1

/-- It is the rule's one match there, and its `requires` (none) is `true`. -/
theorem matches_an1 : Exec.ruleMatches c 100 r1 An1.val = [(σ1, some true)] := by decide +kernel
kernel_rfl matches_an1_wh : ∀ H : HookParams,
  Exec.ruleMatches (cH H) 100 r1 An1.val = Exec.ruleMatches c 100 r1 An1.val

/-- **The step from `a(-1)` to `c()` by the rule of default priority, at σ1**, for every H. -/
theorem stepBy_an1 (H : HookParams) : StepBy (cH H) r1 σ1 (XH An1 H) (XH Cc H) := by
  obtain ⟨σ, hm, hb⟩ := Cert.stepBy_of_checkStep (hokH H) ((Semantics.srReady_withHooks c H).trans hsr)
    ((Semantics.matchReady_withHooks c H).trans hmr) (n := 100) (r := r1)
    (show r1 ∈ c.rules from List.getElem_mem _) (x := XH An1 H) (y := XH Cc H)
    ((Cert.checkStep_withHooks c H noRaw 100 r1 _ _).trans
      (show Cert.checkStep c 100 r1 An1.val Cc.val = true by decide +kernel))
  have hm' : (σ, some true) ∈ Exec.ruleMatches (cH H) 100 r1 An1.val := hm
  rw [matches_an1_wh H, matches_an1, List.mem_singleton] at hm'
  obtain ⟨rfl, -⟩ := Prod.mk.inj hm'
  exact hb

/-- **The guard of W2 at σ1**, for every H: in every model of Γ, `RuleGuard` of the rule's axiom
holds at the valuation `overV` of σ1. Its conjuncts there: the rule of priority 40 does not apply at
`a(-1)` (its `requires` `-1 >Int 0` is false), and the right side `c()` is defined
(`TieRulePair.ruleGuard_of_stepBy`). -/
theorem guard_an1 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) :
    TieRulePair.RuleGuard (prioRuleK (cH H) r1) I
      (overV (cH H) I (tableOf [] (prioRuleK (cH H) r1)) r1.vars σ1 (val0 : Valuation M)) :=
  TieRulePair.ruleGuard_of_stepBy (coreOKH H) (readsConfinedH H) (stepBy_an1 H) hI

/-- **W2 at σ1**: in every model of Γ, for every H, the text's sentence 159 as written,
`<k> a(_) => c() </k>` without the negation of the rule of priority 40, holds at the valuation of
σ1 (`rules_w2` with `guard_an1`). -/
theorem w2_an1 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (m : M) :
    (trS U.ax159).pat.interpret I
      (overV (cH H) I (tableOf [] (prioRuleK (cH H) r1)) r1.vars σ1 (val0 : Valuation M)) m :=
  rules_w2 H (j := 1) (show c.rules[1]? = some r1 from List.getElem?_eq_getElem _) rfl hI _ (guard_an1 H hI) m

end KCore.C3RuleReqPrioComp

#print axioms KCore.C3RuleReqPrioComp.wf_defn
#print axioms KCore.C3RuleReqPrioComp.defs_attrsAgree
#print axioms KCore.C3RuleReqPrioComp.shape
#print axioms KCore.C3RuleReqPrioComp.fns_entailed
#print axioms KCore.C3RuleReqPrioComp.fns_from_text
#print axioms KCore.C3RuleReqPrioComp.cons_entailed
#print axioms KCore.C3RuleReqPrioComp.rule_prios
#print axioms KCore.C3RuleReqPrioComp.rules_tie
#print axioms KCore.C3RuleReqPrioComp.rules_from_text
#print axioms KCore.C3RuleReqPrioComp.rules_w2
#print axioms KCore.C3RuleReqPrioComp.account
#print axioms KCore.C3RuleReqPrioComp.consistent
#print axioms KCore.C3RuleReqPrioComp.pre_model
#print axioms KCore.C3RuleReqPrioComp.a5_step
#print axioms KCore.C3RuleReqPrioComp.a5_succs
#print axioms KCore.C3RuleReqPrioComp.an1_step
#print axioms KCore.C3RuleReqPrioComp.an1_succs
#print axioms KCore.C3RuleReqPrioComp.stepBy_an1
#print axioms KCore.C3RuleReqPrioComp.guard_an1
#print axioms KCore.C3RuleReqPrioComp.w2_an1
