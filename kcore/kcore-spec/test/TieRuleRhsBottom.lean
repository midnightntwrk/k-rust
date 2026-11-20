/-
  The rule sentences of construct fixture e3-ml-rule-rhs-bottom, the first read through
  `bottomAsEnsures`: `rule <k> go(_) => #Bottom ... </k>` beside
  `rule <k> go(_) => done ... </k> [priority(60)]`. The text is
  `f2-examples/e3-ml-rule-rhs-bottom.kompile.kore`, the one test/TieE3MlRuleRhsBottom.lean ties
  sentence by sentence; its section The rules ties the two rules (sentences 157 and 158) by W1
  from the sentence alone, from this file's proofs (uncovered = []). Run from the
  package root: `lake env lean -j1 test/TieRuleRhsBottom.lean`. Every statement is on the literal
  `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Sentence 157. The reader reads the rule with the right side its left side and the `ensures`
  false. Γ's item is `\rewrites(T ∧ ⊤ ∧ ⌈T ∧ {false = true}⌉, T ∧ {false = true})`, T the left
  side's term; the sentence is `\rewrites(T ∧ ⊤, K[append(⊥, R)] ∧ ⊤)`, K the context of the k
  cell's content in T and R the rest of the cell (`rule_text0`: the sentence is the item of that
  axiom at the table of Γ's axiom; kernel).

  - The two right sides hold the same elements, none. The sentence's holds nothing in every model
    of definedness (`rtext0_empty`: an application with an argument that holds nothing holds
    nothing); Γ's holds nothing in a model of definedness, `ΓSig` and `ΓDomains` (`right0_empty`:
    `false` and `true` are two elements of Bool).
  - W1, class *weaker* (`rule0_from_text`): Γ's item is a consequence of sentence 157 alone, for
    every H. Its left side is the sentence's with the conjunct `⌈right⌉` more (`left0`), and an
    element of the sentence's right side, of which there is none, is one of Γ's.
  - The converse (that Γ entails the sentence) is not claimed. The sentence states that its left side holds
    nothing (`sentence157_left_empty`: an element of it would have a successor among the elements
    of the right side); Γ's item states nothing of the left side, since its own left side holds
    nothing in a model of `ΓSig` and `ΓDomains` (`left0_empty`). The step relation gives the
    configuration no successor: the rule applies and its `ensures` is not `true`.
  - Γ refutes the sentence, for every H (`sentence157_refuted`): a model of Γ holds the element of
    the configuration `go(1)`, which is an element of the sentence's left side at the valuation of
    the match, and the sentence would give it a successor among the elements of a right side that
    holds nothing. So the text has no model with Γ, while Γ with the step's closure has one
    (`consistent`).

  Sentence 158 (priority 60), class *weaker* (`rule1_from_text`): Γ's item is the sentence with
  the negation of rule 0's left side and `⌈right⌉` more on its left side (`rule_text1`, `left1`).
  `rule_from_text`: W1 for both. `consistent` for every H.

  The expectation (C7 form (a), through the reading), from `Pre H` (the function equations as
  written, Γ's rule items, the families; it has a model, `pre_model`) with the step's closure:
  `bot_stuck`: `go(1)` has no successor (rule 0 applies there, so rule 1 of the larger priority
  does not, and rule 0's `ensures` is not `true`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRuleRhsBottom

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-rule-rhs-bottom.kompile.kore"
definition_of defn from "f2-examples/e3-ml-rule-rhs-bottom.kompile.kore"
user_axioms U from "f2-examples/e3-ml-rule-rhs-bottom.kompile.kore" module "E3-ML-RULE-RHS-BOTTOM"
user_axioms PreludeKseq from "f2-examples/e3-ml-rule-rhs-bottom.kompile.kore" module "KSEQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The function equations (the premises of the expectation) -/

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`): the user
module's, and the two equations of `append`, which the prelude module KSEQ holds. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c (PreludeKseq.all ++ U.all)

/-- The function equations as written. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-! ## The rule (sentence 157) -/

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0

/-- Its parts `\rewrites{C}(L', right)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl q0_eq : TieRuleLhs.rwParts p0 = some q0

noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)

/-- Γ's axiom of rule 1. -/
noncomputable def p1 : Kore.Pattern := prioRuleK c r1

/-- Its parts `\rewrites{C}(L', right)`. -/
noncomputable def q1 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p1).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl q1_eq : TieRuleLhs.rwParts p1 = some q1

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩] := by kernel_rfl

/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/
noncomputable def ruleText : List AxiomDecl := [U.ax157, U.ax158]

/-- The context of the k cell's content in the left side's term, and the content. -/
noncomputable def cut0 : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0] (TieRuleLhs.andHead q0.2.1)).getD (.hole, .top KoreAML.R)

/-- The rest of the k cell, the rule's variable after `go(_)`. -/
noncomputable def x0 : Kore.Pattern :=
  ((TieRuleLhs.cutAt [0, 0, 1] (TieRuleLhs.andHead q0.2.1)).getD (.hole, .top KoreAML.R)).2

/-- The context of `\bottom` in `append(\bottom, R)`. -/
noncomputable def appCtx : KoreCutCtx :=
  .app ⟨⟨"append"⟩⟩ [] [] .hole [x0]

-- Γ's right side: the left side's term and the `ensures` false.
kernel_rfl right0_eq : q0.2.2 = .and q0.1 [TieRuleLhs.andHead q0.2.1, TieRhs.ensFalse q0.1]

-- Γ's left side: the term, `\top`, then `⌈right⌉`.
kernel_rfl l0_eq : q0.2.1 = .and q0.1 [TieRuleLhs.andHead q0.2.1, .top q0.1, .ceil q0.1 q0.1 q0.2.2]

/-- The left side as the text writes it: no conjunct follows `\top`. -/
noncomputable def Ltext0 : Kore.Pattern := .and q0.1 [TieRuleLhs.andHead q0.2.1, .top q0.1]

/-- The right side as the text writes it: `append(\bottom{SortK{}}(), R)` as the k cell's content,
and `\top`. -/
noncomputable def Rtext0 : Kore.Pattern :=
  .and q0.1 [cut0.1.fill (appCtx.fill (.bottom (KoreAML.srt "K"))), .top q0.1]

noncomputable def fT0 : List VarKey := (freeOf [] (.rewrites q0.1 Ltext0 Rtext0)).eraseDups

/-- **Sentence 157 is the item of `\rewrites{C}(Ltext0, Rtext0)` at the table of Γ's axiom**
(kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 Rtext0) [] = some (trS U.ax157).pat := by
  decide +kernel
theorem fT_free0 : fT0.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel

-- Γ's left side of rule 1: the term, `\top`, then the negation of rule 0's left side and `⌈right⌉`.
kernel_rfl l1_eq : q1.2.1 = .and q1.1 (TieRuleLhs.andHead q1.2.1 :: .top q1.1 :: (TieRuleLhs.andTail q1.2.1).drop 1)

theorem l1_more : ((TieRuleLhs.andTail q1.2.1).drop 1).length = 2 := by decide +kernel

/-- The left side of rule 1 as the text writes it: no conjunct follows `\top`. -/
noncomputable def Ltext1 : Kore.Pattern := .and q1.1 [TieRuleLhs.andHead q1.2.1, .top q1.1]

noncomputable def fT1 : List VarKey := (freeOf [] (.rewrites q1.1 Ltext1 q1.2.2)).eraseDups

/-- **Sentence 158 is the item of `\rewrites{C}(Ltext1, right)` at the table of Γ's axiom**
(kernel). -/
theorem rule_text1 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p1) fT1 q1.1 Ltext1 q1.2.2) [] = some (trS U.ax158).pat := by
  decide +kernel
theorem fT_free1 : fT1.all (fun k => (freeOf [] p1).eraseDups.contains k) = true := by decide +kernel

theorem cut0_noAlias : cut0.1.noAlias ⟨tableOf [] p0, []⟩ = true := by decide +kernel
theorem appCtx_noAlias : appCtx.noAlias ⟨tableOf [] p0, []⟩ = true := by decide +kernel

kernel_rfl C_eq : q0.1 = KoreAML.srt "GeneratedTopCell"
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")
theorem sortOf_false (H : HookParams) : (cH H).sortOf (KCore.bool false) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sortOf_true (H : HookParams) : (cH H).sortOf (KCore.bool true) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem den_false (H : HookParams) : den (cH H) (KCore.bool false) = KoreAML.sym (.dv "false") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.bool false) = _; decide +kernel
theorem den_true (H : HookParams) : den (cH H) (KCore.bool true) = KoreAML.sym (.dv "true") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.bool true) = _; decide +kernel

/-- **The sentence's right side holds nothing**, in every model of definedness: `\bottom` holds
nothing, and an application with an argument that holds nothing holds nothing. -/
theorem rtext0_empty {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) (e : Valuation M) (b : M) :
    ¬ (tr ⟨tableOf [] p0, []⟩ Rtext0).interpret I e b :=
  TieRuleRhs.and_empty (List.mem_cons_self ..)
    (TieRuleRhs.tr_fill_empty _ cut0.1 cut0_noAlias
      (TieRuleRhs.tr_fill_empty _ appCtx appCtx_noAlias (TieRhs.tr_botConst_empty hD rfl e))) b

/-- **Γ's right side holds nothing** in a model of definedness, the signature and the domains: its
`ensures` is `false = true`, and the values `false` and `true` of Bool are two elements. -/
theorem right0_empty (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (hDom : I ⊧ᴵP ΓDomains (cH H)) (e : Valuation M) (b : M) :
    ¬ (tr ⟨tableOf [] p0, []⟩ q0.2.2).interpret I e b := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  rw [right0_eq]
  exact TieRuleRhs.and_empty (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (TieRhs.ensFalse_empty hD hSig hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H)
      (by rw [C_eq, trSort_srt]; exact hσ1) hσ2) b

/-- **The two right sides hold the same elements** (none) in a model of definedness, the signature
and the domains. -/
theorem right0_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (hDom : I ⊧ᴵP ΓDomains (cH H)) (e : Valuation M) (b : M) :
    (tr ⟨tableOf [] p0, []⟩ Rtext0).interpret I e b ↔ (tr ⟨tableOf [] p0, []⟩ q0.2.2).interpret I e b :=
  ⟨fun h => absurd h (rtext0_empty hD e b), fun h => absurd h (right0_empty H hD hSig hDom e b)⟩

/-- **Γ's left side holds nothing** in a model of definedness, the signature and the domains: its
conjunct `⌈right⌉` is the definedness of a right side that holds nothing. -/
theorem left0_empty (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (hDom : I ⊧ᴵP ΓDomains (cH H)) (e : Valuation M) (a : M) :
    ¬ (tr ⟨tableOf [] p0, []⟩ q0.2.1).interpret I e a := by
  rw [l0_eq]
  exact TieRuleRhs.and_empty (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (TieRuleRhs.ceil_empty (right0_empty H hD hSig hDom e)) a

/-- Every element of Γ's left side is an element of the text's left side: the text's conjuncts are
Γ's first two. -/
theorem left0 {M : Type} {I : Interpretation KoreAML.Sym M} (e : Valuation M) (a : M)
    (h : (tr ⟨tableOf [] p0, []⟩ q0.2.1).interpret I e a) : (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a := by
  rw [l0_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h _ (List.mem_cons_self ..)
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- **W1 for rule 0**: Γ's item is a consequence of sentence 157. -/
theorem rule0_from_text : itemsPremises [trS U.ax157] ⊧ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  exact TieRuleRhs.rule_w1_rhs hD q0_eq rule_text0 fT_free0
    (hI _ (Or.inl ⟨trS U.ax157, List.mem_singleton_self _, rfl⟩))
    (fun e _ _ a ha => left0 e a ha)
    (fun e _ _ b hb => absurd hb (rtext0_empty hD e b))

/-- Every element of Γ's left side of rule 1 is an element of the text's left side: the text's
conjuncts are Γ's first two. -/
theorem left1 {M : Type} {I : Interpretation KoreAML.Sym M} (e : Valuation M) (a : M)
    (h : (tr ⟨tableOf [] p1, []⟩ q1.2.1).interpret I e a) : (tr ⟨tableOf [] p1, []⟩ Ltext1).interpret I e a := by
  rw [l1_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext1
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h _ (List.mem_cons_self ..)
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- **W1 for rule 1**: Γ's item is a consequence of sentence 158, which it is with two conjuncts
more on its left side. -/
theorem rule1_from_text : itemsPremises [trS U.ax158] ⊧ (trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  exact TieRuleLhs.rule_w1 hD q1_eq rule_text1 fT_free1
    (hI _ (Or.inl ⟨trS U.ax158, List.mem_singleton_self _, rfl⟩))
    (fun e _ _ a ha => left1 e a ha)

/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's rule items is a
consequence of a text sentence of `ruleText`, for every H. -/
theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ it.pat := by
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  rcases List.mem_cons.mp hit with rfl | hit
  · exact ⟨U.ax157, List.mem_cons_self .., rule0_from_text⟩
  · rw [List.mem_singleton.mp hit]
    exact ⟨U.ax158, List.mem_cons_of_mem _ (List.mem_cons_self ..), rule1_from_text⟩

/-- Sentence 157 is the item of the text's two sides at the table of Γ's axiom. -/
theorem trS157 : (trS U.ax157).pat = TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 Rtext0 := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- **What sentence 157 states: its left side holds nothing**, in every model of it with
definedness, at every valuation where the guards of its variables hold. An element of the left
side would have a successor among the elements of the right side, which holds nothing. -/
theorem sentence157_left_empty {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (h : I ⊧ᴵ (trS U.ax157).pat) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT0, (guardOf (tableOf [] p0) k).interpret I e m) (a : M) :
    ¬ (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a := by
  rw [trS157] at h
  refine TieRuleRhs.left_empty_of_right_empty hD h e m hg (rtext0_empty hD e) (fun a' ha' => ?_) a
  unfold Ltext0 at ha'
  rw [interp_and (List.cons_ne_nil _ _)] at ha'
  have h2 := ha' _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hT : tr ⟨tableOf [] p0, []⟩ (.top q0.1) = sTop (trSort (tableOf [] p0) q0.1) := by rw [tr]
  rw [hT, interp_sTop hD (by rw [C_eq, trSort_srt]; rfl)] at h2
  exact h2

/-! ## The facts the deciders leave -/

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel

def callOrder : List Nat := [388]

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

/-! ## The expectation (C7 form (a)) -/

/-- **The premises of the derivation**: every function equation as written, Γ's rule items (the
reading of the rule sentences 157 and 158, each a consequence of its sentence by `rule_from_text`), and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

theorem readsConfined_c : c.readsConfined = false := by decide +kernel
theorem hrcH (H : HookParams) : (cH H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans readsConfined_c

/-- The configuration with `it` of sort Exp in the k cell and the counter at 0. -/
def cfg (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor 383 [.ctor kseq [.inj 32 Srt.kitem it, .ctor dotk []]], .ctor counterLabel [.dv Srt.int (.int 0)]]

theorem clausesFixed_c : c.clausesFixed = true := by decide +kernel
theorem agreeObligations_c : c.agreeObligations = [] := by decide +kernel
theorem asideFree_c : c.asideFree = true := by decide +kernel

theorem coherentH (H : HookParams) : CoherentAll (cH H) :=
  Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans hok) ((Semantics.srReady_withHooks c H).trans hsr)
    ((Semantics.matchReady_withHooks c H).trans hmr) ((TiePair.clausesFixed_withHooks c H).trans clausesFixed_c)
    ((Semantics.agreeObligations_withHooks c H).trans agreeObligations_c)

/-- A configuration whose successors `listedCheck` finds to be none on the data (a rule that
applies blocks the rules of a larger priority) has no successor, as a consequence of `Pre H` with
the step's closure: `⟦x⟧ → ◦⊥`. -/
theorem stuck_from {x : Config c} (h : TieRulePair.listedCheck c 100 x.val [] = true) (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) x.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  TiePair.cutStep (shapeH H) (complete_at_step _ (coreOKH H) (hrcH H) (TieRulePair.cfgH noRaw x H)
    (stepDecided_of_fnHyp (coreOKH H) (fnHypH H) _) []
    (TieRulePair.listed_sound hok hsr hmr H (coherentH H) (x := x) (n := 100) h asideFree_c noRaw))

theorem names : c.symName 385 = "Lbldone" ∧ c.symName 386 = "Lblgo" ∧ c.symName 387 = "Lblother" ∧ c.sortName 32 = "Exp" := by
  decide +kernel

def Go1 : Config c := ⟨cfg (.ctor 386 [.dv Srt.int (.int 1)]), by decide +kernel⟩

/-- **`go(1)` has no successor, derived from `Pre` with the step's closure**, for every H: rule 0
applies there and its `ensures` is not `true`, and rule 1 does not apply where rule 0 does. -/
theorem bot_stuck (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) Go1.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  stuck_from (x := Go1) (by decide +kernel) H

/-! ## Γ refutes sentence 157 -/

theorem r0_sorted : c.ruleSorted r0 = true := by decide +kernel

-- The text's left side is the left side's term of the rule and `\top`, at the sort of configurations.
kernel_rfl Ltext0_eq : Ltext0 = .and (srtOf c topCellSort)
  [Term.kore c (canonVars c r0.vars) r0.lhs, .top (srtOf c topCellSort)]
kernel_rfl q0C_eq : q0.1 = srtOf c topCellSort

-- The table of Γ's axiom holds the rule's variables, and the sentence's guards are on them.
theorem keys0 : (List.range r0.vars.length).all (fun i => (tableOf [] p0).contains (canonKey c r0.vars i)) = true := by
  decide +kernel
theorem fT0_keys : fT0.all (fun k => (List.range r0.vars.length).any (fun i => k == canonKey c r0.vars i)) = true := by
  decide +kernel

/-- The rule's left side matches the configuration. -/
theorem match0 : ((Exec.matchP c 100 [] r0.lhs Go1.val).filter (Exec.wellSorted c r0.vars)).isEmpty = false := by
  decide +kernel

/-- **Γ refutes sentence 157, for every H**: no model of Γ is a model of the sentence. A model of Γ
holds the element of the configuration `go(1)`, which the sentence's left side holds at the valuation
of the match; the sentence gives it a successor among the elements of its right side, which holds
nothing. -/
theorem sentence157_refuted (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hΓ : I ⊧ᴵP Γ (cH H)) : ¬ (I ⊧ᴵ (trS U.ax157).pat) := by
  intro hsen
  rw [trS157, q0C_eq, Ltext0_eq] at hsen
  exact TieRuleRhs.rhs_empty_refuted_everyH coreOK noRaw r0_sorted Go1 match0 keys0 fT0_keys H hΓ
    (fun _ _ _ b => rtext0_empty (defOK hΓ) _ b) hsen

end KCore.TieRuleRhsBottom

#check @KCore.TieRuleRhsBottom.rule_text0
#check @KCore.TieRuleRhsBottom.rtext0_empty
#check @KCore.TieRuleRhsBottom.right0_empty
#check @KCore.TieRuleRhsBottom.right0_iff
#check @KCore.TieRuleRhsBottom.left0_empty
#check @KCore.TieRuleRhsBottom.rule0_from_text
#check @KCore.TieRuleRhsBottom.rule_text1
#check @KCore.TieRuleRhsBottom.rule1_from_text
#check @KCore.TieRuleRhsBottom.rule_from_text
#check @KCore.TieRuleRhsBottom.sentence157_left_empty
#check @KCore.TieRuleRhsBottom.consistent
#check @KCore.TieRuleRhsBottom.pre_model
#check @KCore.TieRuleRhsBottom.bot_stuck
#print axioms KCore.TieRuleRhsBottom.rule_text0
#print axioms KCore.TieRuleRhsBottom.right0_iff
#print axioms KCore.TieRuleRhsBottom.left0_empty
#print axioms KCore.TieRuleRhsBottom.rule_text1
#print axioms KCore.TieRuleRhsBottom.rule_from_text
#print axioms KCore.TieRuleRhsBottom.sentence157_left_empty
#print axioms KCore.TieRuleRhsBottom.consistent
#print axioms KCore.TieRuleRhsBottom.pre_model
#print axioms KCore.TieRuleRhsBottom.bot_stuck
#check @KCore.TieRuleRhsBottom.sentence157_refuted
#print axioms KCore.TieRuleRhsBottom.sentence157_refuted
