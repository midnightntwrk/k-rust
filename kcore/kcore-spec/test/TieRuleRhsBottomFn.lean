/-
  The rule sentence of construct fixture e3-ml-rule-rhs-bottom-fn, read through `bottomAsEnsures`:
  `rule <k> go(X) => pair(f(X), #Bottom) ... </k>`, a right side that applies a constructor to
  `\bottom{SortInt{}}()`. The text is `f2-examples/e3-ml-rule-rhs-bottom-fn.kompile.kore`, the one
  test/TieE3MlRuleRhsBottomFn.lean ties sentence by sentence with this rule (sentence 155) left
  uncovered. Run from the package root: `lake env lean -j1 test/TieRuleRhsBottomFn.lean`. Every
  statement is on the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or
  `emit`.

  The reader reads the rule with the right side its left side and the `ensures` false. Γ's item is
  `\rewrites(T ∧ ⊤ ∧ ⌈T ∧ {false = true}⌉, T ∧ {false = true})`, T the left side's term; the
  sentence is `\rewrites(T ∧ ⊤, K[pair(f(X), ⊥)] ∧ ⊤)`, K the context of `go(X)` in T
  (`rule_text0`: the sentence is the item of that axiom at the table of Γ's axiom; kernel).

  - The two right sides hold the same elements, none. The sentence's holds nothing in every model
    of definedness (`rtext0_empty`: an application with an argument that holds nothing holds
    nothing); Γ's holds nothing in a model of definedness, `ΓSig` and `ΓDomains` (`right0_empty`:
    `false` and `true` are two elements of Bool).
  - W1, class *weaker* (`rule_from_text`, `rule0_from_text`): Γ's item is a consequence of
    sentence 155 alone, for every H. Its left side is the sentence's with the conjunct `⌈right⌉`
    more (`left0`), and an element of the sentence's right side, of which there is none, is one of
    Γ's.
  - The converse (that Γ entails the sentence) is not claimed. The sentence states that its left side holds
    nothing (`sentence155_left_empty`: an element of it would have a successor among the elements
    of the right side); Γ's item states nothing of the left side, since its own left side holds
    nothing in a model of `ΓSig` and `ΓDomains` (`left0_empty`). The step relation gives the
    configuration no successor: the rule applies and its `ensures` is not `true`.
  `consistent` for every H.

  The expectation (C7 form (a), through the reading), from `Pre H` (the function equations as
  written, Γ's rule items, the families; it has a model, `pre_model`) with the step's closure:
  `bot_stuck`: `go(1)` has no successor.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRuleRhsBottomFn

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-rule-rhs-bottom-fn.kompile.kore"
definition_of defn from "f2-examples/e3-ml-rule-rhs-bottom-fn.kompile.kore"
user_axioms U from "f2-examples/e3-ml-rule-rhs-bottom-fn.kompile.kore" module "E3-ML-RULE-RHS-BOTTOM-FN"

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

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- The function equations as written. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-! ## The rule (sentence 155) -/

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0

/-- Its parts `\rewrites{C}(L', right)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl q0_eq : TieRuleLhs.rwParts p0 = some q0

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/
noncomputable def ruleText : List AxiomDecl := [U.ax155]

/-- The context of `go(X)` in the left side's term, and `go(X)`. -/
noncomputable def cut0 : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0, 0, 0] (TieRuleLhs.andHead q0.2.1)).getD (.hole, .top KoreAML.R)

/-- The rule's variable X. -/
noncomputable def x0 : Kore.Pattern :=
  ((TieRuleLhs.cutAt [0, 0, 0, 0, 0] (TieRuleLhs.andHead q0.2.1)).getD (.hole, .top KoreAML.R)).2

/-- The context of `\bottom` in `pair(f(X), \bottom)`. -/
noncomputable def pairCtx : KoreCutCtx :=
  .app ⟨⟨"Lblpair"⟩⟩ [] [.app ⟨⟨"Lblf"⟩⟩ [] [x0]] .hole []

-- Γ's right side: the left side's term and the `ensures` false.
kernel_rfl right0_eq : q0.2.2 = .and q0.1 [TieRuleLhs.andHead q0.2.1, TieRhs.ensFalse q0.1]

-- Γ's left side: the term, `\top`, then `⌈right⌉`.
kernel_rfl l0_eq : q0.2.1 = .and q0.1 [TieRuleLhs.andHead q0.2.1, .top q0.1, .ceil q0.1 q0.1 q0.2.2]

/-- The left side as the text writes it: no conjunct follows `\top`. -/
noncomputable def Ltext0 : Kore.Pattern := .and q0.1 [TieRuleLhs.andHead q0.2.1, .top q0.1]

/-- The right side as the text writes it: `pair(f(X), \bottom{SortInt{}}())` in the place of
`go(X)`, and `\top`. -/
noncomputable def Rtext0 : Kore.Pattern :=
  .and q0.1 [cut0.1.fill (pairCtx.fill (.bottom (KoreAML.srt "Int"))), .top q0.1]

noncomputable def fT0 : List VarKey := (freeOf [] (.rewrites q0.1 Ltext0 Rtext0)).eraseDups

/-- **Sentence 155 is the item of `\rewrites{C}(Ltext0, Rtext0)` at the table of Γ's axiom**
(kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 Rtext0) [] = some (trS U.ax155).pat := by
  decide +kernel
theorem fT_free0 : fT0.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel

theorem cut0_noAlias : cut0.1.noAlias ⟨tableOf [] p0, []⟩ = true := by decide +kernel
theorem pairCtx_noAlias : pairCtx.noAlias ⟨tableOf [] p0, []⟩ = true := by decide +kernel

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
      (TieRuleRhs.tr_fill_empty _ pairCtx pairCtx_noAlias (TieRhs.tr_botConst_empty hD rfl e))) b

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

/-- **W1 for rule 0**: Γ's item is a consequence of sentence 155. -/
theorem rule0_from_text : itemsPremises [trS U.ax155] ⊧ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  exact TieRuleRhs.rule_w1_rhs hD q0_eq rule_text0 fT_free0
    (hI _ (Or.inl ⟨trS U.ax155, List.mem_singleton_self _, rfl⟩))
    (fun e _ _ a ha => left0 e a ha)
    (fun e _ _ b hb => absurd hb (rtext0_empty hD e b))

/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's rule items is a
consequence of a text sentence of `ruleText`, for every H. -/
theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ it.pat := by
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  rw [List.mem_singleton.mp hit]
  exact ⟨U.ax155, List.mem_singleton_self _, rule0_from_text⟩

/-- Sentence 155 is the item of the text's two sides at the table of Γ's axiom. -/
theorem trS155 : (trS U.ax155).pat = TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 Rtext0 := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- **What sentence 155 states: its left side holds nothing**, in every model of it with
definedness, at every valuation where the guards of its variables hold. An element of the left
side would have a successor among the elements of the right side, which holds nothing. -/
theorem sentence155_left_empty {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (h : I ⊧ᴵ (trS U.ax155).pat) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT0, (guardOf (tableOf [] p0) k).interpret I e m) (a : M) :
    ¬ (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a := by
  rw [trS155] at h
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

def callOrder : List Nat := [387]

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
reading of rule sentence 155, a consequence of it by `rule_from_text`), and the families. -/
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

/-- A configuration `stuckCheck` accepts on the data has no successor, as a consequence of `Pre H`
with the step's closure: `⟦x⟧ → ◦⊥`. -/
theorem stuck_from {x : Config c} (h : Cert.stuckCheck c 50 x.val = true) (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) x.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  TiePair.cutStep (shapeH H) (complete_at_step _ (coreOKH H) (hrcH H) (TieRuleLhs.cfgH noRaw x H)
    (stepDecided_of_fnHyp (coreOKH H) (fnHypH H) _) []
    fun y hy => absurd hy (TieRuleLhs.stuck_everyH hok hsr hmr noRaw clausesFixed_c agreeObligations_c asideFree_c h H y))

theorem names : c.symName 385 = "Lblgo" ∧ c.symName 386 = "Lblpair" ∧ c.symName 387 = "Lblf" ∧ c.sortName 32 = "Exp" := by
  decide +kernel

def Go1 : Config c := ⟨cfg (.ctor 385 [.dv Srt.int (.int 1)]), by decide +kernel⟩

/-- **`go(1)` has no successor, derived from `Pre` with the step's closure**, for every H: the
rule applies there and its `ensures` is not `true`. -/
theorem bot_stuck (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) Go1.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  stuck_from (x := Go1) (by decide +kernel) H

end KCore.TieRuleRhsBottomFn

#check @KCore.TieRuleRhsBottomFn.rule_text0
#check @KCore.TieRuleRhsBottomFn.rtext0_empty
#check @KCore.TieRuleRhsBottomFn.right0_empty
#check @KCore.TieRuleRhsBottomFn.right0_iff
#check @KCore.TieRuleRhsBottomFn.left0_empty
#check @KCore.TieRuleRhsBottomFn.rule0_from_text
#check @KCore.TieRuleRhsBottomFn.rule_from_text
#check @KCore.TieRuleRhsBottomFn.sentence155_left_empty
#check @KCore.TieRuleRhsBottomFn.consistent
#check @KCore.TieRuleRhsBottomFn.pre_model
#check @KCore.TieRuleRhsBottomFn.bot_stuck
#print axioms KCore.TieRuleRhsBottomFn.rule_text0
#print axioms KCore.TieRuleRhsBottomFn.right0_iff
#print axioms KCore.TieRuleRhsBottomFn.left0_empty
#print axioms KCore.TieRuleRhsBottomFn.rule_from_text
#print axioms KCore.TieRuleRhsBottomFn.sentence155_left_empty
#print axioms KCore.TieRuleRhsBottomFn.consistent
#print axioms KCore.TieRuleRhsBottomFn.pre_model
#print axioms KCore.TieRuleRhsBottomFn.bot_stuck
