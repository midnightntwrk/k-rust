/-
  The rule sentence of construct fixture e3-ml-rule-rhs-and-pred, read through `andAsEnsures`:
  `rule <k> go(X) => done #And {(X >Int 0) #Equals true} ... </k>`, a right side that conjoins a
  predicate with its term. The text is `f2-examples/e3-ml-rule-rhs-and-pred.kompile.kore`, the one
  test/TieE3MlRuleRhsAndPred.lean ties sentence by sentence with this rule (sentence 157) left
  uncovered. Run from the package root: `lake env lean -j1 test/TieRuleRhsAndPred.lean`. Every
  statement is on the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or
  `emit`.

  The reader reads the rule with the right side `done` and the `ensures` `X >Int 0`. Γ's item is
  `\rewrites(T ∧ ⊤ ∧ ⌈right⌉, right)` with `right = K[A] ∧ {X >Int 0 = true}`, the predicate
  `\equals{Bool, C}` at the sort C of configurations, A the term `kseq(inj(done), dotk)` and K its
  context `<generatedTop>(<k>(append(□, R)), _)`. The sentence is
  `\rewrites(T ∧ ⊤, K[A ∧ {X >Int 0 = true}] ∧ ⊤)`, the predicate `\equals{Bool, K}` conjoined
  with A at the sort K (`rule_text0`: the sentence is the item of that axiom at the table of Γ's
  axiom; kernel).

  - The two right sides hold the same elements in a model of definedness, `ΓSig` and `ΓDomains`
    (`right0_iff`). An element of the sentence's gives an element of the hole, where the equality
    holds, and the equality at C holds at every element of C (`right0_sub`, from `ΓSig` alone:
    the sorts Bool, K and C and `\ceil`'s definition). Conversely the elements of A are elements
    of K (`ΓDomains`: A is a value's term), so where the equality holds A is the conjunction.
  - W1, class *weaker* (`rule_from_text_sig`, `rule0_from_text_sig`): Γ's item is a consequence
    of sentence 157 and Γ's signature, for every H. Its left side is the sentence's with the
    conjunct `⌈right⌉` more (`left0`), and its right side holds every element of the sentence's.
  - The converse (that Γ entails the sentence) is not claimed. At a valuation where the predicate does not
    hold, the sentence states that its left side holds nothing (`sentence157_left_empty`: an
    element of it would have a successor among the elements of the right side, which holds
    nothing there); Γ's item states nothing there, its left side holding the conjunct `⌈right⌉`.
    The step relation gives such a configuration no successor: the rule applies and its
    `ensures` is not `true`.
  `consistent` for every H.

  The expectations (C7 form (a), through the reading), from `Pre H` (the function equations as
  written, Γ's rule items, the families; it has a model, `pre_model`): `and_step`: `go(1)` steps
  to `done`; with the step's closure, `and_stuck`: `go(0)` has no successor.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRuleRhsAndPred

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-rule-rhs-and-pred.kompile.kore"
definition_of defn from "f2-examples/e3-ml-rule-rhs-and-pred.kompile.kore"
user_axioms U from "f2-examples/e3-ml-rule-rhs-and-pred.kompile.kore" module "E3-ML-RULE-RHS-AND-PRED"
user_axioms PreludeKseq from "f2-examples/e3-ml-rule-rhs-and-pred.kompile.kore" module "KSEQ"

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

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/
noncomputable def ruleText : List AxiomDecl := [U.ax157]

/-- The context of the term A, `kseq(inj(done), dotk)`, in the right side's term, and A. -/
noncomputable def cutR : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0, 0] (TieRuleLhs.andHead q0.2.2)).getD (.hole, .top KoreAML.R)

/-- The two sides of an equality. -/
def eqSides : Kore.Pattern → Kore.Pattern × Kore.Pattern
  | .equals _ _ x y => (x, y)
  | p => (p, p)

/-- The two sides of Γ's `ensures`: `X >Int 0` and `true`. -/
noncomputable def xy : Kore.Pattern × Kore.Pattern :=
  eqSides ((TieRuleLhs.andTail q0.2.2).headD (.top KoreAML.R))

-- Γ's right side: the term, A in its context, and the `ensures` at the sort of configurations.
kernel_rfl right0_eq : q0.2.2 = .and q0.1 [cutR.1.fill cutR.2, .equals (KoreAML.srt "Bool") q0.1 xy.1 xy.2]

-- Γ's left side: the term, `\top`, then `⌈right⌉`.
kernel_rfl l0_eq : q0.2.1 = .and q0.1 [TieRuleLhs.andHead q0.2.1, .top q0.1, .ceil q0.1 q0.1 q0.2.2]

/-- The left side as the text writes it: no conjunct follows `\top`. -/
noncomputable def Ltext0 : Kore.Pattern := .and q0.1 [TieRuleLhs.andHead q0.2.1, .top q0.1]

/-- The right side as the text writes it: the predicate conjoined with A at the sort K, in A's
context, and `\top`. -/
noncomputable def Rtext0 : Kore.Pattern :=
  .and q0.1 [cutR.1.fill (.and (KoreAML.srt "K") [cutR.2, .equals (KoreAML.srt "Bool") (KoreAML.srt "K") xy.1 xy.2]), .top q0.1]

noncomputable def fT0 : List VarKey := (freeOf [] (.rewrites q0.1 Ltext0 Rtext0)).eraseDups

/-- **Sentence 157 is the item of `\rewrites{C}(Ltext0, Rtext0)` at the table of Γ's axiom**
(kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 Rtext0) [] = some (trS U.ax157).pat := by
  decide +kernel
theorem fT_free0 : fT0.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel

theorem cutR_noAlias : cutR.1.noAlias ⟨tableOf [] p0, []⟩ = true := by decide +kernel

kernel_rfl C_eq : q0.1 = KoreAML.srt "GeneratedTopCell"
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")
theorem k_name (H : HookParams) : (cH H).sortName Srt.k = "K" := (by decide +kernel : c.sortName Srt.k = "K")
theorem k_numbered (H : HookParams) : Srt.k < nRegSorts + (cH H).sortNames.length :=
  Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)

/-- The term A is a value's: `kseq(inj{Exp, KItem}(done), dotk)`, of sort K. -/
def vA : GroundTerm := .ctor kseq [.inj 32 Srt.kitem (.ctor 385 []), .ctor dotk []]

theorem A_eq (H : HookParams) : cutR.2 = vA.kore (cH H) := (by decide +kernel : cutR.2 = vA.kore c)
theorem sortOf_vA (H : HookParams) : (cH H).sortOf vA = some Srt.k := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- The sorts Bool, K and C are each one sort, in a model of the signature. -/
theorem sorts (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (t : VarTable) (e : Valuation M) :
    ∃ σB σK σC, (∀ a, (trSort t (KoreAML.srt "Bool")).interpret I e a ↔ a = σB) ∧
      (∀ a, (trSort t (KoreAML.srt "K")).interpret I e a ↔ a = σK) ∧
      (∀ a, (trSort t q0.1).interpret I e a ↔ a = σC) ∧ IsSort I σB ∧ IsSort I σK ∧ IsSort I σC := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σB, hB1, hB2⟩ := TieRhs.sortSing_sig hD hSig (bool_numbered (c := cH H))
  obtain ⟨σK, hK1, hK2⟩ := TieRhs.sortSing_sig hD hSig (k_numbered H)
  obtain ⟨σC, hC1, hC2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [sortName_bool] at hB1
  rw [k_name] at hK1
  rw [top_name] at hC1
  exact ⟨σB, σK, σC, by rw [trSort_srt]; exact hB1, by rw [trSort_srt]; exact hK1,
    by rw [C_eq, trSort_srt]; exact hC1, hB2, hK2, hC2⟩

/-- **Every element of the sentence's right side is an element of Γ's**, in a model of
definedness and the signature: an element of the first gives an element of the hole, where the
equality at K holds, and the equality at C then holds at every element of C. -/
theorem right0_sub (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (e : Valuation M) (b : M)
    (h : (tr ⟨tableOf [] p0, []⟩ Rtext0).interpret I e b) : (tr ⟨tableOf [] p0, []⟩ q0.2.2).interpret I e b := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  obtain ⟨σB, σK, σC, hSB, hSK, hSC, hσB, hσK, hσC⟩ := sorts H hD hSig (tableOf [] p0) e
  rw [right0_eq]
  exact TieRuleRhs.andPred_sub hD hc cutR_noAlias hSB hSK hSC hσB hσK hσC (by rw [C_eq, trSort_srt]; rfl) b h

/-- **The two right sides hold the same elements** in a model of definedness, the signature and
the domains: the elements of A are elements of K (A is a value's term), so where the equality
holds A is its conjunction with the equality at K. -/
theorem right0_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (hDom : I ⊧ᴵP ΓDomains (cH H)) (e : Valuation M) (b : M) :
    (tr ⟨tableOf [] p0, []⟩ Rtext0).interpret I e b ↔ (tr ⟨tableOf [] p0, []⟩ q0.2.2).interpret I e b := by
  refine ⟨right0_sub H hD hSig e b, fun h => ?_⟩
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  obtain ⟨σB, σK, σC, hSB, hSK, hSC, hσB, hσK, hσC⟩ := sorts H hD hSig (tableOf [] p0) e
  rw [right0_eq] at h
  refine TieRuleRhs.andPred_sup hD hc cutR_noAlias hSB hSK hSC hσB hσK hσC (by rw [C_eq, trSort_srt]; rfl)
    (fun a ha => ?_) b h
  rw [A_eq H] at ha
  have h1 := TieRuleLhs.ground_inh hD hDom (sortOf_vA H) a ha
  rw [k_name] at h1
  have hK' : ∀ a', (KoreAML.sym (.sort ("Sort" ++ "K")) : P).interpret I e a' ↔ a' = σK := fun a' => by
    have h2 := hSK a'
    rw [trSort_srt] at h2
    exact h2
  exact (interp_inhOf_of hK').mp h1

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

/-- **W1 for rule 0, over the signature**: Γ's item is a consequence of sentence 157 and Γ's
signature, for every H. -/
theorem rule0_from_text_sig (H : HookParams) :
    itemsPremises [trS U.ax157] ∪ ΓSig (cH H) ⊧ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat := by
  intro M _ I hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inl (Or.inr ⟨x, rfl⟩))
  exact TieRuleRhs.rule_w1_rhs hD q0_eq rule_text0 fT_free0
    (hI _ (Or.inl (Or.inl ⟨trS U.ax157, List.mem_singleton_self _, rfl⟩)))
    (fun e _ _ a ha => left0 e a ha)
    (fun e _ _ b hb => right0_sub H hD hSig e b hb)

/-- **W1 for the rules, over the signature, and the converse for `ruleItems`**: each of Γ's rule
items is a consequence of a text sentence of `ruleText` and Γ's signature, for every H. -/
theorem rule_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  rw [List.mem_singleton.mp hit]
  exact ⟨U.ax157, List.mem_singleton_self _, rule0_from_text_sig H⟩

/-- Sentence 157 is the item of the text's two sides at the table of Γ's axiom. -/
theorem trS157 : (trS U.ax157).pat = TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 Rtext0 := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- **What sentence 157 states where the predicate does not hold: its left side holds nothing**,
in every model of it with definedness and the signature, at every valuation where the guards of
its variables hold and Γ's `ensures` holds nothing. An element of the left side would have a
successor among the elements of the right side, which holds nothing there. -/
theorem sentence157_left_empty (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig (cH H)) (h : I ⊧ᴵ (trS U.ax157).pat) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT0, (guardOf (tableOf [] p0) k).interpret I e m)
    (hens : ∀ b, ¬ (tr ⟨tableOf [] p0, []⟩ (.equals (KoreAML.srt "Bool") q0.1 xy.1 xy.2)).interpret I e b) (a : M) :
    ¬ (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a := by
  rw [trS157] at h
  refine TieRuleRhs.left_empty_of_right_empty hD h e m hg (fun b hb => ?_) (fun a' ha' => ?_) a
  · have h1 := right0_sub H hD hSig e b hb
    rw [right0_eq, interp_and (List.cons_ne_nil _ _)] at h1
    exact hens b (h1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · unfold Ltext0 at ha'
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
reading of rule sentence 157, a consequence of it and Γ's signature by `rule_from_text_sig`), and the families. -/
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

/-- A step the rules' check accepts on the data, as a consequence of `Pre H`: `⟦x⟧ → •⟦y⟧`. -/
theorem step_from {x y : Config c} (h : c.rules.any (fun r => Cert.checkStep c 50 r x.val y.val) = true) (H : HookParams) :
    Pre H ⊧ (den (cH H) x.val ⇒ KoreAML.sNext (den (cH H) y.val)) :=
  TiePair.cut (shapeH H) (sound_at_step _ (coreOKH H) (hrcH H) _ _ (TieRuleLhs.step_everyH hok hsr hmr noRaw h H))

theorem names : c.symName 385 = "Lbldone" ∧ c.symName 386 = "Lblgo" ∧ c.symName 387 = "Lblother" ∧ c.sortName 32 = "Exp" := by
  decide +kernel

def Go1 : Config c := ⟨cfg (.ctor 386 [.dv Srt.int (.int 1)]), by decide +kernel⟩
def Go0 : Config c := ⟨cfg (.ctor 386 [.dv Srt.int (.int 0)]), by decide +kernel⟩
def Done : Config c := ⟨cfg (.ctor 385 []), by decide +kernel⟩

/-- **`go(1)` steps to `done`, derived from `Pre`**, for every H: `1 >Int 0` is `true`. -/
theorem and_step (H : HookParams) : Pre H ⊧ (den (cH H) Go1.val ⇒ KoreAML.sNext (den (cH H) Done.val)) :=
  step_from (x := Go1) (y := Done) (by decide +kernel) H

/-- **`go(0)` has no successor, derived from `Pre` with the step's closure**, for every H: the
rule applies there and its `ensures`, `0 >Int 0`, is not `true`. -/
theorem and_stuck (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) Go0.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  stuck_from (x := Go0) (by decide +kernel) H

end KCore.TieRuleRhsAndPred

#check @KCore.TieRuleRhsAndPred.rule_text0
#check @KCore.TieRuleRhsAndPred.right0_sub
#check @KCore.TieRuleRhsAndPred.right0_iff
#check @KCore.TieRuleRhsAndPred.rule0_from_text_sig
#check @KCore.TieRuleRhsAndPred.rule_from_text_sig
#check @KCore.TieRuleRhsAndPred.sentence157_left_empty
#check @KCore.TieRuleRhsAndPred.consistent
#check @KCore.TieRuleRhsAndPred.pre_model
#check @KCore.TieRuleRhsAndPred.and_step
#check @KCore.TieRuleRhsAndPred.and_stuck
#print axioms KCore.TieRuleRhsAndPred.rule_text0
#print axioms KCore.TieRuleRhsAndPred.right0_iff
#print axioms KCore.TieRuleRhsAndPred.rule_from_text_sig
#print axioms KCore.TieRuleRhsAndPred.sentence157_left_empty
#print axioms KCore.TieRuleRhsAndPred.consistent
#print axioms KCore.TieRuleRhsAndPred.pre_model
#print axioms KCore.TieRuleRhsAndPred.and_step
#print axioms KCore.TieRuleRhsAndPred.and_stuck
