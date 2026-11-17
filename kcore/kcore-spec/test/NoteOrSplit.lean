/-
  The tie (C14) of the reading `orSplit` on its construct fixture e7-guardors:
  `rule <k> c(a() #Or b()) => a() ... </k>`, a rule whose left side holds a disjunction, read as
  one rule per disjunct. The text is `f2-examples/mlor.kompile.kore` (as test/Guards.lean's `DevOr`
  reads it). Run from the package root: `lake env lean -j1 test/NoteOrSplit.lean`. Every statement
  is on the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree` (`attrsAgree`): the one rewrite axiom
  is read as two rules, and each rule's priority is that of the axiom it is read from.
  `account`: the function equations, the constructor sentences and the rule sentence are
  sentences of the user module, apart, with the count of the rest.

  Layer 2. Function equations (the sort predicates'): Γ's items pattern for pattern (`shape`),
  entailed for every H (`fns_entailed`). Constructor sentences: `cons_entailed`.
  The rule (sentence 99), class *weaker*: Γ holds two rule items, one per disjunct. Each is the
  sentence with `a()` (`b()`) in the place of `\or{SortExp{}}(a(), b())` and the conjunct `⌈r⌉`
  more on its left side: the sentence is the item of `\rewrites{C}(Ltext, r)` at the table of
  Γ's axiom (`rule_text0`, `rule_text1`, kernel), and every element of Γ's left side is one of
  `Ltext` (`left0`, `left1`: an application context is monotone, and a disjunct is in the
  disjunction where its elements are in Exp, which `ΓDomains` states of the values `a()` and
  `b()`, not the sentence). So the sentence with the domains entails each item
  (`rule_from_text`, `TieRuleLhs.rule_w1`, every H). `consistent` for every H.

  The expectations (C7 form (a), from sentences; a step that exists), from `Pre H` (the function
  equations as written, Γ's rule items, the families; it has a model, `pre_model`):
  `or_a`: `c(a)` steps to `a`; `or_b`: `c(b)` steps to `a`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NoteOrSplit

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/mlor.kompile.kore"
definition_of defn from "f2-examples/mlor.kompile.kore"
user_axioms U from "f2-examples/mlor.kompile.kore" module "E7-GUARDORS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E7-GUARDORS")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

theorem wf_defn : wf defn = true := by decide +kernel
theorem coreOK : c.coreOK = true := by decide +kernel
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collections, priorities. The one rewrite axiom is read as two rules, each holding the
axiom's id, and each rule's priority is the axiom's, 50. -/
theorem defs_attrsAgree : attrsAgree kore defn = true := by decide +kernel

/-! ## The function equations -/

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

theorem fnText_index : fnText.map (·.index) = [119, 127, 126, 125, 124, 131, 130, 133, 132, 129, 128, 106, 105, 118, 117, 114, 113, 116, 115, 121, 120, 123, 122, 110, 109, 112, 111, 108, 107] := by
  decide +kernel

/-- The function equations as written. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for every function equation**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat :=
  fun _ had => TiePair.entailed (shapeH H) _ (List.mem_map_of_mem had)

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

/-! ## The rule (sentence 99): W1 -/

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

/-- Γ's axiom of rule 0. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0

/-- Its parts `\rewrites{C}(L', r)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl q0_eq : TieRuleLhs.rwParts p0 = some q0

/-- The context of its left side's term around the argument of `c`, and the argument. -/
noncomputable def cut0 : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0, 0, 0, 0] (TieRuleLhs.andHead q0.2.1)).getD (.hole, .top KoreAML.R)

noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)

/-- Γ's axiom of rule 1. -/
noncomputable def p1 : Kore.Pattern := prioRuleK c r1

/-- Its parts `\rewrites{C}(L', r)`. -/
noncomputable def q1 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p1).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

-- The sort and the right side are rule 0's.
kernel_rfl q1_eq : TieRuleLhs.rwParts p1 = some (q0.1, q1.2.1, q0.2.2)

/-- The context of its left side's term around the argument of `c`, and the argument. -/
noncomputable def cut1 : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0, 0, 0, 0] (TieRuleLhs.andHead q1.2.1)).getD (.hole, .top KoreAML.R)

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩] := by kernel_rfl

/-- The two left sides have one context around the argument of `c`. -/
noncomputable def K : KoreCutCtx := cut0.1

kernel_rfl l0_eq : q0.2.1 = .and q0.1 (K.fill cut0.2 :: .top q0.1 :: (TieRuleLhs.andTail q0.2.1).drop 1)
kernel_rfl l1_eq : q1.2.1 = .and q0.1 (K.fill cut1.2 :: .top q0.1 :: (TieRuleLhs.andTail q1.2.1).drop 1)

/-- The left side as the text writes it: the argument of `c` is `\or{SortExp{}}(a(), b())`, and
no conjunct follows `\top`. -/
noncomputable def Ltext : Kore.Pattern :=
  .and q0.1 [K.fill (.or (KoreAML.srt "Exp") [cut0.2, cut1.2]), .top q0.1]

/-- The free variables of the text's form. -/
noncomputable def fT : List VarKey := (freeOf [] (.rewrites q0.1 Ltext q0.2.2)).eraseDups

/-- **The text's sentence 99 is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's axiom**,
for each of Γ's two axioms (kernel): Γ's axiom is the sentence with one disjunct in the place of
the disjunction and the conjunct `⌈r⌉` more. -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT q0.1 Ltext q0.2.2) [] = some (trS U.ax99).pat := by
  decide +kernel
theorem fT_free0 : fT.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem K_noAlias0 : K.noAlias ⟨tableOf [] p0, []⟩ = true := by decide +kernel
theorem rule_text1 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p1) fT q0.1 Ltext q0.2.2) [] = some (trS U.ax99).pat := by
  decide +kernel
theorem fT_free1 : fT.all (fun k => (freeOf [] p1).eraseDups.contains k) = true := by decide +kernel
theorem K_noAlias1 : K.noAlias ⟨tableOf [] p1, []⟩ = true := by decide +kernel

def aV : GroundTerm := .ctor 385 []
def bV : GroundTerm := .ctor 386 []

theorem names : c.symName 385 = "Lbla" ∧ c.symName 386 = "Lblb" ∧ c.symName 387 = "Lblc" ∧ c.sortName 32 = "Exp" := by
  decide +kernel

kernel_rfl a_kore : cut0.2 = aV.kore c
kernel_rfl b_kore : cut1.2 = bV.kore c
theorem a_koreH (H : HookParams) : cut0.2 = aV.kore (cH H) := a_kore
theorem b_koreH (H : HookParams) : cut1.2 = bV.kore (cH H) := b_kore
theorem a_sort (H : HookParams) : (cH H).sortOf aV = some 32 := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem b_sort (H : HookParams) : (cH H).sortOf bV = some 32 := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- A value of Exp denotes an element of Exp, in a model of the domains. -/
theorem exp_inh (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hDom : I ⊧ᴵP ΓDomains (cH H)) {v : GroundTerm} (hv : (cH H).sortOf v = some 32) {t : VarTable} {e : Valuation M}
    (a : M) (h : (tr ⟨t, []⟩ (v.kore (cH H))).interpret I e a) :
    (inhOf (trSort t (KoreAML.srt "Exp"))).interpret I e a := by
  have h1 := TieRuleLhs.ground_inh hD hDom hv (t := t) (e := e) a h
  rw [show (cH H).sortName 32 = "Exp" from names.2.2.2] at h1
  rw [trSort_srt]; exact h1

/-- Every element of Γ's left side of rule 0 is an element of the text's left side. -/
theorem left0 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hDom : I ⊧ᴵP ΓDomains (cH H)) (e : Valuation M) (a : M)
    (h : (tr ⟨tableOf [] p0, []⟩ q0.2.1).interpret I e a) : (tr ⟨tableOf [] p0, []⟩ Ltext).interpret I e a := by
  rw [l0_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ K K_noAlias0 (TieRuleLhs.sub_or_left fun a' h' => exp_inh H hD hDom (a_sort H) a' (a_koreH H ▸ h')) a (h _ (List.mem_cons_self ..))
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- Every element of Γ's left side of rule 1 is an element of the text's left side. -/
theorem left1 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hDom : I ⊧ᴵP ΓDomains (cH H)) (e : Valuation M) (a : M)
    (h : (tr ⟨tableOf [] p1, []⟩ q1.2.1).interpret I e a) : (tr ⟨tableOf [] p1, []⟩ Ltext).interpret I e a := by
  rw [l1_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ K K_noAlias1 (TieRuleLhs.sub_or_right fun a' h' => exp_inh H hD hDom (b_sort H) a' (b_koreH H ▸ h')) a (h _ (List.mem_cons_self ..))
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- **W1 for the rule, and the converse for `ruleItems`**: each of Γ's two rule items is a
consequence of the text's sentence 99 with the domains (a value of Exp is an element of Exp:
`\or{SortExp{}}` holds the elements of its disjuncts that are in Exp), for every H. -/
theorem rule_from_text (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), (TiePair.Texts [(trS U.ax99).pat] ∪ ΓDomains (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hT : I ⊧ᴵ (trS U.ax99).pat := hI _ (Or.inl (Or.inl (List.mem_singleton_self _)))
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  rcases List.mem_cons.mp hit with rfl | hit
  · exact TieRuleLhs.rule_w1 hD q0_eq rule_text0 fT_free0 hT fun e _ _ a ha => left0 H hD hDom e a ha
  · rw [List.mem_singleton.mp hit]
    exact TieRuleLhs.rule_w1 hD q1_eq rule_text1 fT_free1 hT fun e _ _ a ha => left1 H hD hDom e a ha

/-! ## The account -/

noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ consText.map (·.index) ++ [99]

/-- **The account**: the function equations, the constructor sentences and the rule sentences are
sentences of the user module, each once and none in two classes, with the sizes of the three
classes and of the rest (not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length, consText.length, [99].length, U.all.length - tiedIdx.length) = (29, 32, 1, 84) := by decide +kernel

/-! ## The facts the deciders leave -/

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok

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

/-! ## The expectations (C7 form (a)) -/

/-- **The premises of the derivations**: every function equation as written, Γ's rule items (the
reading of the rule sentence 99, each a consequence of it by `rule_from_text`), and the families. -/
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

/-- A step the rules' check accepts on the data, as a consequence of `Pre H`: `⟦x⟧ → •⟦y⟧`. -/
theorem step_from {x y : Config c} (h : c.rules.any (fun r => Cert.checkStep c 50 r x.val y.val) = true) (H : HookParams) :
    Pre H ⊧ (den (cH H) x.val ⇒ KoreAML.sNext (den (cH H) y.val)) :=
  TiePair.cut (shapeH H) (sound_at_step _ (coreOKH H) (hrcH H) _ _ (TieRuleLhs.step_everyH hok hsr hmr noRaw h H))

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

def CA : Config c := ⟨cfg (.ctor 387 [.ctor 385 []]), by decide +kernel⟩
def CB : Config c := ⟨cfg (.ctor 387 [.ctor 386 []]), by decide +kernel⟩
def A : Config c := ⟨cfg (.ctor 385 []), by decide +kernel⟩

/-- **`c(a)` steps to `a`, derived from `Pre`**, for every H. -/
theorem or_a (H : HookParams) : Pre H ⊧ (den (cH H) CA.val ⇒ KoreAML.sNext (den (cH H) A.val)) :=
  step_from (x := CA) (y := A) (by decide +kernel) H

/-- **`c(b)` steps to `a`, derived from `Pre`**, for every H. -/
theorem or_b (H : HookParams) : Pre H ⊧ (den (cH H) CB.val ⇒ KoreAML.sNext (den (cH H) A.val)) :=
  step_from (x := CB) (y := A) (by decide +kernel) H

end KCore.NoteOrSplit

#print axioms KCore.NoteOrSplit.wf_defn
#print axioms KCore.NoteOrSplit.defs_attrsAgree
#print axioms KCore.NoteOrSplit.account
#print axioms KCore.NoteOrSplit.shape
#print axioms KCore.NoteOrSplit.fns_entailed
#print axioms KCore.NoteOrSplit.cons_entailed
#print axioms KCore.NoteOrSplit.rule_text0
#print axioms KCore.NoteOrSplit.rule_text1
#print axioms KCore.NoteOrSplit.rule_from_text
#print axioms KCore.NoteOrSplit.consistent
#print axioms KCore.NoteOrSplit.pre_model
#print axioms KCore.NoteOrSplit.or_a
#print axioms KCore.NoteOrSplit.or_b
