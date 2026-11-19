/-
  The tie (C14) of the reading `ruleRightDefined` on its construct fixture e3-ml-rule-lhs-or:
  `rule <k> d(X, a()) #Or d(a(), X) => X ... </k>`, a rule whose left side holds a disjunction whose
  disjuncts hold the variable the right side reads, read as one rule per disjunct (`orSplit`), each
  with the premise `⌈rhs ∧ ens⌉` (`ruleRightDefined`) that the text does not write. The text is
  `f2-examples/mlorvar.kompile.kore`, the kompiled text that
  `test/constructs/fixtures/e3-ml-rule-lhs-or/kompile.txt` records (sha256 4ef14819…), with its paths
  restored. Run from the package root: `lake env lean -j1 test/NoteOrVar.lean`. Every statement is
  on the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree` (`attrsAgree`): the one rewrite axiom
  is read as two rules, and each rule's priority is that of the axiom it is read from.
  `account`: the function equations, the constructor sentences and the rule sentence are
  sentences of the user module, apart, with the count of the rest.

  Layer 2. Function equations (the sort predicates'): Γ's items pattern for pattern (`shape`),
  entailed for every H (`fns_entailed`). Constructor sentences: `cons_entailed`.
  The rule (sentence 104), class *weaker*: Γ holds two rule items, one per disjunct, each with the
  conjunct `⌈r⌉` (`ruleRightDefined`) more on its left side. The sentence is the item of
  `\rewrites{C}(Ltext, r)` at the table of Γ's axiom (`rule_text0`, `rule_text1`, kernel: the
  variables have one index on both sides), and every element of Γ's left side is one of `Ltext`
  (`left0`, `left1`): an application context is monotone, the conjunct `⌈r⌉` only narrows, and a
  disjunct is in the disjunction where its elements are in Exp, which the arity of `d` (`ΓSig`:
  `d ⟦Exp⟧ ⟦Exp⟧ ⊆ ⟦Exp⟧`) gives from the guard of X and from `a()`, a value of Exp (`ΓDomains`), not
  the sentence (`d_inh`). So the sentence with the signature and the domains entails each item
  (`rule_from_text`, `TieRuleLhs.rule_w1`, every H). `consistent` for every H.

  The expectations (C7 form (a), from sentences; a step that exists), from `Pre H` (the function
  equations as written, Γ's rule items, the families; it has a model, `pre_model`):
  `or_ba`: `d(b, a)` steps to `b`; `or_ab`: `d(a, b)` steps to `b`; `or_aa`: `d(a, a)` steps to `a`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NoteOrVar

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/mlorvar.kompile.kore"
definition_of defn from "f2-examples/mlorvar.kompile.kore"
user_axioms U from "f2-examples/mlorvar.kompile.kore" module "E3-ML-RULE-LHS-OR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-RULE-LHS-OR")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collections, priorities. The one rewrite axiom is read as two rules, each holding the
axiom's id, and each rule's priority is the axiom's, 50. -/
theorem defs_attrsAgree : attrsAgree kore defn = true := by decide +kernel

/-! ## The function equations -/

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

theorem fnText_index : fnText.map (·.index) = [124, 132, 131, 130, 129, 136, 135, 138, 137, 134, 133, 111, 110, 123, 122, 119, 118, 121, 120, 126, 125, 128, 127, 115, 114, 117, 116, 113, 112] := by
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

/-! ## The rule (sentence 104): W1 -/

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

/-- Γ's axiom of rule 0. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0

/-- Its parts `\rewrites{C}(L', r)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl q0_eq : TieRuleLhs.rwParts p0 = some q0

/-- The context of its left side's term around the argument of `c`, and the argument. -/
noncomputable def cut0 : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0, 0, 0] (TieRuleLhs.andHead q0.2.1)).getD (.hole, .top KoreAML.R)

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
  (TieRuleLhs.cutAt [0, 0, 0, 0] (TieRuleLhs.andHead q1.2.1)).getD (.hole, .top KoreAML.R)

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

/-- **The text's sentence 104 is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's axiom**,
for each of Γ's two axioms (kernel): Γ's axiom is the sentence with one disjunct in the place of
the disjunction and the conjunct `⌈r⌉` more. -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT q0.1 Ltext q0.2.2) [] = some (trS U.ax104).pat := by
  decide +kernel
theorem fT_free0 : fT.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem K_noAlias0 : K.noAlias ⟨tableOf [] p0, []⟩ = true := by decide +kernel
theorem rule_text1 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p1) fT q0.1 Ltext q0.2.2) [] = some (trS U.ax104).pat := by
  decide +kernel
theorem fT_free1 : fT.all (fun k => (freeOf [] p1).eraseDups.contains k) = true := by decide +kernel
theorem K_noAlias1 : K.noAlias ⟨tableOf [] p1, []⟩ = true := by decide +kernel

def aV : GroundTerm := .ctor 385 []

theorem names : c.symName 385 = "Lbla" ∧ c.symName 386 = "Lblb" ∧ c.symName 387 = "Lblc" ∧
    c.symName 388 = "Lbld" ∧ c.sortName 32 = "Exp" := by
  decide +kernel

/-- The variable X of both of Γ's rules (index 0 of their tables). -/
noncomputable def x0 : Kore.EVar := KoreAML.evar "VarV0" (KoreAML.srt "Exp")

-- The two disjuncts as Γ writes them: `d(X, a())` and `d(a(), X)`, applications of the
-- constructor `d` (388) and `a` (385) by `symApp`.
kernel_rfl d0_eq : cut0.2 = symApp c 388 [.var (.evar x0), symApp c 385 []]
kernel_rfl d1_eq : cut1.2 = symApp c 388 [symApp c 385 [], .var (.evar x0)]
kernel_rfl a_kore : symApp c 385 [] = aV.kore c

theorem a_sort (H : HookParams) : (cH H).sortOf aV = some 32 := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- `d`'s signature. -/
def kd : CtorSig := ⟨388, [32, 32], 32⟩

theorem kd_mem : kd ∈ kernelSyms c := by decide +kernel
theorem noInst_d : instDecode? (c.symName 388) = none := by decide +kernel

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- **The arity of `d` from `ΓSig`**: what `d` builds from two elements of Exp is in Exp. -/
theorem d_arity {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {e : Valuation M} {a : M} (ha : (symHead c 388).interpret I e a)
    {b0 b1 m : M} (h0 : InS I "Exp" b0) (h1 : InS I "Exp" b1) (hm : AppE I a [b0, b1] m) :
    InS I "Exp" m := by
  have hit : I ⊧ᴵ (symArityItem c kd).pat := hS _ (Or.inl (Or.inl ⟨_, sig_arity kd_mem, rfl⟩))
  rw [symArityItem_noInst (k := kd) noInst_d, show kd.name = 388 from rfl] at hit
  rw [symHead_noInst (c := c) (f := 388) noInst_d] at ha
  unfold KoreAML.arityItem at hit
  dsimp only [KoreAML.paramTable, List.map_nil] at hit
  have hinc := (KoreAML.interp_included hD).mp (hit KoreAML.val0 default) m
  unfold srtOf at hinc
  rw [trSort_srt] at hinc
  have hres : c.sortName kd.result = "Exp" := names.2.2.2.2
  rw [hres] at hinc
  apply (inS_iff (I := I) (s := "Exp") (a := m) KoreAML.val0).mp
  apply hinc
  rw [interp_appList]
  refine ⟨a, ((Closed.sym _).interp e KoreAML.val0 a).mp ha, [b0, b1], ?_, hm⟩
  have hn : c.sortName 32 = "Exp" := names.2.2.2.2
  simp only [kd, List.map_cons, List.map_nil, srtOf, trSort_srt, hn]
  exact .cons ((inS_iff _).mpr h0) (.cons ((inS_iff _).mpr h1) .nil)

/-- A value of Exp denotes an element of Exp, in a model of the domains. -/
theorem a_inh (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hDom : I ⊧ᴵP ΓDomains (cH H)) {t : VarTable} {e : Valuation M}
    (b : M) (h : (tr ⟨t, []⟩ (symApp c 385 [])).interpret I e b) : InS I "Exp" b := by
  rw [a_kore] at h
  have h1 := TieRuleLhs.ground_inh hD hDom (a_sort H) (t := t) (e := e) b h
  rw [show (cH H).sortName 32 = "Exp" from names.2.2.2.2] at h1
  exact (inS_iff _).mp h1

/-- The guard of X puts its value in Exp. -/
theorem x_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {t : VarTable}
    {e : Valuation M} {m0 : M} (hg : (guardOf t (evarKey x0)).interpret I e m0)
    (b : M) (h : (tr ⟨t, []⟩ (.var (.evar x0))).interpret I e b) : InS I "Exp" b := by
  have h1 := (TieRuleLhs.guard_evarKey hD).mp hg
  simp only [tr] at h
  rw [interp_evar] at h
  rw [h]
  have : x0.sort = KoreAML.srt "Exp" := rfl
  rw [this, trSort_srt] at h1
  exact (inS_iff _).mp h1

/-- **`d` at two patterns whose elements are in Exp is in Exp** (`d_arity`). -/
theorem d_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {p q : Kore.Pattern}
    (hp : ∀ b, (tr ⟨t, []⟩ p).interpret I e b → InS I "Exp" b)
    (hq : ∀ b, (tr ⟨t, []⟩ q).interpret I e b → InS I "Exp" b) (m : M)
    (h : (tr ⟨t, []⟩ (symApp c 388 [p, q])).interpret I e m) :
    (inhOf (trSort t (KoreAML.srt "Exp"))).interpret I e m := by
  rw [tr_symApp, trArgs_appList, interp_appList] at h
  obtain ⟨a, ha, bs, hbs, hm⟩ := h
  simp only [List.map_cons, List.map_nil] at hbs
  cases hbs with
  | cons hb0 hbs =>
    cases hbs with
    | cons hb1 hbs =>
      cases hbs
      rw [trSort_srt]
      exact (inS_iff _).mpr (d_arity hD hS ha (hp _ hb0) (hq _ hb1) hm)

theorem x0_free0 : evarKey x0 ∈ (freeOf [] p0).eraseDups := by decide +kernel
theorem x0_free1 : evarKey x0 ∈ (freeOf [] p1).eraseDups := by decide +kernel

/-- Every element of Γ's left side of rule 0 is an element of the text's left side: its first
conjunct with `d(X, a())` in the place of the disjunction is in the first conjunct of `Ltext`, and
its conjunct `⌈r⌉` is not asked. -/
theorem left0 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) (hDom : I ⊧ᴵP ΓDomains (cH H)) (e : Valuation M) (m0 a : M)
    (hg : ∀ k ∈ (freeOf [] p0).eraseDups, (guardOf (tableOf [] p0) k).interpret I e m0)
    (h : (tr ⟨tableOf [] p0, []⟩ q0.2.1).interpret I e a) : (tr ⟨tableOf [] p0, []⟩ Ltext).interpret I e a := by
  rw [l0_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ K K_noAlias0 (TieRuleLhs.sub_or_left fun a' h' => ?_) a (h _ (List.mem_cons_self ..))
    rw [d0_eq] at h'
    exact d_inh hD hS (fun b hb => x_inh hD (hg _ x0_free0) b hb) (fun b hb => a_inh H hD hDom b hb) a' h'
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- Every element of Γ's left side of rule 1 is an element of the text's left side, as `left0`
with `d(a(), X)`. -/
theorem left1 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) (hDom : I ⊧ᴵP ΓDomains (cH H)) (e : Valuation M) (m0 a : M)
    (hg : ∀ k ∈ (freeOf [] p1).eraseDups, (guardOf (tableOf [] p1) k).interpret I e m0)
    (h : (tr ⟨tableOf [] p1, []⟩ q1.2.1).interpret I e a) : (tr ⟨tableOf [] p1, []⟩ Ltext).interpret I e a := by
  rw [l1_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ K K_noAlias1 (TieRuleLhs.sub_or_right fun a' h' => ?_) a (h _ (List.mem_cons_self ..))
    rw [d1_eq] at h'
    exact d_inh hD hS (fun b hb => a_inh H hD hDom b hb) (fun b hb => x_inh hD (hg _ x0_free1) b hb) a' h'
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- **W1 for the rule, and the converse for `ruleItems`**: each of Γ's two rule items, with its
premise `⌈r⌉`, is a consequence of the text's sentence 104 with the signature and the domains (the
arity of `d` and a value of Exp put the disjuncts' elements in Exp: `\or{SortExp{}}` holds the
elements of its disjuncts that are in Exp), for every H. -/
theorem rule_from_text (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), (TiePair.Texts [(trS U.ax104).pat] ∪ ΓSig (cH H) ∪ ΓDomains (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hT : I ⊧ᴵ (trS U.ax104).pat := hI _ (Or.inl (Or.inl (Or.inl (List.mem_singleton_self _))))
  have hS : I ⊧ᴵP ΓSig c := fun φ hφ => hI φ (Or.inl (Or.inr (by
    unfold ΓSig at hφ ⊢; rw [sigItems_withHooks]; exact hφ)))
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  rcases List.mem_cons.mp hit with rfl | hit
  · exact TieRuleLhs.rule_w1 hD q0_eq rule_text0 fT_free0 hT fun e m0 hg a ha => left0 H hD hS hDom e m0 a hg ha
  · rw [List.mem_singleton.mp hit]
    exact TieRuleLhs.rule_w1 hD q1_eq rule_text1 fT_free1 hT fun e m0 hg a ha => left1 H hD hS hDom e m0 a hg ha

/-! ## The account -/

noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ consText.map (·.index) ++ [104]

/-- **The account**: the function equations, the constructor sentences and the rule sentences are
sentences of the user module, each once and none in two classes, with the sizes of the three
classes and of the rest (not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length, consText.length, [104].length, U.all.length - tiedIdx.length) = (29, 37, 1, 84) := by decide +kernel

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
reading of the rule sentence 104, each a consequence of it by `rule_from_text`), and the families. -/
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

def DBA : Config c := ⟨cfg (.ctor 388 [.ctor 386 [], .ctor 385 []]), by decide +kernel⟩
def DAB : Config c := ⟨cfg (.ctor 388 [.ctor 385 [], .ctor 386 []]), by decide +kernel⟩
def DAA : Config c := ⟨cfg (.ctor 388 [.ctor 385 [], .ctor 385 []]), by decide +kernel⟩
def A : Config c := ⟨cfg (.ctor 385 []), by decide +kernel⟩
def B : Config c := ⟨cfg (.ctor 386 []), by decide +kernel⟩

/-- **`d(b, a)` steps to `b`, derived from `Pre`**, for every H (rule 0, X the value `b`). -/
theorem or_ba (H : HookParams) : Pre H ⊧ (den (cH H) DBA.val ⇒ KoreAML.sNext (den (cH H) B.val)) :=
  step_from (x := DBA) (y := B) (by decide +kernel) H

/-- **`d(a, b)` steps to `b`, derived from `Pre`**, for every H (rule 1). -/
theorem or_ab (H : HookParams) : Pre H ⊧ (den (cH H) DAB.val ⇒ KoreAML.sNext (den (cH H) B.val)) :=
  step_from (x := DAB) (y := B) (by decide +kernel) H

/-- **`d(a, a)` steps to `a`, derived from `Pre`**, for every H (either rule). -/
theorem or_aa (H : HookParams) : Pre H ⊧ (den (cH H) DAA.val ⇒ KoreAML.sNext (den (cH H) A.val)) :=
  step_from (x := DAA) (y := A) (by decide +kernel) H

end KCore.NoteOrVar

#print axioms KCore.NoteOrVar.wf_defn
#print axioms KCore.NoteOrVar.defs_attrsAgree
#print axioms KCore.NoteOrVar.account
#print axioms KCore.NoteOrVar.shape
#print axioms KCore.NoteOrVar.fns_entailed
#print axioms KCore.NoteOrVar.cons_entailed
#print axioms KCore.NoteOrVar.rule_text0
#print axioms KCore.NoteOrVar.rule_text1
#print axioms KCore.NoteOrVar.rule_from_text
#print axioms KCore.NoteOrVar.consistent
#print axioms KCore.NoteOrVar.pre_model
#print axioms KCore.NoteOrVar.d_inh
#print axioms KCore.NoteOrVar.or_ba
#print axioms KCore.NoteOrVar.or_ab
#print axioms KCore.NoteOrVar.or_aa
