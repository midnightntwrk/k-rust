/-
  The tie (C14) of the reading `predicateAtBool` on its construct fixture e3-ml-req-top:
  `rule <k> go(_) => done ... </k> requires #Top` beside
  `rule <k> go(_) => other ... </k> [priority(60)]`: a `requires` that is a predicate at sort Bool,
  equated with `true`, read as the `requires` false. The text is
  `f2-examples/e3-ml-req-top.kompile.kore`. Run from the package root:
  `lake env lean -j1 test/NotePredBoolTop.lean`. Every statement is on the literal `defn`, for every
  interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree`; `account`: the function equations,
  the constructor sentences and the two rule sentences are sentences of the user module, apart,
  with the count of the rest.

  Layer 2. Function equations (the sort predicates'): Γ's items pattern for pattern (`shape`),
  entailed for every H (`fns_entailed`). Constructor sentences: `cons_entailed`.
  The rules. Sentence 158 (priority 60), class *weaker*: Γ's item is the sentence with the
  negation of rule 0's left side and `⌈r⌉` more on its left side (`rule_text1`, `left1`).
  Sentence 157: the sentence's `requires` is
  `\equals{Bool, C}(\top{SortBool{}}(), true)` and Γ's item's is
  `\equals{Bool, C}(false, true)` (`rule_text0`: the sentence is the item of the text's left side
  at the table of Γ's axiom, kernel). Γ's left side holds nothing in a model of definedness,
  `ΓSig` and `ΓDomains` (`left0_empty`: `false` and `true` are two elements of Bool), so Γ's item
  holds there whatever the sentence says (`rule_from_text`, W1). What the reading claims is the
  other direction, that the sentence's left side is empty too. Here it is, at every valuation and
  not only at values (`ltext0_empty`): `\top{SortBool{}}()` is the sort Bool (`topBool_const`), which holds `false` as well as `true`. So Γ entails the
  sentence for every H (`rule157_entailed`), and at values in particular (`rule157_at_values`):
  on this text the item and the sentence both hold in every model of Γ, each with an empty left
  side.
  `consistent` for every H.

  The expectation (C7 form (a), through the reading; family the priority premise), from `Pre H`
  (the function equations as written, Γ's rule items, the families; it has a model,
  `pre_model`): `top_other`: `go(1)` steps to `other`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NotePredBoolTop

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-req-top.kompile.kore"
definition_of defn from "f2-examples/e3-ml-req-top.kompile.kore"
user_axioms U from "f2-examples/e3-ml-req-top.kompile.kore" module "E3-ML-REQ-TOP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-REQ-TOP")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The attributes of the text agree with `defn` (`attrsAgree`). -/
theorem defs_attrsAgree : attrsAgree kore defn = true := by decide +kernel

/-! ## The function equations -/

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

theorem fnText_index : fnText.map (·.index) = [231, 239, 238, 237, 236, 243, 242, 245, 244, 241, 240, 218, 217, 230, 229, 226, 225, 228, 227, 233, 232, 235, 234, 222, 221, 224, 223, 220, 219] := by
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

/-! ## The rules (sentences 157 and 158): W1 -/

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

kernel_rfl q1_eq : TieRuleLhs.rwParts p1 = some q1

/-- The context of its left side's term around the argument of `c`, and the argument. -/
noncomputable def cut1 : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0, 0, 0, 0] (TieRuleLhs.andHead q1.2.1)).getD (.hole, .top KoreAML.R)

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩] := by kernel_rfl

theorem names : c.symName 385 = "Lbldone" ∧ c.symName 386 = "Lblgo" ∧ c.symName 387 = "Lblother" ∧ c.sortName 32 = "Exp" := by
  decide +kernel

-- Γ's left side of rule 0: the term, the `requires` false, then `⌈r⌉`.
kernel_rfl l0_eq : q0.2.1 = .and q0.1 (TieRuleLhs.andHead q0.2.1 :: TieRhs.ensFalse q0.1 :: (TieRuleLhs.andTail q0.2.1).drop 1)

/-- The left side of rule 0 as the text writes it: the `requires` is `\top{SortBool{}}()`, equated
with `true`, and no conjunct follows. -/
noncomputable def Ltext0 : Kore.Pattern :=
  .and q0.1 [TieRuleLhs.andHead q0.2.1,
    .equals (KoreAML.srt "Bool") q0.1 (.top (KoreAML.srt "Bool")) (.dv (KoreAML.srt "Bool") "true")]

noncomputable def fT0 : List VarKey := (freeOf [] (.rewrites q0.1 Ltext0 q0.2.2)).eraseDups

-- Γ's left side of rule 1: the term, `\top`, then the negation of rule 0's left side and `⌈r⌉`.
kernel_rfl l1_eq : q1.2.1 = .and q1.1 (TieRuleLhs.andHead q1.2.1 :: .top q1.1 :: (TieRuleLhs.andTail q1.2.1).drop 1)

theorem l1_more : ((TieRuleLhs.andTail q1.2.1).drop 1).length = 2 := by decide +kernel

/-- The left side of rule 1 as the text writes it: no conjunct follows `\top`. -/
noncomputable def Ltext1 : Kore.Pattern := .and q1.1 [TieRuleLhs.andHead q1.2.1, .top q1.1]

noncomputable def fT1 : List VarKey := (freeOf [] (.rewrites q1.1 Ltext1 q1.2.2)).eraseDups

/-- **Each rule sentence is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's axiom**
(kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 q0.2.2) [] = some (trS U.ax157).pat := by
  decide +kernel
theorem fT_free0 : fT0.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem rule_text1 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p1) fT1 q1.1 Ltext1 q1.2.2) [] = some (trS U.ax158).pat := by
  decide +kernel
theorem fT_free1 : fT1.all (fun k => (freeOf [] p1).eraseDups.contains k) = true := by decide +kernel

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

/-- **Γ's left side of rule 0 holds nothing** in a model of definedness, the signature and the
domains: its `requires` is `false = true`, and the values `false` and `true` of Bool are two
elements. -/
theorem left0_empty (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (hDom : I ⊧ᴵP ΓDomains (cH H)) (e : Valuation M) (a : M) :
    ¬ (tr ⟨tableOf [] p0, []⟩ q0.2.1).interpret I e a := by
  intro h
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  rw [l0_eq, interp_and (List.cons_ne_nil _ _)] at h
  exact TieRhs.ensFalse_empty hD hSig hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H)
    (by rw [C_eq, trSort_srt]; exact hσ1) hσ2 a (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

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

/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's two rule items is a
consequence of its sentence with the signature and the domains, for every H. Rule 1's item is
sentence 158 with two conjuncts more on its left side. Rule 0's item holds in every model of
definedness, the signature and the domains, whatever sentence 157 says: its left side is empty
there (`left0_empty`). -/
theorem rule_from_text (H : HookParams) :
    ∀ it ∈ ruleItems (cH H),
      (TiePair.Texts [(trS U.ax157).pat, (trS U.ax158).pat] ∪ ΓSig (cH H) ∪ ΓDomains (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inl (Or.inr hφ))
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  rcases List.mem_cons.mp hit with rfl | hit
  · exact TieRuleLhs.rule_w1 hD q0_eq rule_text0 fT_free0
      (hI _ (Or.inl (Or.inl (Or.inl (List.mem_cons_self ..)))))
      fun e _ _ a ha => absurd ha (left0_empty H hD hSig hDom e a)
  · rw [List.mem_singleton.mp hit]
    exact TieRuleLhs.rule_w1 hD q1_eq rule_text1 fT_free1
      (hI _ (Or.inl (Or.inl (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
      fun e _ _ a ha => left1 e a ha

/-! ## Sentence 157 (entailed, for every H) -/

/-- Sentence 157 is the item of the text's left side at the table of Γ's axiom. -/
theorem trS157 : (trS U.ax157).pat = TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 q0.2.2 := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **`\top{SortBool{}}()` holds the same of every two elements of Bool**: it is the sort Bool. -/
theorem topBool_const (hD : DefOK I) {t : VarTable} {σB : M} {e : Valuation M}
    (hSB : ∀ a, (trSort t (KoreAML.srt "Bool")).interpret I e a ↔ a = σB) (x y : M) (hx : Inh I σB x) (hy : Inh I σB y) :
    (tr ⟨t, []⟩ (.top (KoreAML.srt "Bool"))).interpret I e x ↔ (tr ⟨t, []⟩ (.top (KoreAML.srt "Bool"))).interpret I e y := by
  have hT : tr ⟨t, []⟩ (.top (KoreAML.srt "Bool")) = sTop (trSort t (KoreAML.srt "Bool")) := by rw [tr]
  rw [hT, interp_sTop hD (by rw [trSort_srt]; rfl), interp_sTop hD (by rw [trSort_srt]; rfl),
    interp_inhOf_of hSB, interp_inhOf_of hSB]
  exact ⟨fun _ => hy, fun _ => hx⟩

end

/-- **The text's left side holds nothing**, at every valuation, in a model of definedness, the
signature and the domains: `\top{SortBool{}}()` is the sort Bool (`topBool_const`), so it holds the same of `false` and of `true`, two
elements of Bool, and is not `{true}` (`TieReqBool.eqTrue_empty`). -/
theorem ltext0_empty (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (hDom : I ⊧ᴵP ΓDomains (cH H)) (e : Valuation M) (a : M) :
    ¬ (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a := by
  intro h
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  unfold Ltext0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  exact TieReqBool.eqTrue_empty hD hSig hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H)
    (by rw [C_eq, trSort_srt]; exact hσ1) hσ2
    (fun _ hSB _ x y hx hy => topBool_const hD hSB x y hx hy) a
    (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- **Γ entails sentence 157** (the reading's direction), for every H: its left side holds nothing
at any valuation (`ltext0_empty`), so the sentence holds in every model of Γ. -/
theorem rule157_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax157).pat := by
  intro M _ I hI e m
  rw [trS157]
  exact TieReqBool.ruleItem_of_empty (defOK hI)
    (ltext0_empty H (defOK hI) (fun φ hφ => sat_sig hI hφ) (fun φ hφ => sat_dom hI hφ) e) m

/-- **Sentence 157 is entailed at values** (`EntailsAtValues`), for every H: the instance of
`rule157_entailed` at the valuations that send its variables to values. -/
theorem rule157_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax157 (trS U.ax157).pat :=
  fun _ _ _ hI e _ m => rule157_entailed H hI e m

/-! ## The account -/

noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ consText.map (·.index) ++ [157, 158]

/-- **The account**: the function equations, the constructor sentences and the rule sentences are
sentences of the user module, each once and none in two classes, with the sizes of the three
classes and of the rest (not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length, consText.length, [157, 158].length, U.all.length - tiedIdx.length) = (29, 32, 2, 202) := by decide +kernel

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
reading of the rule sentences 157 and 158, each a consequence of its sentence with `ΓSig` and `ΓDomains` by `rule_from_text`), and the families. -/
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

def Go1 : Config c := ⟨cfg (.ctor 386 [.dv Srt.int (.int 1)]), by decide +kernel⟩
def Other : Config c := ⟨cfg (.ctor 387 []), by decide +kernel⟩

/-- **`go(1)` steps to `other`, derived from `Pre`**, for every H. -/
theorem top_other (H : HookParams) : Pre H ⊧ (den (cH H) Go1.val ⇒ KoreAML.sNext (den (cH H) Other.val)) :=
  step_from (x := Go1) (y := Other) (by decide +kernel) H

end KCore.NotePredBoolTop

#print axioms KCore.NotePredBoolTop.wf_defn
#print axioms KCore.NotePredBoolTop.defs_attrsAgree
#print axioms KCore.NotePredBoolTop.account
#print axioms KCore.NotePredBoolTop.shape
#print axioms KCore.NotePredBoolTop.fns_entailed
#print axioms KCore.NotePredBoolTop.cons_entailed
#print axioms KCore.NotePredBoolTop.rule_text0
#print axioms KCore.NotePredBoolTop.rule_text1
#print axioms KCore.NotePredBoolTop.left0_empty
#print axioms KCore.NotePredBoolTop.rule_from_text
#print axioms KCore.NotePredBoolTop.ltext0_empty
#print axioms KCore.NotePredBoolTop.rule157_entailed
#print axioms KCore.NotePredBoolTop.rule157_at_values
#print axioms KCore.NotePredBoolTop.consistent
#print axioms KCore.NotePredBoolTop.pre_model
#print axioms KCore.NotePredBoolTop.top_other
