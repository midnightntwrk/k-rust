/-
  The tie (C14) of the reading `predicateAtBool` on its construct fixture e3-ml-req-ceil:
  `rule <k> go(X) => done ... </k> requires #Ceil(1 /Int X)` beside
  `rule <k> go(_) => other ... </k> [priority(60)]`: a `requires` that is a predicate at sort Bool,
  equated with `true`, read as the `requires` false. The text is
  `f2-examples/mlceil.kompile.kore` (as test/Guards.lean's `DevCeil` reads it). Run from the
  package root: `lake env lean -j1 test/NotePredBool.lean`. Every statement is on the literal
  `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree`; `account`: the function equations,
  the constructor sentences and the two rule sentences are sentences of the user module, apart,
  with the count of the rest.

  Layer 2. Function equations (the sort predicates'): Γ's items pattern for pattern (`shape`),
  entailed for every H (`fns_entailed`). Constructor sentences: `cons_entailed`.
  The rules, class *weaker*. Sentence 158 (priority 60): Γ's item is the sentence with the
  negation of rule 0's left side and `⌈r⌉` more on its left side (`rule_text1`, `left1`).
  Sentence 157: the sentence's `requires` is
  `\equals{Bool, C}(\ceil{Int, Bool}(1 /Int X), true)` and Γ's item's is
  `\equals{Bool, C}(false, true)` (`rule_text0`: the sentence is the item of the text's left side
  at the table of Γ's axiom, kernel). Γ's left side holds nothing in a model of definedness and
  `ΓSig` in which five other sentences of the text and Int's G-nonempty item hold (`left0_empty`;
  `ruleAux`: 138, 133, 147, 49 and 46, which at an element of Int state that `false` and `true` are
  two elements of Bool, `lit_sents`, `TieReqBool.boolLits_of_text_sig`; `ruleSigAux`, an item of the
  text's signature, `ruleSigAux_text`), so Γ's item holds there whatever sentence 157 says
  (`rule_from_text_aux`, W1: Γ's rule items from the text, no item of `ΓDomains` among the
  premises). That statement names sentence 157 and does not use what it states; rule 1's item
  follows from sentence 158 alone (`left1`). What ties sentence 157 is the other direction
  (`rule157_entailed`), that the sentence's left side is empty too. It is, at every valuation. Where
  X's guard fails the sentence's item holds, its guards being its premise. Where X is an element of
  Int, value or not, the elements of `1 /Int X` are elements of Int by the arity items of `_/Int_`
  and of the literal `1` in `ΓSig` (`TieFRSig.sig_of_core`), so `\ceil{SortInt{}, SortBool{}}(1 /Int
  X)` is every element of Bool or none (`TieReqBool.ceil_const`), and neither is `{true}` where
  `false` and `true` are two elements of Bool (`ltext0_empty_int`); the graph of `/Int` is not read.
  `rule157_at_values` is that direction at values, proved here from the graph (`ltext0_empty`: at a
  value n of X, `1 /Int n` denotes the element of an integer or nothing, `LibEv.den_val`). This
  direction is over Γ, whose `ΓDomains` gives `false` and `true` as two elements of Bool.
  `consistent` for every H.

  The expectation (C7 form (a), through the reading; family the priority premise), from `Pre H`
  (the function equations as written, Γ's rule items, the families; it has a model,
  `pre_model`): `ceil_other`: `go(1)` steps to `other`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

deriving instance DecidableEq for KoreAML.SortDecl

namespace KCore.NotePredBool

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/mlceil.kompile.kore"
definition_of defn from "f2-examples/mlceil.kompile.kore"
user_axioms U from "f2-examples/mlceil.kompile.kore" module "E3-ML-REQ-CEIL"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-REQ-CEIL")

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

/-- The variable of rule 0 at the argument of `go`. -/
noncomputable def x0 : Kore.EVar := (TieRuleLhs.evarOf cut0.2).getD (KoreAML.evar "X" KoreAML.R)

theorem x0_sort : x0.sort = KoreAML.srt "Int" := by decide +kernel

-- Γ's left side of rule 0: the term, the `requires` false, then `⌈r⌉`.
kernel_rfl l0_eq : q0.2.1 = .and q0.1 (TieRuleLhs.andHead q0.2.1 :: TieRhs.ensFalse q0.1 :: (TieRuleLhs.andTail q0.2.1).drop 1)

/-- The left side of rule 0 as the text writes it: the `requires` is the predicate
`\ceil{SortInt{}, SortBool{}}(1 /Int V0)` at Bool, equated with `true`, and no conjunct follows. -/
noncomputable def Ltext0 : Kore.Pattern :=
  .and q0.1 [TieRuleLhs.andHead q0.2.1,
    .equals (KoreAML.srt "Bool") q0.1
      (.ceil (KoreAML.srt "Int") (KoreAML.srt "Bool")
        (.app ⟨⟨"Lbl'UndsSlsh'Int'Unds'"⟩⟩ [] [.dv (KoreAML.srt "Int") "1", .var (.evar x0)]))
      (.dv (KoreAML.srt "Bool") "true")]

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

/-! ## The text's Bool literals

Five sentences of the text, with Int's sort declaration, state that `false` and `true` each denote
one element of Bool and that the two differ (`TieReqBool.boolLits_of_text_sig`):
`INT-KORE.eq-int-true-left` (138), `{K1 ==Int K2 #Equals true} = {K1 #Equals K2}`;
`INT-KORE.neq-int-false-left` (133), `{K1 =/=Int K2 #Equals false} = {K1 #Equals K2}`;
`INT-KORE.eq-int-false-rigth` (147), `{false #Equals K1 ==Int K2} = #Not({K1 #Equals K2})`; and the
functional sentences of `_==Int_` (49) and `_=/=Int_` (46). The three are over element variables
`K1`, `K2` of Int and have no condition; they are read at an element of Int given to both. Nothing
here reads a hook's graph or a value item of `ΓDomains`. -/

/-- **Each of the five is the library's pattern of its sentence** (kernel). -/
theorem lit_sents :
    (trS U.ax138).pat = TieReqBool.sentPat TieReqBool.eqIntTrueLeftAx ∧
    (trS U.ax133).pat = TieReqBool.sentPat TieReqBool.neqIntFalseLeftAx ∧
    (trS U.ax147).pat = TieReqBool.sentPat TieReqBool.eqIntFalseRightAx ∧
    (trS U.ax49).pat = TieReqBool.sentPat (TieReqBool.fnlBoolAx TieReqBool.eqIntName) ∧
    (trS U.ax46).pat = TieReqBool.sentPat (TieReqBool.fnlBoolAx TieReqBool.neqIntName) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The rule sentences. -/
noncomputable def ruleText : List AxiomDecl := [U.ax157, U.ax158]

/-- The other sentences of the text the statement reads: 138, 133, 147, 49 and 46. -/
noncomputable def ruleAux : List AxiomDecl := [U.ax138, U.ax133, U.ax147, U.ax49, U.ax46]

/-- The item of the text's signature the statement reads, which `ΓSig` does not hold: Int has an
element (G-nonempty of the declaration `hooked-sort SortInt{}`). -/
def ruleSigAux : List Item := [nonemptyItem ⟨"SortInt", [], true⟩]

theorem intDecl_mem : (⟨"SortInt", [], true⟩ : SortDecl) ∈ kore.sortDecls := by decide +kernel

/-- Each item of `ruleSigAux` is an item of the signature of the text's theory. -/
theorem ruleSigAux_text : ∀ it ∈ ruleSigAux, it ∈ (Theory.ofDefinition kore).signature := by
  intro it hit
  rw [List.mem_singleton.mp hit]
  simp only [Theory.ofDefinition, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨_, intDecl_mem, rfl⟩)))))

theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := by
  show c.sortName Srt.int = _; decide +kernel

/-- **Γ's left side of rule 0 holds nothing** in a model of definedness and the signature in which
the five sentences and Int's G-nonempty item hold: its `requires` is `false = true`, and there
`false` and `true` denote two elements of Bool (`TieReqBool.boolLits_of_text_sig`). -/
theorem left0_empty (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H))
    (hT : ∀ φ ∈ ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat), I ⊧ᴵ φ) (e : Valuation M) (a : M) :
    ¬ (tr ⟨tableOf [] p0, []⟩ q0.2.1).interpret I e a := by
  intro h
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  have hT' : ∀ φ ∈ [(trS U.ax138).pat, (trS U.ax133).pat, (trS U.ax147).pat, (trS U.ax49).pat, (trS U.ax46).pat,
      (nonemptyItem ⟨"SortInt", [], true⟩).pat], I ⊧ᴵ φ := hT
  obtain ⟨s1, s2, s3, s4, s5⟩ := lit_sents
  have hL := TieReqBool.boolLits_of_text_sig hD hSig
    (Nat.lt_of_lt_of_le (by decide : Srt.int < nRegSorts) (Nat.le_add_right _ _) :
      Srt.int < nRegSorts + (cH H).sortNames.length) (int_name H)
    (hT' _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
    (s1 ▸ hT' _ (.head _)) (s2 ▸ hT' _ (.tail _ (.head _))) (s3 ▸ hT' _ (.tail _ (.tail _ (.head _))))
    (s4 ▸ hT' _ (.tail _ (.tail _ (.tail _ (.head _)))))
    (s5 ▸ hT' _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (tableOf [] p0) e
  rw [l0_eq, interp_and (List.cons_ne_nil _ _)] at h
  exact TieReqBool.ensFalse_empty_lits hD hc hL (by rw [C_eq, trSort_srt]; exact hσ1) hσ2 a
    (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

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

/-- **W1 for the rules, and the converse for `ruleItems`**, from the text: each of Γ's two rule
items is a consequence of its sentence with sentences 138, 133, 147, 49 and 46, Int's G-nonempty
item and the signature, for every H. No item of `ΓDomains` is among the premises. Rule 1's item is
sentence 158 with two conjuncts more on its left side (`left1`, which reads no other premise). Rule
0's item holds in every model of the premises whatever sentence 157 says: its left side is empty
there (`left0_empty`). -/
theorem rule_from_text_aux (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText,
    TiePair.Texts ((trS ad).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  rcases List.mem_cons.mp hit with rfl | hit
  · refine ⟨U.ax157, List.mem_cons_self .., ?_⟩
    intro M _ I hI
    have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
    have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
    exact TieRuleLhs.rule_w1 hD q0_eq rule_text0 fT_free0
      (hI _ (Or.inl (Or.inl (List.mem_cons_self ..))))
      fun e _ _ a ha => absurd ha (left0_empty H hD hSig
        (fun φ hφ => hI _ (Or.inl (Or.inl (List.mem_cons_of_mem _ hφ)))) e a)
  · rw [List.mem_singleton.mp hit]
    refine ⟨U.ax158, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    intro M _ I hI
    have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
    exact TieRuleLhs.rule_w1 hD q1_eq rule_text1 fT_free1
      (hI _ (Or.inl (Or.inl (List.mem_cons_self ..))))
      fun e _ _ a ha => left1 e a ha

/-! ## Sentence 157 at values (`EntailsAtValues`) -/

/-- Sentence 157 is the item of the text's left side at the table of Γ's axiom. -/
theorem trS157 : (trS U.ax157).pat = TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 q0.2.2 := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- The sentence's one variable `X` is free in it and has the index of Γ's variable at the
argument of `go`. -/
theorem x_index : KoreAML.VarKey.evar "VarX" (KoreAML.srt "Int") ∈ (freeOf [] U.ax157.ax.pattern).eraseDups ∧
    (tableOf U.ax157.ax.sortVars U.ax157.ax.pattern).ev (.evar "VarX" (KoreAML.srt "Int")) =
      (tableOf [] p0).ev (evarKey x0) := by decide +kernel

/-- `1 /Int X` as a library term over the one variable of Γ's axiom. -/
noncomputable def divVars : LibEv.Vars := [(x0.var.ident.name, Srt.int)]
def divT : Term := .app intTDiv [.dv Srt.int (.int 1), .var 0]

theorem div_kore_all : (fun H : HookParams => LibEv.kore (cH H) divVars divT) =
    fun _ => .app ⟨⟨"Lbl'UndsSlsh'Int'Unds'"⟩⟩ [] [.dv (KoreAML.srt "Int") "1", .var (.evar x0)] := by
  kernel_rfl
theorem div_kore (H : HookParams) : LibEv.kore (cH H) divVars divT =
    .app ⟨⟨"Lbl'UndsSlsh'Int'Unds'"⟩⟩ [] [.dv (KoreAML.srt "Int") "1", .var (.evar x0)] :=
  congrFun div_kore_all H
theorem div_srt (H : HookParams) : LibEv.srt? (cH H) divVars divT = some Srt.int := by
  simp only [divT, LibEv.srt?, LibEv.srts?, Semantics.sortOf_withHooks _ _ noRaw]
  decide +kernel
theorem div_key (H : HookParams) : LibEv.vkey (cH H) divVars 0 = evarKey x0 := by
  show LibEv.vkey c divVars 0 = _; decide +kernel
/-- The one sort named `Int` is the registry's. -/
theorem int_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "Int") : S = Srt.int := by
  by_cases hS : S < nRegSorts + c.sortNames.length
  · exact (by decide +kernel : ∀ S ∈ List.range (nRegSorts + c.sortNames.length),
      KoreAML.srt (c.sortName S) = KoreAML.srt "Int" → S = Srt.int) S (List.mem_range.mpr hS) h
  · exfalso
    have hlt : ¬ S < nRegSorts := fun h' => hS (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
    have hge : c.sortNames.length ≤ S - nRegSorts :=
      Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.le_of_not_lt hS)
    have he : c.sortName S = "" := by
      unfold Semantics.sortName
      simp only [hlt, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
    rw [he] at h
    exact absurd h (by decide)

/-- **The text's left side holds nothing at values**, in every model of Γ: at a value `n` of X,
`1 /Int n` denotes the element of an integer or nothing (`LibEv.den_val`: the graph of `/Int` in
`ΓDomains`), so `\ceil{SortInt{}, SortBool{}}(1 /Int n)` is all of Bool or none of it
(`TieReqBool.ceil_const`), and neither is `{true}` where `false` and `true` are two elements of Bool
(`TieReqBool.eqTrue_empty`). -/
theorem ltext0_empty (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (hat : AtValues (cH H) I e U.ax157.ax) (a : M) :
    ¬ (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a := by
  intro h
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  obtain ⟨σI, hσI1, hσI2⟩ := TieRhs.sortSing_sig hD hSig
    (Nat.lt_of_lt_of_le (by decide : Srt.int < nRegSorts) (Nat.le_add_right _ _) : Srt.int < nRegSorts + (cH H).sortNames.length)
  rw [int_name] at hσI1
  have hSI : ∀ b, (trSort (tableOf [] p0) (KoreAML.srt "Int")).interpret I e b ↔ b = σI := by
    rw [trSort_srt]; exact hσI1
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarX" (KoreAML.srt "Int") x_index.1
  rw [x_index.2] at hden
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨a0, ha0, -⟩ := den_single hI hv e
  have hσ : ∀ i p, divVars[i]? = some p → ∃ w, [(0, v)].lookup i = some w ∧ (cH H).sortOf w = some p.2 := by
    intro i p hp
    match i, hp with
    | 0, hp => cases hp; exact ⟨v, rfl, hv⟩
  have hag : ∀ i w, i < divVars.length → [(0, v)].lookup i = some w →
      ∀ m, m = e.evalEvar ((tableOf [] p0).ev (LibEv.vkey (cH H) divVars i)) ↔ (den (cH H) w).interpret I e m := by
    intro i w hi hw m
    match i, hi, hw with
    | 0, _, hw =>
      cases hw
      rw [div_key, ha0, (ha0 _).mp hden]
  obtain ⟨hval, hsrt⟩ := LibEv.den_val (coreOKH H) hI hσ hag divT (div_srt H)
  rw [div_kore] at hval
  have hp : ∀ b, (tr ⟨tableOf [] p0, []⟩ (.app ⟨⟨"Lbl'UndsSlsh'Int'Unds'"⟩⟩ [] [.dv (KoreAML.srt "Int") "1", .var (.evar x0)])).interpret I e b → Inh I σI b := by
    intro b hb
    rw [hval] at hb
    cases hw : LibEv.val (cH H) [(0, v)] divT with
    | none => rw [hw] at hb; exact hb.elim
    | some w =>
      rw [hw] at hb
      obtain ⟨a1, ha1, hin⟩ := den_single hI (hsrt w hw) e
      rw [(ha1 b).mp hb]
      rw [int_name] at hin
      exact (interp_inhOf_of (S := sortP "Int") hσI1).mp hin
  unfold Ltext0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  exact TieReqBool.eqTrue_empty hD hSig hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H)
    (by rw [C_eq, trSort_srt]; exact hσ1) hσ2
    (fun σB hSB hσB x y hx hy => TieReqBool.ceil_const hD hc hSI hσI2 hSB hσB hp x y hx hy) a
    (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- **Sentence 157 is entailed at values** (`EntailsAtValues`, the reading's direction), for every
H: at a value of X its left side holds nothing (`ltext0_empty`), so the sentence holds there. -/
theorem rule157_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax157 (trS U.ax157).pat := by
  intro M _ I hI e hat m
  rw [trS157]
  exact TieReqBool.ruleItem_of_empty (defOK hI) (ltext0_empty H hI e hat) m

/-! ## Sentence 157 (entailed, for every H)

At a valuation that gives X an element of Int, value or not, the elements of `1 /Int X` are
elements of Int: the arity item of `_/Int_` and the arity of the literal `1`, items of `ΓSig`
(`TieFRSig.sig_of_core`). The graph of `/Int` is not read. Where X's guard fails the sentence's
item holds, its guards being its premise. -/

theorem div_injFree : TieFRSig.injFree divT = true := by decide
theorem div_occs : varOccs divT = [0] := by decide

theorem div_term_all : (fun H : HookParams => Term.kore (cH H) (canonVars (cH H) [Srt.int]) divT) =
    fun _ => .app ⟨⟨"Lbl'UndsSlsh'Int'Unds'"⟩⟩ [] [.dv (KoreAML.srt "Int") "1", .var (.evar x0)] := by
  kernel_rfl
theorem div_sort_all : (fun H : HookParams => sortOfTerm ((cH H).rhsCtx ((cH H).fns.map Fn.sig)) [Srt.int] divT) =
    fun _ => some Srt.int := by
  kernel_rfl
theorem div_canonKey_all : (fun H : HookParams => canonKey (cH H) [Srt.int] 0) = fun _ => evarKey x0 := by
  kernel_rfl

/-- X is among the variables whose guards sentence 157's item has. -/
theorem x0_guarded : fT0.contains (evarKey x0) = true := by decide +kernel

/-- **The text's left side holds nothing where X is an element of Int**, value or not, in every
model of Γ: the elements of `1 /Int X` are then elements of Int (the arity items of `_/Int_` and of
the literal `1`, in `ΓSig`), so `\ceil{SortInt{}, SortBool{}}(1 /Int X)` is all of Bool or none of
it (`TieReqBool.ceil_const`), and neither is `{true}` where `false` and `true` are two elements of
Bool (`TieReqBool.eqTrue_empty`). -/
theorem ltext0_empty_int (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M)
    (hx : (inhOf (trSort (tableOf [] p0) x0.sort)).interpret I e (e.evalEvar ((tableOf [] p0).ev (evarKey x0))))
    (a : M) : ¬ (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a := by
  intro h
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  have hnI : Srt.int < nRegSorts + (cH H).sortNames.length :=
    Nat.lt_of_lt_of_le (by decide : Srt.int < nRegSorts) (Nat.le_add_right _ _)
  obtain ⟨σI, hσI1, hσI2⟩ := TieRhs.sortSing_sig hD hSig hnI
  rw [int_name] at hσI1
  have hSI : ∀ b, (trSort (tableOf [] p0) (KoreAML.srt "Int")).interpret I e b ↔ b = σI := by
    rw [trSort_srt]; exact hσI1
  have hTS : TieFRSig.TermsInSortNI (cH H) I := (TieFRSig.sig_of_core (coreOKH H) hD hSig).2
  have hv : ∀ i ∈ varOccs divT, InS I ((cH H).sortName ([Srt.int].getD i 0))
      (e.evalEvar ((tableOf [] p0).ev (canonKey (cH H) [Srt.int] i))) := by
    intro i hi
    rw [div_occs] at hi
    rw [List.mem_singleton.mp hi, congrFun div_canonKey_all H]
    show InS I ((cH H).sortName Srt.int) _
    rw [int_name]
    rw [x0_sort, trSort_srt] at hx
    exact (inS_iff e).mp hx
  have hp : ∀ b, (tr ⟨tableOf [] p0, []⟩ (.app ⟨⟨"Lbl'UndsSlsh'Int'Unds'"⟩⟩ [] [.dv (KoreAML.srt "Int") "1", .var (.evar x0)])).interpret I e b → Inh I σI b := by
    intro b hb
    rw [← congrFun div_term_all H] at hb
    have hin := hTS div_injFree (congrFun div_sort_all H) hnI hv b hb
    rw [int_name] at hin
    exact (interp_inhOf_of (S := sortP "Int") hσI1).mp hin
  unfold Ltext0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  exact TieReqBool.eqTrue_empty hD hSig hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H)
    (by rw [C_eq, trSort_srt]; exact hσ1) hσ2
    (fun σB hSB hσB x y hx hy => TieReqBool.ceil_const hD hc hSI hσI2 hSB hσB hp x y hx hy) a
    (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- **Γ entails sentence 157** (the reading's direction), for every H and at every valuation:
where X's guard holds its left side holds nothing (`ltext0_empty_int`), and where it does not the
item's premise fails. -/
theorem rule157_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax157).pat := by
  intro M _ I hI e m
  rw [trS157]
  by_cases hg : (conjList (fT0.map (guardOf (tableOf [] p0)))).interpret I e m
  · have hx := (TieUnion.interp_conjListAll.mp hg) _ (List.mem_map_of_mem (List.contains_iff_mem.mp x0_guarded))
    exact TieReqBool.ruleItem_of_empty (defOK hI)
      (ltext0_empty_int H hI e ((TieRuleLhs.guard_evarKey (defOK hI)).mp hx)) m
  · unfold TieRuleLhs.itemAt
    rw [interpret_impl]
    exact fun h => absurd h hg

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
reading of the rule sentences 157 and 158, each a consequence of the text's sentences with `ΓSig` by `rule_from_text_aux`), and the families. -/
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
theorem ceil_other (H : HookParams) : Pre H ⊧ (den (cH H) Go1.val ⇒ KoreAML.sNext (den (cH H) Other.val)) :=
  step_from (x := Go1) (y := Other) (by decide +kernel) H

end KCore.NotePredBool

#print axioms KCore.NotePredBool.wf_defn
#print axioms KCore.NotePredBool.defs_attrsAgree
#print axioms KCore.NotePredBool.account
#print axioms KCore.NotePredBool.shape
#print axioms KCore.NotePredBool.fns_entailed
#print axioms KCore.NotePredBool.cons_entailed
#print axioms KCore.NotePredBool.rule_text0
#print axioms KCore.NotePredBool.rule_text1
#print axioms KCore.NotePredBool.left0_empty
#print axioms KCore.NotePredBool.lit_sents
#print axioms KCore.NotePredBool.ruleSigAux_text
#print axioms KCore.NotePredBool.rule_from_text_aux
#print axioms KCore.NotePredBool.ltext0_empty
#print axioms KCore.NotePredBool.rule157_at_values
#print axioms KCore.NotePredBool.ltext0_empty_int
#print axioms KCore.NotePredBool.rule157_entailed
#print axioms KCore.NotePredBool.consistent
#print axioms KCore.NotePredBool.pre_model
#print axioms KCore.NotePredBool.ceil_other
