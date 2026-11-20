/-
  The tie (C14) of the reading `predicateAtBool` on its construct fixture e3-ml-req-forall:
  `rule <k> go(_) => done ... </k> requires #Forall Y:Int. {f(Y) #Equals Y}`, the text's one rule,
  beside `rule f(X) => X`: a `requires` that is a predicate at sort Bool, equated with `true`, read
  as the `requires` false. The text is `f2-examples/e3-ml-req-forall.kompile.kore`. Run from the
  package root: `lake env lean -j1 test/NotePredBoolForall.lean`. Every statement is on the literal
  `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree`; `account`: the function equations,
  the constructor sentences and the rule sentence are sentences of the user module, apart, with
  the count of the rest.

  Layer 2. Function equations (`f`'s and the sort predicates'): Γ's items pattern for pattern
  (`shape`), entailed for every H (`fns_entailed`). Constructor sentences: `cons_entailed`.
  The rule, sentence 157: the sentence's `requires` is
  `\equals{Bool, C}(\forall{Bool}(Y:Int, \equals{Int, Bool}(f(Y), Y)), true)` and Γ's item's
  is `\equals{Bool, C}(false, true)` (`rule_text0`: the sentence is the item of the text's left
  side at the table of Γ's axiom, kernel; the bound `Y`, which Γ's axiom does not have, has in
  that table the index the sentence gives it). Γ's left side holds nothing in a model of definedness
  and `ΓSig` in which five other sentences of the text and Int's G-nonempty item hold
  (`left0_empty`; `ruleAux`: 138, 133, 147, 49 and 46, which at an element of Int state that `false`
  and `true` are two elements of Bool, `lit_sents`, `TieReqBool.boolLits_of_text_sig`; `ruleSigAux`,
  an item of the text's signature, `ruleSigAux_text`), so Γ's item holds there whatever sentence 157
  says (`rule_from_text_aux`, W1: Γ's rule item from the text, no item of `ΓDomains` among the
  premises). That statement names sentence 157 and does not use what it states. What ties sentence
  157 is the other direction (`rule157_entailed`), that the sentence's left side is empty too. Here
  it is, at every valuation and not only at values (`ltext0_empty`): an `\equals` into Bool is all
  of Bool or none of it whatever its operands are, so the `\forall` over `Y`, the part of Bool that
  every one of these over the elements of Int holds, is all of Bool or none of it
  (`forallEqBool_const`; `f(Y)` is not evaluated, and `f`'s equation is not read), and neither is
  `{true}`. So Γ entails the sentence for every H (`rule157_entailed`), and at values in particular
  (`rule157_at_values`): on this text the item and the sentence both hold in every model of Γ, each
  with an empty left side. This direction is over Γ, whose `ΓDomains` gives `false` and `true` as
  two elements of Bool.
  `consistent` for every H.

  The expectation (C7 form (a), through the reading; family the step's closure), from `Pre H`
  (the function equations as written, Γ's rule item, the families) with `Γstep` (it has a model,
  `pre_model`): `forall_stuck`: `go(1)` has no successor.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

deriving instance DecidableEq for KoreAML.SortDecl

namespace KCore.NotePredBoolForall

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-req-forall.kompile.kore"
definition_of defn from "f2-examples/e3-ml-req-forall.kompile.kore"
user_axioms U from "f2-examples/e3-ml-req-forall.kompile.kore" module "E3-ML-REQ-FORALL"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-REQ-FORALL")

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

theorem fnText_index : fnText.map (·.index) = [211, 231, 239, 238, 237, 236, 243, 242, 245, 244, 241, 240, 218, 217, 230, 229, 226, 225, 228, 227, 233, 232, 235, 234, 222, 221, 224, 223, 220, 219] := by
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

/-! ## The rule (sentence 157): W1 -/

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

/-- Γ's axiom of rule 0. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0

/-- Its parts `\rewrites{C}(L', r)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl q0_eq : TieRuleLhs.rwParts p0 = some q0

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

theorem names : c.symName 385 = "Lbldone" ∧ c.symName 386 = "Lblgo" ∧ c.symName 387 = "Lblother" ∧ c.sortName 32 = "Exp" := by
  decide +kernel

-- Γ's left side of rule 0: the term, the `requires` false, then `⌈r⌉`.
kernel_rfl l0_eq : q0.2.1 = .and q0.1 (TieRuleLhs.andHead q0.2.1 :: TieRhs.ensFalse q0.1 :: (TieRuleLhs.andTail q0.2.1).drop 1)

/-- The variable the sentence's `\forall` binds. -/
def y0 : Kore.EVar := KoreAML.evar "VarY" (KoreAML.srt "Int")

/-- The left side of rule 0 as the text writes it: the `requires` is the predicate
`\forall{SortBool{}}(VarY:SortInt{}, \equals{SortInt{}, SortBool{}}(Lblf{}(VarY), VarY))`, equated
with `true`, and no conjunct follows. -/
noncomputable def Ltext0 : Kore.Pattern :=
  .and q0.1 [TieRuleLhs.andHead q0.2.1,
    .equals (KoreAML.srt "Bool") q0.1
      (.forall (KoreAML.srt "Bool") y0
        (.equals (KoreAML.srt "Int") (KoreAML.srt "Bool")
          (.app ⟨⟨"Lblf"⟩⟩ [] [.var (.evar y0)]) (.var (.evar y0))))
      (.dv (KoreAML.srt "Bool") "true")]

noncomputable def fT0 : List VarKey := (freeOf [] (.rewrites q0.1 Ltext0 q0.2.2)).eraseDups

/-- **The rule sentence is the item of `\rewrites{C}(Ltext0, r)` at the table of Γ's axiom**
(kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 q0.2.2) [] = some (trS U.ax157).pat := by
  decide +kernel
theorem fT_free0 : fT0.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel

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

/-- The rule sentence. -/
noncomputable def ruleText : List AxiomDecl := [U.ax157]

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

/-- **W1 for the rule, and the converse for `ruleItems`**, from the text: Γ's rule item is a
consequence of sentence 157 with sentences 138, 133, 147, 49 and 46, Int's G-nonempty item and the
signature, for every H. No item of `ΓDomains` is among the premises. The item holds in every model
of the premises whatever sentence 157 says: its left side is empty there (`left0_empty`). -/
theorem rule_from_text_aux (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText,
    TiePair.Texts ((trS ad).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  rw [List.mem_singleton.mp hit]
  refine ⟨U.ax157, List.mem_cons_self .., ?_⟩
  intro M _ I hI
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  exact TieRuleLhs.rule_w1 hD q0_eq rule_text0 fT_free0
    (hI _ (Or.inl (Or.inl (List.mem_cons_self ..))))
    fun e _ _ a ha => absurd ha (left0_empty H hD hSig
      (fun φ hφ => hI _ (Or.inl (Or.inl (List.mem_cons_of_mem _ hφ)))) e a)

/-! ## Sentence 157 (entailed, for every H) -/

/-- Sentence 157 is the item of the text's left side at the table of Γ's axiom. -/
theorem trS157 : (trS U.ax157).pat = TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 q0.2.2 := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **`\forall{SortBool{}}(v, \equals{S, SortBool{}}(p, q))` is all of Bool or none of it**,
whatever `p` and `q` are: at each element given to `v` the `\equals` is all of Bool or none of
it, so the part of Bool outside it is none of Bool or all of it, and whether some element of
`v`'s sort leaves an element of Bool outside does not depend on the element of Bool. -/
theorem forallEqBool_const [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable} {S : Kore.KSort} {σS σB : M}
    (hS : ∀ (e : Valuation M) a, (trSort t S).interpret I e a ↔ a = σS) (hσS : IsSort I σS)
    (hSB : ∀ (e : Valuation M) a, (trSort t (KoreAML.srt "Bool")).interpret I e a ↔ a = σB) (hσB : IsSort I σB)
    (v : Kore.EVar) (p q : Kore.Pattern) (e : Valuation M) (x y : M) (hx : Inh I σB x) (hy : Inh I σB y) :
    (tr ⟨t, []⟩ (.forall (KoreAML.srt "Bool") v (.equals S (KoreAML.srt "Bool") p q))).interpret I e x ↔
      (tr ⟨t, []⟩ (.forall (KoreAML.srt "Bool") v (.equals S (KoreAML.srt "Bool") p q))).interpret I e y := by
  have hT : tr ⟨t, []⟩ (.forall (KoreAML.srt "Bool") v (.equals S (KoreAML.srt "Bool") p q)) =
      sForall (trSort t (KoreAML.srt "Bool")) (t.ev (evarKey v)) (trSort t v.sort)
        (sEquals (trSort t S) (trSort t (KoreAML.srt "Bool")) (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ q)) := by rw [tr, tr]
  rw [hT]
  unfold sForall
  have key : ∀ x y : M, Inh I σB x → Inh I σB y →
      (sNot (trSort t (KoreAML.srt "Bool")) (sExists (t.ev (evarKey v)) (trSort t v.sort)
        (sNot (trSort t (KoreAML.srt "Bool"))
          (sEquals (trSort t S) (trSort t (KoreAML.srt "Bool")) (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ q))))).interpret I e x →
      (sNot (trSort t (KoreAML.srt "Bool")) (sExists (t.ev (evarKey v)) (trSort t v.sort)
        (sNot (trSort t (KoreAML.srt "Bool"))
          (sEquals (trSort t S) (trSort t (KoreAML.srt "Bool")) (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ q))))).interpret I e y := by
    intro x y hx hy h
    have h1 := interp_sNot.mp h
    refine interp_sNot.mpr ⟨fun hex => h1.1 ?_, (interp_inhOf_of (hSB e)).mpr hy⟩
    obtain ⟨a, ha, hn⟩ := (interp_sExists_elem hD).mp hex
    have hn1 := interp_sNot.mp hn
    exact (interp_sExists_elem hD).mpr ⟨a, ha, interp_sNot.mpr
      ⟨fun hq => hn1.1 ((interp_sEquals hD hc (hS _) (hSB _) hσS hσB y).mpr
          ⟨hy, ((interp_sEquals hD hc (hS _) (hSB _) hσS hσB x).mp hq).2⟩),
        (interp_inhOf_of (hSB _)).mpr hx⟩⟩
  exact ⟨key x y hx hy, key y x hy hx⟩

end

/-- **The text's left side holds nothing**, at every valuation, in a model of Γ: the `\forall` of
an `\equals` into Bool is all of Bool or none of it (`forallEqBool_const`, whatever the operands
are), so it holds the same of `false` and of `true`, two elements of Bool, and is not `{true}`
(`TieReqBool.eqTrue_empty`). -/
theorem ltext0_empty (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (a : M) :
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
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig (bool_numbered (c := cH H))
  rw [sortName_bool] at hσB1
  have hSI : ∀ (e' : Valuation M) b, (trSort (tableOf [] p0) (KoreAML.srt "Int")).interpret I e' b ↔ b = σI := by
    intro e' b; rw [trSort_srt]; exact hσI1 b
  have hSB : ∀ (e' : Valuation M) b, (trSort (tableOf [] p0) (KoreAML.srt "Bool")).interpret I e' b ↔ b = σB := by
    intro e' b; rw [trSort_srt]; exact hσB1 b
  unfold Ltext0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  exact TieReqBool.eqTrue_empty hD hSig hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H)
    (by rw [C_eq, trSort_srt]; exact hσ1) hσ2
    (fun σB' hSB' _ x y hx hy => by
      have hσ : σB = σB' := (hSB' σB).mp ((hSB e σB).mpr rfl)
      subst hσ
      exact forallEqBool_const hD hc hSI hσI2 hSB hσB2 _ _ _ e x y hx hy) a
    (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- **Γ entails sentence 157** (the reading's direction), for every H: its left side holds nothing
at any valuation (`ltext0_empty`), so the sentence holds in every model of Γ. -/
theorem rule157_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax157).pat := by
  intro M _ I hI e m
  rw [trS157]
  exact TieReqBool.ruleItem_of_empty (defOK hI) (ltext0_empty H hI e) m

/-- **Sentence 157 is entailed at values** (`EntailsAtValues`), for every H: the instance of
`rule157_entailed` at the valuations that send its variables to values. -/
theorem rule157_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax157 (trS U.ax157).pat :=
  fun _ _ _ hI e _ m => rule157_entailed H hI e m

/-! ## The account -/

noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ consText.map (·.index) ++ [157]

/-- **The account**: the function equations, the constructor sentences and the rule sentence are
sentences of the user module, each once and none in two classes, with the sizes of the three
classes and of the rest (not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length, consText.length, [157].length, U.all.length - tiedIdx.length) = (30, 32, 1, 202) := by decide +kernel

/-! ## The facts the deciders leave -/

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok

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

/-! ## The expectations (C7 form (a)) -/

/-- **The premises of the derivations**: every function equation as written, Γ's rule item (the
reading of the rule sentence 157, a consequence of the text's sentences with `ΓSig` by
`rule_from_text_aux`), and the families. -/
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

def Go1 : Config c := ⟨cfg (.ctor 386 [.dv Srt.int (.int 1)]), by decide +kernel⟩

/-- **`go(1)` has no successor, derived from `Pre` with the step's closure**, for every H: the
one rule's `requires` is read as false. -/
theorem forall_stuck (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) Go1.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  stuck_from (x := Go1) (by decide +kernel) H

end KCore.NotePredBoolForall

#print axioms KCore.NotePredBoolForall.wf_defn
#print axioms KCore.NotePredBoolForall.defs_attrsAgree
#print axioms KCore.NotePredBoolForall.account
#print axioms KCore.NotePredBoolForall.shape
#print axioms KCore.NotePredBoolForall.fns_entailed
#print axioms KCore.NotePredBoolForall.cons_entailed
#print axioms KCore.NotePredBoolForall.rule_text0
#print axioms KCore.NotePredBoolForall.left0_empty
#print axioms KCore.NotePredBoolForall.lit_sents
#print axioms KCore.NotePredBoolForall.ruleSigAux_text
#print axioms KCore.NotePredBoolForall.rule_from_text_aux
#print axioms KCore.NotePredBoolForall.ltext0_empty
#print axioms KCore.NotePredBoolForall.rule157_entailed
#print axioms KCore.NotePredBoolForall.rule157_at_values
#print axioms KCore.NotePredBoolForall.consistent
#print axioms KCore.NotePredBoolForall.pre_model
#print axioms KCore.NotePredBoolForall.forall_stuck
#print axioms KCore.NotePredBoolForall.forallEqBool_const
#print axioms KCore.NotePredBoolForall.names
