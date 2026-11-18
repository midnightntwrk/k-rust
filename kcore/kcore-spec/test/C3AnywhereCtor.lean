/-
  The tie (C14) of the fixture c3-anywhere-ctor (the pair `anywhere` rule x constructor, the overload
  form): `syntax Exp ::= Int | sum(Exp, Int) [symbol(sumEI), overload(sum)] | sum(Exp, Exp)
  [symbol(sumEE), overload(sum)]` and `rule <k> sum(E:Exp, I:Int) => sum(E, E) ... </k>`.
  The text is `f2-examples/c3-anywhere-ctor.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-anywhere-ctor/kompile.txt` records, with its paths restored.
  Run from the package root: `lake env lean -j1 test/C3AnywhereCtor.lean`. Every statement is on the
  literal `defn`; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree`; `names`: sumEE (386) is an overloading
  symbol over sumEI (385); `account`: the function equations, the constructor sentences, the rule
  sentence and the no-confusion sentence of sumEE and sumEI are sentences of the user module, apart,
  with the count of the rest.

  Layer 2, for every H.
  - Function equations (`fnText`, the sort predicates'): `shape`, `fns_entailed`, `fns_from_text`.
  - Constructor sentences (`consText`): `cons_entailed`.
  - The rule sentence (axiom 157): `rules_tie`, `rules_from_text` (W1), `rules_w2` (W2 with the guard
    `TieRulePair.RuleGuard`).
  - The no-confusion sentence of sumEE and sumEI (axiom 111, `//@ 249` of kore.txt, sentence 263 in
    the account's numbering, the one user-module axiom with its pattern: `nc_unique`):
    `\not{SortExp{}}(\and{SortExp{}}(sumEE(X0, X1), sumEI(Y0, Y1)))`. The reader leaves it inert
    (`distinctCtors`, `nc_class`) and lists it as stated by the text and not read
    (`overloadConfusion`); no constructor item of Γ entails it (`nc_not_cons`). Γ refutes it
    (`nc_refuted`): Γ's overload item states `sumEE(K0, inj{Int,Exp}(K1)) = sumEI(K0, K1)`, so in
    every model of Γ, at X0 = Y0 = inj{Int,Exp}(5), X1 = inj{Int,Exp}(5) and Y1 = 5, both sides
    build the element of `sumEI(inj{Int,Exp}(5), 5)` (`Faithful.norm_gs`,
    `Faithful.tieDist_refuted`). Read, the sentence would make Γ inconsistent wherever Exp and Int
    have elements: it belongs to no premise set of a derivation (`Pre`, `PreS`).
  - `consistent`: Γ with the step's closure has a model.

  The expectations (C7 form (a)): the executable step `CExec`, which reads the overloading symbol
  (the text's matcher `Exec` does not: `matchReady` is false here), lists one successor of
  `<k> sumEI(inj{Int,Exp}(5), 1) </k>`, namely `<k> sumEI(inj{Int,Exp}(5), 5) </k>`: the rule's right
  side `sum(E, E)` at E = inj{Int,Exp}(5) is `sumEE(inj(5), inj(5))`, whose normal form is
  `sumEI(inj(5), 5)` by the overload. `x5_step`: the step, derived from `PreS` (the function and rule
  sentences as written, and the families) by W1 and the cut; `x5_succs`: it is the only successor,
  from `Pre` with the step's closure (`CExec.run_exact`, with `x5_listed`: the
  list `CExec` gives there).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3AnywhereCtor

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-anywhere-ctor.kompile.kore"
definition_of defn from "f2-examples/c3-anywhere-ctor.kompile.kore"
user_axioms U from "f2-examples/c3-anywhere-ctor.kompile.kore" module "C3-ANYWHERE-CTOR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## Layer 1 -/

theorem wf_defn : wf defn = true := by decide +kernel
theorem coreOK : c.coreOK = true := by decide +kernel
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The attributes of the text agree with `defn` (`attrsAgree`). -/
theorem defs_attrsAgree : attrsAgree kore defn = true := by decide +kernel

def kCell : Sym := 383
def sumEI : Sym := 385
def sumEE : Sym := 386
def exp : Srt := 32

/-- The symbols and the sort; sumEE is the one overloading symbol. -/
theorem names : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName sumEI = "LblsumEI" ∧
    c.symName sumEE = "LblsumEE" ∧ c.sortName exp = "Exp" ∧ c.ovls.length = 1 ∧ c.isOvl sumEE = true := by
  decide +kernel

/-! ## The function equations (the sort predicates') -/

noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

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

/-! ## The rule sentence -/

noncomputable def ruleText : List AxiomDecl := [U.ax157]

noncomputable def rulePats : List P := ruleText.map (trS · |>.pat)

theorem rule_prios : c.rules.map (·.prio) = [50] ∧ ruleText.map (·.index) = [157] := by
  decide +kernel

/-- **Γ's axiom of the rule is its sentence with conjuncts more on the left side** (kernel). -/
theorem rules_tie : TieRulePair.rulesTieB c rulePats = true := by decide +kernel

theorem rules_tieH (H : HookParams) : TieRulePair.rulesTieB (cH H) rulePats = true :=
  (TieRulePair.rulesTieB_withHooks c H rulePats).trans rules_tie

/-- **W1 for the rule**: Γ's rule item is a consequence of its sentence, for every H. -/
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

/-- **W2 for the rule, with the guard**, for every H. -/
theorem rules_w2 (H : HookParams) {j : Nat} {r : Rule} {ad : AxiomDecl} (hr : (cH H).rules[j]? = some r)
    (had : ruleText[j]? = some ad) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (hx : TieRulePair.RuleGuard (prioRuleK (cH H) r) I e) (m : M) :
    (trS ad).pat.interpret I e m :=
  TieRulePair.rules_w2 (rules_tieH H) hr (by unfold rulePats; rw [List.getElem?_map, had]; rfl) hI e hx m

/-! ## The no-confusion sentence of sumEE and sumEI -/

noncomputable abbrev ncAx : AxiomDecl := U.ax111

def kX0 : Kore.EVar := evar "X0" (srt "Exp")
def kX1 : Kore.EVar := evar "X1" (srt "Exp")
def kY0 : Kore.EVar := evar "Y0" (srt "Exp")
def kY1 : Kore.EVar := evar "Y1" (srt "Int")
def ncL : Kore.Pattern := ap "LblsumEE" [.var (.evar kX0), .var (.evar kX1)]
def ncR : Kore.Pattern := ap "LblsumEI" [.var (.evar kY0), .var (.evar kY1)]
def gEE : KoreAML.Gen := .ctor ⟨"LblsumEE", ["Exp", "Exp"], "Exp"⟩
def gEI : KoreAML.Gen := .ctor ⟨"LblsumEI", ["Exp", "Int"], "Exp"⟩

/-- The variable table of the sentence. -/
noncomputable def ncTbl : VarTable := tableOf ncAx.ax.sortVars ncAx.ax.pattern

/-- **The sentence**: its pattern, its free variables, the translations of its two sides as the two
generators applied to their variables, and the variables' places. -/
theorem nc_parts : ncAx.ax.pattern = .not (srt "Exp") (.and (srt "Exp") [ncL, ncR]) ∧
    (ncAx.ax.sortVars.map sortVarKey ++ freeOf [] ncAx.ax.pattern).eraseDups =
      [.evar "X0" (srt "Exp"), .evar "X1" (srt "Exp"), .evar "Y0" (srt "Exp"), .evar "Y1" (srt "Int")] ∧
    tr ⟨ncTbl, []⟩ ncL = Cons.genPat "Exp" gEE (([kX0, kX1].map fun k => ncTbl.ev (evarKey k)).map .evar) ∧
    tr ⟨ncTbl, []⟩ ncR = Cons.genPat "Exp" gEI (([kY0, kY1].map fun k => ncTbl.ev (evarKey k)).map .evar) ∧
    ncTbl.ev (evarKey kX0) ≠ ncTbl.ev (evarKey kY1) ∧ ncTbl.ev (evarKey kX1) ≠ ncTbl.ev (evarKey kY1) ∧
    ncTbl.ev (evarKey kY0) ≠ ncTbl.ev (evarKey kY1) ∧
    (trS ncAx).pat = (trAxiom [] [] ncAx).pat := by
  decide +kernel

/-- It is the one axiom of the user module with that pattern. -/
theorem nc_unique : (U.all.filter fun ad => decide (ad.ax.pattern = ncAx.ax.pattern)).map (·.index) = [111] := by
  decide +kernel

/-- The reader's class of the sentence, and no constructor item of Γ entails it in the form
`tieConsB` decides. -/
theorem nc_class : Parse.classifyShape (.axiom ncAx.ax) = .inert .distinctCtors := by decide +kernel
theorem nc_not_cons : tieConsB c ncAx.ax = false := by decide +kernel

def i5 : GroundTerm := .inj Srt.int exp (int 5)
def y5 : GroundTerm := .ctor sumEI [i5, int 5]
def kEE : CtorSig := ⟨sumEE, [exp, exp], exp⟩
def kEI : CtorSig := ⟨sumEI, [exp, Srt.int], exp⟩

/-- The normal forms: `sumEE(inj(5), inj(5))` is `sumEI(inj(5), 5)` by the overload, and so is
`sumEI(inj(5), 5)`; the signatures, ranks and sorts `Faithful.norm_gs` reads. -/
theorem ovl_facts : c.norm sumEE [i5, i5] = y5 ∧ c.norm sumEI [i5, int 5] = y5 ∧
    lookupSig (c.ctorSigs ++ c.ovlSigs) sumEE = some kEE ∧ lookupSig (c.ctorSigs ++ c.ovlSigs) sumEI = some kEI ∧
    OvlLaws.ovlRank c sumEE ≤ 1 ∧ OvlLaws.ovlRank c sumEI ≤ 1 ∧
    Gen.toK c (.ctor kEE) = gEE ∧ Gen.toK c (.ctor kEI) = gEI ∧
    c.sortsOf [i5, i5] = some [exp, exp] ∧ c.sortsOf [i5, int 5] = some [exp, Srt.int] ∧
    c.sortOf i5 = some exp ∧ c.sortOf (int 5) = some Srt.int ∧ c.sortOf y5 = some exp ∧
    c.sortName Srt.int = "Int" := by
  decide +kernel

theorem subsorts_trans : c.subsorts.all (fun p => c.subsorts.all fun q =>
    !(p.2 == q.1) || c.subsorts.contains (p.1, q.2)) = true := by
  decide +kernel

kernel_rfl normEE_wh : ∀ H : HookParams, (cH H).norm sumEE [i5, i5] = c.norm sumEE [i5, i5]
kernel_rfl normEI_wh : ∀ H : HookParams, (cH H).norm sumEI [i5, int 5] = c.norm sumEI [i5, int 5]
kernel_rfl lookupEE_wh : ∀ H : HookParams,
  lookupSig ((cH H).ctorSigs ++ (cH H).ovlSigs) sumEE = lookupSig (c.ctorSigs ++ c.ovlSigs) sumEE
kernel_rfl lookupEI_wh : ∀ H : HookParams,
  lookupSig ((cH H).ctorSigs ++ (cH H).ovlSigs) sumEI = lookupSig (c.ctorSigs ++ c.ovlSigs) sumEI
kernel_rfl rankEE_wh : ∀ H : HookParams, OvlLaws.ovlRank (cH H) sumEE = OvlLaws.ovlRank c sumEE
kernel_rfl rankEI_wh : ∀ H : HookParams, OvlLaws.ovlRank (cH H) sumEI = OvlLaws.ovlRank c sumEI
kernel_rfl toKEE_wh : ∀ H : HookParams, Gen.toK (cH H) (.ctor kEE) = Gen.toK c (.ctor kEE)
kernel_rfl toKEI_wh : ∀ H : HookParams, Gen.toK (cH H) (.ctor kEI) = Gen.toK c (.ctor kEI)
kernel_rfl sortNameE_wh : ∀ H : HookParams, (cH H).sortName exp = c.sortName exp
kernel_rfl sortNameI_wh : ∀ H : HookParams, (cH H).sortName Srt.int = c.sortName Srt.int
kernel_rfl subsorts_wh : ∀ H : HookParams, (cH H).subsorts = c.subsorts
kernel_rfl fnOvlSyms_wh : ∀ H : HookParams, (cH H).fnOvlSyms = c.fnOvlSyms

/-- No overloading symbol of this semantics overloads a function. -/
theorem fnOvlSyms_nil : c.fnOvlSyms = [] := by decide +kernel

/-- The valuation of the refutation: Y1 to the element `y2`, every other variable to `y0`. -/
noncomputable def ncVal {M : Type} (y0 y2 : M) : Valuation M :=
  ⟨fun v => if v = ncTbl.ev (evarKey kY1) then y2 else y0, fun _ _ => False⟩

/-- **Γ refutes the no-confusion sentence of sumEE and sumEI**, for every H: in no model of Γ is it
satisfied, since Γ's overload item makes the two generators build one element at
X0 = Y0 = inj{Int,Exp}(5), X1 = inj{Int,Exp}(5), Y1 = 5. -/
theorem nc_refuted (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : ¬ (I ⊧ᴵ (trS ncAx).pat) := by
  obtain ⟨hpat, hfree, hp1, hp2, hn0, hn1, hn2, htr⟩ := nc_parts
  obtain ⟨hnEE, hnEI, hkEE, hkEI, hrEE, hrEI, htEE, htEI, hsEE, hsEI, hs5, hsI, hsy, hnI⟩ := ovl_facts
  obtain ⟨-, -, -, hnE, -, -⟩ := names
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hso : (cH H).sortOf = c.sortOf := Semantics.sortOf_withHooks c H noRaw
  have hsos : (cH H).sortsOf = c.sortsOf := Semantics.sortsOf_withHooks c H noRaw
  have hsnE : (cH H).sortName exp = "Exp" := (sortNameE_wh H).trans hnE
  have hsnI : (cH H).sortName Srt.int = "Int" := (sortNameI_wh H).trans hnI
  have htrH : ∀ a b d, (a, b) ∈ (cH H).subsorts → (b, d) ∈ (cH H).subsorts → (a, d) ∈ (cH H).subsorts := by
    rw [subsorts_wh H]
    intro a b d h1 h2
    have := List.all_eq_true.mp (List.all_eq_true.mp subsorts_trans _ h1) _ h2
    simpa using this
  -- the common element
  have hEE := (Faithful.norm_gs hI htrH 1 kEE (by
      show lookupSig ((cH H).ctorSigs ++ (cH H).ovlSigs) sumEE = some kEE
      rw [lookupEE_wh H]; exact hkEE)
    (by show OvlLaws.ovlRank (cH H) sumEE ≤ 1; rw [rankEE_wh H]; exact hrEE) [i5, i5] (by rw [hsos]; exact hsEE) (OvlLaws.fnCover_none_of_noFnOvl ((fnOvlSyms_wh H).trans fnOvlSyms_nil) _ _) (elemOf (cH H) I y5)).mpr
    (by show elemOf (cH H) I y5 = elemOf (cH H) I ((cH H).norm sumEE [i5, i5]); rw [normEE_wh H, hnEE])
  have hEI := (Faithful.norm_gs hI htrH 1 kEI (by
      show lookupSig ((cH H).ctorSigs ++ (cH H).ovlSigs) sumEI = some kEI
      rw [lookupEI_wh H]; exact hkEI)
    (by show OvlLaws.ovlRank (cH H) sumEI ≤ 1; rw [rankEI_wh H]; exact hrEI) [i5, int 5] (by rw [hsos]; exact hsEI) (OvlLaws.fnCover_none_of_noFnOvl ((fnOvlSyms_wh H).trans fnOvlSyms_nil) _ _) (elemOf (cH H) I y5)).mpr
    (by show elemOf (cH H) I y5 = elemOf (cH H) I ((cH H).norm sumEI [i5, int 5]); rw [normEI_wh H, hnEI])
  have hres : kEE.result = exp := rfl
  have hres' : kEI.result = exp := rfl
  rw [hres, hsnE, (toKEE_wh H), htEE] at hEE
  rw [hres', hsnE, (toKEI_wh H), htEI] at hEI
  simp only [List.map_cons, List.map_nil] at hEE hEI
  -- the valuation and its guards
  generalize hy0 : elemOf (cH H) I i5 = y0 at hEE hEI
  generalize hy2 : elemOf (cH H) I (int 5) = y2 at hEI
  have hev : ∀ v, (ncVal y0 y2).evalEvar v = if v = ncTbl.ev (evarKey kY1) then y2 else y0 := fun _ => rfl
  have hin0 : ∀ e : Valuation M, (KoreAML.inhOf (KoreAML.Cons.sortP "Exp")).interpret I e y0 := fun e => by
    have := (elemOf_spec hI (show (cH H).sortOf i5 = some exp by rw [hso]; exact hs5) e).2
    rw [hsnE, hy0] at this; exact this
  have hin2 : ∀ e : Valuation M, (KoreAML.inhOf (KoreAML.Cons.sortP "Int")).interpret I e y2 := fun e => by
    have := (elemOf_spec hI (show (cH H).sortOf (int 5) = some Srt.int by rw [hso]; exact hsI) e).2
    rw [hsnI, hy2] at this; exact this
  rw [htr]
  refine Faithful.tieDist_refuted hD (xs := [kX0, kX1]) (ys := [kY0, kY1]) (m := elemOf (cH H) I y5) hpat hp1 hp2
    (ncVal y0 y2) ?_ ?_ ?_ ?_
  · intro k hk m'
    have hk' : k ∈ [VarKey.evar "X0" (srt "Exp"), VarKey.evar "X1" (srt "Exp"), VarKey.evar "Y0" (srt "Exp"),
        VarKey.evar "Y1" (srt "Int")] := by rw [← hfree]; exact hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
    rcases hk' with rfl | rfl | rfl | rfl
    · rw [KoreAML.interp_guard_evar hD, trSort_srt]
      show (KoreAML.inhOf (KoreAML.Cons.sortP "Exp")).interpret I _ ((ncVal y0 y2).evalEvar (ncTbl.ev (evarKey kX0)))
      rw [hev, if_neg hn0]; exact hin0 _
    · rw [KoreAML.interp_guard_evar hD, trSort_srt]
      show (KoreAML.inhOf (KoreAML.Cons.sortP "Exp")).interpret I _ ((ncVal y0 y2).evalEvar (ncTbl.ev (evarKey kX1)))
      rw [hev, if_neg hn1]; exact hin0 _
    · rw [KoreAML.interp_guard_evar hD, trSort_srt]
      show (KoreAML.inhOf (KoreAML.Cons.sortP "Exp")).interpret I _ ((ncVal y0 y2).evalEvar (ncTbl.ev (evarKey kY0)))
      rw [hev, if_neg hn2]; exact hin0 _
    · rw [KoreAML.interp_guard_evar hD, trSort_srt]
      show (KoreAML.inhOf (KoreAML.Cons.sortP "Int")).interpret I _ ((ncVal y0 y2).evalEvar (ncTbl.ev (evarKey kY1)))
      rw [hev, if_pos rfl]; exact hin2 _
  · exact (inS_iff KoreAML.val0).mp (by
      have := (elemOf_spec hI (show (cH H).sortOf y5 = some exp by rw [hso]; exact hsy) KoreAML.val0).2
      rw [hsnE] at this; exact this)
  · show GS I "Exp" gEE [(ncVal y0 y2).evalEvar (ncTbl.ev (evarKey kX0)),
      (ncVal y0 y2).evalEvar (ncTbl.ev (evarKey kX1))] _
    rw [hev, hev, if_neg hn0, if_neg hn1]; exact hEE
  · show GS I "Exp" gEI [(ncVal y0 y2).evalEvar (ncTbl.ev (evarKey kY0)),
      (ncVal y0 y2).evalEvar (ncTbl.ev (evarKey kY1))] _
    rw [hev, hev, if_neg hn2, if_pos rfl]; exact hEI

/-! ## The account -/

noncomputable def tiedIdx : List Nat :=
  fnText.map (·.index) ++ consText.map (·.index) ++ ruleText.map (·.index) ++ [ncAx.index]

/-- **The account**: the function equations, the constructor sentences, the rule sentence and the
no-confusion sentence of sumEE and sumEI are sentences of the user module, each once and none in two
classes; the sizes of the classes and of the rest (library sentences, hooked symbols' `functional`
sentences, collection laws, no junk, the overload axiom read into `Semantics.ovls`, the projections
and initializers: not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length, consText.length, ruleText.length, U.all.length - tiedIdx.length) = (29, 30, 1, 203) := by
  decide +kernel

/-! ## The facts the deciders leave -/

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
/-- The text's matcher `Exec` does not read the overloading symbol in a pattern; `CExec` does. -/
theorem not_matchReady : c.matchReady = false := by decide +kernel
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

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

noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

noncomputable abbrev PreS (H : HookParams) : Premises KoreAML.Sym := TieRulePair.PreS (cH H) textPats rulePats

def x5 : GroundTerm := .ctor sumEI [i5, int 1]

/-- The configuration with `it` in the k cell and the counter at 0. -/
def cfg (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj exp Srt.kitem it, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

noncomputable abbrev XH (x : Config c) (H : HookParams) : Config (cH H) := TieRulePair.cfgH noRaw x H
noncomputable def X5 : Config c := ⟨cfg x5, by decide +kernel⟩
noncomputable def Y5 : Config c := ⟨cfg y5, by decide +kernel⟩

theorem ready : CExec.execReady c = true := by decide +kernel
theorem fuel : CExec.outOfFuel c 100 (cfg x5) = false := by decide +kernel
theorem succ : CExec.successorsN c 100 (cfg x5) = [cfg y5] := by decide +kernel
kernel_rfl ready_wh : ∀ H : HookParams, CExec.execReady (cH H) = CExec.execReady c
kernel_rfl fuel_wh : ∀ H : HookParams, CExec.outOfFuel (cH H) 100 (cfg x5) = CExec.outOfFuel c 100 (cfg x5)
kernel_rfl succ_wh : ∀ H : HookParams, CExec.successorsN (cH H) 100 (cfg x5) = CExec.successorsN c 100 (cfg x5)

theorem fnDetH (H : HookParams) : FnDet (cH H) := (fnModel_of_fnHyp (coreOKH H) (fnHypH H)).1

/-- **`sum(inj(5), 1)` steps to `sumEI(inj(5), 5)`**, for every H: derived from `PreS`, the
sentences as written, by W1 and the cut. -/
theorem x5_step (H : HookParams) :
    PreS H ⊧ (den (cH H) (XH X5 H).val ⇒ KoreAML.sNext (den (cH H) (XH Y5 H).val)) :=
  TieRulePair.cutS (shapeH H) (rules_tieH H)
    ((CExec.run_exact (coreOKH H) ((ready_wh H).trans ready) (fnDetH H) (x := XH X5 H)
      ((fuel_wh H).trans fuel)).2 _ (by
        show cfg y5 ∈ CExec.successorsN (cH H) 100 (cfg x5)
        rw [succ_wh H, succ]; exact List.mem_singleton_self _))

/-- With the step's closure, every successor of `sum(inj(5), 1)` is one `CExec` lists, for every H. -/
theorem x5_closure (H : HookParams) :
    (Γ (cH H) ∪ Γstep (cH H)) ⊧ (den (cH H) (XH X5 H).val ⇒
      KoreAML.allNext (KoreAML.disjList ((CExec.successorsN (cH H) 100 (XH X5 H).val).map (den (cH H))))) :=
  (CExec.run_exact (coreOKH H) ((ready_wh H).trans ready) (fnDetH H) (x := XH X5 H) ((fuel_wh H).trans fuel)).1

/-- The list `CExec` gives at `sum(inj(5), 1)` is `[sumEI(inj(5), 5)]`, for every H. -/
theorem x5_listed (H : HookParams) : CExec.successorsN (cH H) 100 (XH X5 H).val = [(XH Y5 H).val] :=
  (succ_wh H).trans succ

/-- **`sumEI(inj(5), 5)` is the only successor**, for every H: from `Pre` with the step's closure. -/
theorem x5_succs (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) (XH X5 H).val ⇒
      KoreAML.allNext (KoreAML.disjList ([(XH Y5 H).val].map (den (cH H))))) :=
  fun hI => by
    have h := TiePair.cutStep (shapeH H) (x5_closure H) hI
    rw [x5_listed H] at h
    exact h

end KCore.C3AnywhereCtor

#print axioms KCore.C3AnywhereCtor.wf_defn
#print axioms KCore.C3AnywhereCtor.defs_attrsAgree
#print axioms KCore.C3AnywhereCtor.shape
#print axioms KCore.C3AnywhereCtor.fns_entailed
#print axioms KCore.C3AnywhereCtor.fns_from_text
#print axioms KCore.C3AnywhereCtor.cons_entailed
#print axioms KCore.C3AnywhereCtor.rules_tie
#print axioms KCore.C3AnywhereCtor.rules_from_text
#print axioms KCore.C3AnywhereCtor.rules_w2
#print axioms KCore.C3AnywhereCtor.nc_parts
#print axioms KCore.C3AnywhereCtor.nc_unique
#print axioms KCore.C3AnywhereCtor.nc_class
#print axioms KCore.C3AnywhereCtor.nc_refuted
#print axioms KCore.C3AnywhereCtor.account
#print axioms KCore.C3AnywhereCtor.consistent
#print axioms KCore.C3AnywhereCtor.pre_model
#print axioms KCore.C3AnywhereCtor.x5_step
#print axioms KCore.C3AnywhereCtor.x5_listed
#print axioms KCore.C3AnywhereCtor.x5_succs
