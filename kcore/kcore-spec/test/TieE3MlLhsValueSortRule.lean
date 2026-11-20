/-
  The rule sentences of construct fixture e3-ml-lhs-value-sort, beside its tie
  test/TieE3MlLhsValueSort.lean (written by tiegen, which leaves the rules uncovered), on the same
  text `f2-examples/e3-ml-lhs-value-sort.kompile.kore`: three rules, each with a variable of its
  axiom that a rule read from it does not hold, at a sort with a value (Val, with `v()`; Int).
  Run from the package root: `lake env lean -j1 test/TieE3MlLhsValueSortRule.lean`. Every statement
  is on the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Each sentence states its rewrite for every element of its variables' sorts. Γ's item of a rule
  read without a variable states the rewrite once. The sentence entails the item (W1, class
  *weaker*: the item has the conjunct `⌈r⌉`, `ruleRightDefined`, more on its left side) where the
  variable's sort has an element, which the text's G-nonempty item of the sort gives (an item of
  the signature of `Theory.ofDefinition kore` that `ΓSig` does not hold); at a sort without
  an element the sentence states nothing and the direction fails, and the reader refuses such a
  sentence (`unheldVariable`).

  - Sentence 186, `e(_:Val) #Or d() => b()`, two rules (`orSplit`). `rE`, `e(X) => b()`, holds the
    variable: the sentence is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's axiom and
    `e(X)` is in the disjunction (`rule_textE`, `leftE`, `TieRuleLhs.rule_w1`). `rD`, `d() => b()`,
    does not: the sentence at an element of Val, which Val's G-nonempty item gives, is the item of
    `rD` (`rule_textD`, `leftD`, `TieRuleUnheld.rule_w1_drop`); `d()` is in Exp by the arity item
    of the constant `d` (`d_inh`).
  - Sentence 187, `p(_:Int) #Or q(_:Int) => b()`, two rules. Each holds its disjunct's variable and
    not the other's: the sentence at an element of Int for the other variable (Int's G-nonempty
    item) is the rule's item (`rule_textP`, `rule_textQ`, `leftP`, `leftQ`).
  - Sentence 188, `c(#Exists Y:Val. a()) => b()`, one rule `rC`, `c(a()) => b()`
    (`existsAsVariable`, the binder dropped). `a()` is in `\exists Y:Val. a()` where Val has an
    element (`TieRuleUnheld.sub_exists_unheld`), so the sentence entails the item (`rule_textC`,
    `ruleC_item`, `leftC`).
  `rule_from_text_aux`: each of Γ's five rule items is a consequence of its sentence with the
  G-nonempty items of Val and Int (`ruleSigAux`, `ruleSigAux_text`) and `ΓSig`, for every H; no
  item of `ΓDomains` is a premise. `consistent` for every H.

  The expectations (C7 form (a), from sentences; a step that exists), from `Pre H` (the function
  equations as written, Γ's rule items, the families; it has a model, `pre_model`), one per
  disjunct and one for the `\exists`: `step_e` (`e(v())` steps to `b()`), `step_d`, `step_p`
  (`p(1)`), `step_q` (`q(1)`), `step_c` (`c(a())`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

deriving instance DecidableEq for KoreAML.SortDecl

namespace KCore.TieE3MlLhsValueSortRule

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-lhs-value-sort.kompile.kore"
definition_of defn from "f2-examples/e3-ml-lhs-value-sort.kompile.kore"
user_axioms U from "f2-examples/e3-ml-lhs-value-sort.kompile.kore" module "E3-ML-LHS-VALUE-SORT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

def kCell : Sym := 384
def symA : Sym := 386
def symB : Sym := 387
def symC : Sym := 388
def symD : Sym := 389
def symE : Sym := 390
def symP : Sym := 391
def symQ : Sym := 392
def symV : Sym := 393
def sVal : Srt := 32
def sExp : Srt := 33

theorem names : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧
    c.symName symC = "Lblc" ∧ c.symName symD = "Lbld" ∧ c.symName symE = "Lble" ∧ c.symName symP = "Lblp" ∧
    c.symName symQ = "Lblq" ∧ c.symName symV = "Lblv" := by
  decide +kernel

theorem sort_names : c.sortName sVal = "Val" ∧ c.sortName sExp = "Exp" ∧ c.sortName Srt.int = "Int" := by
  decide +kernel

/-! ## The function equations (for the premises of the expectations) -/

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- The function equations as written. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-! ## The rules: Γ's five axioms -/

noncomputable def rE : Rule := c.rules[0]'(by decide +kernel)
noncomputable def rD : Rule := c.rules[1]'(by decide +kernel)
noncomputable def rP : Rule := c.rules[2]'(by decide +kernel)
noncomputable def rQ : Rule := c.rules[3]'(by decide +kernel)
noncomputable def rC : Rule := c.rules[4]'(by decide +kernel)

/-- Γ's axioms of the rules: `e(X) => b()`, `d() => b()`, `p(X) => b()`, `q(X) => b()`,
`c(a()) => b()`. -/
noncomputable def pE : Kore.Pattern := prioRuleK c rE
noncomputable def pD : Kore.Pattern := prioRuleK c rD
noncomputable def pP : Kore.Pattern := prioRuleK c rP
noncomputable def pQ : Kore.Pattern := prioRuleK c rQ
noncomputable def pC : Kore.Pattern := prioRuleK c rC

theorem ruleItems_eq : ruleItems c =
    [trAxiom [] [] ⟨0, "kernel", ⟨[], pE, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], pD, []⟩⟩,
     trAxiom [] [] ⟨0, "kernel", ⟨[], pP, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], pQ, []⟩⟩,
     trAxiom [] [] ⟨0, "kernel", ⟨[], pC, []⟩⟩] := by kernel_rfl

/-- The parts `\rewrites{C}(L', r)` of an axiom. -/
noncomputable def partsOf (p : Kore.Pattern) : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

noncomputable def qE := partsOf pE
noncomputable def qD := partsOf pD
noncomputable def qP := partsOf pP
noncomputable def qQ := partsOf pQ
noncomputable def qC := partsOf pC

kernel_rfl qE_eq : TieRuleLhs.rwParts pE = some qE
kernel_rfl qD_eq : TieRuleLhs.rwParts pD = some qD
kernel_rfl qP_eq : TieRuleLhs.rwParts pP = some qP
kernel_rfl qQ_eq : TieRuleLhs.rwParts pQ = some qQ
kernel_rfl qC_eq : TieRuleLhs.rwParts pC = some qC

/-- The context of a left side's term around the subterm at `path`, and the subterm. -/
noncomputable def cutOf (path : List Nat) (q : Kore.KSort × Kore.Pattern × Kore.Pattern) : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt path (TieRuleLhs.andHead q.2.1)).getD (.hole, .top KoreAML.R)

/-- Around the item of the `k` cell, for the four rules read from a disjunction. -/
noncomputable def cutE := cutOf [0, 0, 0, 0] qE
noncomputable def cutD := cutOf [0, 0, 0, 0] qD
noncomputable def cutP := cutOf [0, 0, 0, 0] qP
noncomputable def cutQ := cutOf [0, 0, 0, 0] qQ
/-- Around the argument of `c`. -/
noncomputable def cutC := cutOf [0, 0, 0, 0, 0] qC

kernel_rfl lE_eq : qE.2.1 = .and qE.1 (cutE.1.fill cutE.2 :: .top qE.1 :: (TieRuleLhs.andTail qE.2.1).drop 1)
kernel_rfl lD_eq : qD.2.1 = .and qD.1 (cutD.1.fill cutD.2 :: .top qD.1 :: (TieRuleLhs.andTail qD.2.1).drop 1)
kernel_rfl lP_eq : qP.2.1 = .and qP.1 (cutP.1.fill cutP.2 :: .top qP.1 :: (TieRuleLhs.andTail qP.2.1).drop 1)
kernel_rfl lQ_eq : qQ.2.1 = .and qQ.1 (cutQ.1.fill cutQ.2 :: .top qQ.1 :: (TieRuleLhs.andTail qQ.2.1).drop 1)
kernel_rfl lC_eq : qC.2.1 = .and qC.1 (cutC.1.fill cutC.2 :: .top qC.1 :: (TieRuleLhs.andTail qC.2.1).drop 1)

/-- The variable of `rE`, of Val, and of `rP` and `rQ`, of Int (the first of each rule). -/
noncomputable def xV : Kore.EVar := KoreAML.evar "VarV0" (KoreAML.srt "Val")
noncomputable def xI : Kore.EVar := KoreAML.evar "VarV0" (KoreAML.srt "Int")

/-- The variable of the sentence that the rule does not hold: a name no axiom of Γ holds. -/
noncomputable def yV : Kore.EVar := KoreAML.evar "VarUnheld" (KoreAML.srt "Val")
noncomputable def yI : Kore.EVar := KoreAML.evar "VarUnheld" (KoreAML.srt "Int")

-- The subterms as Γ writes them.
kernel_rfl dE_eq : cutE.2 = symApp c symE [.var (.evar xV)]
kernel_rfl dD_eq : cutD.2 = symApp c symD []
kernel_rfl dP_eq : cutP.2 = symApp c symP [.var (.evar xI)]
kernel_rfl dQ_eq : cutQ.2 = symApp c symQ [.var (.evar xI)]
kernel_rfl dC_eq : cutC.2 = symApp c symA []

/-! ## The left sides as the text writes them -/

/-- Sentence 186 in the variables of `rE`: the item of the `k` cell is `\or{SortExp{}}(e(X), d())`. -/
noncomputable def LtextE : Kore.Pattern :=
  .and qE.1 [cutE.1.fill (.or (KoreAML.srt "Exp") [cutE.2, symApp c symD []]), .top qE.1]

/-- Sentence 186 in the variables of `rD`, with the variable `rD` does not hold. -/
noncomputable def LtextD : Kore.Pattern :=
  .and qD.1 [cutD.1.fill (.or (KoreAML.srt "Exp") [symApp c symE [.var (.evar yV)], cutD.2]), .top qD.1]

/-- Sentence 187 in the variables of `rP`: `\or{SortExp{}}(p(X), q(Y))`, Y not held by `rP`. -/
noncomputable def LtextP : Kore.Pattern :=
  .and qP.1 [cutP.1.fill (.or (KoreAML.srt "Exp") [cutP.2, symApp c symQ [.var (.evar yI)]]), .top qP.1]

/-- Sentence 187 in the variables of `rQ`: `\or{SortExp{}}(p(Y), q(X))`, Y not held by `rQ`. -/
noncomputable def LtextQ : Kore.Pattern :=
  .and qQ.1 [cutQ.1.fill (.or (KoreAML.srt "Exp") [symApp c symP [.var (.evar yI)], cutQ.2]), .top qQ.1]

/-- Sentence 188 in the variables of `rC`: the argument of `c` is `\exists{SortExp{}}(Y:Val, a())`. -/
noncomputable def LtextC : Kore.Pattern :=
  .and qC.1 [cutC.1.fill (.exist (KoreAML.srt "Exp") yV cutC.2), .top qC.1]

noncomputable def fTE : List VarKey := (freeOf [] (.rewrites qE.1 LtextE qE.2.2)).eraseDups
noncomputable def fTD : List VarKey := (freeOf [] (.rewrites qD.1 LtextD qD.2.2)).eraseDups
noncomputable def fTP : List VarKey := (freeOf [] (.rewrites qP.1 LtextP qP.2.2)).eraseDups
noncomputable def fTQ : List VarKey := (freeOf [] (.rewrites qQ.1 LtextQ qQ.2.2)).eraseDups
noncomputable def fTC : List VarKey := (freeOf [] (.rewrites qC.1 LtextC qC.2.2)).eraseDups

/-- The table of sentence 188's form: the bound variable first, as in the text. -/
noncomputable def tC : VarTable := tableOf [] (.rewrites qC.1 LtextC qC.2.2)

/-! ## Each sentence is the item of its form (kernel), up to the indices of the variables -/

theorem rule_textE : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] pE) fTE qE.1 LtextE qE.2.2) [] = some (trS U.ax186).pat := by
  decide +kernel
theorem fT_freeE : fTE.all (fun k => (freeOf [] pE).eraseDups.contains k) = true := by decide +kernel
theorem K_noAliasE : cutE.1.noAlias ⟨tableOf [] pE, []⟩ = true := by decide +kernel

theorem rule_textD : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] pD) fTD qD.1 LtextD qD.2.2) [(3, 9), (2, 3), (1, 2), (9, 1)] = some (trS U.ax186).pat := by
  decide +kernel
theorem K_noAliasD : cutD.1.noAlias ⟨tableOf [] pD, []⟩ = true := by decide +kernel

theorem rule_textP : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] pP) fTP qP.1 LtextP qP.2.2) [(4, 9), (3, 4), (2, 3), (9, 2)] = some (trS U.ax187).pat := by
  decide +kernel
theorem K_noAliasP : cutP.1.noAlias ⟨tableOf [] pP, []⟩ = true := by decide +kernel

theorem rule_textQ : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] pQ) fTQ qQ.1 LtextQ qQ.2.2) [(4, 9), (3, 4), (2, 3), (1, 2), (9, 1)] = some (trS U.ax187).pat := by
  decide +kernel
theorem K_noAliasQ : cutQ.1.noAlias ⟨tableOf [] pQ, []⟩ = true := by decide +kernel

/-- Sentence 188 is the item of its form at the form's own table. -/
theorem rule_textC : TiePair.renSeq (TieRuleLhs.itemAt tC fTC qC.1 LtextC qC.2.2) [] = some (trS U.ax188).pat := by
  decide +kernel
/-- Γ's item of `rC` is the item of its axiom at that table, up to the indices of the variables. -/
theorem ruleC_item : TiePair.renSeq (TieRuleLhs.itemAt tC fTC qC.1 qC.2.1 qC.2.2) [(2, 1), (3, 2)] =
    some (trAxiom [] [] ⟨0, "kernel", ⟨[], pC, []⟩⟩).pat := by
  decide +kernel
theorem K_noAliasC : cutC.1.noAlias ⟨tC, []⟩ = true := by decide +kernel

/-! ## The variable a rule does not hold is in no part of its item -/

theorem dropD : (∀ k ∈ fTD, k = evarKey yV ∨ k ∈ (freeOf [] pD).eraseDups) ∧
    (tr ⟨tableOf [] pD, []⟩ (.rewrites qD.1 qD.2.1 qD.2.2) ≡ inhOf (trSort (tableOf [] pD) qD.1)).isFreeEvar
      ((tableOf [] pD).ev (evarKey yV)) = false ∧
    (∀ k ∈ (freeOf [] pD).eraseDups, (guardOf (tableOf [] pD) k).isFreeEvar ((tableOf [] pD).ev (evarKey yV)) = false) := by
  decide +kernel

theorem dropP : (∀ k ∈ fTP, k = evarKey yI ∨ k ∈ (freeOf [] pP).eraseDups) ∧
    (tr ⟨tableOf [] pP, []⟩ (.rewrites qP.1 qP.2.1 qP.2.2) ≡ inhOf (trSort (tableOf [] pP) qP.1)).isFreeEvar
      ((tableOf [] pP).ev (evarKey yI)) = false ∧
    (∀ k ∈ (freeOf [] pP).eraseDups, (guardOf (tableOf [] pP) k).isFreeEvar ((tableOf [] pP).ev (evarKey yI)) = false) := by
  decide +kernel

theorem dropQ : (∀ k ∈ fTQ, k = evarKey yI ∨ k ∈ (freeOf [] pQ).eraseDups) ∧
    (tr ⟨tableOf [] pQ, []⟩ (.rewrites qQ.1 qQ.2.1 qQ.2.2) ≡ inhOf (trSort (tableOf [] pQ) qQ.1)).isFreeEvar
      ((tableOf [] pQ).ev (evarKey yI)) = false ∧
    (∀ k ∈ (freeOf [] pQ).eraseDups, (guardOf (tableOf [] pQ) k).isFreeEvar ((tableOf [] pQ).ev (evarKey yI)) = false) := by
  decide +kernel

/-- The body `a()` of the `\exists` does not hold its variable. -/
theorem freeC : (tr ⟨tC, []⟩ cutC.2).isFreeEvar (tC.ev (evarKey yV)) = false := by decide +kernel

/-! ## Elements of the sorts, and the disjuncts' sort -/

def vV : GroundTerm := .ctor symV []
def dV : GroundTerm := .ctor symD []

/-- The items of the text's signature that give Val and Int an element (G-nonempty of the
declarations `sort SortVal{}` and `hooked-sort SortInt{}`), which `ΓSig` does not hold. -/
def valNonempty : Item := nonemptyItem ⟨"SortVal", [], false⟩
def intNonempty : Item := nonemptyItem ⟨"SortInt", [], true⟩

theorem sortDecls_mem : (⟨"SortVal", [], false⟩ : SortDecl) ∈ kore.sortDecls ∧
    (⟨"SortInt", [], true⟩ : SortDecl) ∈ kore.sortDecls := by decide +kernel

/-- G-nonempty of a declared sort is an item of the signature of the text's theory. -/
theorem nonempty_text {sd : SortDecl} (h : sd ∈ kore.sortDecls) :
    nonemptyItem sd ∈ (Theory.ofDefinition kore).signature := by
  simp only [Theory.ofDefinition, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨_, h, rfl⟩)))))

/-- **Val has an element**, in a model of Val's G-nonempty item. -/
theorem val_elem {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hN : I ⊧ᴵ valNonempty.pat) : ∃ a, InS I "Val" a :=
  nonempty_of hD hN (e := KoreAML.val0)

/-- **Int has an element**, in a model of Int's G-nonempty item. -/
theorem int_elem {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hN : I ⊧ᴵ intNonempty.pat) : ∃ a, InS I "Int" a :=
  nonempty_of hD hN (e := KoreAML.val0)

/-- `d`'s signature: a constant of Exp. -/
def kd : CtorSig := ⟨symD, [], sExp⟩

theorem kd_mem : kd ∈ kernelSyms c := by decide +kernel
theorem noInst_d : instDecode? (c.symName kd.name) = none := by decide +kernel

/-- **The arity of a constant, from `ΓSig`**: what a symbol of no argument denotes is in its result
sort. -/
theorem app0_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {k : CtorSig} (hk : k ∈ kernelSyms c) (hargs : k.args = [])
    (hno : instDecode? (c.symName k.name) = none) {t : VarTable} {e : Valuation M} (m : M)
    (h : (tr ⟨t, []⟩ (symApp c k.name [])).interpret I e m) : InS I (c.sortName k.result) m := by
  rw [tr_symApp, trArgs_appList, interp_appList] at h
  obtain ⟨a, ha, bs, hbs, hm⟩ := h
  cases hbs
  have hit : I ⊧ᴵ (symArityItem c k).pat := hS _ (Or.inl (Or.inl ⟨_, sig_arity hk, rfl⟩))
  rw [symArityItem_noInst hno] at hit
  rw [symHead_noInst (c := c) hno] at ha
  unfold KoreAML.arityItem at hit
  dsimp only [KoreAML.paramTable, List.map_nil] at hit
  have hinc := (KoreAML.interp_included hD).mp (hit KoreAML.val0 default) m
  unfold srtOf at hinc
  rw [trSort_srt] at hinc
  apply (inS_iff (I := I) KoreAML.val0).mp
  apply hinc
  rw [interp_appList]
  refine ⟨a, ((Closed.sym _).interp e KoreAML.val0 a).mp ha, [], ?_, hm⟩
  simp only [hargs, List.map_nil]
  exact .nil

/-- **`d()` denotes elements of Exp** (the arity of the constant `d`, `ΓSig`). -/
theorem d_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M}
    (b : M) (h : (tr ⟨t, []⟩ (symApp c symD [])).interpret I e b) :
    (inhOf (trSort t (KoreAML.srt "Exp"))).interpret I e b := by
  have h1 := app0_inh hD hS (k := kd) kd_mem rfl noInst_d b h
  rw [show c.sortName kd.result = "Exp" from sort_names.2.1] at h1
  rw [trSort_srt]
  exact (inS_iff _).mpr h1

/-- The signatures of `e`, `p` and `q`. -/
def ke : CtorSig := ⟨symE, [sVal], sExp⟩
def kp : CtorSig := ⟨symP, [Srt.int], sExp⟩
def kq : CtorSig := ⟨symQ, [Srt.int], sExp⟩

theorem k_mem : ke ∈ kernelSyms c ∧ kp ∈ kernelSyms c ∧ kq ∈ kernelSyms c := by decide +kernel
theorem noInst : instDecode? (c.symName ke.name) = none ∧ instDecode? (c.symName kp.name) = none ∧
    instDecode? (c.symName kq.name) = none := by decide +kernel

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- The guard of a variable of the sort n puts its value in n. -/
theorem x_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {t : VarTable}
    {e : Valuation M} {m0 : M} {x : Kore.EVar} {n : String} (hx : x.sort = KoreAML.srt n)
    (hg : (guardOf t (evarKey x)).interpret I e m0)
    (b : M) (h : (tr ⟨t, []⟩ (.var (.evar x))).interpret I e b) : InS I n b := by
  have h1 := (TieRuleLhs.guard_evarKey hD).mp hg
  simp only [tr] at h
  rw [interp_evar] at h
  rw [h]
  rw [hx, trSort_srt] at h1
  exact (inS_iff _).mp h1

/-- **`e` at a pattern whose elements are in Val is in Exp** (the arity of `e`, `ΓSig`). -/
theorem e_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {p : Kore.Pattern}
    (hp : ∀ b, (tr ⟨t, []⟩ p).interpret I e b → InS I "Val" b) (m : M)
    (h : (tr ⟨t, []⟩ (symApp c symE [p])).interpret I e m) :
    (inhOf (trSort t (KoreAML.srt "Exp"))).interpret I e m := by
  have h1 := TieRuleUnheld.app1_inh hD hS (k := ke) (s := sVal) k_mem.1 rfl noInst.1
    (fun b hb => by rw [show c.sortName sVal = "Val" from sort_names.1]; exact hp b hb) m h
  rw [show c.sortName ke.result = "Exp" from sort_names.2.1] at h1
  rw [trSort_srt]
  exact (inS_iff _).mpr h1

/-- **`p` at a pattern whose elements are in Int is in Exp.** -/
theorem p_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {p : Kore.Pattern}
    (hp : ∀ b, (tr ⟨t, []⟩ p).interpret I e b → InS I "Int" b) (m : M)
    (h : (tr ⟨t, []⟩ (symApp c symP [p])).interpret I e m) :
    (inhOf (trSort t (KoreAML.srt "Exp"))).interpret I e m := by
  have h1 := TieRuleUnheld.app1_inh hD hS (k := kp) (s := Srt.int) k_mem.2.1 rfl noInst.2.1
    (fun b hb => by rw [show c.sortName Srt.int = "Int" from sort_names.2.2]; exact hp b hb) m h
  rw [show c.sortName kp.result = "Exp" from sort_names.2.1] at h1
  rw [trSort_srt]
  exact (inS_iff _).mpr h1

/-- **`q` at a pattern whose elements are in Int is in Exp.** -/
theorem q_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {p : Kore.Pattern}
    (hp : ∀ b, (tr ⟨t, []⟩ p).interpret I e b → InS I "Int" b) (m : M)
    (h : (tr ⟨t, []⟩ (symApp c symQ [p])).interpret I e m) :
    (inhOf (trSort t (KoreAML.srt "Exp"))).interpret I e m := by
  have h1 := TieRuleUnheld.app1_inh hD hS (k := kq) (s := Srt.int) k_mem.2.2 rfl noInst.2.2
    (fun b hb => by rw [show c.sortName Srt.int = "Int" from sort_names.2.2]; exact hp b hb) m h
  rw [show c.sortName kq.result = "Exp" from sort_names.2.1] at h1
  rw [trSort_srt]
  exact (inS_iff _).mpr h1

theorem x_freeE : evarKey xV ∈ (freeOf [] pE).eraseDups := by decide +kernel
theorem x_inP : evarKey xI ∈ fTP := by decide +kernel
theorem x_inQ : evarKey xI ∈ fTQ := by decide +kernel

/-! ## Every element of Γ's left side is one of the text's -/

/-- `rE`: `e(X)` is in `\or{SortExp{}}(e(X), d())`. -/
theorem leftE {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) (e : Valuation M) (m0 a : M)
    (hg : ∀ k ∈ (freeOf [] pE).eraseDups, (guardOf (tableOf [] pE) k).interpret I e m0)
    (h : (tr ⟨tableOf [] pE, []⟩ qE.2.1).interpret I e a) : (tr ⟨tableOf [] pE, []⟩ LtextE).interpret I e a := by
  rw [lE_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold LtextE
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ cutE.1 K_noAliasE (TieRuleLhs.sub_or_left fun a' h' => ?_) a (h _ (List.mem_cons_self ..))
    rw [dE_eq] at h'
    exact e_inh hD hS (fun b hb => x_inh hD rfl (hg _ x_freeE) b hb) a' h'
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- `rD`: `d()` is in `\or{SortExp{}}(e(Y), d())`. -/
theorem leftD {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) (e : Valuation M) (a : M)
    (h : (tr ⟨tableOf [] pD, []⟩ qD.2.1).interpret I e a) : (tr ⟨tableOf [] pD, []⟩ LtextD).interpret I e a := by
  rw [lD_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold LtextD
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ cutD.1 K_noAliasD (TieRuleLhs.sub_or_right fun a' h' => ?_) a (h _ (List.mem_cons_self ..))
    rw [dD_eq] at h'
    exact d_inh hD hS a' h'
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- `rP`: `p(X)` is in `\or{SortExp{}}(p(X), q(Y))`. -/
theorem leftP {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) (e : Valuation M) (m0 a : M)
    (hg : ∀ k ∈ fTP, (guardOf (tableOf [] pP) k).interpret I e m0)
    (h : (tr ⟨tableOf [] pP, []⟩ qP.2.1).interpret I e a) : (tr ⟨tableOf [] pP, []⟩ LtextP).interpret I e a := by
  rw [lP_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold LtextP
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ cutP.1 K_noAliasP (TieRuleLhs.sub_or_left fun a' h' => ?_) a (h _ (List.mem_cons_self ..))
    rw [dP_eq] at h'
    exact p_inh hD hS (fun b hb => x_inh hD rfl (hg _ x_inP) b hb) a' h'
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- `rQ`: `q(X)` is in `\or{SortExp{}}(p(Y), q(X))`. -/
theorem leftQ {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) (e : Valuation M) (m0 a : M)
    (hg : ∀ k ∈ fTQ, (guardOf (tableOf [] pQ) k).interpret I e m0)
    (h : (tr ⟨tableOf [] pQ, []⟩ qQ.2.1).interpret I e a) : (tr ⟨tableOf [] pQ, []⟩ LtextQ).interpret I e a := by
  rw [lQ_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold LtextQ
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine TieRuleLhs.tr_fill_mono _ cutQ.1 K_noAliasQ (TieRuleLhs.sub_or_right fun a' h' => ?_) a (h _ (List.mem_cons_self ..))
    rw [dQ_eq] at h'
    exact q_inh hD hS (fun b hb => x_inh hD rfl (hg _ x_inQ) b hb) a' h'
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- `rC`: `a()` is in `\exists Y:Val. a()`, Val having an element. -/
theorem leftC {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hex : ∃ a, InS I "Val" a) (e : Valuation M) (a : M)
    (h : (tr ⟨tC, []⟩ qC.2.1).interpret I e a) : (tr ⟨tC, []⟩ LtextC).interpret I e a := by
  rw [lC_eq, interp_and (List.cons_ne_nil _ _)] at h
  unfold LtextC
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact TieRuleLhs.tr_fill_mono _ cutC.1 K_noAliasC
      (fun a' h' => TieRuleUnheld.sub_exists_unheld hD rfl hex freeC a' h') a (h _ (List.mem_cons_self ..))
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-! ## W1 -/

/-- The rule sentences. -/
noncomputable def ruleText : List AxiomDecl := [U.ax186, U.ax187, U.ax188]

/-- The sentence each of Γ's rule items is read from, in `ruleItems`' order. -/
noncomputable def ruleTextOf : List AxiomDecl := [U.ax186, U.ax186, U.ax187, U.ax187, U.ax188]

/-- No other sentence of the text is a premise. -/
noncomputable def ruleAux : List AxiomDecl := []

/-- The items of the text's signature the statement reads, which `ΓSig` does not hold: Val and Int
have an element. -/
def ruleSigAux : List Item := [nonemptyItem ⟨"SortVal", [], false⟩, nonemptyItem ⟨"SortInt", [], true⟩]

/-- Each item of `ruleSigAux` is an item of the signature of the text's theory. -/
theorem ruleSigAux_text : ∀ it ∈ ruleSigAux, it ∈ (Theory.ofDefinition kore).signature := by
  intro it hit
  rcases List.mem_cons.mp hit with rfl | hit
  · exact nonempty_text sortDecls_mem.1
  · rw [List.mem_singleton.mp hit]; exact nonempty_text sortDecls_mem.2

/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's five rule items, with its
premise `⌈r⌉`, is a consequence of the sentence it is read from (`ruleTextOf`) with the G-nonempty
items of Val and Int (`ruleSigAux`) and the text's signature (`ΓSig`), for every H. The signature
gives the arities of `e`, `p` and `q` (a disjunct `f(X)` is in `\or{SortExp{}}`) and of the
constant `d` (`d()` is in Exp); the G-nonempty items give, for the four items that do not hold a
variable of their sentence, an element of that variable's sort. No item of `ΓDomains` is a
premise. -/
theorem rule_from_text_aux (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText,
    TiePair.Texts ((trS ad).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪ ΓSig (cH H) ⊧ it.pat := by
  have pre : ∀ {ad : AxiomDecl} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M},
      I ⊧ᴵP (TiePair.Texts ((trS ad).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪ ΓSig (cH H)) →
        DefOK I ∧ (I ⊧ᴵ (trS ad).pat) ∧ (I ⊧ᴵP ΓSig c) ∧ (I ⊧ᴵ valNonempty.pat) ∧ (I ⊧ᴵ intNonempty.pat) := fun hI =>
    ⟨TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ),
     hI _ (Or.inl (Or.inl (List.mem_cons_self ..))),
     fun φ hφ => hI φ (Or.inr (by unfold ΓSig at hφ ⊢; rw [sigItems_withHooks]; exact hφ)),
     hI _ (Or.inl (Or.inl (by simp [ruleAux, ruleSigAux, valNonempty]))),
     hI _ (Or.inl (Or.inl (by simp [ruleAux, ruleSigAux, intNonempty])))⟩
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl | rfl
  · refine ⟨U.ax186, by simp [ruleText], ?_⟩
    intro M _ I hI
    obtain ⟨hD, hT, hS, -, -⟩ := pre hI
    exact TieRuleLhs.rule_w1 hD qE_eq rule_textE fT_freeE hT fun e m0 hg a ha => leftE hD hS e m0 a hg ha
  · refine ⟨U.ax186, by simp [ruleText], ?_⟩
    intro M _ I hI
    obtain ⟨hD, hT, hS, hV, -⟩ := pre hI
    exact TieRuleUnheld.rule_w1_drop hD (x := yV) rfl qD_eq rule_textD dropD.1 dropD.2.1 dropD.2.2
      (val_elem hD hV) hT fun e _ _ a ha => leftD hD hS e a ha
  · refine ⟨U.ax187, by simp [ruleText], ?_⟩
    intro M _ I hI
    obtain ⟨hD, hT, hS, -, hN⟩ := pre hI
    exact TieRuleUnheld.rule_w1_drop hD (x := yI) rfl qP_eq rule_textP dropP.1 dropP.2.1 dropP.2.2
      (int_elem hD hN) hT fun e m0 hg a ha => leftP hD hS e m0 a hg ha
  · refine ⟨U.ax187, by simp [ruleText], ?_⟩
    intro M _ I hI
    obtain ⟨hD, hT, hS, -, hN⟩ := pre hI
    exact TieRuleUnheld.rule_w1_drop hD (x := yI) rfl qQ_eq rule_textQ dropQ.1 dropQ.2.1 dropQ.2.2
      (int_elem hD hN) hT fun e m0 hg a ha => leftQ hD hS e m0 a hg ha
  · refine ⟨U.ax188, by simp [ruleText], ?_⟩
    intro M _ I hI
    obtain ⟨hD, hT, -, hV, -⟩ := pre hI
    have h1 : I ⊧ᴵ TieRuleLhs.itemAt tC fTC qC.1 qC.2.1 qC.2.2 := fun e m =>
      TieRuleLhs.lhs_entails hD (fT := fTC) (fG := fTC) (fun _ hk => hk) ((TiePair.renSeq_iff rule_textC).mp hT) e m
        (fun _ a ha => leftC hD (val_elem hD hV) e a ha)
    exact (TiePair.renSeq_iff ruleC_item).mpr h1

/-- The priority each sentence's attributes state is its rules'. -/
theorem rule_prios : ruleTextOf.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) = c.rules.map (·.prio) := by
  decide +kernel

/-! ## The facts the deciders leave -/

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel

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
reading of the rule sentences 186, 187 and 188, each a consequence of its sentence by
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
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem it, .ctor dotk []]], .ctor counterLabel [.dv Srt.int (.int 0)]]

/-- A step the rules' check accepts on the data, as a consequence of `Pre H`: `⟦x⟧ → •⟦y⟧`. -/
theorem step_from {x y : Config c} (h : c.rules.any (fun r => Cert.checkStep c 50 r x.val y.val) = true) (H : HookParams) :
    Pre H ⊧ (den (cH H) x.val ⇒ KoreAML.sNext (den (cH H) y.val)) :=
  TiePair.cut (shapeH H) (sound_at_step _ (coreOKH H) (hrcH H) _ _ (TieRuleLhs.step_everyH hok hsr hmr noRaw h H))

def EV : Config c := ⟨cfg (.ctor symE [vV]), by decide +kernel⟩
def D : Config c := ⟨cfg dV, by decide +kernel⟩
def P1 : Config c := ⟨cfg (.ctor symP [.dv Srt.int (.int 1)]), by decide +kernel⟩
def Q1 : Config c := ⟨cfg (.ctor symQ [.dv Srt.int (.int 1)]), by decide +kernel⟩
def CA : Config c := ⟨cfg (.ctor symC [.ctor symA []]), by decide +kernel⟩
def B : Config c := ⟨cfg (.ctor symB []), by decide +kernel⟩

/-- **`e(v())` steps to `b()`, derived from `Pre`**, for every H (the rule read from the first
disjunct of sentence 186). -/
theorem step_e (H : HookParams) : Pre H ⊧ (den (cH H) EV.val ⇒ KoreAML.sNext (den (cH H) B.val)) :=
  step_from (x := EV) (y := B) (by decide +kernel) H

/-- **`d()` steps to `b()`, derived from `Pre`**, for every H (the second disjunct of 186: the rule
without the variable of the first). -/
theorem step_d (H : HookParams) : Pre H ⊧ (den (cH H) D.val ⇒ KoreAML.sNext (den (cH H) B.val)) :=
  step_from (x := D) (y := B) (by decide +kernel) H

/-- **`p(1)` steps to `b()`, derived from `Pre`**, for every H (the first disjunct of 187). -/
theorem step_p (H : HookParams) : Pre H ⊧ (den (cH H) P1.val ⇒ KoreAML.sNext (den (cH H) B.val)) :=
  step_from (x := P1) (y := B) (by decide +kernel) H

/-- **`q(1)` steps to `b()`, derived from `Pre`**, for every H (the second disjunct of 187). -/
theorem step_q (H : HookParams) : Pre H ⊧ (den (cH H) Q1.val ⇒ KoreAML.sNext (den (cH H) B.val)) :=
  step_from (x := Q1) (y := B) (by decide +kernel) H

/-- **`c(a())` steps to `b()`, derived from `Pre`**, for every H (sentence 188: the rule without
the bound variable). -/
theorem step_c (H : HookParams) : Pre H ⊧ (den (cH H) CA.val ⇒ KoreAML.sNext (den (cH H) B.val)) :=
  step_from (x := CA) (y := B) (by decide +kernel) H

end KCore.TieE3MlLhsValueSortRule

#check @KCore.TieE3MlLhsValueSortRule.rule_textE
#check @KCore.TieE3MlLhsValueSortRule.rule_textD
#check @KCore.TieE3MlLhsValueSortRule.rule_textP
#check @KCore.TieE3MlLhsValueSortRule.rule_textQ
#check @KCore.TieE3MlLhsValueSortRule.rule_textC
#check @KCore.TieE3MlLhsValueSortRule.ruleC_item
#check @KCore.TieE3MlLhsValueSortRule.rule_from_text_aux
#check @KCore.TieE3MlLhsValueSortRule.ruleSigAux_text
#check @KCore.TieE3MlLhsValueSortRule.rule_prios
#check @KCore.TieE3MlLhsValueSortRule.consistent
#check @KCore.TieE3MlLhsValueSortRule.pre_model
#check @KCore.TieE3MlLhsValueSortRule.step_e
#check @KCore.TieE3MlLhsValueSortRule.step_d
#check @KCore.TieE3MlLhsValueSortRule.step_p
#check @KCore.TieE3MlLhsValueSortRule.step_q
#check @KCore.TieE3MlLhsValueSortRule.step_c
#print axioms KCore.TieE3MlLhsValueSortRule.coreOK
#print axioms KCore.TieE3MlLhsValueSortRule.shape
#print axioms KCore.TieE3MlLhsValueSortRule.rule_textE
#print axioms KCore.TieE3MlLhsValueSortRule.rule_textD
#print axioms KCore.TieE3MlLhsValueSortRule.rule_textP
#print axioms KCore.TieE3MlLhsValueSortRule.rule_textQ
#print axioms KCore.TieE3MlLhsValueSortRule.rule_textC
#print axioms KCore.TieE3MlLhsValueSortRule.ruleC_item
#print axioms KCore.TieE3MlLhsValueSortRule.rule_from_text_aux
#print axioms KCore.TieE3MlLhsValueSortRule.ruleSigAux_text
#print axioms KCore.TieE3MlLhsValueSortRule.rule_prios
#print axioms KCore.TieE3MlLhsValueSortRule.consistent
#print axioms KCore.TieE3MlLhsValueSortRule.pre_model
#print axioms KCore.TieE3MlLhsValueSortRule.step_e
#print axioms KCore.TieE3MlLhsValueSortRule.step_d
#print axioms KCore.TieE3MlLhsValueSortRule.step_p
#print axioms KCore.TieE3MlLhsValueSortRule.step_q
#print axioms KCore.TieE3MlLhsValueSortRule.step_c
