/-
  The rule sentence of construct fixture e3-ml-lhs-or-rhs-var, beside its tie
  test/TieE3MlLhsOrRhsVar.lean (written by tiegen, which leaves the rule uncovered), on the same
  text `f2-examples/e3-ml-lhs-or-rhs-var.kompile.kore`:
  `rule <k> e(X:Val) #Or d() => r(X) ... </k>`, a left side `\or` one of whose disjuncts does not
  hold the variable the right side reads. Run from the package root:
  `lake env lean -j1 test/TieE3MlLhsOrRhsVarRule.lean`. Every statement is on the literal `defn`,
  for every interpretation H; nothing reads `Parse.parse` or `emit`.

  The rule (sentence 104), class *weaker*. The sentence is `(e(X) ∨ d()) → •r(X)` for every X of
  Val. Γ holds two rule items (`orSplit`), each with the conjunct `⌈r⌉` (`ruleRightDefined`) more
  on its left side: the rule read from `d()` (`rD`), `d() → •r(X)` with X a variable of the rule that its left side does not
  hold (an open variable), and the rule read from `e(X)` (`rE`), `e(X) → •r(X)`. X is free in both items, so each is the
  sentence with one disjunct in the place of the disjunction: the sentence is the item of
  `\rewrites{C}(Ltext, r)` at the table of Γ's axiom (`rule_textD`, `rule_textE`, kernel), and
  every element of Γ's left side is one of `Ltext` (`leftD`, `leftE`): a disjunct is in the
  disjunction where its elements are in Exp, which the arity item of the constant `d` (`ΓSig`,
  `d_inh`) gives for `d()` and the arity of `e` for `e(X)` from the guard of X. So the sentence
  with the text's signature entails each item (`rule_from_text_sig`, `TieRuleLhs.rule_w1`, every
  H); no item of `ΓDomains` is a premise. No element of Val is asked: the variable is in both
  items. The tie closes the sentence with the same section (its `Rules`).

  The expectation (C7 form (a), through the reading; the definition reads a confined sort, so the
  theory is `Γc`): for every value x of Val, `d()` steps to `r(x)` (`step_dr`), and in every model
  of `Γc` the configuration `d()` has `r(x)` as a successor (`sound_dr`), for every H.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlLhsOrRhsVarRule

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-lhs-or-rhs-var.kompile.kore"
definition_of defn from "f2-examples/e3-ml-lhs-or-rhs-var.kompile.kore"
user_axioms U from "f2-examples/e3-ml-lhs-or-rhs-var.kompile.kore" module "E3-ML-LHS-OR-RHS-VAR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads a confined sort: its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

def kCell : Sym := 384
def symD : Sym := 386
def symE : Sym := 387
def symR : Sym := 388
def symV : Sym := 389
def sVal : Srt := 32
def sExp : Srt := 33

theorem names : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName symD = "Lbld" ∧ c.symName symE = "Lble" ∧
    c.symName symR = "Lblr" ∧ c.symName symV = "Lblv" ∧ c.sortName sVal = "Val" ∧ c.sortName sExp = "Exp" := by
  decide +kernel

/-! ## The rule (sentence 104): W1 -/

noncomputable def rD : Rule := c.rules[1]'(by decide +kernel)

/-- Γ's axiom of the rule read from `d()`, `d() => r(X)`. -/
noncomputable def pD : Kore.Pattern := prioRuleK c rD

/-- Its parts `\rewrites{C}(L', r)`. -/
noncomputable def qD : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts pD).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl qD_eq : TieRuleLhs.rwParts pD = some qD

/-- The context of its left side's term around the item of the `k` cell, and the item. -/
noncomputable def cutD : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0, 0, 0] (TieRuleLhs.andHead qD.2.1)).getD (.hole, .top KoreAML.R)

noncomputable def rE : Rule := c.rules[0]'(by decide +kernel)

/-- Γ's axiom of the rule read from `e(X)`, `e(X) => r(X)`. -/
noncomputable def pE : Kore.Pattern := prioRuleK c rE

noncomputable def qE : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts pE).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl qE_eq : TieRuleLhs.rwParts pE = some qE

noncomputable def cutE : KoreCutCtx × Kore.Pattern :=
  (TieRuleLhs.cutAt [0, 0, 0, 0] (TieRuleLhs.andHead qE.2.1)).getD (.hole, .top KoreAML.R)

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], pE, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], pD, []⟩⟩] := by kernel_rfl

kernel_rfl lD_eq : qD.2.1 = .and qD.1 (cutD.1.fill cutD.2 :: .top qD.1 :: (TieRuleLhs.andTail qD.2.1).drop 1)
kernel_rfl lE_eq : qE.2.1 = .and qE.1 (cutE.1.fill cutE.2 :: .top qE.1 :: (TieRuleLhs.andTail qE.2.1).drop 1)

/-- The variable X as Γ's rule `rD` names it (its third variable: the left side holds the other two). -/
noncomputable def xD : Kore.EVar := KoreAML.evar "VarV2" (KoreAML.srt "Val")

/-- The variable X as Γ's rule `rE` names it. -/
noncomputable def xE : Kore.EVar := KoreAML.evar "VarV0" (KoreAML.srt "Val")

-- The two disjuncts as Γ writes them: `d()` and `e(X)`.
kernel_rfl dD_eq : cutD.2 = symApp c symD []
kernel_rfl dE_eq : cutE.2 = symApp c symE [.var (.evar xE)]

/-- The left side as the text writes it, in the variables of `rD`: the item of the `k` cell is
`\or{SortExp{}}(e(X), d())`, and no conjunct follows `\top`. -/
noncomputable def LtextD : Kore.Pattern :=
  .and qD.1 [cutD.1.fill (.or (KoreAML.srt "Exp") [symApp c symE [.var (.evar xD)], cutD.2]), .top qD.1]

/-- The same in the variables of `rE`. -/
noncomputable def LtextE : Kore.Pattern :=
  .and qE.1 [cutE.1.fill (.or (KoreAML.srt "Exp") [cutE.2, symApp c symD []]), .top qE.1]

/-- The free variables of the text's form. -/
noncomputable def fTD : List VarKey := (freeOf [] (.rewrites qD.1 LtextD qD.2.2)).eraseDups
noncomputable def fTE : List VarKey := (freeOf [] (.rewrites qE.1 LtextE qE.2.2)).eraseDups

/-- **The text's sentence 104 is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's axiom**,
for each of Γ's two axioms (kernel), up to the indices of the variables: Γ's axiom is the sentence
with one disjunct in the place of the disjunction and the conjunct `⌈r⌉` more. -/
theorem rule_textD : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] pD) fTD qD.1 LtextD qD.2.2) [(3, 9), (2, 3), (1, 2), (9, 1)] = some (trS U.ax104).pat := by
  decide +kernel
theorem fT_freeD : fTD.all (fun k => (freeOf [] pD).eraseDups.contains k) = true := by decide +kernel
theorem K_noAliasD : cutD.1.noAlias ⟨tableOf [] pD, []⟩ = true := by decide +kernel
theorem rule_textE : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] pE) fTE qE.1 LtextE qE.2.2) [] = some (trS U.ax104).pat := by
  decide +kernel
theorem fT_freeE : fTE.all (fun k => (freeOf [] pE).eraseDups.contains k) = true := by decide +kernel
theorem K_noAliasE : cutE.1.noAlias ⟨tableOf [] pE, []⟩ = true := by decide +kernel

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
  rw [show c.sortName kd.result = "Exp" from names.2.2.2.2.2.2] at h1
  rw [trSort_srt]
  exact (inS_iff _).mpr h1

/-- `e`'s signature. -/
def ke : CtorSig := ⟨symE, [sVal], sExp⟩

theorem ke_mem : ke ∈ kernelSyms c := by decide +kernel
theorem noInst_e : instDecode? (c.symName ke.name) = none := by decide +kernel

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- The guard of a variable of Val puts its value in Val. -/
theorem x_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {t : VarTable}
    {e : Valuation M} {m0 : M} {x : Kore.EVar} (hx : x.sort = KoreAML.srt "Val")
    (hg : (guardOf t (evarKey x)).interpret I e m0)
    (b : M) (h : (tr ⟨t, []⟩ (.var (.evar x))).interpret I e b) : InS I "Val" b := by
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
  have h1 := TieRuleUnheld.app1_inh hD hS (k := ke) (s := sVal) ke_mem rfl noInst_e
    (fun b hb => by rw [show c.sortName sVal = "Val" from names.2.2.2.2.2.1]; exact hp b hb) m h
  rw [show c.sortName ke.result = "Exp" from names.2.2.2.2.2.2] at h1
  rw [trSort_srt]
  exact (inS_iff _).mpr h1

theorem xE_free : evarKey xE ∈ (freeOf [] pE).eraseDups := by decide +kernel

/-- Every element of Γ's left side of `rD` is an element of the text's left side: its first
conjunct with `d()` in the place of the disjunction is in the first conjunct of `LtextD`, and its
conjunct `⌈r⌉` is not asked. -/
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

/-- Every element of Γ's left side of `rE` is an element of the text's left side, with `e(X)`. -/
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
    exact e_inh hD hS (fun b hb => x_inh hD rfl (hg _ xE_free) b hb) a' h'
  · rw [List.mem_singleton.mp hp]; exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- The rule sentence. -/
noncomputable def ruleText : List AxiomDecl := [U.ax104]

/-- **W1 for the rule, and the converse for `ruleItems`**: each of Γ's two rule items, with its
premise `⌈r⌉`, is a consequence of the text's sentence 104 with the text's signature (`ΓSig`), for
every H. `\or{SortExp{}}` holds the elements of its disjuncts that are in Exp, and the arities put
them there: of the constant `d` for `d()`, of `e` for `e(X)` from the guard of X. The item of the
rule read from `d()` holds X as the sentence does: no element of Val is a premise. -/
theorem rule_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  refine ⟨U.ax104, List.mem_cons_self .., ?_⟩
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inl (Or.inr ⟨x, rfl⟩))
  have hT : I ⊧ᴵ (trS U.ax104).pat := hI _ (Or.inl (Or.inl ⟨trS U.ax104, List.mem_singleton_self _, rfl⟩))
  have hS : I ⊧ᴵP ΓSig c := fun φ hφ => hI φ (Or.inr (by
    unfold ΓSig at hφ ⊢; rw [sigItems_withHooks]; exact hφ))
  rcases List.mem_cons.mp hit with rfl | hit
  · exact TieRuleLhs.rule_w1 hD qE_eq rule_textE fT_freeE hT fun e m0 hg a ha => leftE hD hS e m0 a hg ha
  · rw [List.mem_singleton.mp hit]
    exact TieRuleLhs.rule_w1 hD qD_eq rule_textD fT_freeD hT fun e _ _ a ha => leftD hD hS e a ha

/-! ## The expectation (C7 form (a), through the reading): `d()` steps to `r(x)` for every value x of Val -/

theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

theorem rD_vars : rD.vars = [Srt.k, 19, sVal] := by decide +kernel
theorem rD_lhs : rD.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symD []), .var 0]], .var 1] := by
  kernel_rfl
theorem rD_rhs : rD.rhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symR [.var 2]), .var 0]], .var 1] := by
  kernel_rfl
theorem rD_shape : rD.req = none ∧ rD.ens = none ∧ rD.pre = .top ∧ rD.post = .top ∧ rD.exs = [] ∧ rD.prio = 50 :=
  ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

/-- The variable X of `rD` is open: no side of the left binds it, and the right side holds it
under the constructor `r`. -/
theorem rD_open : rD.opens = [2] ∧ rD.needsWitness c = false := by decide +kernel

/-- Both rules have the priority 50. -/
theorem prios : ∀ r' ∈ c.rules, r'.prio = 50 := by decide +kernel

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symD = true ∧ c.isCtor symR = true := by
  decide +kernel

theorem syms_okH (H : HookParams) : (cH H).isCtor topLabel = true ∧ (cH H).isCtor kCell = true ∧
    (cH H).isCtor kseq = true ∧ (cH H).isCtor symD = true ∧ (cH H).isCtor symR = true := syms_ok

/-- The configuration `<k> st ~> . </k>` with the counter 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

section Congr
variable {c' : Semantics}

/-- A constructor application has the sort of another of the same constructor whose arguments have
the same sorts. -/
theorem sortOf_ctor_congr_buv {f : Sym} {ts ts0 : List GroundTerm}
    (hl : (lookupSig c'.ctorSigs f).isSome = true)
    (h : c'.sortsOf ts = c'.sortsOf ts0) : c'.sortOf (.ctor f ts) = c'.sortOf (.ctor f ts0) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hl
  simp only [Semantics.sortOf, hk, h]

theorem sortsOf_head_congr_buv {t t0 : GroundTerm} {ts : List GroundTerm} (h : c'.sortOf t = c'.sortOf t0) :
    c'.sortsOf (t :: ts) = c'.sortsOf (t0 :: ts) := by
  simp only [Semantics.sortsOf, h]

theorem sortOf_inj_congr_buv {a b : Srt} {t t0 : GroundTerm} (h : c'.sortOf t = c'.sortOf t0)
    (hi : t.isInj = t0.isInj) : c'.sortOf (.inj a b t) = c'.sortOf (.inj a b t0) := by
  simp only [Semantics.sortOf, h, hi]

end Congr

theorem lookups_ok : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs kCell).isSome = true ∧
    (lookupSig c.ctorSigs kseq).isSome = true ∧ (lookupSig c.ctorSigs symR).isSome = true := by
  decide +kernel

/-- `<k> r(x) </k>` is a configuration for every value x of Val: its sort is that of
`<k> r(v()) </k>`, layer by layer. -/
theorem sortOf_cfgR {x : GroundTerm} (hv : c.sortOf x = some sVal) :
    c.sortOf (cfg (.ctor symR [x])) = some topCellSort := by
  have h0 : c.sortOf (cfg (.ctor symR [.ctor symV []])) = some topCellSort := by decide +kernel
  have hv0 : c.sortOf (.ctor symV []) = some sVal := by decide +kernel
  rw [← h0]
  exact sortOf_ctor_congr_buv lookups_ok.1 (sortsOf_head_congr_buv (sortOf_ctor_congr_buv lookups_ok.2.1
    (sortsOf_head_congr_buv (sortOf_ctor_congr_buv lookups_ok.2.2.1 (sortsOf_head_congr_buv (sortOf_inj_congr_buv
      (sortOf_ctor_congr_buv lookups_ok.2.2.2 (sortsOf_head_congr_buv (by rw [hv, hv0]))) rfl))))))

/-- `<k> d() </k>`. -/
def D (H : HookParams) : Config (cH H) :=
  ⟨cfg (.ctor symD []), by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel⟩

/-- `<k> r(x) </k>`, x a value of Val. -/
def Rx (H : HookParams) (x : GroundTerm) (hv : (cH H).sortOf x = some sVal) : Config (cH H) :=
  ⟨cfg (.ctor symR [x]), by
    rw [Semantics.sortOf_withHooks _ _ noRaw] at hv ⊢; exact sortOf_cfgR hv⟩

/-- The match of `rD` at `d()`, with X := x. -/
def σ (x : GroundTerm) : Subst :=
  [(0, .ctor dotk []), (1, .ctor counterLabel [.dv Srt.int (.int 0)]), (2, x)]

/-- **`d()` steps to `r(x)` by `rD`**, X := x, for every value x of Val and every H. -/
theorem stepBy (H : HookParams) (x : GroundTerm) (hv : (cH H).sortOf x = some sVal) :
    StepBy (cH H) rD (σ x) (D H) (Rx H x hv) where
  mem := by unfold rD; exact List.getElem_mem _
  hσ := fun j s hs => by
    rw [rD_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, rfl, hv⟩
  hmatch := by
    rw [rD_lhs]
    exact .ctor (syms_okH H).1 (.cons (.ctor (syms_okH H).2.1 (.cons (.ctor (syms_okH H).2.2.1
      (.cons (.inj (.ctor (syms_okH H).2.2.2.1 .nil)) (.cons (.var rfl) .nil))) .nil)) (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [rD_shape.1] at ht; cases ht
  hpre := by rw [rD_shape.2.2.1]; exact .top
  heval := by
    rw [rD_rhs]
    exact .ctor (syms_okH H).1 (.cons (.ctor (syms_okH H).2.1 (.cons (.ctor (syms_okH H).2.2.1
      (.cons (.inj (.ctor (syms_okH H).2.2.2.2 (.cons .var .nil))) (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [rD_shape.2.1] at ht; cases ht
  hpost := by rw [rD_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => by
    rw [prios r' hr', rD_shape.2.2.2.2.2] at hlt
    exact absurd hlt (Nat.lt_irrefl _)

/-- **`d()` steps to `r(x)`**, for every value x of Val and every H. -/
theorem step_dr (H : HookParams) (x : GroundTerm) (hv : (cH H).sortOf x = some sVal) :
    Step (cH H) (D H) (Rx H x hv) := step_iff_by.mpr ⟨rD, σ x, stepBy H x hv⟩

/-- **In every model of `Γc`, `<k> d() </k>` has `<k> r(x) </k>` as a successor**, for every value
x of Val and every H. -/
theorem sound_dr (H : HookParams) (x : GroundTerm) (hv : (cH H).sortOf x = some sVal) :
    Γc (cH H) ⊧ (den (cH H) (D H).val ⇒ KoreAML.sNext (den (cH H) (Rx H x hv).val)) := by
  obtain ⟨h1, -⟩ := sound_at (cH H) (coreOKH H) (D H) (Rx H x hv) rD (σ x) (stepBy H x hv)
    (fun r' hr' _ hn _ => (openDecidedH H).1 r' hr' hn) (openDecidedH H).2
  have hcl : Γc (cH H) ⊧ (famEx (cH H) rD (σ x) ≡ den (cH H) (Rx H x hv).val) :=
    famEx_closed (cH H) (coreOKH H) (stepBy H x hv) rD_shape.2.2.2.2.1 (openDecidedH H).2
  intro M _ I hI e m
  have hst := h1 hI e m
  rw [interpret_impl] at hst ⊢
  intro hx
  exact sNext_congr ((KoreAML.interp_equal (defOK fun φ hφ => hI φ (Or.inl hφ))).mp (hcl hI e m)) (hst hx)

end KCore.TieE3MlLhsOrRhsVarRule

#check @KCore.TieE3MlLhsOrRhsVarRule.rule_textD
#check @KCore.TieE3MlLhsOrRhsVarRule.rule_textE
#check @KCore.TieE3MlLhsOrRhsVarRule.rule_from_text_sig
#check @KCore.TieE3MlLhsOrRhsVarRule.step_dr
#check @KCore.TieE3MlLhsOrRhsVarRule.sound_dr
#print axioms KCore.TieE3MlLhsOrRhsVarRule.coreOK
#print axioms KCore.TieE3MlLhsOrRhsVarRule.rule_textD
#print axioms KCore.TieE3MlLhsOrRhsVarRule.rule_textE
#print axioms KCore.TieE3MlLhsOrRhsVarRule.rule_from_text_sig
#print axioms KCore.TieE3MlLhsOrRhsVarRule.openDecidedH
#print axioms KCore.TieE3MlLhsOrRhsVarRule.stepBy
#print axioms KCore.TieE3MlLhsOrRhsVarRule.step_dr
#print axioms KCore.TieE3MlLhsOrRhsVarRule.sound_dr
