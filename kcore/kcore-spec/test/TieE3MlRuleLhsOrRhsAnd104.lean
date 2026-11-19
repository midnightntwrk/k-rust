/-
  The tie of sentence 104 of `f2-examples/e3-ml-rule-lhs-or-rhs-and.kompile.kore` (the rule of
  construct fixture e3-ml-rule-lhs-or-rhs-and, `c(X) #Or d(X) => X #And a()` in the `k` cell, read
  through `orSplit` with `andTermsCut` on each rule read) with Γ's two rule items (`prioRuleK`),
  for every interpretation H.
  Run from the package root: `lake env lean -j1 test/TieE3MlRuleLhsOrRhsAnd104.lean`.

  The sentence's left side holds `c(X) ∨ d(X)` in the cell and its right side `X ∧ a()`. Γ has one
  rule per disjunct, `c(X) => X` and `d(X) => X`, each with the cut's condition `X ∈ a()` in its
  right side (the variable form) and `⌈right⌉` more on its left side (`p0_eq`, `p1_eq`,
  `right_read`).

  - `rule_text0`: sentence 104 is the item of the text's two sides at the table of Γ's axioms
    (kernel; the two axioms have one table, `tbl1_eq`).
  - `right_iff`, the cut's statement at each rule read: where X has an element of Exp, Γ's right
    side `C[X] ∧ ⊤ ∧ X ∈ a()` and the text's `C[X ∧ a()] ∧ ⊤` denote one set, in a model of
    definedness and the signature (`and_var_top`: `KoreAML.rule_and_var` with the conjunct `\top`
    of the two sides in the place of its premise on `C[X]`).
  - `left_c`, `left_d`: each of Γ's left sides is inside the text's. `\or{SortExp{}}` holds the
    elements of its disjuncts that are in Exp; the arity of `c` and of `d` (`ΓSig`) puts them
    there (`un_arity`).
  - `rule_from_text_sig` (W1 per disjunct): each of Γ's two rule items is a consequence of
    sentence 104 and the signature, for every H.
  - `rule_w2` (W2, with the guard): in a model of Γ, sentence 104 holds at each valuation at
    which `⌈right⌉` holds wherever the text's left side does: an application holds the elements
    its arguments' elements give, so an element of the text's left side is one of the left side
    of the rule of `c` or of `d` (`fill_or104`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlRuleLhsOrRhsAnd104

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-rule-lhs-or-rhs-and.kompile.kore"
definition_of defn from "f2-examples/e3-ml-rule-lhs-or-rhs-and.kompile.kore"
user_axioms U from "f2-examples/e3-ml-rule-lhs-or-rhs-and.kompile.kore" module "E3-ML-RULE-LHS-OR-RHS-AND"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem names : c.symName 385 = "Lbla" ∧ c.symName 387 = "Lblc" ∧ c.symName 388 = "Lbld" ∧
    c.sortName 32 = "Exp" := by decide +kernel

/-! ## The rule's forms -/

def tC : Kore.KSort := srt "GeneratedTopCell"
def eS : Kore.KSort := srt "Exp"
/-- The variable X of the rule. -/
def v : Kore.EVar := evar "VarV0" eS
def xP : Kore.Pattern := .var (.evar v)
def kP : Kore.Pattern := ev "VarV1" (srt "K")
def cP : Kore.Pattern := ev "VarV2" (srt "GeneratedCounterCell")
def aP : Kore.Pattern := ap "Lbla" []
def cX : Kore.Pattern := ap "Lblc" [xP]
def dX : Kore.Pattern := ap "Lbld" [xP]

/-- The context of the `k` cell's first item at the sort Exp:
`<generatedTop>(<k>(kseq(inj{Exp, KItem}(·), K)), C)`. -/
def K : KoreCutCtx :=
  .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] []
      (.app ⟨⟨"kseq"⟩⟩ [] [] (.app ⟨⟨"inj"⟩⟩ [eS, srt "KItem"] [] .hole []) [kP]) []) [cP]

/-- The text's left side: `c(X) ∨ d(X)` in the cell. -/
def Ltext : Kore.Pattern := .and tC [K.fill (.or eS [cX, dX]), .top tC]
/-- The text's right side: `X ∧ a()` in the cell. -/
def rtext : Kore.Pattern := .and tC [K.fill (.and eS [xP, aP]), .top tC]
/-- Γ's right side, of both rules: X in the cell, with the cut's condition `X ∈ a()`. -/
def rhs0 : Kore.Pattern := .and tC [K.fill xP, .top tC, .in eS tC xP aP]
/-- `⌈right⌉`, the last conjunct of Γ's left sides. -/
def ceilR : Kore.Pattern := .ceil tC tC rhs0
/-- Γ's left side of the rule of the disjunct `d`: the term, no `requires`, `⌈right⌉`. -/
def Lof (d : Kore.Pattern) : Kore.Pattern := .and tC [K.fill d, .top tC, ceilR]

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)
/-- Γ's axioms of the two rules. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0
noncomputable def p1 : Kore.Pattern := prioRuleK c r1
theorem ruleItems_eq : ruleItems c =
    [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩] := by kernel_rfl
/-- **Γ's axioms of the two rules** (kernel): one per disjunct, with one right side. -/
theorem p0_eq : p0 = .rewrites tC (Lof cX) rhs0 := by decide +kernel
theorem p1_eq : p1 = .rewrites tC (Lof dX) rhs0 := by decide +kernel
/-- **The right side of each rule read is the cut's** (`ruleRight`, kernel). -/
theorem right_read : ruleRight c r0 = rhs0 ∧ ruleRight c r1 = rhs0 := by decide +kernel

/-- The table of Γ's axioms. -/
noncomputable def tbl : VarTable := tableOf [] p0
theorem tbl1_eq : tableOf [] p1 = tbl := by decide +kernel

def fT : List VarKey := (freeOf [] (.rewrites tC Ltext rtext)).eraseDups

/-- **Sentence 104 is the item of `\rewrites{C}(Ltext, rtext)` at the table of Γ's axioms**
(kernel). -/
theorem rule_text0 :
    TiePair.renSeq (TieRuleLhs.itemAt tbl fT tC Ltext rtext) [] = some (trS U.ax104).pat := by
  decide +kernel
theorem free_sub0 : ∀ k ∈ fT, k ∈ (freeOf [] p0).eraseDups := by decide +kernel
theorem free_sub1 : ∀ k ∈ fT, k ∈ (freeOf [] p1).eraseDups := by decide +kernel
theorem free_sup0 : ∀ k ∈ (freeOf [] p0).eraseDups, k ∈ fT := by decide +kernel
theorem free_sup1 : ∀ k ∈ (freeOf [] p1).eraseDups, k ∈ fT := by decide +kernel
theorem v_free : evarKey v ∈ fT := by decide +kernel

theorem trS104 : (trS U.ax104).pat = TieRuleLhs.itemAt tbl fT tC Ltext rtext := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- Γ's items of the rules are the items of Γ's sides at the table and their free variables. -/
theorem item_eq0 : (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat =
    TieRuleLhs.itemAt tbl (freeOf [] p0).eraseDups tC (Lof cX) rhs0 := by
  have h := TieRuleLhs.trAxiom_rule tC (Lof cX) rhs0
  rw [← p0_eq] at h
  exact h
theorem item_eq1 : (trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩).pat =
    TieRuleLhs.itemAt tbl (freeOf [] p1).eraseDups tC (Lof dX) rhs0 := by
  have h := TieRuleLhs.trAxiom_rule tC (Lof dX) rhs0
  rw [← p1_eq, tbl1_eq] at h
  exact h

theorem exp_name (H : HookParams) : (cH H).sortName 32 = "Exp" := names.2.2.2
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")

/-! ## A rule item, pointwise -/

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

theorem tr_rw104 (t : VarTable) (C : Kore.KSort) (L r : Kore.Pattern) :
    tr ⟨t, []⟩ (.rewrites C L r) = sRewrites (trSort t C) (tr ⟨t, []⟩ L) (tr ⟨t, []⟩ r) := by rw [tr]

/-- A rule item that holds gives, where its guards hold, a successor in its right side to each
element of its left side that is in the rule's sort. -/
theorem item_elim104 (hD : DefOK I) {t : VarTable} {f : List VarKey} {C : Kore.KSort} {L r : Kore.Pattern}
    (h : I ⊧ᴵ TieRuleLhs.itemAt t f C L r) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ f, (guardOf t k).interpret I e m) (a : M)
    (ha : (inhOf (trSort t C)).interpret I e a) (hl : (tr ⟨t, []⟩ L).interpret I e a) :
    (sNext (tr ⟨t, []⟩ r)).interpret I e a := by
  have h1 := h e m
  unfold TieRuleLhs.itemAt at h1
  rw [interpret_impl] at h1
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
    exact hg k hk)
  rw [interp_equal hD] at h2
  have h3 := (h2 a).mpr ha
  rw [tr_rw104] at h3
  unfold sRewrites at h3
  rw [interp_sImp] at h3
  exact h3.2 hl

/-- A rule item holds at a valuation where, under its guards, each element of its left side in
the rule's sort has a successor in its right side. -/
theorem item_intro104 (hD : DefOK I) {t : VarTable} {f : List VarKey} {C : Kore.KSort} {L r : Kore.Pattern}
    (e : Valuation M) (m : M)
    (h : (∀ k ∈ f, (guardOf t k).interpret I e m) → ∀ a, (inhOf (trSort t C)).interpret I e a →
      (tr ⟨t, []⟩ L).interpret I e a → (sNext (tr ⟨t, []⟩ r)).interpret I e a) :
    (TieRuleLhs.itemAt t f C L r).interpret I e m := by
  unfold TieRuleLhs.itemAt
  rw [interpret_impl]
  intro hg
  rw [TieUnion.interp_conjListAll] at hg
  have hg' : ∀ k ∈ f, (guardOf t k).interpret I e m := fun k hk => hg _ (List.mem_map_of_mem hk)
  rw [interp_equal hD]
  intro a
  rw [tr_rw104]
  unfold sRewrites
  rw [interp_sImp]
  exact ⟨fun hf => hf.1, fun ha => ⟨ha, h hg' a ha⟩⟩

/-- The next-step operator is monotone. -/
theorem next_mono104 {φ ψ : P} {e : Valuation M} {a : M} (h : ∀ b, φ.interpret I e b → ψ.interpret I e b) :
    (sNext φ).interpret I e a → (sNext ψ).interpret I e a := by
  unfold sNext
  rw [interp_app, interp_app]
  rintro ⟨x, b, hx, hb, hxb⟩
  exact ⟨x, b, hx, h b hb, hxb⟩

/-- An application context at a disjunction: each element is one of the context at a disjunct. -/
theorem fill_or104 {s φ ψ : P} {e : Valuation M} : ∀ (C : CutCtx) (m : M),
    (C.fill (sOr s φ ψ)).interpret I e m → (C.fill φ).interpret I e m ∨ (C.fill ψ).interpret I e m
  | .hole, _, hm => (interp_sOr.mp hm).2
  | .fn C χ, m, hm => by
    obtain ⟨a, b, ha, hb, hab⟩ := interp_app.mp hm
    rcases fill_or104 C a ha with h | h
    · exact .inl (interp_app.mpr ⟨a, b, h, hb, hab⟩)
    · exact .inr (interp_app.mpr ⟨a, b, h, hb, hab⟩)
  | .arg χ C, m, hm => by
    obtain ⟨a, b, ha, hb, hab⟩ := interp_app.mp hm
    rcases fill_or104 C b hb with h | h
    · exact .inl (interp_app.mpr ⟨a, b, ha, h, hab⟩)
    · exact .inr (interp_app.mpr ⟨a, b, ha, h, hab⟩)

/-- **The variable form of the cut, with a conjunct inside the sort**: `\and{C}(K[V], E,
\in{S,C}(V, u))` is `\and{C}(K[\and{S}(V, u)], E)` where V has an element of S and every element
of E is in C. -/
theorem and_var_top [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true)
    (S C : Kore.KSort) (v : Kore.EVar) (u E : Kore.Pattern) (e : Valuation M) {σ σ' : M}
    (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort ctx.vars C).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hv : Inh I σ (e.evalEvar (ctx.vars.ev (evarKey v))))
    (hE : ∀ m, (tr ctx E).interpret I e m → Inh I σ' m) (m : M) :
    (tr ctx (.and C [K.fill (.var (.evar v)), E, .in S C (.var (.evar v)) u])).interpret I e m ↔
      (tr ctx (.and C [K.fill (.and S [.var (.evar v), u]), E])).interpret I e m := by
  have hand : tr ctx (.and S [.var (.evar v), u]) =
      sAnd (.evar (ctx.vars.ev (evarKey v))) (tr ctx u) := by simp only [tr, trAndList]
  have hfillv : tr ctx (K.fill (.var (.evar v))) =
      (K.toCut ctx).fill (.evar (ctx.vars.ev (evarKey v))) := by
    rw [tr_cutCtx ctx _ K hK]; rfl
  have hl : tr ctx (.and C [K.fill (.var (.evar v)), E, .in S C (.var (.evar v)) u]) =
      sAnd ((K.toCut ctx).fill (.evar (ctx.vars.ev (evarKey v)))) (sAnd (tr ctx E)
        (sIn (trSort ctx.vars S) (trSort ctx.vars C) (.evar (ctx.vars.ev (evarKey v))) (tr ctx u))) := by
    simp only [tr, trAndList]
    rw [hfillv]
  have hr : tr ctx (.and C [K.fill (.and S [.var (.evar v), u]), E]) =
      sAnd ((K.toCut ctx).fill (sAnd (.evar (ctx.vars.ev (evarKey v))) (tr ctx u))) (tr ctx E) := by
    simp only [tr, trAndList]
    rw [tr_cutCtx ctx _ K hK, hand]
  rw [hl, hr, interp_sAnd, interp_sAnd, interp_sAnd, CutCtx.fill_evar_and,
    mem_iff_cut hD hc hS hC hσ hσ' _ hv]
  constructor
  · rintro ⟨hCx, hEm, hu, -⟩; exact ⟨⟨hu, hCx⟩, hEm⟩
  · rintro ⟨⟨hu, hCx⟩, hEm⟩; exact ⟨hCx, hEm, hu, hE m hEm⟩

end

/-! ## The arity of `c` and `d` -/

/-- The signatures of `c` and `d`. -/
def kc : CtorSig := ⟨387, [32], 32⟩
def kd : CtorSig := ⟨388, [32], 32⟩

theorem kc_mem : kc ∈ kernelSyms c := by decide +kernel
theorem kd_mem : kd ∈ kernelSyms c := by decide +kernel
theorem noInst_c : instDecode? (c.symName kc.name) = none := by decide +kernel
theorem noInst_d : instDecode? (c.symName kd.name) = none := by decide +kernel

kernel_rfl sigItems_withHooks104 : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

kernel_rfl cX_eq : cX = symApp c kc.name [xP]
kernel_rfl dX_eq : dX = symApp c kd.name [xP]

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The arity of a symbol of one argument from Exp to Exp, from `ΓSig`**: what it builds from
an element of Exp is in Exp. -/
theorem un_arity (k : CtorSig) (hk : k ∈ kernelSyms c) (hni : instDecode? (c.symName k.name) = none)
    (hargs : k.args = [32]) (hres : k.result = 32) (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {e : Valuation M} {a : M} (ha : (symHead c k.name).interpret I e a)
    {b0 m : M} (h0 : InS I "Exp" b0) (hm : AppE I a [b0] m) : InS I "Exp" m := by
  have hit : I ⊧ᴵ (symArityItem c k).pat := hS _ (Or.inl (Or.inl ⟨_, sig_arity hk, rfl⟩))
  rw [symArityItem_noInst (k := k) hni] at hit
  rw [symHead_noInst (c := c) (f := k.name) hni] at ha
  unfold KoreAML.arityItem at hit
  dsimp only [KoreAML.paramTable, List.map_nil] at hit
  have hinc := (KoreAML.interp_included hD).mp (hit KoreAML.val0 default) m
  unfold srtOf at hinc
  rw [trSort_srt] at hinc
  have hn : c.sortName 32 = "Exp" := names.2.2.2
  rw [hres, hn] at hinc
  apply (inS_iff (I := I) (s := "Exp") (a := m) KoreAML.val0).mp
  apply hinc
  rw [interp_appList]
  refine ⟨a, ((Closed.sym _).interp e KoreAML.val0 a).mp ha, [b0], ?_, hm⟩
  simp only [hargs, List.map_cons, List.map_nil, trSort_srt, hn]
  exact .cons ((inS_iff _).mpr h0) .nil

/-- Such a symbol at a pattern whose elements are in Exp is in Exp. -/
theorem un_inh (k : CtorSig) (hk : k ∈ kernelSyms c) (hni : instDecode? (c.symName k.name) = none)
    (hargs : k.args = [32]) (hres : k.result = 32) (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {p : Kore.Pattern}
    (hp : ∀ b, (tr ⟨t, []⟩ p).interpret I e b → InS I "Exp" b) (m : M)
    (h : (tr ⟨t, []⟩ (symApp c k.name [p])).interpret I e m) :
    (inhOf (trSort t eS)).interpret I e m := by
  rw [tr_symApp, trArgs_appList, interp_appList] at h
  obtain ⟨a, ha, bs, hbs, hm⟩ := h
  simp only [List.map_cons, List.map_nil] at hbs
  cases hbs with
  | cons hb0 hbs =>
    cases hbs
    unfold eS
    rw [trSort_srt]
    exact (inS_iff _).mpr (un_arity k hk hni hargs hres hD hS ha (hp _ hb0) hm)

/-- The guard of X puts its value in Exp. -/
theorem x_inh (hD : DefOK I) {t : VarTable} {e : Valuation M} {m0 : M}
    (hg : (guardOf t (evarKey v)).interpret I e m0)
    (b : M) (h : (tr ⟨t, []⟩ xP).interpret I e b) : InS I "Exp" b := by
  have h1 := (TieRuleLhs.guard_evarKey hD).mp hg
  unfold xP at h
  simp only [tr] at h
  rw [interp_evar] at h
  rw [h]
  have : v.sort = KoreAML.srt "Exp" := rfl
  rw [this, trSort_srt] at h1
  exact (inS_iff _).mp h1

/-! ## The inclusions -/

omit [Inhabited M] in
/-- **Γ's left side of the rule of a disjunct is inside the text's**, the disjunct's elements in
Exp: its first conjunct is inside the cell at the disjunction, and its conjunct `⌈right⌉` is not
asked. -/
theorem left_of {t : VarTable} {e : Valuation M} {d : Kore.Pattern}
    (hor : ∀ a, (tr ⟨t, []⟩ d).interpret I e a → (tr ⟨t, []⟩ (.or eS [cX, dX])).interpret I e a)
    (a : M) (h : (tr ⟨t, []⟩ (Lof d)).interpret I e a) : (tr ⟨t, []⟩ Ltext).interpret I e a := by
  unfold Lof at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact TieRuleLhs.tr_fill_mono ⟨t, []⟩ K rfl hor a (h _ (List.mem_cons_self ..))
  · exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- **Γ's left side of the rule of `c` is inside the text's**, where X's guard holds. -/
theorem left_c (hD : DefOK I) (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {m0 : M}
    (hg : (guardOf t (evarKey v)).interpret I e m0)
    (a : M) (h : (tr ⟨t, []⟩ (Lof cX)).interpret I e a) : (tr ⟨t, []⟩ Ltext).interpret I e a :=
  left_of (TieRuleLhs.sub_or_left fun a' h' => by
    rw [cX_eq] at h'
    exact un_inh kc kc_mem noInst_c rfl rfl hD hS (fun b hb => x_inh hD hg b hb) a' h') a h

/-- **Γ's left side of the rule of `d` is inside the text's**, where X's guard holds. -/
theorem left_d (hD : DefOK I) (hS : I ⊧ᴵP ΓSig c) {t : VarTable} {e : Valuation M} {m0 : M}
    (hg : (guardOf t (evarKey v)).interpret I e m0)
    (a : M) (h : (tr ⟨t, []⟩ (Lof dX)).interpret I e a) : (tr ⟨t, []⟩ Ltext).interpret I e a :=
  left_of (TieRuleLhs.sub_or_right fun a' h' => by
    rw [dX_eq] at h'
    exact un_inh kd kd_mem noInst_d rfl rfl hD hS (fun b hb => x_inh hD hg b hb) a' h') a h

/-- **The cut's statement at each rule read**: where X's guard holds, Γ's right side `C[X] ∧ ⊤ ∧
X ∈ a()` and the text's `C[X ∧ a()] ∧ ⊤` denote one set, in a model of definedness and the
signature. -/
theorem right_iff (H : HookParams) (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    {t : VarTable} {e : Valuation M} {m0 : M} (hg : (guardOf t (evarKey v)).interpret I e m0) (m : M) :
    (tr ⟨t, []⟩ rhs0).interpret I e m ↔ (tr ⟨t, []⟩ rtext).interpret I e m := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σE, hσE1, hσE2⟩ := TieRhs.sortSing_sig hD hSig (s := 32)
    (by decide +kernel : (32 : Srt) < nRegSorts + c.sortNames.length)
  rw [exp_name] at hσE1
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  have hSE : ∀ x, (trSort t eS).interpret I e x ↔ x = σE := by unfold eS; rw [trSort_srt]; exact hσE1
  have hSC : ∀ x, (trSort t tC).interpret I e x ↔ x = σ := by unfold tC; rw [trSort_srt]; exact hσ1
  have hv : Inh I σE (e.evalEvar (t.ev (evarKey v))) := by
    have h1 := (TieRuleLhs.guard_evarKey hD).mp hg
    rw [show v.sort = eS from rfl] at h1
    exact (interp_inhOf_of hSE).mp h1
  exact and_var_top hD hc ⟨t, []⟩ K rfl eS tC v aP (.top tC) e hSE hSC hσE2 hσ2 hv
    (fun x hx => by
      rw [tr] at hx
      exact (interp_inhOf_of hSC).mp ((interp_sTop hD (by unfold tC; rw [trSort_srt]; rfl) x).mp hx)) m

end

/-! ## W1, per disjunct -/

/-- Γ's item of a rule whose left side is inside the text's is a consequence of sentence 104 and
the signature. -/
theorem item_of_sentence (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    (hT : I ⊧ᴵ (trS U.ax104).pat) {L' : Kore.Pattern} {fG : List VarKey} (hfG : ∀ k ∈ fT, k ∈ fG)
    (hL : ∀ (e : Valuation M) (m0 : M), (guardOf tbl (evarKey v)).interpret I e m0 →
      ∀ a, (tr ⟨tbl, []⟩ L').interpret I e a → (tr ⟨tbl, []⟩ Ltext).interpret I e a) :
    I ⊧ᴵ TieRuleLhs.itemAt tbl fG tC L' rhs0 := by
  rw [trS104] at hT
  intro e m
  refine item_intro104 hD e m fun hg a ha hl => ?_
  have hgv := hg _ (hfG _ v_free)
  exact next_mono104 (fun b hb => (right_iff H hD hc hSig hgv b).mpr hb)
    (item_elim104 hD hT e m (fun k hk => hg k (hfG k hk)) a ha (hL e m hgv a hl))

/-- The text sentences of Γ's rules, in `ruleItems`'s order: the one sentence, once per disjunct. -/
noncomputable def ruleText : List AxiomDecl := [U.ax104, U.ax104]

/-- **W1 per disjunct, over the signature, and the converse for `ruleItems`**: each of Γ's two
rule items is a consequence of sentence 104 and Γ's signature, for every H. -/
theorem rule_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  refine ⟨U.ax104, List.mem_cons_self, ?_⟩
  intro M _ I hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have hS : I ⊧ᴵP ΓSig c := fun φ hφ => hSig φ (by
    unfold ΓSig at hφ ⊢; rw [sigItems_withHooks104]; exact hφ)
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inl (Or.inr ⟨x, rfl⟩))
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  have hT : I ⊧ᴵ (trS U.ax104).pat := hI _ (Or.inl (Or.inl ⟨trS U.ax104, List.mem_singleton_self _, rfl⟩))
  rcases List.mem_cons.mp hit with rfl | hit
  · rw [item_eq0]
    exact item_of_sentence H hD hc hSig hT free_sub0 fun e m0 hg a ha => left_c hD hS hg a ha
  · rw [List.mem_singleton.mp hit, item_eq1]
    exact item_of_sentence H hD hc hSig hT free_sub1 fun e m0 hg a ha => left_d hD hS hg a ha

/-- The priority the rule sentence's attributes state is each rule's. -/
theorem rule_prios : ruleText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) = c.rules.map (·.prio) := by
  decide +kernel

/-! ## W2, with the guard -/

/-- **W2 for the rule, with the guard**: in a model of Γ, sentence 104 holds at each valuation at
which `⌈right⌉` (of the text's right side) holds wherever the text's left side holds, for every
H. -/
theorem rule_w2 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M)
    (hR : ∀ a, (tr ⟨tbl, []⟩ Ltext).interpret I e a → (tr ⟨tbl, []⟩ (.ceil tC tC rtext)).interpret I e a)
    (m : M) : (trS U.ax104).pat.interpret I e m := by
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hit0 : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_cons_self
  have hit1 : trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hg0 : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit0, rfl⟩)))
  have hg1 : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit1, rfl⟩)))
  rw [item_eq0] at hg0
  rw [item_eq1] at hg1
  rw [trS104]
  refine item_intro104 hD e m fun hg a ha hl => ?_
  have hgv := hg _ v_free
  -- `⌈right⌉` of Γ's right side, from the text's
  have hceil : (tr ⟨tbl, []⟩ ceilR).interpret I e a := by
    have h := hR a hl
    unfold ceilR
    rw [tr] at h ⊢
    obtain ⟨σ, σ', x, h1, h2, h3, h4⟩ := interp_sCeil_raw.mp h
    exact interp_sCeil_raw.mpr ⟨σ, σ', x, h1, h2, (right_iff H hD hc hSig hgv x).mpr h3, h4⟩
  have hl' := hl
  unfold Ltext at hl'
  rw [interp_and (List.cons_ne_nil _ _)] at hl'
  have hl1 := hl' _ (List.mem_cons_self ..)
  have hl2 := hl' (.top tC) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hLof : ∀ d, (tr ⟨tbl, []⟩ (K.fill d)).interpret I e a → (tr ⟨tbl, []⟩ (Lof d)).interpret I e a := by
    intro d hd
    unfold Lof
    rw [interp_and (List.cons_ne_nil _ _)]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hd
    · exact hl2
    · exact hceil
  have hor : tr ⟨tbl, []⟩ (.or eS [cX, dX]) = sOr (trSort tbl eS) (tr ⟨tbl, []⟩ cX) (tr ⟨tbl, []⟩ dX) := by
    simp only [tr, trOrList]
  rw [tr_cutCtx ⟨tbl, []⟩ _ K rfl, hor] at hl1
  rcases fill_or104 _ a hl1 with h | h
  · rw [← tr_cutCtx ⟨tbl, []⟩ _ K rfl] at h
    exact next_mono104 (fun b hb => (right_iff H hD hc hSig hgv b).mp hb)
      (item_elim104 hD hg0 e m (fun k hk => hg k (free_sup0 k hk)) a ha (hLof cX h))
  · rw [← tr_cutCtx ⟨tbl, []⟩ _ K rfl] at h
    exact next_mono104 (fun b hb => (right_iff H hD hc hSig hgv b).mp hb)
      (item_elim104 hD hg1 e m (fun k hk => hg k (free_sup1 k hk)) a ha (hLof dX h))

end KCore.TieE3MlRuleLhsOrRhsAnd104

#check @KCore.TieE3MlRuleLhsOrRhsAnd104.p0_eq
#check @KCore.TieE3MlRuleLhsOrRhsAnd104.p1_eq
#check @KCore.TieE3MlRuleLhsOrRhsAnd104.right_read
#check @KCore.TieE3MlRuleLhsOrRhsAnd104.rule_text0
#check @KCore.TieE3MlRuleLhsOrRhsAnd104.and_var_top
#check @KCore.TieE3MlRuleLhsOrRhsAnd104.left_c
#check @KCore.TieE3MlRuleLhsOrRhsAnd104.left_d
#check @KCore.TieE3MlRuleLhsOrRhsAnd104.right_iff
#check @KCore.TieE3MlRuleLhsOrRhsAnd104.rule_from_text_sig
#check @KCore.TieE3MlRuleLhsOrRhsAnd104.rule_prios
#check @KCore.TieE3MlRuleLhsOrRhsAnd104.rule_w2
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd104.p0_eq
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd104.right_read
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd104.rule_text0
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd104.right_iff
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd104.rule_from_text_sig
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd104.rule_prios
#print axioms KCore.TieE3MlRuleLhsOrRhsAnd104.rule_w2
