/-
  `KoreAML.rule_cut_mem` at the three fixtures whose rule holds a connective at a term position
  under applications, each read by `Parse.parse` through the cut (`Parse.connRuleBody`,
  `ReadingNote.connectiveCut`). Run from the package root, after the library:
  `lake env lean -j1 test/TieRuleConn.lean`.

  - `RhsOr` (e3-ml-rule-rhs-or, `go => a() #Or b()`, f2-examples/mlror): `rz` is the rule with the
    position cut by an existential variable Z:Exp and `post := Z ∈ a ∨ Z ∈ b`, the rule the reader
    reads (`read`). `left_eq`: `ruleRight c rz` is the theorem's left pattern (the context K of the
    position, the `ensures` `\top`, the membership `\or` of the two `\in`). `right_text`: the
    theorem's right pattern, its canonical names spelled as the text spells them, is the right
    argument of the text's `\rewrites`; `right_tie`: the two have one translation under their own
    tables (`tr_occurrence_order`). `tie`: `rule_cut_mem` at these, its membership premise from
    `MemOf.or` of two `MemOf.in'`, its inclusion premise from `or_inh`.
    The sentence (109 of the user module, `U.ax109`), for every H: Γ's axiom `p0` is
    `\rewrites(K₀[go] ∧ ⊤ ∧ ⌈r⌉, r)`, r `ruleRight` (`p0_parts`), and the sentence is the item of
    `\rewrites(K₀[go] ∧ ⊤, right)` at `p0`'s table (`rule_text0`, kernel). `right_iff`: r is `right`
    at that table in every model of the signature, at every valuation: no side of the context and
    no operand holds Z (`cut_free`, a decision on the patterns, `TieRuleConnText.noRead_of_notFree`),
    the two sorts denote sorts (`TieRuleConnText.sort_sig`, from `ΓSig`), and every element of the
    `ensures` `\top` is in the top cell's sort, which is where the membership is read
    (`TieRuleConnText.rule_cut_mem_in`). `rule_from_text_sig` (W1): Γ's rule item is a consequence
    of the sentence with `ΓSig`. `rule_w2` (W2): in a model of Γ the sentence holds where `⌈r⌉`,
    the conjunct Γ's left side adds, holds wherever the text's left side holds (under the guards).
  - `LhsNot` (e3-ml-rule-lhs-not, `c(#Not(a())) => a()`, kompiled with `_Gen5` bound only under
    `\not`, f2-examples/mlnot) and `LhsNotOther` (e3-ml-rule-lhs-not-other, `c(#Not(a())) => b()`,
    f2-examples/mlnoto): the rule with the position held by the rule's variable Z:Exp and
    `pre := ¬(Z ∈ a ∧ Z ∈ G)` (G the variable `_Gen5`), resp. `pre := ¬(Z ∈ a)`, the rule the reader
    reads (`read`). `left_eq`: Γ's axiom of the rule, `prioRuleK c r`, is
    `\rewrites(K[Z] ∧ ⊤ ∧ q ∧ ⌈R⌉, R)`, q the membership written by `pre`, R the right side
    (`ruleRight`), which does not hold Z. `left_text`, `left_tie`: the theorem's pattern
    `K[φ] ∧ ⊤`, φ the connective, is the left argument of the text's `\rewrites`. `tie`:
    `rule_cut_mem` read from right to left: `∃Z:Exp. (K[Z] ∧ ⊤ ∧ q)` is `K[φ] ∧ ⊤`. `left_tie_def`:
    with the premise `⌈R⌉` of Γ's axiom, which reads no Z, Γ's left side closed by `∃Z` is the
    text's left side and `⌈R⌉`; `at_rule`: at the rule's own Z, an element of Exp, an element of Γ's
    left side is one of the text's left side and of `⌈R⌉`.
    The sentence (104 of each user module, `U.ax104`), for every H: Γ's axiom `p0` is
    `\rewrites(Lg, R)`, `Lg` := `K[Z] ∧ ⊤ ∧ q ∧ ⌈R⌉` (`p0_parts`), and the sentence is the item of
    `\rewrites(left, R)` at `p0`'s table, the indices of its variables renamed (`rule_text0`,
    kernel); Z is free in Γ's axiom and absent from the sentence (`free_cases0`). `left_iff`:
    closed by `∃Z` over Exp, `Lg` is `left` with `⌈R⌉` at that table in every model of the
    signature, at every valuation (`cutLeft_def`: `TieRuleConnText.rule_cut_mem_in` with the
    conjunct `⌈R⌉`; `cut_free`: Z is free in no side, not in φ, `⌈R⌉`, R, another variable's guard
    nor the top cell's sort, a decision on the patterns). `rule_from_text_sig` (W1): Γ's rule item
    is a consequence of the sentence with `ΓSig`: where Z's guard holds, an element of `Lg` is one
    of `left`, Z its own witness. `rule_w2` (W2): in a model of Γ the sentence holds where `⌈R⌉`
    holds wherever the text's left side holds (under the guards): an element of `left` is one of
    `Lg` at some value of Z in Exp, Γ's item is read at that value (`item_inst_transfer`), and
    neither R nor a guard of the sentence reads Z.
  - `right_defined`, `rule_w2_noprem` (each of the three): the premise `⌈R⌉` of `rule_w2` holds in
    every model of Γ where the guards hold, so Γ entails the sentence, for every H. `LhsNot`,
    `LhsNotOther`: the right side is built of the text's variables, constructors and
    `inj{Exp,KItem}`, each with its Cons-Fun item in Γ (`TieRuleCutG.rightDefined_top`). `RhsOr`:
    `K[a()] ∧ ⊤` is built so and holds one element, which is one of `K[a() ∨ b()] ∧ ⊤` and so, by
    `right_iff`, of Γ's right side.
  - `RhsOr.memTop`: `MemOf.top` and `MemOf.bot` at the sorts of `RhsOr`: `\top{C}` is the
    membership in `\top{Exp}` and `\bottom{C}` in `\bottom{Exp}` (the shapes of
    test/PredReader.lean's hand-edited texts).
  - The theorems `tie`, `left_tie_def`, `at_rule` and `memTop` hold at any table and leave as
    premises what `rule_cut_mem` lists of the table and the interpretation: definedness, the sorts' patterns, the sides, φ and the sort not reading
    Z, and every element of the filled context in the outer sort. The statements on the
    sentences (`rule_text0`, `right_iff`, `left_iff`, `rule_from_text_sig`, `rule_w2`) are at the
    table of Γ's axiom and carry none of these premises.
  - The successors are test/PredFixtures.lean's: `LhsNot.step_iff`, `RhsOr.step_a`, `step_b`,
    `step_inv`, `famEx_values_iff`, `not_entailed_a`, `not_entailed_b`, `LhsNotOther.step_iff`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Faithful KoreAML ML

namespace TieRuleConn

def topC : Kore.KSort := srt "GeneratedTopCell"

/-- The context of the `k` cell's first item at the sort X: `<generatedTop>(<k>(kseq(inj{X,
KItem}(·), k)), counter)`. -/
def cellCtx (X : String) (k counter : Kore.Pattern) : KoreCutCtx :=
  .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] []
      (.app ⟨⟨"kseq"⟩⟩ [] [] (.app ⟨⟨"inj"⟩⟩ [srt X, srt "KItem"] [] .hole []) [k]) []) [counter]

/-- The `\rewrites` axiom at the place i of the text's last module: its left and right arguments. -/
def rewritesAt (k : Kore.Definition) (i : Nat) : Option (Kore.Pattern × Kore.Pattern) :=
  match k.modules.getLast?.bind (·.sentences[i]?) with
  | some (.axiom a) => match a.pattern with
    | .rewrites _ l r => some (l, r)
    | _ => none
  | _ => none

/-- The places of the `\rewrites` axioms of the text's last module. -/
def rewritesPlaces (k : Kore.Definition) : List Nat :=
  (List.range ((k.modules.getLast?.map (·.sentences.length)).getD 0)).filter fun i => (rewritesAt k i).isSome

/-- `∧` of four is `∧` of the first three and the fourth. -/
theorem and4_iff {M : Type} {I : Interpretation KoreAML.Sym M} (ctx : Ctx) (C : Kore.KSort)
    (x y q d : Kore.Pattern) (e : Valuation M) (m : M) :
    (tr ctx (.and C [x, y, q, d])).interpret I e m ↔
      (tr ctx (.and C [x, y, q])).interpret I e m ∧ (tr ctx d).interpret I e m := by
  simp only [tr, trAndList, interp_sAnd, and_assoc]

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **A rule axiom entails the one whose left side it reaches at another valuation.** The item of
`\rewrites{C}(L', r')` with the guards of `fG` holds in `I`. At the valuation `e`, where the guards
of `fT` hold, every element a of `L` is, at some valuation `e'` where the guards of `fG` hold, an
element of `L'`, the outer sort's elements at `e` being its elements at `e'` and every element of
`r'` at `e'` one of `r` at `e`. Then the item of `\rewrites{C}(L, r)` with the guards of `fT` holds
at `e`. (`TieRuleConnText.item_transfer` is the case `e' = e`.) -/
theorem item_inst_transfer (hD : DefOK I) {t : VarTable} {fT fG : List VarKey} {C : Kore.KSort}
    {L L' r r' : Kore.Pattern} (h : I ⊧ᴵ TieRuleLhs.itemAt t fG C L' r') (e : Valuation M) (m : M)
    (hstep : (∀ k ∈ fT, (guardOf t k).interpret I e m) → ∀ a, (tr ⟨t, []⟩ L).interpret I e a →
      ∃ e' : Valuation M, (∀ k ∈ fG, (guardOf t k).interpret I e' m) ∧
        ((inhOf (trSort t C)).interpret I e a → (inhOf (trSort t C)).interpret I e' a) ∧
        (tr ⟨t, []⟩ L').interpret I e' a ∧
        ∀ b, (tr ⟨t, []⟩ r').interpret I e' b → (tr ⟨t, []⟩ r).interpret I e b) :
    (TieRuleLhs.itemAt t fT C L r).interpret I e m := by
  unfold TieRuleLhs.itemAt
  rw [interpret_impl]
  intro hg
  rw [TieUnion.interp_conjListAll] at hg
  have hg' : ∀ k ∈ fT, (guardOf t k).interpret I e m := fun k hk => hg _ (List.mem_map_of_mem hk)
  rw [interp_equal hD]
  intro a
  have hT : ∀ X Y, tr ⟨t, []⟩ (.rewrites C X Y) = sRewrites (trSort t C) (tr ⟨t, []⟩ X) (tr ⟨t, []⟩ Y) :=
    fun X Y => by rw [tr]
  rw [hT]
  unfold sRewrites
  rw [interp_sImp]
  refine ⟨fun hf => hf.1, fun ht' => ⟨ht', fun hl => ?_⟩⟩
  obtain ⟨e', hge, hCe, hL', hr⟩ := hstep hg' a hl
  have h1 := h e' m
  unfold TieRuleLhs.itemAt at h1
  rw [interpret_impl] at h1
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
    exact hge k hk)
  rw [interp_equal hD] at h2
  have h3 := h2 a
  rw [hT] at h3
  unfold sRewrites at h3
  rw [interp_sImp] at h3
  have hn := (h3.mpr (hCe ht')).2 hL'
  unfold sNext at hn ⊢
  obtain ⟨x, b, hx, hb, happ⟩ := interp_app.mp hn
  exact interp_app.mpr ⟨x, b, hx, hr b hb, happ⟩

/-- **The cut of a left side, with the conjunct `⌈R⌉`, the outer sort read from E**: closed by
`∃Z:S`, `K[Z] ∧ E ∧ q ∧ ⌈R⌉` is `K[φ] ∧ E` with `⌈R⌉`, q the membership of Z in φ, where `⌈R⌉` does
not read Z and every element of E is in C. -/
theorem cutLeft_def (hD : DefOK I) (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true)
    (S C : Kore.KSort) (z : Kore.EVar) (hz : z.sort = S) (φ q E D : Kore.Pattern)
    (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ctx (ctx.vars.ev (evarKey z)))
    (hφ : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx φ))
    (hE : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx E))
    (hR : NoReadCut I (ctx.vars.ev (evarKey z)) (tr ctx D))
    (hSz : NoReadCut I (ctx.vars.ev (evarKey z)) (trSort ctx.vars S))
    (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ)
    (hq : MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' q φ)
    (hin : ∀ a, (tr ctx φ).interpret I e a → Inh I σ a)
    (hEin : ∀ m, (tr ctx E).interpret I e m → Inh I σ' m) (m : M) :
    (∃ x, Inh I σ x ∧ (tr ctx (.and C [K.fill (.var (.evar z)), E, q, D])).interpret I
        ⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) x, e.evalSvar⟩ m) ↔
      (tr ctx (.and C [K.fill φ, E])).interpret I e m ∧ (tr ctx D).interpret I e m := by
  have ht := TieRuleConnText.rule_cut_mem_in hD ctx K hK S C z hz φ q E e hsides hφ hE hSz hS hq hin hEin m
  have hex : (tr ctx (.exist C z (.and C [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔
      ∃ x, Inh I σ x ∧ (tr ctx (.and C [K.fill (.var (.evar z)), E, q])).interpret I
        ⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) x, e.evalSvar⟩ m := by
    subst hz
    show (sExists (ctx.vars.ev (evarKey z)) (trSort ctx.vars z.sort)
      (tr ctx (.and C [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔ _
    rw [interp_sExists]
    refine exists_congr fun x => and_congr_left' ?_
    rw [interp_member hD, interp_inhOf_of fun b => (hSz e x b).trans (hS b)]
    simp
  rw [← ht, hex]
  constructor
  · rintro ⟨x, hx, h4⟩
    rw [and4_iff] at h4
    exact ⟨⟨x, hx, h4.1⟩, (hR e x m).mp h4.2⟩
  · rintro ⟨⟨x, hx, h3⟩, hd⟩
    exact ⟨x, hx, (and4_iff _ _ _ _ _ _ _ _).mpr ⟨h3, (hR e x m).mpr hd⟩⟩

end

namespace RhsOr

kore_term kore from "f2-examples/mlror.kompile.kore"
definition_of defn from "f2-examples/mlror.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

example : c.sortName 32 = "Exp" ∧ c.sortName 0 = "K" ∧ c.sortName 19 = "GeneratedCounterCell" ∧
    c.symName 385 = "Lbla" ∧ c.symName 386 = "Lblb" ∧ c.symName 389 = "Lblgo" := by decide +kernel

def cfg (x : Term) : Term := .app 71 [.app 383 [.app 0 [.inj 32 1 x, .var 0]], .var 1]

/-- `go => ?Z` with `post := Z ∈ a ∨ Z ∈ b`, Z:Exp the third variable. -/
def rz : Rule :=
  { vars := [0, 19, 32], lhs := cfg (.app 389 []), req := none, rhs := cfg (.var 2), ens := none,
    prio := 50, exs := [2],
    post := .or (.mem 32 (.var 2) (.app 385 [])) (.mem 32 (.var 2) (.app 386 [])) }

/-- The reader reads the text's rule as `rz` (`Parse.parse`, through the cut). -/
theorem read : c.rules = [rz] := rfl

def S : Kore.KSort := srt "Exp"
def z : Kore.EVar := evar "VarV2" S
def a : Kore.Pattern := ap "Lbla" []
def b : Kore.Pattern := ap "Lblb" []
def E : Kore.Pattern := .top topC
def K : KoreCutCtx := cellCtx "Exp" (ev "VarV0" (srt "K")) (ev "VarV1" (srt "GeneratedCounterCell"))

/-- The theorem's right pattern: the right side with the disjunction in its position. -/
def right : Kore.Pattern := .and topC [K.fill (.or S [a, b]), E]

theorem left_eq : ruleRight c rz =
    .exist topC z (.and topC [K.fill (.var (.evar z)), E,
      .or topC [.in S topC (.var (.evar z)) a, .in S topC (.var (.evar z)) b]]) := by decide +kernel

/-- The text's spelling of the canonical names of the rule's variables. -/
def spell (n : String) (_ : Kore.KSort) : String :=
  if n == "VarV0" then "Var'Unds'DotVar1" else if n == "VarV1" then "Var'Unds'DotVar0" else n

theorem right_text : some (renVars spell (fun n _ => n) right) = (rewritesAt kore 206).map (·.2) := by
  decide +kernel

theorem right_tie (r : Kore.Pattern) (h : (rewritesAt kore 206).map (·.2) = some r) :
    tr ⟨tableOf [] r, []⟩ r = tr ⟨tableOf [] right, []⟩ right := by
  have hr : r = renVars spell (fun n _ => n) right := by
    have := right_text; rw [h] at this; exact (Option.some.inj this).symm
  rw [hr]
  exact tr_occurrence_order spell (fun n _ => n) [] [] right (by decide +kernel)

/-- **`rule_cut_mem` at the fixture**: `ruleRight c rz` is the right side with the disjunction in
its position, under the theorem's premises at a table without aliases. -/
theorem tie {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ⟨tbl, []⟩ (tbl.ev (evarKey z)))
    (hφ : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ (.or S [a, b])))
    (hE : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ E))
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill (.or S [a, b]))).interpret I e m → Inh I σ' m) (m : M) :
    (tr ⟨tbl, []⟩ (ruleRight c rz)).interpret I e m ↔ (tr ⟨tbl, []⟩ right).interpret I e m := by
  rw [left_eq]
  have hq : MemOf I ⟨tbl, []⟩ e (tbl.ev (evarKey z)) σ σ'
      (.or topC [.in S topC (.var (.evar z)) a, .in S topC (.var (.evar z)) b]) (.or S [a, b]) :=
    MemOf.or (ctx := ⟨tbl, []⟩) hSz hCz hS hC
      (MemOf.in' (ctx := ⟨tbl, []⟩) hSz hCz hS hC hD hc hσ hσ' a)
      (MemOf.in' (ctx := ⟨tbl, []⟩) hSz hCz hS hC hD hc hσ hσ' b)
  exact rule_cut_mem hD ⟨tbl, []⟩ K rfl S topC z rfl (.or S [a, b]) _ E e hsides hφ hE hSz hS hq
    (fun x hx => or_inh (ctx := ⟨tbl, []⟩) hS a b x hx) hout m

/-- `\top{C}` is the membership in `\top{Exp}`, and `\bottom{C}` in `\bottom{Exp}`, at the sorts of
the fixture. -/
theorem memTop {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) (tbl : VarTable)
    (e : Valuation M) {σ σ' : M}
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ') :
    MemOf I ⟨tbl, []⟩ e (tbl.ev (evarKey z)) σ σ' (.top topC) (.top S) ∧
      MemOf I ⟨tbl, []⟩ e (tbl.ev (evarKey z)) σ σ' (.bottom topC) (.bottom S) :=
  ⟨MemOf.top (ctx := ⟨tbl, []⟩) hSz hCz hS hC hD (by unfold S; rw [trSort_srt]; rfl)
      (by unfold topC; rw [trSort_srt]; rfl),
    MemOf.bot (ctx := ⟨tbl, []⟩) (S := S) (C := topC) hD (by unfold S; rw [trSort_srt]; rfl)
      (by unfold topC; rw [trSort_srt]; rfl)⟩

/-! ## The rule's sentence (109), for every H: W1 and W2 -/

user_axioms U from "f2-examples/mlror.kompile.kore" module "E3-ML-RULE-RHS-OR"

noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c rz

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

def go : Kore.Pattern := ap "Lblgo" []
/-- The membership of Z in `a() #Or b()`, as `post` writes it. -/
def qM : Kore.Pattern := .or topC [.in S topC (.var (.evar z)) a, .in S topC (.var (.evar z)) b]
/-- Γ's right side: `∃Z:Exp. (K[Z] ∧ ⊤ ∧ q)`. -/
def rG : Kore.Pattern := .exist topC z (.and topC [K.fill (.var (.evar z)), E, qM])
/-- The left side as the text writes it: the term and the `requires` `\top`. -/
def Ltext : Kore.Pattern := .and topC [K.fill go, E]

/-- Γ's axiom: `\rewrites(K[go] ∧ ⊤ ∧ ⌈r⌉, r)`, r Γ's right side. -/
theorem p0_parts : TieRuleLhs.rwParts p0 = some (topC, .and topC [K.fill go, E, .ceil topC topC rG], rG) := by
  decide +kernel

/-- The free variables of the text's form. -/
def fT : List VarKey := (freeOf [] (.rewrites topC Ltext right)).eraseDups

/-- **The text's sentence 109 is the item of `\rewrites{C}(Ltext, right)` at the table of Γ's
axiom** (kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT topC Ltext right) [] = some (trS U.ax109).pat := by
  decide +kernel
theorem fT_free0 : fT.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem free_sub0 : ∀ k ∈ (freeOf [] p0).eraseDups, k ∈ fT := by decide +kernel

/-- At the table of Γ's axiom, no side of the context and no operand of the disjunction holds Z. -/
theorem cut_free : TieRuleConnText.sidesFree ⟨tableOf [] p0, []⟩ ((tableOf [] p0).ev (evarKey z)) K = true ∧
    (tr ⟨tableOf [] p0, []⟩ (.or S [a, b])).isFreeEvar ((tableOf [] p0).ev (evarKey z)) = false := by
  decide +kernel

/-- **Γ's right side is the text's**, at the table of Γ's axiom, in every model of the signature
and at every valuation: the premises of `rule_cut_mem` hold there. -/
theorem right_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (e : Valuation M) (m : M) :
    (tr ⟨tableOf [] p0, []⟩ rG).interpret I e m ↔ (tr ⟨tableOf [] p0, []⟩ right).interpret I e m := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  obtain ⟨σ, hσ, hS, hSz⟩ := TieRuleConnText.sort_sig hD hSig (s := 32)
    (by decide +kernel : (32 : Srt) < nRegSorts + c.sortNames.length)
    (show (cH H).sortName 32 = "Exp" from (by decide +kernel : c.sortName 32 = "Exp"))
  obtain ⟨σ', hσ', hC, hCz⟩ := TieRuleConnText.sort_sig hD hSig (s := topCellSort)
    (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
    (show (cH H).sortName topCellSort = "GeneratedTopCell" from
      (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell"))
  have hq : MemOf I ⟨tableOf [] p0, []⟩ e ((tableOf [] p0).ev (evarKey z)) σ σ' qM (.or S [a, b]) :=
    MemOf.or (ctx := ⟨tableOf [] p0, []⟩) (hSz _ _) (hCz _ _) (hS _ e) (hC _ e)
      (MemOf.in' (ctx := ⟨tableOf [] p0, []⟩) (hSz _ _) (hCz _ _) (hS _ e) (hC _ e) hD hc hσ hσ' a)
      (MemOf.in' (ctx := ⟨tableOf [] p0, []⟩) (hSz _ _) (hCz _ _) (hS _ e) (hC _ e) hD hc hσ hσ' b)
  exact TieRuleConnText.rule_cut_mem_in hD ⟨tableOf [] p0, []⟩ K rfl S topC z rfl (.or S [a, b]) qM E e
    (TieRuleConnText.sidesNoRead_of_free K cut_free.1) (TieRuleConnText.noRead_of_notFree cut_free.2)
    (TieRuleConnText.top_noRead hD (hCz _ _)) (hSz _ _) (hS _ e) hq
    (fun x hx => or_inh (ctx := ⟨tableOf [] p0, []⟩) (hS _ e) a b x hx)
    (fun m hm => TieRuleConnText.top_inh hD (hC _ e) m hm) m

/-- W1 for the rule, and the converse for `ruleItems`: Γ's one rule item is a consequence of
sentence 109 with the signature, for every H. Γ's left side is the text's with the conjunct `⌈r⌉`
more, and every element of the text's right side is one of Γ's (`right_iff`). -/
theorem rule0_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), (TiePair.Texts [(trS U.ax109).pat] ∪ ΓSig (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  rw [List.mem_singleton.mp hit]
  exact TieRuleConnText.rule_w1_sides hD p0_parts rule_text0 fT_free0
    (hI _ (Or.inl (Or.inl (List.mem_singleton_self _))))
    (fun e m _ x hx => TieRuleConnText.and_sub (List.cons_ne_nil _ _) (fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact List.mem_cons_self ..
      · rw [List.mem_singleton.mp hq]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)) x hx)
    (fun e m _ x hx => (right_iff H hD hSig e x).mpr hx)

/-- The sentence with definedness is the premise set of its item with definedness. -/
theorem texts_items_sig {ad : AxiomDecl} {Δ : Premises KoreAML.Sym} {φ : P}
    (h : φ ∈ TiePair.Texts [(trS ad).pat] ∪ Δ) : φ ∈ itemsPremises [trS ad] ∪ Δ := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl ⟨_, List.mem_singleton_self _, (List.mem_singleton.mp h).symm⟩)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/
noncomputable def ruleText : List AxiomDecl := [U.ax109]

/-- **W1 for the rule, and the converse for `ruleItems`**: each of Γ's rule items (one) is a consequence of
sentence 109 with the signature, for every H. Γ's left side is the text's with the conjunct `⌈r⌉`
more, and every element of the text's right side is one of Γ's (`right_iff`). -/
theorem rule_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ∪ ΓSig (cH H) ⊧ it.pat :=
  fun it hit => ⟨U.ax109, List.mem_cons_self, fun hI => rule0_from_text_sig H it hit fun φ hφ => hI φ (texts_items_sig hφ)⟩

/-- **W2 for the rule, with the guard**: in a model of Γ, sentence 109 holds where, at each
valuation at which the guards of its variables hold, `⌈r⌉` (the conjunct Γ's left side adds, r Γ's
right side) holds wherever the text's left side holds, for every H. -/
theorem rule_w2 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (hR : ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) →
      ∀ x, (tr ⟨tableOf [] p0, []⟩ Ltext).interpret I e x →
        (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC rG)).interpret I e x) :
    I ⊧ᴵ (trS U.ax109).pat := by
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  refine TieRuleConnText.rule_w2_sides hD p0_parts rule_text0 free_sub0 hg (fun e m hgs x hx => ?_)
    (fun e m _ x hx => (right_iff H hD hSig e x).mp hx)
  have h1 := (interp_and (List.cons_ne_nil _ _)).mp hx
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h1 _ (List.mem_cons_self ..)
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · rw [List.mem_singleton.mp hp]; exact hR e m hgs x hx

/-- The generators of `K[a()]`: the top cell, the `k` cell, `kseq`, the injection of Exp into KItem
and the constructor `a`. -/
def rightGens : List (String × KoreAML.Gen) :=
  [("GeneratedTopCell", .ctor ⟨"Lbl'-LT-'generatedTop'-GT-'", ["KCell", "GeneratedCounterCell"], "GeneratedTopCell"⟩),
   ("KCell", .ctor ⟨"Lbl'-LT-'k'-GT-'", ["K"], "KCell"⟩),
   ("K", .ctor ⟨"kseq", ["KItem", "K"], "K"⟩),
   ("KItem", .inj "Exp"),
   ("Exp", .ctor ⟨"Lbla", [], "Exp"⟩)]

/-- Γ has the Cons-Fun item of each (kernel). -/
theorem right_funs : TieRuleCutG.funsInGB c rightGens = true := by decide +kernel

/-- `K[a()]` and `a()` are built of the text's variables and of those generators (kernel). -/
theorem right_built : TieRuleCutG.builtGB rightGens fT (K.fill a) "GeneratedTopCell" = true ∧
    TieRuleCutG.builtGB rightGens fT a "Exp" = true := by decide +kernel

/-- **The premise of `rule_w2` holds in every model of Γ**, for every H: where the guards of the
text's variables hold, `K[a()] ∧ ⊤` holds one element (the Cons-Fun items of its generators), which
is one of the text's right side `K[a() ∨ b()] ∧ ⊤` (a's element is in Exp, and a context of
applications is monotone) and so of Γ's right side r (`right_iff`); so `⌈r⌉` holds of every element
of the top cell's sort, which the `\top` of the text's left side keeps its elements in. -/
theorem right_defined (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) (x : M)
    (hx : (tr ⟨tableOf [] p0, []⟩ Ltext).interpret I e x) :
    (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC rG)).interpret I e x := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hfun := (TieRuleCutG.funsInGB_withHooks c H rightGens).trans right_funs
  have hx' : (tr ⟨tableOf [] p0, []⟩ (.and topC [K.fill go, E])).interpret I e x := hx
  have h : (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC (.and topC [K.fill a, E]))).interpret I e x :=
    TieRuleCutG.rightDefined_top hI
      (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
      (show (cH H).sortName topCellSort = "GeneratedTopCell" from
        (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell"))
      hfun right_built.1 e m hg x
      ((interp_and (List.cons_ne_nil _ _)).mp hx' E (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [tr] at h ⊢
  obtain ⟨σ, σ', y, h1, h2, h3, h4⟩ := interp_sCeil_raw.mp h
  refine interp_sCeil_raw.mpr ⟨σ, σ', y, h1, h2, (right_iff H hD hSig e y).mpr ?_, h4⟩
  have h3' := (interp_and (List.cons_ne_nil _ _)).mp h3
  show (tr ⟨tableOf [] p0, []⟩ (.and topC [K.fill (.or S [a, b]), E])).interpret I e y
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact TieRuleLhs.tr_fill_mono ⟨tableOf [] p0, []⟩ K rfl
      (TieRuleLhs.sub_or_left (q := b) (TieRuleCutG.built_inh hI hfun right_built.2 e m hg)) y
      (h3' _ List.mem_cons_self)
  · rw [List.mem_singleton.mp hp]; exact h3' E (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **W2 for the rule, without a premise**: sentence 109 holds in every model of Γ, for every H
(`rule_w2` with `right_defined`). -/
theorem rule_w2_noprem (H : HookParams) : Γ (cH H) ⊧ (trS U.ax109).pat :=
  fun {_} _ {_} hI => rule_w2 H hI (right_defined H hI)

end RhsOr

namespace LhsNot

kore_term kore from "f2-examples/mlnot.kompile.kore"
definition_of defn from "f2-examples/mlnot.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

example : c.sortName 32 = "Exp" ∧ c.sortName 0 = "K" ∧ c.sortName 19 = "GeneratedCounterCell" ∧
    c.symName 385 = "Lbla" ∧ c.symName 387 = "Lblc" := by decide +kernel

def cfg (x : Term) : Term := .app 71 [.app 383 [.app 0 [.inj 32 1 x, .var 1]], .var 2]

/-- `c(Z) => G` with `pre := ¬(Z ∈ a ∧ Z ∈ G)`, Z:Exp the first variable, G:Exp the fourth. -/
def rz : Rule :=
  { vars := [32, 0, 19, 32], lhs := cfg (.app 387 [.var 0]), req := none, rhs := cfg (.var 3), ens := none,
    prio := 50, pre := .not (.and (.mem 32 (.var 0) (.app 385 [])) (.mem 32 (.var 0) (.var 3))) }

/-- The reader reads the text's rule as `rz` (`Parse.parse`, through the cut). -/
theorem read : c.rules = [rz] := rfl

def S : Kore.KSort := srt "Exp"
def z : Kore.EVar := evar "VarV0" S
def a : Kore.Pattern := ap "Lbla" []
def g : Kore.Pattern := ev "VarV3" S
/-- The connective at the position. -/
def φ : Kore.Pattern := .not S (.and S [a, g])
/-- The membership of Z in φ, as `pre` writes it. -/
def q : Kore.Pattern := .not topC (.and topC [.in S topC (.var (.evar z)) a, .in S topC (.var (.evar z)) g])
def E : Kore.Pattern := .top topC
def K : KoreCutCtx := .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] []
      (.app ⟨⟨"kseq"⟩⟩ [] [] (.app ⟨⟨"inj"⟩⟩ [S, srt "KItem"] []
        (.app ⟨⟨"Lblc"⟩⟩ [] [] .hole []) []) [ev "VarV1" (srt "K")]) [])
    [ev "VarV2" (srt "GeneratedCounterCell")]
/-- The rule's right side, `<k> G </k>`. -/
def R : Kore.Pattern := .and topC [cellCtx "Exp" (ev "VarV1" (srt "K")) (ev "VarV2" (srt "GeneratedCounterCell")) |>.fill g, E]

/-- The theorem's right pattern: the left side with the complement in its position. -/
def left : Kore.Pattern := .and topC [K.fill φ, E]

theorem right_eq : ruleRight c rz = R := by decide +kernel

/-- Γ's axiom of the rule: `\rewrites(K[Z] ∧ ⊤ ∧ q ∧ ⌈R⌉, R)`. -/
theorem left_eq : prioRuleK c rz = .rewrites topC (.and topC [K.fill (.var (.evar z)), E, q, .ceil topC topC R]) R := by
  decide +kernel

/-- The text's spelling of the canonical names of the rule's variables. -/
def spell (n : String) (_ : Kore.KSort) : String :=
  if n == "VarV1" then "Var'Unds'DotVar1" else if n == "VarV2" then "Var'Unds'DotVar0"
  else if n == "VarV3" then "Var'Unds'Gen5" else n

theorem left_text : some (renVars spell (fun n _ => n) left) = (rewritesAt kore 200).map (·.1) := by
  decide +kernel

theorem left_tie (l : Kore.Pattern) (h : (rewritesAt kore 200).map (·.1) = some l) :
    tr ⟨tableOf [] l, []⟩ l = tr ⟨tableOf [] left, []⟩ left := by
  have hl : l = renVars spell (fun n _ => n) left := by
    have := left_text; rw [h] at this; exact (Option.some.inj this).symm
  rw [hl]
  exact tr_occurrence_order spell (fun n _ => n) [] [] left (by decide +kernel)

/-- **`rule_cut_mem` at the fixture's left side**: `∃Z:Exp. (K[Z] ∧ ⊤ ∧ q)` is the text's left side
`K[¬(a ∧ G)] ∧ ⊤`, under the theorem's premises at a table without aliases. -/
theorem tie {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ⟨tbl, []⟩ (tbl.ev (evarKey z)))
    (hφ : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ φ))
    (hE : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ E))
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill φ)).interpret I e m → Inh I σ' m) (m : M) :
    (tr ⟨tbl, []⟩ (.exist topC z (.and topC [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔
      (tr ⟨tbl, []⟩ left).interpret I e m := by
  have hq : MemOf I ⟨tbl, []⟩ e (tbl.ev (evarKey z)) σ σ' q φ :=
    MemOf.not (ctx := ⟨tbl, []⟩) hSz hCz hS hC
      (MemOf.and (ctx := ⟨tbl, []⟩)
        (MemOf.in' (ctx := ⟨tbl, []⟩) hSz hCz hS hC hD hc hσ hσ' a)
        (MemOf.in' (ctx := ⟨tbl, []⟩) hSz hCz hS hC hD hc hσ hσ' g))
  exact rule_cut_mem hD ⟨tbl, []⟩ K rfl S topC z rfl φ q E e hsides hφ hE hSz hS hq
    (fun x hx => not_inh (ctx := ⟨tbl, []⟩) hS _ x hx) hout m

/-- **Γ's left side, closed by `∃Z`, is the text's left side with `⌈R⌉`**: R does not hold Z. -/
theorem left_tie_def {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ⟨tbl, []⟩ (tbl.ev (evarKey z)))
    (hφ : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ φ))
    (hE : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ E))
    (hR : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ (.ceil topC topC R)))
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill φ)).interpret I e m → Inh I σ' m) (m : M) :
    (∃ x, Inh I σ x ∧ (tr ⟨tbl, []⟩ (.and topC [K.fill (.var (.evar z)), E, q, .ceil topC topC R])).interpret I
        ⟨Function.update e.evalEvar (tbl.ev (evarKey z)) x, e.evalSvar⟩ m) ↔
      (tr ⟨tbl, []⟩ left).interpret I e m ∧ (tr ⟨tbl, []⟩ (.ceil topC topC R)).interpret I e m := by
  have ht := tie hD hc tbl e hsides hφ hE hSz hCz hS hC hσ hσ' hout m
  have hex : (tr ⟨tbl, []⟩ (.exist topC z (.and topC [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔
      ∃ x, Inh I σ x ∧ (tr ⟨tbl, []⟩ (.and topC [K.fill (.var (.evar z)), E, q])).interpret I
        ⟨Function.update e.evalEvar (tbl.ev (evarKey z)) x, e.evalSvar⟩ m := by
    show (sExists (tbl.ev (evarKey z)) (trSort tbl S) (tr ⟨tbl, []⟩ (.and topC [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔ _
    rw [interp_sExists]
    refine exists_congr fun x => and_congr_left' ?_
    rw [interp_member hD, interp_inhOf_of fun b => (hSz e x b).trans (hS b)]
    simp
  rw [← ht, hex]
  constructor
  · rintro ⟨x, hx, h4⟩
    rw [and4_iff] at h4
    exact ⟨⟨x, hx, h4.1⟩, (hR e x m).mp h4.2⟩
  · rintro ⟨⟨x, hx, h3⟩, hd⟩
    exact ⟨x, hx, (and4_iff _ _ _ _ _ _ _ _).mpr ⟨h3, (hR e x m).mpr hd⟩⟩

/-- **At the rule's own Z**: where Z's value is an element of Exp, an element of Γ's left side is
one of the text's left side and of `⌈R⌉`. -/
theorem at_rule {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ⟨tbl, []⟩ (tbl.ev (evarKey z)))
    (hφ : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ φ))
    (hE : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ E))
    (hR : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ (.ceil topC topC R)))
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill φ)).interpret I e m → Inh I σ' m) (m : M)
    (hZ : Inh I σ (e.evalEvar (tbl.ev (evarKey z))))
    (h : (tr ⟨tbl, []⟩ (.and topC [K.fill (.var (.evar z)), E, q, .ceil topC topC R])).interpret I e m) :
    (tr ⟨tbl, []⟩ left).interpret I e m ∧ (tr ⟨tbl, []⟩ (.ceil topC topC R)).interpret I e m :=
  (left_tie_def hD hc tbl e hsides hφ hE hR hSz hCz hS hC hσ hσ' hout m).mp
    ⟨_, hZ, by
      have hu : Function.update e.evalEvar (tbl.ev (evarKey z)) (e.evalEvar (tbl.ev (evarKey z))) = e.evalEvar := by
        funext y; rw [Function.update_apply]; by_cases hy : y = tbl.ev (evarKey z) <;> simp [hy]
      rw [hu]; exact h⟩

/-! ## The rule's sentence (104), for every H: W1 and W2 -/

user_axioms U from "f2-examples/mlnot.kompile.kore" module "E3-ML-RULE-LHS-NOT"

noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c rz

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

/-- Γ's left side: `K[Z] ∧ ⊤ ∧ q ∧ ⌈R⌉`. -/
def Lg : Kore.Pattern := .and topC [K.fill (.var (.evar z)), E, q, .ceil topC topC R]

theorem p0_parts : TieRuleLhs.rwParts p0 = some (topC, Lg, R) := by decide +kernel

/-- The free variables of the text's form: Z is not among them. -/
def fT : List VarKey := (freeOf [] (.rewrites topC left R)).eraseDups

/-- **The text's sentence 104 is the item of `\rewrites{C}(left, R)` at the table of Γ's axiom**,
the index of G renamed (kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT topC left R) [(4, 1)] =
    some (trS U.ax104).pat := by
  decide +kernel
theorem fT_free0 : fT.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
/-- A free variable of Γ's axiom is Z or one of the text's. -/
theorem free_cases0 : ∀ k ∈ (freeOf [] p0).eraseDups, k = evarKey z ∨ k ∈ fT := by decide +kernel
theorem z_free0 : evarKey z ∈ (freeOf [] p0).eraseDups := by decide +kernel

/-- At the table of Γ's axiom, Z is free in no side of the context, not in the connective, in
`⌈R⌉`, in R, in the guard of a variable of the text's form, nor in the top cell's sort. -/
theorem cut_free : TieRuleConnText.sidesFree ⟨tableOf [] p0, []⟩ ((tableOf [] p0).ev (evarKey z)) K = true ∧
    (tr ⟨tableOf [] p0, []⟩ φ).isFreeEvar ((tableOf [] p0).ev (evarKey z)) = false ∧
    (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).isFreeEvar ((tableOf [] p0).ev (evarKey z)) = false ∧
    (tr ⟨tableOf [] p0, []⟩ R).isFreeEvar ((tableOf [] p0).ev (evarKey z)) = false ∧
    (inhOf (trSort (tableOf [] p0) topC)).isFreeEvar ((tableOf [] p0).ev (evarKey z)) = false ∧
    ∀ k ∈ fT, (guardOf (tableOf [] p0) k).isFreeEvar ((tableOf [] p0).ev (evarKey z)) = false := by
  decide +kernel

/-- **Γ's left side, closed by `∃Z`, is the text's left side with `⌈R⌉`**, at the table of Γ's
axiom, in every model of the signature and at every valuation: the premises of the cut hold there,
the outer sort read from the `requires` `\top`. σ is the sort Exp denotes. -/
theorem left_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) : ∃ σ, (∀ (t : VarTable) (e : Valuation M) (a : M), (trSort t S).interpret I e a ↔ a = σ) ∧
      ∀ (e : Valuation M) (m : M),
        ((∃ x, Inh I σ x ∧ (tr ⟨tableOf [] p0, []⟩ Lg).interpret I
          ⟨Function.update e.evalEvar ((tableOf [] p0).ev (evarKey z)) x, e.evalSvar⟩ m) ↔
        (tr ⟨tableOf [] p0, []⟩ left).interpret I e m ∧
          (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).interpret I e m) := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  obtain ⟨σ, hσ, hS, hSz⟩ := TieRuleConnText.sort_sig hD hSig (s := 32)
    (by decide +kernel : (32 : Srt) < nRegSorts + c.sortNames.length)
    (show (cH H).sortName 32 = "Exp" from (by decide +kernel : c.sortName 32 = "Exp"))
  obtain ⟨σ', hσ', hC, hCz⟩ := TieRuleConnText.sort_sig hD hSig (s := topCellSort)
    (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
    (show (cH H).sortName topCellSort = "GeneratedTopCell" from
      (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell"))
  refine ⟨σ, hS, fun e m => ?_⟩
  have hq : MemOf I ⟨tableOf [] p0, []⟩ e ((tableOf [] p0).ev (evarKey z)) σ σ' q φ :=
    MemOf.not (ctx := ⟨tableOf [] p0, []⟩) (hSz _ _) (hCz _ _) (hS _ e) (hC _ e)
      (MemOf.and (ctx := ⟨tableOf [] p0, []⟩)
        (MemOf.in' (ctx := ⟨tableOf [] p0, []⟩) (hSz _ _) (hCz _ _) (hS _ e) (hC _ e) hD hc hσ hσ' a)
        (MemOf.in' (ctx := ⟨tableOf [] p0, []⟩) (hSz _ _) (hCz _ _) (hS _ e) (hC _ e) hD hc hσ hσ' g))
  exact cutLeft_def hD ⟨tableOf [] p0, []⟩ K rfl S topC z rfl φ q E (.ceil topC topC R) e
    (TieRuleConnText.sidesNoRead_of_free K cut_free.1) (TieRuleConnText.noRead_of_notFree cut_free.2.1)
    (TieRuleConnText.top_noRead hD (hCz _ _)) (TieRuleConnText.noRead_of_notFree cut_free.2.2.1)
    (hSz _ _) (hS _ e) hq
    (fun x hx => not_inh (ctx := ⟨tableOf [] p0, []⟩) (hS _ e) _ x hx)
    (fun m hm => TieRuleConnText.top_inh hD (hC _ e) m hm) m

/-- W1 for the rule, and the converse for `ruleItems`: Γ's one rule item is a consequence of
sentence 104 with the signature, for every H. Where the guard of Z holds, an element of Γ's left
side at Z is one of the text's left side (`left_iff`, Z its own witness); the right sides are one
pattern. -/
theorem rule0_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), (TiePair.Texts [(trS U.ax104).pat] ∪ ΓSig (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  obtain ⟨σ, hS, hiff⟩ := left_iff H hD hSig
  rw [List.mem_singleton.mp hit]
  refine TieRuleConnText.rule_w1_sides hD p0_parts rule_text0 fT_free0
    (hI _ (Or.inl (Or.inl (List.mem_singleton_self _)))) (fun e m hg x hx => ?_) (fun e m _ x hx => hx)
  have hz := hg _ z_free0
  rw [show evarKey z = .evar "VarV0" S from rfl, interp_guard_evar hD, interp_inhOf_of (hS _ e)] at hz
  refine ((hiff e x).mp ⟨e.evalEvar ((tableOf [] p0).ev (evarKey z)), hz, ?_⟩).1
  have hu : Function.update e.evalEvar ((tableOf [] p0).ev (evarKey z))
      (e.evalEvar ((tableOf [] p0).ev (evarKey z))) = e.evalEvar := by
    funext y; rw [Function.update_apply]; by_cases hy : y = (tableOf [] p0).ev (evarKey z) <;> simp [hy]
  rw [hu]; exact hx

/-- The sentence with definedness is the premise set of its item with definedness. -/
theorem texts_items_sig {ad : AxiomDecl} {Δ : Premises KoreAML.Sym} {φ : P}
    (h : φ ∈ TiePair.Texts [(trS ad).pat] ∪ Δ) : φ ∈ itemsPremises [trS ad] ∪ Δ := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl ⟨_, List.mem_singleton_self _, (List.mem_singleton.mp h).symm⟩)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/
noncomputable def ruleText : List AxiomDecl := [U.ax104]

/-- **W1 for the rule, and the converse for `ruleItems`**: each of Γ's rule items (one) is a consequence of
sentence 104 with the signature, for every H. Where the guard of Z holds, an element of Γ's left
side at Z is one of the text's left side (`left_iff`, Z its own witness); the right sides are one
pattern. -/
theorem rule_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ∪ ΓSig (cH H) ⊧ it.pat :=
  fun it hit => ⟨U.ax104, List.mem_cons_self, fun hI => rule0_from_text_sig H it hit fun φ hφ => hI φ (texts_items_sig hφ)⟩

/-- **W2 for the rule, with the guard**: in a model of Γ, sentence 104 holds where, at each
valuation at which the guards of its variables hold, `⌈R⌉` (the conjunct Γ's left side adds) holds
wherever the text's left side holds, for every H. An element of the text's left side is one of
Γ's at some value of Z in Exp (`left_iff`), Γ's item is read at that value, and neither R nor a
guard of the sentence reads Z. -/
theorem rule_w2 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (hR : ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) →
      ∀ x, (tr ⟨tableOf [] p0, []⟩ left).interpret I e x →
        (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).interpret I e x) :
    I ⊧ᴵ (trS U.ax104).pat := by
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  have hpe := TieRuleLhs.rwParts_eq p0_parts
  rw [hpe, TieRuleLhs.trAxiom_rule] at hg
  rw [← hpe] at hg
  obtain ⟨σ, hS, hiff⟩ := left_iff H hD hSig
  refine (TiePair.renSeq_iff rule_text0).mpr fun e m => item_inst_transfer hD hg e m fun hgs a hl => ?_
  obtain ⟨x, hx, h4⟩ := (hiff e a).mpr ⟨hl, hR e m hgs a hl⟩
  refine ⟨⟨Function.update e.evalEvar ((tableOf [] p0).ev (evarKey z)) x, e.evalSvar⟩, fun k hk => ?_,
    fun h => (TieRuleConnText.noRead_of_notFree cut_free.2.2.2.2.1 e x a).mpr h, h4,
    fun b hb => (TieRuleConnText.noRead_of_notFree cut_free.2.2.2.1 e x b).mp hb⟩
  rcases free_cases0 k hk with rfl | hk'
  · rw [show evarKey z = .evar "VarV0" S from rfl, interp_guard_evar hD, interp_inhOf_of (hS _ _)]
    simpa using hx
  · exact (TieRuleConnText.noRead_of_notFree (cut_free.2.2.2.2.2 k hk') e x m).mpr (hgs k hk')

/-- The generators of the right side's term: the top cell, the `k` cell, `kseq`, the injection of
Exp into KItem. -/
def rightGens : List (String × KoreAML.Gen) :=
  [("GeneratedTopCell", .ctor ⟨"Lbl'-LT-'generatedTop'-GT-'", ["KCell", "GeneratedCounterCell"], "GeneratedTopCell"⟩),
   ("KCell", .ctor ⟨"Lbl'-LT-'k'-GT-'", ["K"], "KCell"⟩),
   ("K", .ctor ⟨"kseq", ["KItem", "K"], "K"⟩),
   ("KItem", .inj "Exp")]

/-- Γ has the Cons-Fun item of each (kernel). -/
theorem right_funs : TieRuleCutG.funsInGB c rightGens = true := by decide +kernel

/-- The right side's term, `<k> G </k>`, is built of the text's variables and of those generators, at
arguments of their sorts (kernel). -/
theorem right_built : TieRuleCutG.builtGB rightGens fT
    ((cellCtx "Exp" (ev "VarV1" (srt "K")) (ev "VarV2" (srt "GeneratedCounterCell"))).fill g)
    "GeneratedTopCell" = true := by decide +kernel

/-- **The premise of `rule_w2` holds in every model of Γ**, for every H: where the guards of the
text's variables hold, the right side holds one element, by the Cons-Fun items of its generators,
so `⌈R⌉` holds of every element of the top cell's sort, which the `\top` of the text's left side
keeps its elements in. -/
theorem right_defined (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) (x : M)
    (hx : (tr ⟨tableOf [] p0, []⟩ left).interpret I e x) :
    (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).interpret I e x := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hx' : (tr ⟨tableOf [] p0, []⟩ (.and topC [K.fill φ, E])).interpret I e x := hx
  exact TieRuleCutG.rightDefined_top hI
    (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
    (show (cH H).sortName topCellSort = "GeneratedTopCell" from
      (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell"))
    ((TieRuleCutG.funsInGB_withHooks c H rightGens).trans right_funs) right_built e m hg x
    ((interp_and (List.cons_ne_nil _ _)).mp hx' E (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **W2 for the rule, without a premise**: sentence 104 holds in every model of Γ, for every H
(`rule_w2` with `right_defined`). -/
theorem rule_w2_noprem (H : HookParams) : Γ (cH H) ⊧ (trS U.ax104).pat :=
  fun {_} _ {_} hI => rule_w2 H hI (right_defined H hI)

/-- info: 'TieRuleConn.LhsNot.rule_from_text_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_from_text_sig
/-- info: 'TieRuleConn.LhsNot.rule_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_w2
/-- info: 'TieRuleConn.LhsNot.rule_w2_noprem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_w2_noprem
#check @left_iff
#check @rule_from_text_sig
#check @rule_w2
#check @right_defined
#check @rule_w2_noprem

end LhsNot

namespace LhsNotOther

kore_term kore from "f2-examples/mlnoto.kompile.kore"
definition_of defn from "f2-examples/mlnoto.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

example : c.sortName 32 = "Exp" ∧ c.sortName 0 = "K" ∧ c.sortName 19 = "GeneratedCounterCell" ∧
    c.symName 385 = "Lbla" ∧ c.symName 386 = "Lblb" ∧ c.symName 387 = "Lblc" := by decide +kernel

def cfg (x : Term) : Term := .app 71 [.app 383 [.app 0 [.inj 32 1 x, .var 1]], .var 2]

/-- `c(Z) => b` with `pre := ¬(Z ∈ a)`, Z:Exp the first variable. -/
def rz : Rule :=
  { vars := [32, 0, 19], lhs := cfg (.app 387 [.var 0]), req := none, rhs := cfg (.app 386 []), ens := none,
    prio := 50, pre := .not (.mem 32 (.var 0) (.app 385 [])) }

/-- The reader reads the text's rule as `rz` (`Parse.parse`, through the cut). -/
theorem read : c.rules = [rz] := rfl

def S : Kore.KSort := srt "Exp"
def z : Kore.EVar := evar "VarV0" S
def a : Kore.Pattern := ap "Lbla" []
def b : Kore.Pattern := ap "Lblb" []
/-- The connective at the position. -/
def φ : Kore.Pattern := .not S a
/-- The membership of Z in φ, as `pre` writes it. -/
def q : Kore.Pattern := .not topC (.in S topC (.var (.evar z)) a)
def E : Kore.Pattern := .top topC
def K : KoreCutCtx := .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] []
      (.app ⟨⟨"kseq"⟩⟩ [] [] (.app ⟨⟨"inj"⟩⟩ [S, srt "KItem"] []
        (.app ⟨⟨"Lblc"⟩⟩ [] [] .hole []) []) [ev "VarV1" (srt "K")]) [])
    [ev "VarV2" (srt "GeneratedCounterCell")]
/-- The rule's right side, `<k> b </k>`. -/
def R : Kore.Pattern := .and topC [cellCtx "Exp" (ev "VarV1" (srt "K")) (ev "VarV2" (srt "GeneratedCounterCell")) |>.fill b, E]

/-- The theorem's right pattern: the left side with the complement in its position. -/
def left : Kore.Pattern := .and topC [K.fill φ, E]

theorem right_eq : ruleRight c rz = R := by decide +kernel

/-- Γ's axiom of the rule: `\rewrites(K[Z] ∧ ⊤ ∧ q ∧ ⌈R⌉, R)`. -/
theorem left_eq : prioRuleK c rz = .rewrites topC (.and topC [K.fill (.var (.evar z)), E, q, .ceil topC topC R]) R := by
  decide +kernel

/-- The text's spelling of the canonical names of the rule's variables. -/
def spell (n : String) (_ : Kore.KSort) : String :=
  if n == "VarV1" then "Var'Unds'DotVar1" else if n == "VarV2" then "Var'Unds'DotVar0" else n

theorem left_text : some (renVars spell (fun n _ => n) left) = (rewritesAt kore 200).map (·.1) := by
  decide +kernel

theorem left_tie (l : Kore.Pattern) (h : (rewritesAt kore 200).map (·.1) = some l) :
    tr ⟨tableOf [] l, []⟩ l = tr ⟨tableOf [] left, []⟩ left := by
  have hl : l = renVars spell (fun n _ => n) left := by
    have := left_text; rw [h] at this; exact (Option.some.inj this).symm
  rw [hl]
  exact tr_occurrence_order spell (fun n _ => n) [] [] left (by decide +kernel)

/-- **`rule_cut_mem` at the fixture's left side**: `∃Z:Exp. (K[Z] ∧ ⊤ ∧ q)` is the text's left side
`K[¬a] ∧ ⊤`, under the theorem's premises at a table without aliases. -/
theorem tie {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ⟨tbl, []⟩ (tbl.ev (evarKey z)))
    (hφ : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ φ))
    (hE : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ E))
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill φ)).interpret I e m → Inh I σ' m) (m : M) :
    (tr ⟨tbl, []⟩ (.exist topC z (.and topC [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔
      (tr ⟨tbl, []⟩ left).interpret I e m := by
  have hq : MemOf I ⟨tbl, []⟩ e (tbl.ev (evarKey z)) σ σ' q φ :=
    MemOf.not (ctx := ⟨tbl, []⟩) hSz hCz hS hC
      (MemOf.in' (ctx := ⟨tbl, []⟩) hSz hCz hS hC hD hc hσ hσ' a)
  exact rule_cut_mem hD ⟨tbl, []⟩ K rfl S topC z rfl φ q E e hsides hφ hE hSz hS hq
    (fun x hx => not_inh (ctx := ⟨tbl, []⟩) hS _ x hx) hout m

/-- **Γ's left side, closed by `∃Z`, is the text's left side with `⌈R⌉`**: R does not hold Z. -/
theorem left_tie_def {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ⟨tbl, []⟩ (tbl.ev (evarKey z)))
    (hφ : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ φ))
    (hE : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ E))
    (hR : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ (.ceil topC topC R)))
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill φ)).interpret I e m → Inh I σ' m) (m : M) :
    (∃ x, Inh I σ x ∧ (tr ⟨tbl, []⟩ (.and topC [K.fill (.var (.evar z)), E, q, .ceil topC topC R])).interpret I
        ⟨Function.update e.evalEvar (tbl.ev (evarKey z)) x, e.evalSvar⟩ m) ↔
      (tr ⟨tbl, []⟩ left).interpret I e m ∧ (tr ⟨tbl, []⟩ (.ceil topC topC R)).interpret I e m := by
  have ht := tie hD hc tbl e hsides hφ hE hSz hCz hS hC hσ hσ' hout m
  have hex : (tr ⟨tbl, []⟩ (.exist topC z (.and topC [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔
      ∃ x, Inh I σ x ∧ (tr ⟨tbl, []⟩ (.and topC [K.fill (.var (.evar z)), E, q])).interpret I
        ⟨Function.update e.evalEvar (tbl.ev (evarKey z)) x, e.evalSvar⟩ m := by
    show (sExists (tbl.ev (evarKey z)) (trSort tbl S) (tr ⟨tbl, []⟩ (.and topC [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔ _
    rw [interp_sExists]
    refine exists_congr fun x => and_congr_left' ?_
    rw [interp_member hD, interp_inhOf_of fun b => (hSz e x b).trans (hS b)]
    simp
  rw [← ht, hex]
  constructor
  · rintro ⟨x, hx, h4⟩
    rw [and4_iff] at h4
    exact ⟨⟨x, hx, h4.1⟩, (hR e x m).mp h4.2⟩
  · rintro ⟨⟨x, hx, h3⟩, hd⟩
    exact ⟨x, hx, (and4_iff _ _ _ _ _ _ _ _).mpr ⟨h3, (hR e x m).mpr hd⟩⟩

/-- **At the rule's own Z**: where Z's value is an element of Exp, an element of Γ's left side is
one of the text's left side and of `⌈R⌉`. -/
theorem at_rule {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ⟨tbl, []⟩ (tbl.ev (evarKey z)))
    (hφ : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ φ))
    (hE : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ E))
    (hR : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ (.ceil topC topC R)))
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill φ)).interpret I e m → Inh I σ' m) (m : M)
    (hZ : Inh I σ (e.evalEvar (tbl.ev (evarKey z))))
    (h : (tr ⟨tbl, []⟩ (.and topC [K.fill (.var (.evar z)), E, q, .ceil topC topC R])).interpret I e m) :
    (tr ⟨tbl, []⟩ left).interpret I e m ∧ (tr ⟨tbl, []⟩ (.ceil topC topC R)).interpret I e m :=
  (left_tie_def hD hc tbl e hsides hφ hE hR hSz hCz hS hC hσ hσ' hout m).mp
    ⟨_, hZ, by
      have hu : Function.update e.evalEvar (tbl.ev (evarKey z)) (e.evalEvar (tbl.ev (evarKey z))) = e.evalEvar := by
        funext y; rw [Function.update_apply]; by_cases hy : y = tbl.ev (evarKey z) <;> simp [hy]
      rw [hu]; exact h⟩

/-! ## The rule's sentence (104), for every H: W1 and W2 -/

user_axioms U from "f2-examples/mlnoto.kompile.kore" module "E3-ML-RULE-LHS-NOT-OTHER"

noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c rz

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

/-- Γ's left side: `K[Z] ∧ ⊤ ∧ q ∧ ⌈R⌉`. -/
def Lg : Kore.Pattern := .and topC [K.fill (.var (.evar z)), E, q, .ceil topC topC R]

theorem p0_parts : TieRuleLhs.rwParts p0 = some (topC, Lg, R) := by decide +kernel

/-- The free variables of the text's form: Z is not among them. -/
def fT : List VarKey := (freeOf [] (.rewrites topC left R)).eraseDups

/-- **The text's sentence 104 is the item of `\rewrites{C}(left, R)` at the table of Γ's axiom**,
the indices of its two variables renamed (kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT topC left R) [(2, 1), (3, 2)] =
    some (trS U.ax104).pat := by
  decide +kernel
theorem fT_free0 : fT.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
/-- A free variable of Γ's axiom is Z or one of the text's. -/
theorem free_cases0 : ∀ k ∈ (freeOf [] p0).eraseDups, k = evarKey z ∨ k ∈ fT := by decide +kernel
theorem z_free0 : evarKey z ∈ (freeOf [] p0).eraseDups := by decide +kernel

/-- At the table of Γ's axiom, Z is free in no side of the context, not in the connective, in
`⌈R⌉`, in R, in the guard of a variable of the text's form, nor in the top cell's sort. -/
theorem cut_free : TieRuleConnText.sidesFree ⟨tableOf [] p0, []⟩ ((tableOf [] p0).ev (evarKey z)) K = true ∧
    (tr ⟨tableOf [] p0, []⟩ φ).isFreeEvar ((tableOf [] p0).ev (evarKey z)) = false ∧
    (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).isFreeEvar ((tableOf [] p0).ev (evarKey z)) = false ∧
    (tr ⟨tableOf [] p0, []⟩ R).isFreeEvar ((tableOf [] p0).ev (evarKey z)) = false ∧
    (inhOf (trSort (tableOf [] p0) topC)).isFreeEvar ((tableOf [] p0).ev (evarKey z)) = false ∧
    ∀ k ∈ fT, (guardOf (tableOf [] p0) k).isFreeEvar ((tableOf [] p0).ev (evarKey z)) = false := by
  decide +kernel

/-- **Γ's left side, closed by `∃Z`, is the text's left side with `⌈R⌉`**, at the table of Γ's
axiom, in every model of the signature and at every valuation: the premises of the cut hold there,
the outer sort read from the `requires` `\top`. σ is the sort Exp denotes. -/
theorem left_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) : ∃ σ, (∀ (t : VarTable) (e : Valuation M) (a : M), (trSort t S).interpret I e a ↔ a = σ) ∧
      ∀ (e : Valuation M) (m : M),
        ((∃ x, Inh I σ x ∧ (tr ⟨tableOf [] p0, []⟩ Lg).interpret I
          ⟨Function.update e.evalEvar ((tableOf [] p0).ev (evarKey z)) x, e.evalSvar⟩ m) ↔
        (tr ⟨tableOf [] p0, []⟩ left).interpret I e m ∧
          (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).interpret I e m) := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  obtain ⟨σ, hσ, hS, hSz⟩ := TieRuleConnText.sort_sig hD hSig (s := 32)
    (by decide +kernel : (32 : Srt) < nRegSorts + c.sortNames.length)
    (show (cH H).sortName 32 = "Exp" from (by decide +kernel : c.sortName 32 = "Exp"))
  obtain ⟨σ', hσ', hC, hCz⟩ := TieRuleConnText.sort_sig hD hSig (s := topCellSort)
    (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
    (show (cH H).sortName topCellSort = "GeneratedTopCell" from
      (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell"))
  refine ⟨σ, hS, fun e m => ?_⟩
  have hq : MemOf I ⟨tableOf [] p0, []⟩ e ((tableOf [] p0).ev (evarKey z)) σ σ' q φ :=
    MemOf.not (ctx := ⟨tableOf [] p0, []⟩) (hSz _ _) (hCz _ _) (hS _ e) (hC _ e)
      (MemOf.in' (ctx := ⟨tableOf [] p0, []⟩) (hSz _ _) (hCz _ _) (hS _ e) (hC _ e) hD hc hσ hσ' a)
  exact cutLeft_def hD ⟨tableOf [] p0, []⟩ K rfl S topC z rfl φ q E (.ceil topC topC R) e
    (TieRuleConnText.sidesNoRead_of_free K cut_free.1) (TieRuleConnText.noRead_of_notFree cut_free.2.1)
    (TieRuleConnText.top_noRead hD (hCz _ _)) (TieRuleConnText.noRead_of_notFree cut_free.2.2.1)
    (hSz _ _) (hS _ e) hq
    (fun x hx => not_inh (ctx := ⟨tableOf [] p0, []⟩) (hS _ e) _ x hx)
    (fun m hm => TieRuleConnText.top_inh hD (hC _ e) m hm) m

/-- W1 for the rule, and the converse for `ruleItems`: Γ's one rule item is a consequence of
sentence 104 with the signature, for every H. Where the guard of Z holds, an element of Γ's left
side at Z is one of the text's left side (`left_iff`, Z its own witness); the right sides are one
pattern. -/
theorem rule0_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), (TiePair.Texts [(trS U.ax104).pat] ∪ ΓSig (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  obtain ⟨σ, hS, hiff⟩ := left_iff H hD hSig
  rw [List.mem_singleton.mp hit]
  refine TieRuleConnText.rule_w1_sides hD p0_parts rule_text0 fT_free0
    (hI _ (Or.inl (Or.inl (List.mem_singleton_self _)))) (fun e m hg x hx => ?_) (fun e m _ x hx => hx)
  have hz := hg _ z_free0
  rw [show evarKey z = .evar "VarV0" S from rfl, interp_guard_evar hD, interp_inhOf_of (hS _ e)] at hz
  refine ((hiff e x).mp ⟨e.evalEvar ((tableOf [] p0).ev (evarKey z)), hz, ?_⟩).1
  have hu : Function.update e.evalEvar ((tableOf [] p0).ev (evarKey z))
      (e.evalEvar ((tableOf [] p0).ev (evarKey z))) = e.evalEvar := by
    funext y; rw [Function.update_apply]; by_cases hy : y = (tableOf [] p0).ev (evarKey z) <;> simp [hy]
  rw [hu]; exact hx

/-- The sentence with definedness is the premise set of its item with definedness. -/
theorem texts_items_sig {ad : AxiomDecl} {Δ : Premises KoreAML.Sym} {φ : P}
    (h : φ ∈ TiePair.Texts [(trS ad).pat] ∪ Δ) : φ ∈ itemsPremises [trS ad] ∪ Δ := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl ⟨_, List.mem_singleton_self _, (List.mem_singleton.mp h).symm⟩)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/
noncomputable def ruleText : List AxiomDecl := [U.ax104]

/-- **W1 for the rule, and the converse for `ruleItems`**: each of Γ's rule items (one) is a consequence of
sentence 104 with the signature, for every H. Where the guard of Z holds, an element of Γ's left
side at Z is one of the text's left side (`left_iff`, Z its own witness); the right sides are one
pattern. -/
theorem rule_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ∪ ΓSig (cH H) ⊧ it.pat :=
  fun it hit => ⟨U.ax104, List.mem_cons_self, fun hI => rule0_from_text_sig H it hit fun φ hφ => hI φ (texts_items_sig hφ)⟩

/-- **W2 for the rule, with the guard**: in a model of Γ, sentence 104 holds where, at each
valuation at which the guards of its variables hold, `⌈R⌉` (the conjunct Γ's left side adds) holds
wherever the text's left side holds, for every H. An element of the text's left side is one of
Γ's at some value of Z in Exp (`left_iff`), Γ's item is read at that value, and neither R nor a
guard of the sentence reads Z. -/
theorem rule_w2 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (hR : ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) →
      ∀ x, (tr ⟨tableOf [] p0, []⟩ left).interpret I e x →
        (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).interpret I e x) :
    I ⊧ᴵ (trS U.ax104).pat := by
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  have hpe := TieRuleLhs.rwParts_eq p0_parts
  rw [hpe, TieRuleLhs.trAxiom_rule] at hg
  rw [← hpe] at hg
  obtain ⟨σ, hS, hiff⟩ := left_iff H hD hSig
  refine (TiePair.renSeq_iff rule_text0).mpr fun e m => item_inst_transfer hD hg e m fun hgs a hl => ?_
  obtain ⟨x, hx, h4⟩ := (hiff e a).mpr ⟨hl, hR e m hgs a hl⟩
  refine ⟨⟨Function.update e.evalEvar ((tableOf [] p0).ev (evarKey z)) x, e.evalSvar⟩, fun k hk => ?_,
    fun h => (TieRuleConnText.noRead_of_notFree cut_free.2.2.2.2.1 e x a).mpr h, h4,
    fun b hb => (TieRuleConnText.noRead_of_notFree cut_free.2.2.2.1 e x b).mp hb⟩
  rcases free_cases0 k hk with rfl | hk'
  · rw [show evarKey z = .evar "VarV0" S from rfl, interp_guard_evar hD, interp_inhOf_of (hS _ _)]
    simpa using hx
  · exact (TieRuleConnText.noRead_of_notFree (cut_free.2.2.2.2.2 k hk') e x m).mpr (hgs k hk')

/-- The generators of the right side's term: the top cell, the `k` cell, `kseq`, the injection of
Exp into KItem and the constructor `b`. -/
def rightGens : List (String × KoreAML.Gen) :=
  [("GeneratedTopCell", .ctor ⟨"Lbl'-LT-'generatedTop'-GT-'", ["KCell", "GeneratedCounterCell"], "GeneratedTopCell"⟩),
   ("KCell", .ctor ⟨"Lbl'-LT-'k'-GT-'", ["K"], "KCell"⟩),
   ("K", .ctor ⟨"kseq", ["KItem", "K"], "K"⟩),
   ("KItem", .inj "Exp"),
   ("Exp", .ctor ⟨"Lblb", [], "Exp"⟩)]

/-- Γ has the Cons-Fun item of each (kernel). -/
theorem right_funs : TieRuleCutG.funsInGB c rightGens = true := by decide +kernel

/-- The right side's term, `<k> b </k>`, is built of the text's variables and of those generators, at
arguments of their sorts (kernel). -/
theorem right_built : TieRuleCutG.builtGB rightGens fT
    ((cellCtx "Exp" (ev "VarV1" (srt "K")) (ev "VarV2" (srt "GeneratedCounterCell"))).fill b)
    "GeneratedTopCell" = true := by decide +kernel

/-- **The premise of `rule_w2` holds in every model of Γ**, for every H: where the guards of the
text's variables hold, the right side holds one element, by the Cons-Fun items of its generators,
so `⌈R⌉` holds of every element of the top cell's sort, which the `\top` of the text's left side
keeps its elements in. -/
theorem right_defined (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) (x : M)
    (hx : (tr ⟨tableOf [] p0, []⟩ left).interpret I e x) :
    (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).interpret I e x := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hx' : (tr ⟨tableOf [] p0, []⟩ (.and topC [K.fill φ, E])).interpret I e x := hx
  exact TieRuleCutG.rightDefined_top hI
    (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
    (show (cH H).sortName topCellSort = "GeneratedTopCell" from
      (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell"))
    ((TieRuleCutG.funsInGB_withHooks c H rightGens).trans right_funs) right_built e m hg x
    ((interp_and (List.cons_ne_nil _ _)).mp hx' E (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **W2 for the rule, without a premise**: sentence 104 holds in every model of Γ, for every H
(`rule_w2` with `right_defined`). -/
theorem rule_w2_noprem (H : HookParams) : Γ (cH H) ⊧ (trS U.ax104).pat :=
  fun {_} _ {_} hI => rule_w2 H hI (right_defined H hI)

/-- info: 'TieRuleConn.LhsNotOther.rule_from_text_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_from_text_sig
/-- info: 'TieRuleConn.LhsNotOther.rule_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_w2
/-- info: 'TieRuleConn.LhsNotOther.rule_w2_noprem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_w2_noprem
#check @left_iff
#check @rule_from_text_sig
#check @rule_w2
#check @right_defined
#check @rule_w2_noprem

end LhsNotOther

/-- info: 'TieRuleConn.RhsOr.tie' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsOr.tie
/-- info: 'TieRuleConn.RhsOr.memTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsOr.memTop
/-- info: 'TieRuleConn.LhsNot.at_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LhsNot.at_rule
/-- info: 'TieRuleConn.LhsNotOther.at_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LhsNotOther.at_rule
/-- info: 'TieRuleConn.RhsOr.rule_from_text_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsOr.rule_from_text_sig
/-- info: 'TieRuleConn.RhsOr.rule_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsOr.rule_w2
#check @RhsOr.right_iff
#check @RhsOr.rule_from_text_sig
#check @RhsOr.rule_w2
/-- info: 'TieRuleConn.RhsOr.rule_w2_noprem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsOr.rule_w2_noprem
#check @RhsOr.right_defined
#check @RhsOr.rule_w2_noprem

end TieRuleConn
