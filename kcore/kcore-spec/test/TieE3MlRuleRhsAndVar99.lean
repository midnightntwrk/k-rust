/-
  The tie of sentence 99 of `f2-examples/e3-ml-rule-rhs-and-var.kompile.kore` (the rule of
  construct fixture e3-ml-rule-rhs-and-var, `c(X) => a() #And X`, read through `andTermsCut` in
  the variable form) with Γ's item of the rule (`prioRuleK`), for every interpretation H.
  Run from the package root: `lake env lean -j1 test/TieE3MlRuleRhsAndVar99.lean`.

  The sentence's right side holds `\and{Exp}(a(), X)` in the `k` cell; Γ's item holds X there and
  the membership `X ∈ a()` beside it (`Rule.post`), and its left side holds `⌈R⌉`, R its right side
  (`ruleRightDefined`). X is an element of Exp, so `a() ∧ X` is X where X is a's element and nothing
  elsewhere, and a context of applications holds the elements its argument's elements give: the two
  right sides denote one set (`right_iff`: `TieRuleRhsAnd.rule_and_var_top`, and the two orders of
  the conjunction under the context, `and_swap`) where definedness is
  read, Exp and GeneratedTopCell each denote one sort and X is in Exp. Those hold in every model of
  Γ's signature at a valuation where the guards of Γ's axiom hold.

  - `p0_eq`: Γ's axiom, `\rewrites(L ∧ ⊤ ∧ ⌈R⌉, R)`, `R = K[X] ∧ ⊤ ∧ X ∈ a()` (kernel).
  - `rule_text0`: sentence 99 is the item of `\rewrites(L ∧ ⊤, K[a() ∧ X] ∧ ⊤)` at the table of
    Γ's axiom (kernel).
  - `rule_from_text_sig` (W1): Γ's one rule item is a consequence of sentence 99 and the
    signature, for every H.
  - `rule_w2` (W2, with the guard): in a model of Γ, sentence 99 holds at each valuation at which
    `⌈R⌉` holds wherever the text's left side does, for every H. Without the guard the sentence is
    not Γ's: at X other than `a()` its right side is empty, and it would leave `c(X)` no element.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlRuleRhsAndVar99

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-rule-rhs-and-var.kompile.kore"
definition_of defn from "f2-examples/e3-ml-rule-rhs-and-var.kompile.kore"
user_axioms U from "f2-examples/e3-ml-rule-rhs-and-var.kompile.kore" module "E3-ML-RULE-RHS-AND-VAR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The rule's two forms -/

def tC : Kore.KSort := srt "GeneratedTopCell"
def S : Kore.KSort := srt "Exp"
def v : Kore.EVar := evar "VarV0" S
def u : Kore.Pattern := ap "Lbla" []
def E : Kore.Pattern := .top tC
/-- The context of the `k` cell's first item at Exp. -/
def K : KoreCutCtx :=
  .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] []
      (.app ⟨⟨"kseq"⟩⟩ [] [] (.app ⟨⟨"inj"⟩⟩ [S, srt "KItem"] [] .hole []) [ev "VarV1" (srt "K")]) [])
    [ev "VarV2" (srt "GeneratedCounterCell")]
/-- The rule's left term, `c(X)` in the `k` cell. -/
def lhs0 : Kore.Pattern := K.fill (ap "Lblc" [.var (.evar v)])
/-- Γ's right side: X in the position, no `ensures`, the membership `X ∈ a()`. -/
def R0 : Kore.Pattern := .and tC [K.fill (.var (.evar v)), E, .in S tC (.var (.evar v)) u]
/-- The text's right side: `a() ∧ X` in the position. -/
def Rtext0 : Kore.Pattern := .and tC [K.fill (.and S [u, .var (.evar v)]), E]
/-- The same with X first, the order `TieRuleRhsAnd.rule_and_var_top` states. -/
def Rswap0 : Kore.Pattern := .and tC [K.fill (.and S [.var (.evar v), u]), E]
/-- `⌈R⌉`, the last conjunct of Γ's left side. -/
def ceilR : Kore.Pattern := .ceil tC tC R0
/-- Γ's left side: the term, no `requires`, `⌈R⌉`. -/
def L0 : Kore.Pattern := .and tC [lhs0, .top tC, ceilR]
/-- The text's left side: the term and no `requires`. -/
def Ltext0 : Kore.Pattern := .and tC [lhs0, .top tC]

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0
theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl
theorem p0_eq : p0 = .rewrites tC L0 R0 := by decide +kernel
theorem q0_eq : TieRuleLhs.rwParts p0 = some (tC, L0, R0) := by rw [p0_eq]; rfl

def fT0 : List VarKey := (freeOf [] (.rewrites tC Ltext0 Rtext0)).eraseDups

/-- **The rule sentence is the item of `\rewrites{C}(Ltext, Rtext)` at the table of Γ's axiom**
(kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT0 tC Ltext0 Rtext0) [] =
    some (trS U.ax99).pat := by decide +kernel
theorem fT_free0 : fT0.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem free_sub : ∀ k ∈ (freeOf [] p0).eraseDups, k ∈ fT0 := by decide +kernel
theorem v_free : evarKey v ∈ (freeOf [] p0).eraseDups ∧ evarKey v ∈ fT0 := by decide +kernel

theorem exp_name (H : HookParams) : (cH H).sortName 32 = "Exp" := (by decide +kernel : c.sortName 32 = "Exp")
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")

/-! ## The two right sides denote one set -/

/-- The two orders of the conjunction in the position denote one set. -/
theorem and_swap {M : Type} {I : Interpretation KoreAML.Sym M} (t : VarTable) (e : Valuation M) (a : M) :
    (tr ⟨t, []⟩ Rswap0).interpret I e a ↔ (tr ⟨t, []⟩ Rtext0).interpret I e a := by
  have hsw : ∀ p q : Kore.Pattern, ∀ b, (tr ⟨t, []⟩ (.and S [p, q])).interpret I e b →
      (tr ⟨t, []⟩ (.and S [q, p])).interpret I e b := fun p q b hb => by
    rw [interp_and (List.cons_ne_nil _ _)] at hb ⊢
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hb _ (by simp)
    · rw [hx]; exact hb _ (by simp)
  unfold Rswap0 Rtext0
  rw [interp_and (List.cons_ne_nil _ _), interp_and (List.cons_ne_nil _ _)]
  constructor
  · intro h x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · rw [hx]; exact TieRuleLhs.tr_fill_mono ⟨t, []⟩ K rfl (hsw _ _) a (h _ (by simp))
    · rw [hx]; exact h _ (by simp)
  · intro h x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · rw [hx]; exact TieRuleLhs.tr_fill_mono ⟨t, []⟩ K rfl (hsw _ _) a (h _ (by simp))
    · rw [hx]; exact h _ (by simp)

/-- **Γ's right side is the text's**, in a model of definedness and the signature, at a valuation
where X is an element of Exp. -/
theorem right_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (t : VarTable) (e : Valuation M) (m : M)
    (hg : (guardOf t (evarKey v)).interpret I e m) (a : M) :
    (tr ⟨t, []⟩ R0).interpret I e a ↔ (tr ⟨t, []⟩ Rtext0).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  obtain ⟨σe, hE, hσe⟩ := TieRhs.sortSing_sig hD hSig (s := 32)
    (by decide +kernel : (32 : Srt) < nRegSorts + c.sortNames.length)
  rw [exp_name] at hE
  obtain ⟨σt, hT, hσt⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hT
  have hSE : ∀ b, (trSort t S).interpret I e b ↔ b = σe := by unfold S; rw [trSort_srt]; exact hE
  have hSC : ∀ b, (trSort t tC).interpret I e b ↔ b = σt := by unfold tC; rw [trSort_srt]; exact hT
  have hv : Inh I σe (e.evalEvar (t.ev (evarKey v))) :=
    (interp_inhOf_of hSE).mp ((TieRuleLhs.guard_evarKey hD).mp hg)
  have hCf : (trSort t tC).isFreeEvar topVar = false := by unfold tC; rw [trSort_srt]; rfl
  exact (TieRuleRhsAnd.rule_and_var_top hD hc ⟨t, []⟩ K rfl S tC v u E e hSE hSC hσe hσt hv
    (fun b hb => TieRuleRhsAnd.top_inh hD hCf hSC b hb) a).trans (and_swap t e a)

/-! ## W1 and W2 -/

/-- Γ's left side is inside the text's. -/
theorem left_sub {M : Type} {I : Interpretation KoreAML.Sym M} (t : VarTable) (e : Valuation M) (a : M)
    (h : (tr ⟨t, []⟩ L0).interpret I e a) : (tr ⟨t, []⟩ Ltext0).interpret I e a := by
  unfold L0 at h; unfold Ltext0
  rw [interp_and (List.cons_ne_nil _ _)] at h ⊢
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp
  · rw [hp]; exact h _ (by simp)
  · rw [hp]; exact h _ (by simp)

/-- The text's left side with `⌈R⌉` is Γ's. -/
theorem left_sup {M : Type} {I : Interpretation KoreAML.Sym M} (t : VarTable) (e : Valuation M) (a : M)
    (h : (tr ⟨t, []⟩ Ltext0).interpret I e a) (hR : (tr ⟨t, []⟩ ceilR).interpret I e a) :
    (tr ⟨t, []⟩ L0).interpret I e a := by
  unfold Ltext0 at h; unfold L0
  rw [interp_and (List.cons_ne_nil _ _)] at h ⊢
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp
  · rw [hp]; exact h _ (by simp)
  · rw [hp]; exact h _ (by simp)
  · rw [hp]; exact hR

/-- **W1 for the rule, over the signature, and the converse for `ruleItems`**: Γ's one rule item
is a consequence of sentence 99 and Γ's signature, for every H. -/
theorem rule_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), (TiePair.Texts [(trS U.ax99).pat] ∪ ΓSig (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  rw [List.mem_singleton.mp hit]
  exact TieRuleRhsAnd.rule_w1_rhs hD q0_eq rule_text0 fT_free0 (hI _ (Or.inl (Or.inl (List.mem_singleton_self _))))
    fun e m hg => ⟨fun a ha => left_sub _ e a ha,
      fun a ha => (right_iff H hD hSig _ e m (hg _ v_free.1) a).mpr ha⟩

/-- Sentence 99 is the item of the text's two sides at the table of Γ's axiom. -/
theorem trS99 : (trS U.ax99).pat = TieRuleLhs.itemAt (tableOf [] p0) fT0 tC Ltext0 Rtext0 := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- **W2 for the rule, with the guard**: in a model of Γ, sentence 99 holds at each valuation at
which `⌈R⌉` holds wherever the text's left side holds, for every H. -/
theorem rule_w2 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (e : Valuation M)
    (hR : ∀ a, (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a → (tr ⟨tableOf [] p0, []⟩ ceilR).interpret I e a)
    (m : M) : (trS U.ax99).pat.interpret I e m := by
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  rw [trS99]
  exact TieRuleRhsAnd.rule_w2_rhs hD q0_eq free_sub hg e m fun hgs =>
    ⟨fun a ha => left_sup _ e a ha (hR a ha),
      fun a ha => (right_iff H hD hSig _ e m (hgs _ v_free.2) a).mp ha⟩

end KCore.TieE3MlRuleRhsAndVar99

#check @KCore.TieE3MlRuleRhsAndVar99.rule_from_text_sig
#check @KCore.TieE3MlRuleRhsAndVar99.rule_w2
#print axioms KCore.TieE3MlRuleRhsAndVar99.rule_from_text_sig
#print axioms KCore.TieE3MlRuleRhsAndVar99.rule_w2
