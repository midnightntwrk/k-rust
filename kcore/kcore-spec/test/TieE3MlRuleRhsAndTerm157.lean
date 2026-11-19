/-
  The tie of sentence 157 of `f2-examples/e3-ml-rule-rhs-and-term.kompile.kore` (the rule of
  construct fixture e3-ml-rule-rhs-and-term, `go(X) => f(X) #And g(X)`, read through `andTermsCut`
  in the fresh form) with Γ's item of the rule (`prioRuleK`), for every interpretation H.
  Run from the package root: `lake env lean -j1 test/TieE3MlRuleRhsAndTerm157.lean`.

  The sentence's right side holds `\and{Int}(f(X), g(X))` in the `k` cell; Γ's item holds there an
  existential variable Z:Int with the memberships `Z ∈ f(X)` and `Z ∈ g(X)` beside it (`Rule.exs`,
  `Rule.post`), and its left side holds `⌈R⌉`, R its right side (`ruleRightDefined`). A context of
  applications holds the elements its argument's elements give, so `K[f(X) ∧ g(X)]` is the union
  of `K[Z]` over the elements Z of both: the two right sides denote one set (`right_iff`,
  `TieRuleRhsAnd.rule_and_in_top`) where definedness is read, Int and GeneratedTopCell each denote
  one sort, no side reads Z (Z is free in none: `noRead`, kernel) and every element of `f(X)` is in
  Int (`f_in`: f's arity, an item of the signature, X being in Int). Those hold in every model of
  Γ's signature at a valuation where the guards of Γ's axiom hold.

  - `p0_eq`: Γ's axiom, `\rewrites(L ∧ ⊤ ∧ ⌈R⌉, R)`,
    `R = ∃Z:Int. (K[Z] ∧ ⊤ ∧ (Z ∈ f(X) ∧ Z ∈ g(X)))` (kernel).
  - `rule_text0`: sentence 157 is the item of `\rewrites(L ∧ ⊤, K[f(X) ∧ g(X)] ∧ ⊤)` at the table
    of Γ's axiom (kernel).
  - `rule_from_text_sig` (W1): Γ's one rule item is a consequence of sentence 157 and the
    signature, for every H.
  - `rule_w2` (W2, with the guard): in a model of Γ, sentence 157 holds at each valuation at which
    `⌈R⌉` holds wherever the text's left side does, for every H. Without the guard the sentence is
    not Γ's: at X where `f(X)` and `g(X)` share no element its right side is empty, and it would
    leave `go(X)` no element.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlRuleRhsAndTerm157

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-rule-rhs-and-term.kompile.kore"
definition_of defn from "f2-examples/e3-ml-rule-rhs-and-term.kompile.kore"
user_axioms U from "f2-examples/e3-ml-rule-rhs-and-term.kompile.kore" module "E3-ML-RULE-RHS-AND-TERM"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The rule's two forms -/

def tC : Kore.KSort := srt "GeneratedTopCell"
def S : Kore.KSort := srt "Int"
/-- The rule's variable X:Int. -/
def xV : Kore.EVar := evar "VarV0" S
/-- The cut's variable Z:Int. -/
def z : Kore.EVar := evar "VarV3" S
def t : Kore.Pattern := ap "Lblf" [.var (.evar xV)]
def u : Kore.Pattern := ap "Lblg" [.var (.evar xV)]
def E : Kore.Pattern := .top tC
/-- The context of the `k` cell's first item at the sort X. -/
def cellK (X : String) : KoreCutCtx :=
  .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] []
      (.app ⟨⟨"kseq"⟩⟩ [] [] (.app ⟨⟨"inj"⟩⟩ [srt X, srt "KItem"] [] .hole []) [ev "VarV1" (srt "K")]) [])
    [ev "VarV2" (srt "GeneratedCounterCell")]
def K : KoreCutCtx := cellK "Int"
/-- The rule's left term, `go(X)` in the `k` cell. -/
def lhs0 : Kore.Pattern := (cellK "Exp").fill (ap "Lblgo" [.var (.evar xV)])
/-- Γ's right side: Z in the position under its binder, no `ensures`, the two memberships. -/
def R0 : Kore.Pattern := .exist tC z (.and tC [K.fill (.var (.evar z)), E,
  .and tC [.in S tC (.var (.evar z)) t, .in S tC (.var (.evar z)) u]])
/-- The text's right side: `f(X) ∧ g(X)` in the position. -/
def Rtext0 : Kore.Pattern := .and tC [K.fill (.and S [t, u]), E]
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
    some (trS U.ax157).pat := by decide +kernel
theorem fT_free0 : fT0.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem free_sub : ∀ k ∈ (freeOf [] p0).eraseDups, k ∈ fT0 := by decide +kernel
theorem x_free : evarKey xV ∈ (freeOf [] p0).eraseDups ∧ evarKey xV ∈ fT0 := by decide +kernel

theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")

/-! ## The premises of the cut, at the table of Γ's axiom -/

/-- The table of Γ's axiom. -/
def tbl0 : VarTable := tableOf [] (.rewrites tC L0 R0)
theorem tbl_eq : tableOf [] p0 = tbl0 := by rw [p0_eq]; rfl

/-- Z is free in no side of the context, in neither conjunct, in `\top` and in neither sort
(kernel). -/
theorem noRead : TieRuleRhsAnd.sidesFreeB ⟨tbl0, []⟩ (tbl0.ev (evarKey z)) K = true ∧
    (tr ⟨tbl0, []⟩ t).isFreeEvar (tbl0.ev (evarKey z)) = false ∧
    (tr ⟨tbl0, []⟩ u).isFreeEvar (tbl0.ev (evarKey z)) = false ∧
    (tr ⟨tbl0, []⟩ E).isFreeEvar (tbl0.ev (evarKey z)) = false ∧
    (trSort tbl0 S).isFreeEvar (tbl0.ev (evarKey z)) = false ∧
    (trSort tbl0 tC).isFreeEvar (tbl0.ev (evarKey z)) = false := by decide +kernel

/-- f's signature, Int to Int. -/
def kf : CtorSig := ⟨388, [Srt.int], Srt.int⟩
theorem kf_mem (H : HookParams) : kf ∈ kernelSyms (cH H) := (by decide +kernel : kf ∈ kernelSyms c)
/-- f's arity item: f of elements of Int holds elements of Int only. -/
theorem kf_arity_c : (symArityItem c kf).pat =
    (sym (.symbol "Lblf") ⬝ inhOf (sortP "Int") ⊆⊆ inhOf (sortP "Int")) := by decide +kernel
kernel_rfl kf_arity_withHooks : ∀ H : HookParams, (symArityItem (c.withHooks H) kf).pat = (symArityItem c kf).pat
theorem kf_arity (H : HookParams) : (symArityItem (cH H) kf).pat =
    (sym (.symbol "Lblf") ⬝ inhOf (sortP "Int") ⊆⊆ inhOf (sortP "Int")) :=
  (kf_arity_withHooks H).trans kf_arity_c

/-- Every element of `f(X)` is in Int, in a model of the signature at a valuation where X is. -/
theorem f_in (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (tb : VarTable) (e : Valuation M)
    (hx : (inhOf (sortP "Int")).interpret I e (e.evalEvar (tb.ev (evarKey xV)))) (a : M)
    (ha : (tr ⟨tb, []⟩ t).interpret I e a) : (inhOf (sortP "Int")).interpret I e a := by
  have hit : I ⊧ᴵ (symArityItem (cH H) kf).pat := hSig _ (Or.inl (Or.inl ⟨_, sig_arity (kf_mem H), rfl⟩))
  rw [kf_arity] at hit
  refine (interp_included hD).mp (hit e default) a ?_
  unfold t ap at ha
  simp only [trArgs_cons, trArgs_nil, tr] at ha
  obtain ⟨p, b, hp, hb, hpb⟩ := interp_app.mp ha
  rw [interp_evar] at hb
  exact interp_app.mpr ⟨p, b, hp, by rw [hb]; exact hx, hpb⟩

/-! ## The two right sides denote one set -/

/-- **Γ's right side is the text's**, at the table of Γ's axiom, in a model of definedness and the
signature, at a valuation where X is an element of Int. -/
theorem right_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (e : Valuation M) (m : M)
    (hg : (guardOf tbl0 (evarKey xV)).interpret I e m) (a : M) :
    (tr ⟨tbl0, []⟩ R0).interpret I e a ↔ (tr ⟨tbl0, []⟩ Rtext0).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  obtain ⟨σi, hI', hσi⟩ := TieRhs.sortSing_sig hD hSig
    (Nat.lt_of_lt_of_le (by decide : Srt.int < nRegSorts) (Nat.le_add_right _ _) : Srt.int < nRegSorts + (cH H).sortNames.length)
  rw [int_name] at hI'
  obtain ⟨σt, hT, hσt⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hT
  have hSI : ∀ b, (trSort tbl0 S).interpret I e b ↔ b = σi := by unfold S; rw [trSort_srt]; exact hI'
  have hSC : ∀ b, (trSort tbl0 tC).interpret I e b ↔ b = σt := by unfold tC; rw [trSort_srt]; exact hT
  have hx : (inhOf (sortP "Int")).interpret I e (e.evalEvar (tbl0.ev (evarKey xV))) := by
    have := (TieRuleLhs.guard_evarKey hD).mp hg
    rw [show xV.sort = srt "Int" from rfl, trSort_srt] at this
    exact this
  have hCf : (trSort tbl0 tC).isFreeEvar topVar = false := by unfold tC; rw [trSort_srt]; rfl
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := noRead
  refine TieRuleRhsAnd.rule_and_in_top hD hc ⟨tbl0, []⟩ K rfl S tC z rfl t u E e
    (TieRuleRhsAnd.sidesNoRead_of_free K n1) (TieRuleRhsAnd.noRead_of_notFree n2)
    (TieRuleRhsAnd.noRead_of_notFree n3) (TieRuleRhsAnd.noRead_of_notFree n4)
    (TieRuleRhsAnd.noRead_of_notFree n5) (TieRuleRhsAnd.noRead_of_notFree n6) hSI hSC hσi hσt ?_
    (fun b hb => TieRuleRhsAnd.top_inh hD hCf hSC b hb) a
  intro b hb
  rw [interp_and (List.cons_ne_nil _ _)] at hb
  exact (interp_inhOf_of (S := sortP "Int") hI').mp (f_in H hD hSig tbl0 e hx b (hb _ (by simp)))

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
is a consequence of sentence 157 and Γ's signature, for every H. -/
theorem rule_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), (TiePair.Texts [(trS U.ax157).pat] ∪ ΓSig (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  rw [List.mem_singleton.mp hit]
  exact TieRuleRhsAnd.rule_w1_rhs hD q0_eq rule_text0 fT_free0 (hI _ (Or.inl (Or.inl (List.mem_singleton_self _))))
    fun e m hg => by
      rw [tbl_eq] at hg ⊢
      exact ⟨fun a ha => left_sub _ e a ha, fun a ha => (right_iff H hD hSig e m (hg _ x_free.1) a).mpr ha⟩

/-- Sentence 157 is the item of the text's two sides at the table of Γ's axiom. -/
theorem trS157 : (trS U.ax157).pat = TieRuleLhs.itemAt (tableOf [] p0) fT0 tC Ltext0 Rtext0 := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- **W2 for the rule, with the guard**: in a model of Γ, sentence 157 holds at each valuation at
which `⌈R⌉` holds wherever the text's left side holds, for every H. -/
theorem rule_w2 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (e : Valuation M)
    (hR : ∀ a, (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a → (tr ⟨tableOf [] p0, []⟩ ceilR).interpret I e a)
    (m : M) : (trS U.ax157).pat.interpret I e m := by
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  rw [trS157]
  refine TieRuleRhsAnd.rule_w2_rhs hD q0_eq free_sub hg e m fun hgs => ?_
  refine ⟨fun a ha => left_sup _ e a ha (hR a ha), ?_⟩
  rw [tbl_eq] at hgs ⊢
  exact fun a ha => (right_iff H hD hSig e m (hgs _ x_free.2) a).mp ha

end KCore.TieE3MlRuleRhsAndTerm157

#check @KCore.TieE3MlRuleRhsAndTerm157.rule_from_text_sig
#check @KCore.TieE3MlRuleRhsAndTerm157.rule_w2
#print axioms KCore.TieE3MlRuleRhsAndTerm157.rule_from_text_sig
#print axioms KCore.TieE3MlRuleRhsAndTerm157.rule_w2
