/-
  The tie of sentence 157 of `f2-examples/e3-ml-rule-rhs-and-fn.kompile.kore` (the rule of
  construct fixture e3-ml-rule-rhs-and-fn, `go(X) => f(f(X) #And g(X))` in the `k` cell, read
  through `andTermsWeaker`) with Γ's item of the rule (`prioRuleK`), for every interpretation H.
  Run from the package root: `lake env lean -j1 test/TieE3MlRuleRhsAndFn157.lean`.

  The sentence's right side is `f(f(X) ∧ g(X))` in the cell. Γ's item has the right side
  `f(f(X))` in the cell with the `ensures` `f(X) ==Int g(X) = true`, and `⌈right⌉` more on its
  left side (`p0_eq`). The class is *weaker*: Γ's item is a consequence of the sentence, and the
  sentence is not a consequence of Γ's item.

  - `rule_text0`: sentence 157 is the item of the text's two sides at the table of Γ's axiom
    (kernel).
  - `left_sub`: Γ's left side is inside the text's (it holds one conjunct more).
  - `right_sub`: where `⌈right⌉` holds, the text's right side is inside Γ's. `f(f(X) ∧ g(X))` is
    inside `f(f(X))`, an application holding the elements its arguments' elements give; the
    `ensures` is an equality, all of the top cell's sort or nothing, and `⌈right⌉` says it is not
    nothing; the text's right side is inside the top cell's sort by its conjunct `\top`.
  - `rule0_from_text_sig`, `rule_from_text_sig` (W1): Γ's one rule item is a consequence of
    sentence 157 and the signature (`ΓSig`: the sorts and `\ceil`'s definition), for every H. The
    next-step operator is monotone, so the successor the sentence gives in its right side is one
    in Γ's.
  The weakening, by name: the sentence's right side `C[t ∧ u]` is replaced by `C[t] ∧ (t ==Int u
  = true)`, which holds it and is larger where the hook answers `true` at two elements that are
  not equal, off the values. No converse is stated here; test/RuleAndWeaken.lean shows it failing
  for a rule of this shape in an interpretation of definedness and the sorts (`strict_more`,
  `exact_text_step`), not on this text.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlRuleRhsAndFn157

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-rule-rhs-and-fn.kompile.kore"
definition_of defn from "f2-examples/e3-ml-rule-rhs-and-fn.kompile.kore"
user_axioms U from "f2-examples/e3-ml-rule-rhs-and-fn.kompile.kore" module "E3-ML-RULE-RHS-AND-FN"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The rule's two forms -/

def tC : Kore.KSort := srt "GeneratedTopCell"
def xP : Kore.Pattern := ev "VarV0" (srt "Int")
def kP : Kore.Pattern := ev "VarV1" (srt "K")
def cP : Kore.Pattern := ev "VarV2" (srt "GeneratedCounterCell")
/-- `f(X)` and `g(X)`. -/
def fX : Kore.Pattern := ap "Lblf" [xP]
def gX : Kore.Pattern := ap "Lblg" [xP]

/-- The context of the `k` cell's first item at the sort s:
`<generatedTop>(<k>(kseq(inj{s, KItem}(·), K)), C)`. -/
def cellK (s : String) (inner : KoreCutCtx) : KoreCutCtx :=
  .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] []
      (.app ⟨⟨"kseq"⟩⟩ [] [] (.app ⟨⟨"inj"⟩⟩ [srt s, srt "KItem"] [] inner []) [kP]) []) [cP]

/-- The context of the right side around the argument of the outer `f`. -/
def fK : KoreCutCtx := cellK "Int" (.app ⟨⟨"Lblf"⟩⟩ [] [] .hole [])

/-- The `ensures` of the reading: `f(X) ==Int g(X) = true`, in the top cell's sort. -/
def eqE : Kore.Pattern :=
  .equals (srt "Bool") tC (ap "Lbl'UndsEqlsEqls'Int'Unds'" [fX, gX]) (.dv (srt "Bool") "true")

/-- The left side's term: `go(X)` in the cell. -/
def lhsT : Kore.Pattern := (cellK "Exp" .hole).fill (ap "Lblgo" [xP])
/-- The text's right side: `f(f(X) ∧ g(X))` in the cell. -/
def rtext0 : Kore.Pattern := .and tC [fK.fill (.and (srt "Int") [fX, gX]), .top tC]
/-- Γ's right side: `f(f(X))` in the cell, with the `ensures`. -/
def rhs0 : Kore.Pattern := .and tC [fK.fill fX, eqE]
/-- `⌈right⌉`, the last conjunct of Γ's left side. -/
def ceilR : Kore.Pattern := .ceil tC tC rhs0
/-- Γ's left side: the term, no `requires`, `⌈right⌉`. -/
def L0 : Kore.Pattern := .and tC [lhsT, .top tC, ceilR]
/-- The text's left side. -/
def Ltext0 : Kore.Pattern := .and tC [lhsT, .top tC]

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0
theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl
/-- **Γ's axiom of the rule**: the right side `f(f(X))` with the `ensures`, and `⌈right⌉` on the
left side (kernel). -/
theorem p0_eq : p0 = .rewrites tC L0 rhs0 := by decide +kernel

def fT0 : List VarKey := (freeOf [] (.rewrites tC Ltext0 rtext0)).eraseDups

/-- **Sentence 157 is the item of `\rewrites{C}(Ltext0, rtext0)` at the table of Γ's axiom**
(kernel). -/
theorem rule_text0 :
    TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT0 tC Ltext0 rtext0) [] = some (trS U.ax157).pat := by
  decide +kernel
theorem free_sub : ∀ k ∈ fT0, k ∈ (freeOf [] p0).eraseDups := by decide +kernel

theorem trS157 : (trS U.ax157).pat = TieRuleLhs.itemAt (tableOf [] p0) fT0 tC Ltext0 rtext0 := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- Γ's item of the rule is the item of Γ's two sides at its table and its free variables. -/
theorem item_eq : (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat =
    TieRuleLhs.itemAt (tableOf [] p0) (freeOf [] p0).eraseDups tC L0 rhs0 := by
  have h := TieRuleLhs.trAxiom_rule tC L0 rhs0
  rw [← p0_eq] at h
  exact h

theorem bool_name (H : HookParams) : (cH H).sortName Srt.bool = "Bool" := (by decide +kernel : c.sortName Srt.bool = "Bool")
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")

/-! ## A rule item, pointwise -/

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

theorem tr_rw157 (t : VarTable) (C : Kore.KSort) (L r : Kore.Pattern) :
    tr ⟨t, []⟩ (.rewrites C L r) = sRewrites (trSort t C) (tr ⟨t, []⟩ L) (tr ⟨t, []⟩ r) := by rw [tr]

/-- A rule item that holds gives, where its guards hold, a successor in its right side to each
element of its left side that is in the rule's sort. -/
theorem item_elim157 (hD : DefOK I) {t : VarTable} {f : List VarKey} {C : Kore.KSort} {L r : Kore.Pattern}
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
  rw [tr_rw157] at h3
  unfold sRewrites at h3
  rw [interp_sImp] at h3
  exact h3.2 hl

/-- A rule item holds at a valuation where, under its guards, each element of its left side in
the rule's sort has a successor in its right side. -/
theorem item_intro157 (hD : DefOK I) {t : VarTable} {f : List VarKey} {C : Kore.KSort} {L r : Kore.Pattern}
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
  rw [tr_rw157]
  unfold sRewrites
  rw [interp_sImp]
  exact ⟨fun hf => hf.1, fun ha => ⟨ha, h hg' a ha⟩⟩

/-- The next-step operator is monotone. -/
theorem next_mono157 {φ ψ : P} {e : Valuation M} {a : M} (h : ∀ b, φ.interpret I e b → ψ.interpret I e b) :
    (sNext φ).interpret I e a → (sNext ψ).interpret I e a := by
  unfold sNext
  rw [interp_app, interp_app]
  rintro ⟨x, b, hx, hb, hxb⟩
  exact ⟨x, b, hx, h b hb, hxb⟩

end

/-! ## The two inclusions -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem eqE_tr (t : VarTable) : tr ⟨t, []⟩ eqE =
    sEquals (trSort t (srt "Bool")) (trSort t tC) (tr ⟨t, []⟩ (ap "Lbl'UndsEqlsEqls'Int'Unds'" [fX, gX]))
      (tr ⟨t, []⟩ (.dv (srt "Bool") "true")) := by
  unfold eqE; rw [tr]

omit [Inhabited M] in
/-- **Γ's left side of the rule is inside the text's**: it holds the conjunct `⌈right⌉` more. -/
theorem left_sub (t : VarTable) (e : Valuation M) (a : M)
    (h : (tr ⟨t, []⟩ L0).interpret I e a) : (tr ⟨t, []⟩ Ltext0).interpret I e a := by
  unfold L0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h _ (List.mem_cons_self ..)
  · exact h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- **Where `⌈right⌉` holds, the text's right side is inside Γ's**, in a model of definedness
and the signature: `f(f(X) ∧ g(X))` is inside `f(f(X))`, and the `ensures`, an equality that
`⌈right⌉` says holds somewhere, holds of every element of the top cell's sort. -/
theorem right_sub (H : HookParams) (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    (t : VarTable) (e : Valuation M) (a b : M)
    (hR : (tr ⟨t, []⟩ ceilR).interpret I e a) (hb : (tr ⟨t, []⟩ rtext0).interpret I e b) :
    (tr ⟨t, []⟩ rhs0).interpret I e b := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig
    (Nat.lt_of_lt_of_le (by decide : Srt.bool < nRegSorts) (Nat.le_add_right _ _) : Srt.bool < nRegSorts + (cH H).sortNames.length)
  rw [bool_name] at hσB1
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  have hSB : ∀ x, (trSort t (srt "Bool")).interpret I e x ↔ x = σB := by rw [trSort_srt]; exact hσB1
  have hSC : ∀ x, (trSort t tC).interpret I e x ↔ x = σ := by unfold tC; rw [trSort_srt]; exact hσ1
  unfold rtext0 at hb
  rw [interp_and (List.cons_ne_nil _ _)] at hb
  have hb1 := hb _ (List.mem_cons_self ..)
  have hb2 := hb (.top tC) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hbC : Inh I σ b := by
    rw [tr] at hb2
    exact (interp_inhOf_of hSC).mp ((interp_sTop hD (by unfold tC; rw [trSort_srt]; rfl) b).mp hb2)
  unfold ceilR at hR
  rw [tr] at hR
  obtain ⟨_, _, x, _, _, hx, _⟩ := interp_sCeil_raw.mp hR
  unfold rhs0 at hx
  rw [interp_and (List.cons_ne_nil _ _)] at hx
  have hx2 := hx eqE (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  rw [eqE_tr, interp_sEquals hD hc hSB hSC hσB2 hσ2] at hx2
  unfold rhs0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · refine TieRuleLhs.tr_fill_mono ⟨t, []⟩ fK rfl (fun y hy => ?_) b hb1
    rw [interp_and (List.cons_ne_nil _ _)] at hy
    exact hy _ (List.mem_cons_self ..)
  · rw [eqE_tr, interp_sEquals hD hc hSB hSC hσB2 hσ2]
    exact ⟨hbC, hx2.2⟩

end

/-! ## W1 -/

/-- **W1 for the rule, over the signature**: Γ's item is a consequence of sentence 157 and Γ's
signature, for every H. -/
theorem rule0_from_text_sig (H : HookParams) :
    itemsPremises [trS U.ax157] ∪ ΓSig (cH H) ⊧ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat := by
  intro M _ I hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inl (Or.inr ⟨x, rfl⟩))
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  have hT : I ⊧ᴵ TieRuleLhs.itemAt (tableOf [] p0) fT0 tC Ltext0 rtext0 := by
    rw [← trS157]
    exact hI _ (Or.inl (Or.inl ⟨trS U.ax157, List.mem_singleton_self _, rfl⟩))
  rw [item_eq]
  intro e m
  refine item_intro157 hD e m fun hg a ha hl => ?_
  have hR : (tr ⟨tableOf [] p0, []⟩ ceilR).interpret I e a := by
    have hl' := hl
    unfold L0 at hl'
    rw [interp_and (List.cons_ne_nil _ _)] at hl'
    exact hl' ceilR (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  exact next_mono157 (fun b hb => right_sub H hD hc hSig _ e a b hR hb)
    (item_elim157 hD hT e m (fun k hk => hg k (free_sub k hk)) a ha (left_sub _ e a hl))

/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/
noncomputable def ruleText : List AxiomDecl := [U.ax157]

/-- **W1 for the rules, over the signature, and the converse for `ruleItems`**: each of Γ's rule
items is a consequence of a text sentence of `ruleText` and Γ's signature, for every H. -/
theorem rule_from_text_sig (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl
  exact ⟨U.ax157, List.mem_cons_self, rule0_from_text_sig H⟩

/-- The priority the rule sentence's attributes state is the rule's. -/
theorem rule_prios : ruleText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) = c.rules.map (·.prio) := by
  decide +kernel

end KCore.TieE3MlRuleRhsAndFn157

#check @KCore.TieE3MlRuleRhsAndFn157.p0_eq
#check @KCore.TieE3MlRuleRhsAndFn157.rule_text0
#check @KCore.TieE3MlRuleRhsAndFn157.left_sub
#check @KCore.TieE3MlRuleRhsAndFn157.right_sub
#check @KCore.TieE3MlRuleRhsAndFn157.rule0_from_text_sig
#check @KCore.TieE3MlRuleRhsAndFn157.rule_from_text_sig
#check @KCore.TieE3MlRuleRhsAndFn157.rule_prios
#print axioms KCore.TieE3MlRuleRhsAndFn157.p0_eq
#print axioms KCore.TieE3MlRuleRhsAndFn157.rule_text0
#print axioms KCore.TieE3MlRuleRhsAndFn157.right_sub
#print axioms KCore.TieE3MlRuleRhsAndFn157.rule_from_text_sig
#print axioms KCore.TieE3MlRuleRhsAndFn157.rule_prios
