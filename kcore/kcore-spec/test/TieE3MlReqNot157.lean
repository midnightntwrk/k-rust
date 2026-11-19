/-
  The tie of sentence 157 of `f2-examples/mlreqnot.kompile.kore` (the rule of construct fixture
  e3-ml-req-not, `go(X) => done requires #Not(X >Int 0)`, read through `notAsCondition`) with Γ's
  item of the rule (`prioRuleK`), for every interpretation H, under the premise `boolClosed`.
  Run from the package root: `lake env lean -j1 test/TieE3MlReqNot157.lean`.

  The sentence's left side holds `\equals{Bool}(\not{Bool}(X >Int 0), true)`; Γ's item holds the
  reading's condition `\equals{Bool}(X >Int 0, false)`. `\not{Bool}(B)` is the complement of B in
  Bool's elements. The two conditions denote one set where every element of Bool is `true`'s or
  `false`'s (`boolClosed`) and no element is both (`boolDist`, an item of `ΓDomains`): there the
  complement of B is `true`'s element exactly where B is `false`'s (`cond_iff`).

  `boolClosed` is a fact of the builtin domain Bool. No sentence of the text states it and Γc of
  this text does not hold it (the text reads no confined sort, so Γc is Γ). It is a hypothesis
  here, named in each statement.

  - `rule_text0`: sentence 157 is the item of the text's left side at the table of Γ's axiom
    (kernel).
  - `boolDist_mem`: `boolDist H` is an item of `ΓDomains (cH H)`.
  - `cond_iff`: the two conditions denote one set, from `boolDist` and `boolClosed`.
  - `left_sub`, `left_sup`: Γ's left side is inside the text's, and the text's with `⌈R⌉` inside
    Γ's.
  - `rule_from_text_closed` (W1): Γ's one rule item is a consequence of sentence 157, `boolDist`,
    the signature and `boolClosed`.
  - `rule_w2_closed` (W2, with the guard): in a model of Γ that satisfies `boolClosed`, sentence
    157 holds at each valuation at which `⌈R⌉` holds wherever the text's left side does.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3MlReqNot157

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/mlreqnot.kompile.kore"
definition_of defn from "f2-examples/mlreqnot.kompile.kore"
user_axioms U from "f2-examples/mlreqnot.kompile.kore" module "E3-ML-REQ-NOT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The rule's two forms -/

def gtName : String := "Lbl'Unds-GT-'Int'Unds'"
def tC : Kore.KSort := srt "GeneratedTopCell"
def xP : Kore.Pattern := ev "VarV0" (srt "Int")
def kP : Kore.Pattern := ev "VarV1" (srt "K")
def cP : Kore.Pattern := ev "VarV2" (srt "GeneratedCounterCell")
/-- `X >Int 0`. -/
def gtX : Kore.Pattern := ap gtName [xP, .dv (srt "Int") "0"]
/-- `t = lit` at Bool, in the top cell's sort. -/
def eqB (a : Kore.Pattern) (lit : String) : Kore.Pattern := .equals (srt "Bool") tC a (.dv (srt "Bool") lit)
/-- The configuration `<generatedTop> <k> inj{Exp,KItem}(t) ~> K </k> C </generatedTop>`. -/
def cfg (a : Kore.Pattern) : Kore.Pattern :=
  ap "Lbl'-LT-'generatedTop'-GT-'" [ap "Lbl'-LT-'k'-GT-'" [ap "kseq" [injP "Exp" "KItem" a, kP]], cP]
/-- The rule's right side. -/
def rhs0 : Kore.Pattern := .and tC [cfg (ap "Lbldone" []), .top tC]
/-- `⌈R⌉`, the last conjunct of Γ's left side. -/
def ceilR : Kore.Pattern := .ceil tC tC rhs0
/-- Γ's left side: the term, no `requires`, the reading's condition `X >Int 0 = false`, `⌈R⌉`. -/
def L0 : Kore.Pattern := .and tC [cfg (ap "Lblgo" [xP]), .top tC, eqB gtX "false", ceilR]
/-- The text's left side: the term and `\not{Bool}(X >Int 0) = true`. -/
def Ltext0 : Kore.Pattern := .and tC [cfg (ap "Lblgo" [xP]), eqB (.not (srt "Bool") gtX) "true"]

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0
theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl
theorem p0_eq : p0 = .rewrites tC L0 rhs0 := by decide +kernel
theorem p0_parts : TieRuleLhs.rwParts p0 = some (tC, L0, rhs0) := by rw [p0_eq]; rfl

def fT0 : List VarKey := (freeOf [] (.rewrites tC Ltext0 rhs0)).eraseDups

/-- **Sentence 157 is the item of `\rewrites{C}(Ltext0, rhs0)` at the table of Γ's axiom** (kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT0 tC Ltext0 rhs0) [] = some (trS U.ax157).pat := by
  decide +kernel
theorem fT_free0 : fT0.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem free_sub : ∀ k ∈ (freeOf [] p0).eraseDups, k ∈ fT0 := by decide +kernel

/-- Sentence 157 is the item of the text's left side at the table of Γ's axiom. -/
theorem trS157 : (trS U.ax157).pat = TieRuleLhs.itemAt (tableOf [] p0) fT0 tC Ltext0 rhs0 := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- Γ's item of the rule is the item of Γ's left side at its table and its free variables. -/
theorem item_eq : (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat =
    TieRuleLhs.itemAt (tableOf [] p0) (freeOf [] p0).eraseDups tC L0 rhs0 := by
  have h := TieRuleLhs.trAxiom_rule tC L0 rhs0
  rw [← p0_eq] at h
  exact h

/-! ## The two facts of Bool -/

/-- ΓDomains' item for the values `true` and `false`: no element is both. -/
noncomputable def boolDist (H : HookParams) : P :=
  ∼(den (cH H) (KCore.bool true) ⋀ den (cH H) (KCore.bool false))

theorem boolDist_mem (H : HookParams) : ΓDomains (cH H) (boolDist H) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨KCore.bool true, KCore.bool false, Srt.bool, (by decide +kernel : (distinctSorts c).contains Srt.bool = true),
    by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel,
    by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel, by decide, rfl⟩)))

theorem den_true (H : HookParams) : den (cH H) (KCore.bool true) = tr ⟨[], []⟩ (.dv (srt "Bool") "true") := by
  show den c (KCore.bool true) = _; decide +kernel
theorem den_false (H : HookParams) : den (cH H) (KCore.bool false) = tr ⟨[], []⟩ (.dv (srt "Bool") "false") := by
  show den c (KCore.bool false) = _; decide +kernel

/-- `boolClosed` of this text: every element of Bool is `true`'s or `false`'s. -/
theorem boolClosed_eq (H : HookParams) : boolClosed (cH H) =
    (inhOf (sortP "Bool") ⊆⊆
      (tr ⟨[], []⟩ (.dv (srt "Bool") "true") ⋁ tr ⟨[], []⟩ (.dv (srt "Bool") "false"))) := by
  show boolClosed c = _; decide +kernel

theorem bool_name (H : HookParams) : (cH H).sortName Srt.bool = "Bool" := (by decide +kernel : c.sortName Srt.bool = "Bool")
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

omit [Inhabited M] in
/-- **On Bool, `true`'s elements are those that are not `false`'s**: no element is both
(`boolDist`), and every element of Bool is one of them (`boolClosed`). -/
theorem true_iff_not_false (H : HookParams) (hD : DefOK I) (hdist : I ⊧ᴵ boolDist H)
    (hcl : I ⊧ᴵ boolClosed (cH H)) {σB : M} (hσB : ∀ a, I.evalSymb (.sort ("Sort" ++ "Bool")) a ↔ a = σB)
    (t : VarTable) (e : Valuation M) (b : M) (hb : Inh I σB b) :
    (tr ⟨t, []⟩ (.dv (srt "Bool") "true")).interpret I e b ↔
      ¬ (tr ⟨t, []⟩ (.dv (srt "Bool") "false")).interpret I e b := by
  rw [tr_dv, tr_dv]
  constructor
  · intro hT hF
    have h := hdist e b
    unfold boolDist at h
    rw [den_true, den_false, tr_dv, tr_dv, interpret_neg, interpret_conj] at h
    exact h ⟨hT, hF⟩
  · intro hF
    have h := hcl e b
    rw [boolClosed_eq, interp_included hD] at h
    have h' := h b ((interp_inhOf_of (S := sortP "Bool") hσB).mpr hb)
    rw [tr_dv, tr_dv, interpret_disj] at h'
    exact h'.resolve_right hF

theorem eqB_tr (t : VarTable) (p : Kore.Pattern) (lit : String) : tr ⟨t, []⟩ (eqB p lit) =
    sEquals (trSort t (srt "Bool")) (trSort t tC) (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ (.dv (srt "Bool") lit)) := by
  unfold eqB; rw [tr]

/-- **The reading's condition and the text's denote one set**: `X >Int 0 = false` and
`\not{Bool}(X >Int 0) = true`, in a model of definedness and the signature with `boolDist` and
`boolClosed`. -/
theorem cond_iff (H : HookParams) (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    (hdist : I ⊧ᴵ boolDist H) (hcl : I ⊧ᴵ boolClosed (cH H)) (t : VarTable) (e : Valuation M) (a : M) :
    (tr ⟨t, []⟩ (eqB gtX "false")).interpret I e a ↔
      (tr ⟨t, []⟩ (eqB (.not (srt "Bool") gtX) "true")).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig
    (Nat.lt_of_lt_of_le (by decide : Srt.bool < nRegSorts) (Nat.le_add_right _ _) : Srt.bool < nRegSorts + (cH H).sortNames.length)
  rw [bool_name] at hσB1
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  have hSB : ∀ b, (trSort t (srt "Bool")).interpret I e b ↔ b = σB := by rw [trSort_srt]; exact hσB1
  have hSC : ∀ b, (trSort t tC).interpret I e b ↔ b = σ := by unfold tC; rw [trSort_srt]; exact hσ1
  have hnot : ∀ b, Inh I σB b → ((tr ⟨t, []⟩ (.not (srt "Bool") gtX)).interpret I e b ↔
      ¬ (tr ⟨t, []⟩ gtX).interpret I e b) := by
    intro b hb
    rw [tr, interp_sNot]
    exact ⟨fun h => h.1, fun h => ⟨h, (interp_inhOf_of hSB).mpr hb⟩⟩
  have hlit := fun b hb => true_iff_not_false H hD hdist hcl hσB1 t e b hb
  rw [eqB_tr, eqB_tr, interp_sEquals hD hc hSB hSC hσB2 hσ2, interp_sEquals hD hc hSB hSC hσB2 hσ2]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, fun b hb => by rw [hnot b hb, hlit b hb, h b hb]⟩
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun b hb => ?_⟩
    have h1 := h b hb
    rw [hnot b hb, hlit b hb] at h1
    exact ⟨fun hg => Classical.byContradiction fun hF => h1.mpr hF hg,
      fun hF => Classical.byContradiction fun hg => h1.mp hg hF⟩

/-- `⊤` of the top cell's sort holds of the elements a condition at that sort holds of. -/
theorem top_of_cond (H : HookParams) (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    (t : VarTable) (e : Valuation M) (a : M) {p : Kore.Pattern} {lit : String}
    (h : (tr ⟨t, []⟩ (eqB p lit)).interpret I e a) : (tr ⟨t, []⟩ (.top tC)).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig
    (Nat.lt_of_lt_of_le (by decide : Srt.bool < nRegSorts) (Nat.le_add_right _ _) : Srt.bool < nRegSorts + (cH H).sortNames.length)
  rw [bool_name] at hσB1
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  have hSB : ∀ b, (trSort t (srt "Bool")).interpret I e b ↔ b = σB := by rw [trSort_srt]; exact hσB1
  have hSC : ∀ b, (trSort t tC).interpret I e b ↔ b = σ := by unfold tC; rw [trSort_srt]; exact hσ1
  rw [eqB_tr, interp_sEquals hD hc hSB hSC hσB2 hσ2] at h
  rw [tr]
  exact (interp_sTop hD (by unfold tC; rw [trSort_srt]; rfl) a).mpr ((interp_inhOf_of hSC).mpr h.1)

/-- **Γ's left side of the rule is inside the text's**, in a model of definedness and the
signature with `boolDist` and `boolClosed`. -/
theorem left_sub (H : HookParams) (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    (hdist : I ⊧ᴵ boolDist H) (hcl : I ⊧ᴵ boolClosed (cH H)) (t : VarTable) (e : Valuation M) (a : M)
    (h : (tr ⟨t, []⟩ L0).interpret I e a) : (tr ⟨t, []⟩ Ltext0).interpret I e a := by
  unfold L0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  unfold Ltext0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h _ (List.mem_cons_self ..)
  · exact (cond_iff H hD hc hSig hdist hcl t e a).mp (h (eqB gtX "false") (by simp))

/-- **The text's left side with `⌈R⌉` is inside Γ's**, in a model of definedness and the signature
with `boolDist` and `boolClosed`. `⌈R⌉` is the hypothesis `hR`. -/
theorem left_sup (H : HookParams) (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H))
    (hdist : I ⊧ᴵ boolDist H) (hcl : I ⊧ᴵ boolClosed (cH H)) (t : VarTable) (e : Valuation M) (a : M)
    (h : (tr ⟨t, []⟩ Ltext0).interpret I e a) (hR : (tr ⟨t, []⟩ ceilR).interpret I e a) :
    (tr ⟨t, []⟩ L0).interpret I e a := by
  unfold Ltext0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have h1 := h (eqB (.not (srt "Bool") gtX) "true") (by simp)
  unfold L0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h _ (List.mem_cons_self ..)
  · exact top_of_cond H hD hc hSig t e a h1
  · exact (cond_iff H hD hc hSig hdist hcl t e a).mpr h1
  · exact hR

end

/-! ## W1 and W2 -/

/-- The premise `boolClosed`: every element of Bool is `true`'s or `false`'s. -/
noncomputable def BoolCl (H : HookParams) : Premises KoreAML.Sym := fun φ => φ = boolClosed (cH H)

/-- The premises of W1: sentence 157, `true` and `false` apart (Γ's item `boolDist_mem`), the
signature, and `boolClosed`. -/
noncomputable abbrev Pre157Cl (H : HookParams) : Premises KoreAML.Sym :=
  (TiePair.Texts [(trS U.ax157).pat, boolDist H] ∪ ΓSig (cH H)) ∪ BoolCl H

/-- **W1 for the rule, under `boolClosed`**: Γ's one rule item is a consequence of sentence 157
with `boolDist`, the signature and `boolClosed`, for every H. -/
theorem rule_from_text_closed (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), Pre157Cl H ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inl (Or.inr hφ))
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  have hdist : I ⊧ᴵ boolDist H :=
    hI _ (Or.inl (Or.inl (Or.inl (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))
  have hcl : I ⊧ᴵ boolClosed (cH H) := hI _ (Or.inr rfl)
  rw [List.mem_singleton.mp hit]
  exact TieRuleLhs.rule_w1 hD p0_parts rule_text0 fT_free0 (hI _ (Or.inl (Or.inl (Or.inl (List.mem_cons_self ..)))))
    fun e _ _ a ha => left_sub H hD hc hSig hdist hcl _ e a ha

/-- **W2 for the rule, with the guard, under `boolClosed`**: in a model of Γ that satisfies
`boolClosed`, sentence 157 holds at each valuation at which `⌈R⌉` holds wherever the text's left
side holds, for every H. -/
theorem rule_w2_closed (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hcl : I ⊧ᴵ boolClosed (cH H)) (e : Valuation M)
    (hR : ∀ a, (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a → (tr ⟨tableOf [] p0, []⟩ ceilR).interpret I e a)
    (m : M) : (trS U.ax157).pat.interpret I e m := by
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hdist : I ⊧ᴵ boolDist H := sat_dom hI (boolDist_mem H)
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  rw [item_eq] at hg
  rw [trS157]
  exact TieRuleLhs.lhs_entails hD free_sub hg e m fun _ a ha =>
    left_sup H hD hc hSig hdist hcl _ e a ha (hR a ha)

end KCore.TieE3MlReqNot157

#check @KCore.TieE3MlReqNot157.rule_text0
#check @KCore.TieE3MlReqNot157.boolDist_mem
#check @KCore.TieE3MlReqNot157.cond_iff
#check @KCore.TieE3MlReqNot157.left_sub
#check @KCore.TieE3MlReqNot157.left_sup
#check @KCore.TieE3MlReqNot157.rule_from_text_closed
#check @KCore.TieE3MlReqNot157.rule_w2_closed
#print axioms KCore.TieE3MlReqNot157.rule_text0
#print axioms KCore.TieE3MlReqNot157.boolDist_mem
#print axioms KCore.TieE3MlReqNot157.cond_iff
#print axioms KCore.TieE3MlReqNot157.rule_from_text_closed
#print axioms KCore.TieE3MlReqNot157.rule_w2_closed
