/-
  The tie of sentence 157 of `f2-examples/mlreqnot.kompile.kore` (the rule of construct fixture
  e3-ml-req-not, `go(X) => done requires #Not(X >Int 0)`, read through `notAsCondition`) with Γ's
  item of the rule (`prioRuleK`), for every interpretation H.
  Run from the package root: `lake env lean -j1 test/TieE3MlReqNot157.lean`.

  The sentence's left side holds `\equals{Bool}(\not{Bool}(X >Int 0), true)`; Γ's item holds the
  reading's condition `\equals{Bool}(X >Int 0, false)`. `\not{Bool}(B)` is the complement of B in
  Bool's elements. The two conditions denote one set where every element of Bool is `true`'s or
  `false`'s (`boolClosed`) and no element is both (`boolDist`): there the complement of B is
  `true`'s element exactly where B is `false`'s (`cond_iff`).

  `boolDist` is an item of `ΓDomains` (`boolDist_mem`) and a consequence of the text: of its
  sentences 138, 133, 147 (INT-KORE.eq-int-true-left, neq-int-false-left, eq-int-false-rigth), 49
  and 46 (the functional sentences of `_==Int_`, `_=/=Int_`), with Int's G-nonempty item of the
  text's signature and `ΓSig` (`lit_sents`, `ruleAux`, `ruleSigAux`, `ruleSigAux_text`,
  `boolDist_from_text`; the proof from the sentences is `LitsText157`).

  `boolClosed` is a fact of the builtin domain Bool. No sentence of the text is known to state it
  and Γc of this text does not hold it (the text reads no confined sort, so Γc is Γ). It is a
  hypothesis of W1 and of the direction entailed at every valuation, named in each statement, and
  the one premise of W1, beside `ΓSig`, that is no sentence or signature item of the text. It does
  not empty the W2 statements: Γ with the step's closure has a model that satisfies it, for every
  H (`closed_model`, the value model at its own step). That the premises of W1 (`Pre157Cl H`)
  have a model is argued, not proved here: it asks of that model the sentences `ruleAux` too.

  - `rule_text0`: sentence 157 is the item of the text's left side at the table of Γ's axiom
    (kernel).
  - `cond_iff`: the two conditions denote one set, from `boolDist` and `boolClosed`.
  - `left_sub`, `left_sup`: Γ's left side is inside the text's, and the text's with `⌈R⌉` inside
    Γ's.
  - `rule_from_text_closed` (W1): Γ's one rule item is a consequence of `Pre157Cl H`: sentence 157,
    the sentences `ruleAux`, the signature item `ruleSigAux`, `ΓSig` and `boolClosed`. No item of
    `ΓDomains` is a premise.
  - `rule_w2_closed` (W2, with the guard): in a model of Γ that satisfies `boolClosed`, sentence
    157 holds at each valuation at which `⌈R⌉` holds wherever the text's left side does.
  - `right_defined`, `rule_w2_closed_noprem`: `⌈R⌉` holds in every model of Γ where the guards hold
    (R is built of variables, constructors and `inj{Exp,KItem}`; the `requires` keeps the left
    side's elements in the top cell's sort, `TieRuleCutG.equals_top`), so sentence 157 holds in
    every model of Γ that satisfies `boolClosed`.
  - `rule157_at_values` (`EntailsAtValues`): Γ entails sentence 157 at values, with no closure of
    Bool. At a value of X, `X >Int 0` is `true`'s element, `false`'s, or holds nothing
    (`gt_at_value`: `LibEv.den_val`, the graph of `>Int` in `ΓDomains`). In the first and the last
    case the text's condition fails (`true`'s element is not in the complement; the complement
    holds `false`'s element, which is not `true`'s), and in the second Γ's condition holds
    (`left_sup_values`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

deriving instance DecidableEq for KoreAML.SortDecl

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

/-! ## The Bool literals from the text's sentences

The text writes no sentence about `\dv{SortBool{}}("true")` alone. It writes three sentences of
module INT-KORE over element variables and the functional sentences of `_==Int_` and `_=/=Int_`.
At an element n of Int, with both sort variables at Int: `n ==Int n` is one element of Bool among
Bool's and agrees with `true` on Bool; `n =/=Int n` likewise with `false`; and `false` does not
agree with `n ==Int n` on Bool. -/

namespace LitsText157

set_option linter.unusedSectionVars false

/-- The sort variable `Q0` of a simplification sentence. -/
def Q0v : Kore.SortVar := ⟨⟨⟨"Q0"⟩⟩⟩
def Q0 : Kore.KSort := .var Q0v
def eqIntName : String := "Lbl'UndsEqlsEqls'Int'Unds'"
def neqIntName : String := "Lbl'UndsEqlsSlshEqls'Int'Unds'"

/-- The functional sentence of a symbol `f` from two Ints to Bool:
`axiom{R} \exists{R}(Val:SortBool{}, \equals{SortBool{}, R}(Val, f(K0:SortInt{}, K1:SortInt{})))`. -/
def fnlBoolAx (f : String) : Kore.Axiom :=
  ⟨[Rv], .exist R (evar "Val" (srt "Bool"))
    (.equals (srt "Bool") R (ev "Val" (srt "Bool")) (ap f [ev "K0" (srt "Int"), ev "K1" (srt "Int")])), []⟩

/-- A sentence `axiom{R, Q0} \implies{R}(\top{R}(), \equals{Q0, R}(l, \and{Q0}(r, \top{Q0}())))`. -/
def simpAx (l r : Kore.Pattern) : Kore.Axiom :=
  ⟨[Rv, Q0v], .implies R (.top R) (.equals Q0 R l (.and Q0 [r, .top Q0])), []⟩

/-- `\equals{SortInt{}, Q0}(K1, K2)`. -/
def k12Eq : Kore.Pattern := .equals (srt "Int") Q0 (ev "VarK1" (srt "Int")) (ev "VarK2" (srt "Int"))
def k12App (f : String) : Kore.Pattern := ap f [ev "VarK1" (srt "Int"), ev "VarK2" (srt "Int")]

/-- INT-KORE.eq-int-true-left: `{K1 ==Int K2 #Equals true} => {K1 #Equals K2}`. -/
def eqIntTrueLeftAx : Kore.Axiom :=
  simpAx (.equals (srt "Bool") Q0 (k12App eqIntName) (.dv (srt "Bool") "true")) k12Eq
/-- INT-KORE.neq-int-false-left: `{K1 =/=Int K2 #Equals false} => {K1 #Equals K2}`. -/
def neqIntFalseLeftAx : Kore.Axiom :=
  simpAx (.equals (srt "Bool") Q0 (k12App neqIntName) (.dv (srt "Bool") "false")) k12Eq
/-- INT-KORE.eq-int-false-rigth: `{false #Equals K1 ==Int K2} => #Not({K1 #Equals K2})`. -/
def eqIntFalseRightAx : Kore.Axiom :=
  simpAx (.equals (srt "Bool") Q0 (.dv (srt "Bool") "false") (k12App eqIntName)) (.not Q0 k12Eq)

/-- The translation of a sentence, whatever its place in a text: the pattern of `trAxiom` reads
neither the index nor the module, and the sort of these sentences is read without the symbol
declarations. -/
def sentPat (a : Kore.Axiom) : P := (trAxiom [] [] ⟨0, "", a⟩).pat

def intP : P := sym (.sort "SortInt")
def boolP : P := sym (.sort "SortBool")
/-- `f(x, y)` at the variables 3 and 4, the two Int variables of each of the five sentences. -/
def app34 (f : String) : P := sym (.symbol f) ⬝ .evar ⟨3⟩ ⬝ .evar ⟨4⟩
def litP (n : String) : P := sym (.dv n) ⬝ boolP
def g34 : List P := [(⟨3⟩ : EVar) ∈∈ inhOf intP, (⟨4⟩ : EVar) ∈∈ inhOf intP]

theorem fnlBool_shape (f : String) : sentPat (fnlBoolAx f) =
    (conjList (sortGuard ⟨1⟩ :: g34) ⇒
      (sExists ⟨2⟩ boolP (sEquals boolP (.evar ⟨1⟩) (.evar ⟨2⟩) (app34 f)) ≡ inhOf (.evar ⟨1⟩))) := by
  rfl

theorem simp_shape_tt : sentPat eqIntTrueLeftAx =
    (conjList (sortGuard ⟨1⟩ :: sortGuard ⟨2⟩ :: g34) ⇒
      (sImp (.evar ⟨1⟩) (sTop (.evar ⟨1⟩)) (sEquals (.evar ⟨2⟩) (.evar ⟨1⟩)
        (sEquals boolP (.evar ⟨2⟩) (app34 eqIntName) (litP "true"))
        (sAnd (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩)) (sTop (.evar ⟨2⟩)))) ≡ inhOf (.evar ⟨1⟩))) := by
  decide +kernel

theorem simp_shape_nf : sentPat neqIntFalseLeftAx =
    (conjList (sortGuard ⟨1⟩ :: sortGuard ⟨2⟩ :: g34) ⇒
      (sImp (.evar ⟨1⟩) (sTop (.evar ⟨1⟩)) (sEquals (.evar ⟨2⟩) (.evar ⟨1⟩)
        (sEquals boolP (.evar ⟨2⟩) (app34 neqIntName) (litP "false"))
        (sAnd (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩)) (sTop (.evar ⟨2⟩)))) ≡ inhOf (.evar ⟨1⟩))) := by
  decide +kernel

theorem simp_shape_ff : sentPat eqIntFalseRightAx =
    (conjList (sortGuard ⟨1⟩ :: sortGuard ⟨2⟩ :: g34) ⇒
      (sImp (.evar ⟨1⟩) (sTop (.evar ⟨1⟩)) (sEquals (.evar ⟨2⟩) (.evar ⟨1⟩)
        (sEquals boolP (.evar ⟨2⟩) (litP "false") (app34 eqIntName))
        (sAnd (sNot (.evar ⟨2⟩) (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩))) (sTop (.evar ⟨2⟩)))) ≡
        inhOf (.evar ⟨1⟩))) := by
  decide +kernel

section lits
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The valuation that gives the variables 1 and 2 (the sort variables) `σ` and every other
variable `n`. -/
def valAt (σ n : M) : Valuation M := ⟨fun x => match x with | ⟨1⟩ => σ | ⟨2⟩ => σ | _ => n, fun _ _ => False⟩

/-- An element of `f(n, n)`. -/
def AppAt (I : Interpretation KoreAML.Sym M) (f : String) (n b : M) : Prop :=
  ∃ s x, I.evalSymb (.symbol f) s ∧ I.evalApp s n x ∧ I.evalApp x n b

theorem interp_app34 {f : String} {e : Valuation M} {n : M} (h3 : e.evalEvar ⟨3⟩ = n) (h4 : e.evalEvar ⟨4⟩ = n)
    (b : M) : (app34 f).interpret I e b ↔ AppAt I f n b := by
  unfold app34 AppAt
  simp only [interp_app, interp_sym, interp_evar]
  constructor
  · rintro ⟨x, y, ⟨s, z, hs, rfl, hx⟩, rfl, hb⟩
    exact ⟨s, x, hs, h3 ▸ hx, h4 ▸ hb⟩
  · rintro ⟨s, x, hs, hx, hb⟩
    exact ⟨x, _, ⟨s, _, hs, rfl, h3 ▸ hx⟩, rfl, h4 ▸ hb⟩

variable [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σI σB n : M}
  (hI : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) (hσI : IsSort I σI)
  (hB : ∀ a, I.evalSymb (.sort "SortBool") a ↔ a = σB) (hσB : IsSort I σB) (hn : Inh I σI n)
include hD hI hσI hn

theorem g34_at (e : Valuation M) (h3 : e.evalEvar ⟨3⟩ = n) (h4 : e.evalEvar ⟨4⟩ = n) (m : M) :
    ∀ w ∈ g34, w.interpret I e m := by
  intro w hw
  simp only [g34, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rw [interp_member hD, interp_inhOf_of (S := intP) (σ := σI) (fun a => hI a), h3]; exact hn
  · rw [interp_member hD, interp_inhOf_of (S := intP) (σ := σI) (fun a => hI a), h4]; exact hn

omit hI hn in
theorem sortGuard_at (e : Valuation M) {x : EVar} (hx : e.evalEvar x = σI) (m : M) :
    (sortGuard x).interpret I e m := by
  unfold sortGuard; rw [interp_member hD, interp_sortsDomain, hx]; exact hσI

include hc hB hσB

/-- **A functional sentence at `(n, n)`**: among Bool's elements, `f(n, n)` holds exactly one. -/
theorem fnl_one {f : String} (h : I ⊧ᴵ sentPat (fnlBoolAx f)) :
    ∃ y, Inh I σB y ∧ ∀ b, Inh I σB b → (AppAt I f n b ↔ b = y) := by
  have h1 := h (valAt σI n) n
  rw [fnlBool_shape, interpret_impl] at h1
  have h2 := h1 (interp_conjList fun w hw => by
    rcases List.mem_cons.mp hw with rfl | hw
    · exact sortGuard_at hD hσI _ rfl n
    · exact g34_at hD hI hσI hn _ rfl rfl n w hw)
  rw [interp_equal hD] at h2
  have h3 := (h2 n).mpr ((interp_inhOf_of (σ := σI) (fun a => Iff.rfl)).mpr hn)
  rw [interp_sExists] at h3
  obtain ⟨y, hy1, hy2⟩ := h3
  rw [interp_member hD, interp_inhOf_of (S := boolP) (σ := σB) (fun a => hB a)] at hy1
  simp only [Function.update_same] at hy1
  rw [interp_sEquals hD hc (S := boolP) (σ := σB) (σ' := σI) (fun a => hB a) (fun a => Iff.rfl) hσB hσI] at hy2
  refine ⟨y, hy1, fun b hb => ?_⟩
  have h4 := hy2.2 b hb
  rw [interp_app34 (n := n) rfl rfl, interp_evar] at h4
  simp only [Function.update_same] at h4
  exact h4.symm

/-- **A simplification sentence at `(n, n)`**, the sort variables at Int: its two sides hold the
same of `n`. -/
theorem simp_at {L Rr : P}
    (h : I ⊧ᴵ (conjList (sortGuard ⟨1⟩ :: sortGuard ⟨2⟩ :: g34) ⇒
      (sImp (.evar ⟨1⟩) (sTop (.evar ⟨1⟩)) (sEquals (.evar ⟨2⟩) (.evar ⟨1⟩) L Rr) ≡ inhOf (.evar ⟨1⟩)))) :
    L.interpret I (valAt σI n) n ↔ Rr.interpret I (valAt σI n) n := by
  have h1 := h (valAt σI n) n
  rw [interpret_impl] at h1
  have h2 := h1 (interp_conjList fun w hw => by
    rcases List.mem_cons.mp hw with rfl | hw
    · exact sortGuard_at hD hσI _ rfl n
    rcases List.mem_cons.mp hw with rfl | hw
    · exact sortGuard_at hD hσI _ rfl n
    · exact g34_at hD hI hσI hn _ rfl rfl n w hw)
  rw [interp_equal hD] at h2
  have hin : (inhOf (.evar ⟨1⟩) : P).interpret I (valAt σI n) n :=
    (interp_inhOf_of (σ := σI) (fun a => Iff.rfl)).mpr hn
  have h3 := (h2 n).mpr hin
  rw [interp_sImp] at h3
  have h4 := h3.2 ((interp_sTop hD rfl n).mpr hin)
  rw [interp_sEquals hD hc (σ := σI) (σ' := σI) (fun a => Iff.rfl) (fun a => Iff.rfl) hσI hσI] at h4
  exact h4.2 n hn

/-- `\equals{SortBool{}, Q0}(x, y)` at `n`, Q0 at Int: `x` and `y` hold the same of Bool's
elements. -/
theorem boolEq_at {x y : P} : (sEquals boolP (.evar ⟨2⟩) x y).interpret I (valAt σI n) n ↔
    ∀ b, Inh I σB b → (x.interpret I (valAt σI n) b ↔ y.interpret I (valAt σI n) b) := by
  rw [interp_sEquals hD hc (S := boolP) (σ := σB) (σ' := σI) (fun a => hB a) (fun a => Iff.rfl) hσB hσI]
  exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩

/-- `\and{Q0}(\equals{SortInt{}, Q0}(K1, K2), \top{Q0}())` holds of `n` at `(n, n)`. -/
theorem k12_at : (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩)).interpret I (valAt σI n) n := by
  rw [interp_sEquals hD hc (S := intP) (σ := σI) (σ' := σI) (fun a => hI a) (fun a => Iff.rfl) hσI hσI]
  exact ⟨hn, fun _ _ => Iff.rfl⟩

omit hI hσI hn hc in
/-- A literal of Bool holds elements of Bool only (its arity item). -/
theorem lit_in_bool {lit : String} (hd : I ⊧ᴵ (dvArityItem lit).pat) (e : Valuation M) (m : M)
    (h : (litP lit).interpret I e m) : Inh I σB m := by
  have h1 := hd ⟨fun _ => σB, e.evalSvar⟩ default
  unfold dvArityItem at h1
  dsimp only at h1
  unfold guarded at h1
  have h2 := h1 (by
    unfold conjList sortGuard; rw [interp_member hD, interp_sortsDomain]; exact hσB)
  rw [interp_included hD] at h2
  have h3 := h2 m (by
    unfold litP boolP at h
    rw [interp_app] at h ⊢
    obtain ⟨a, b, ha, hb, hab⟩ := h
    exact ⟨a, σB, ha, rfl, (hB b).mp hb ▸ hab⟩)
  exact (interp_inhOf_of (σ := σB) (fun a => Iff.rfl)).mp h3

/-- **The Bool literals from the text's sentences.** In an interpretation with definedness,
`⌈_⌉`'s definition, the sort constants Int and Bool, an element `n` of Int and the arity of the
literals `true` and `false`, that satisfies eq-int-true-left, neq-int-false-left,
eq-int-false-rigth and the functional sentences of `_==Int_` and `_=/=Int_`: `false` and `true`
each denote one element of Bool, and the two elements differ. `n ==Int n` is one element of Bool
among Bool's and agrees there with `true`; `n =/=Int n` likewise with `false`; and `false` does
not agree with `n ==Int n` on Bool. -/
theorem boolLits_core (hdT : I ⊧ᴵ (dvArityItem "true").pat) (hdF : I ⊧ᴵ (dvArityItem "false").pat)
    (h1 : I ⊧ᴵ sentPat eqIntTrueLeftAx) (h2 : I ⊧ᴵ sentPat neqIntFalseLeftAx)
    (h3 : I ⊧ᴵ sentPat eqIntFalseRightAx)
    (hf1 : I ⊧ᴵ sentPat (fnlBoolAx eqIntName)) (hf2 : I ⊧ᴵ sentPat (fnlBoolAx neqIntName)) (e : Valuation M) :
    ∃ aF aT, (∀ m, (litP "false").interpret I e m ↔ m = aF) ∧ (∀ m, (litP "true").interpret I e m ↔ m = aT) ∧
      aF ≠ aT ∧ Inh I σB aF ∧ Inh I σB aT := by
  have hcl : ∀ (lit : String) m, (litP lit).interpret I e m ↔ (litP lit).interpret I (valAt σI n) m :=
    fun lit m => ((Closed.sym _).app (Closed.sym _)).interp _ _ m
  obtain ⟨v, hv, hv1⟩ := fnl_one hD hc hI hσI hB hσB hn hf1
  obtain ⟨w, hw, hw1⟩ := fnl_one hD hc hI hσI hB hσB hn hf2
  rw [simp_shape_tt] at h1
  rw [simp_shape_nf] at h2
  rw [simp_shape_ff] at h3
  have hk : (sAnd (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩)) (sTop (.evar ⟨2⟩)) : P).interpret I (valAt σI n) n :=
    interp_sAnd.mpr ⟨k12_at hD hc hI hσI hB hσB hn,
      (interp_sTop hD rfl n).mpr ((interp_inhOf_of (σ := σI) (fun a => Iff.rfl)).mpr hn)⟩
  have e1 := (boolEq_at hD hc hI hσI hB hσB hn).mp ((simp_at hD hc hI hσI hB hσB hn h1).mpr hk)
  have e2 := (boolEq_at hD hc hI hσI hB hσB hn).mp ((simp_at hD hc hI hσI hB hσB hn h2).mpr hk)
  have e3 : ¬ ∀ b, Inh I σB b → ((litP "false").interpret I (valAt σI n) b ↔ (app34 eqIntName).interpret I (valAt σI n) b) :=
    fun hall => by
      have := (simp_at hD hc hI hσI hB hσB hn h3).mp ((boolEq_at hD hc hI hσI hB hσB hn).mpr hall)
      rw [interp_sAnd, interp_sNot] at this
      exact this.1.1 (k12_at hD hc hI hσI hB hσB hn)
  have hT : ∀ m, (litP "true").interpret I e m ↔ m = v := fun m => by
    rw [hcl]
    constructor
    · intro hm
      have hmB := lit_in_bool hD hB hσB hdT _ m hm
      exact (hv1 m hmB).mp ((interp_app34 rfl rfl m).mp ((e1 m hmB).mpr hm))
    · rintro rfl
      exact (e1 m hv).mp ((interp_app34 rfl rfl m).mpr ((hv1 m hv).mpr rfl))
  have hF : ∀ m, (litP "false").interpret I e m ↔ m = w := fun m => by
    rw [hcl]
    constructor
    · intro hm
      have hmB := lit_in_bool hD hB hσB hdF _ m hm
      exact (hw1 m hmB).mp ((interp_app34 rfl rfl m).mp ((e2 m hmB).mpr hm))
    · rintro rfl
      exact (e2 m hw).mp ((interp_app34 rfl rfl m).mpr ((hw1 m hw).mpr rfl))
  refine ⟨w, v, hF, hT, fun hwv => e3 fun b hb => ?_, hw, hv⟩
  rw [← hcl, hF, interp_app34 (n := n) rfl rfl, hv1 b hb, hwv]

end lits

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- `boolLits_of_text` with the signature items from `ΓSig c`, for a semantics whose sort `sI`
is named Int. -/
theorem boolLits_of_text_sig [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c)
    {sI : Srt} (hsI : sI < nRegSorts + c.sortNames.length) (hnI : c.sortName sI = "Int") {bn : Bool}
    (hne : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], bn⟩).pat)
    (h1 : I ⊧ᴵ sentPat eqIntTrueLeftAx) (h2 : I ⊧ᴵ sentPat neqIntFalseLeftAx)
    (h3 : I ⊧ᴵ sentPat eqIntFalseRightAx)
    (hf1 : I ⊧ᴵ sentPat (fnlBoolAx eqIntName)) (hf2 : I ⊧ᴵ sentPat (fnlBoolAx neqIntName))
    (t : VarTable) (e : Valuation M) :
    ∃ σB aF aT, (∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "false")).interpret I e m ↔ m = aF) ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "true")).interpret I e m ↔ m = aT) ∧
      aF ≠ aT ∧ Inh I σB aF ∧ Inh I σB aT := by
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  obtain ⟨σI, hI, hσI⟩ := TieRhs.sortSing_sig hD hSig hsI
  rw [hnI] at hI
  have hI : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI := hI
  obtain ⟨σB, hB, hσB⟩ := TieRhs.sortSing_sig hD hSig (bool_numbered (c := c))
  rw [sortName_bool] at hB
  obtain ⟨n, hn⟩ := nonempty_of hD hne (e := e)
  have hn' : Inh I σI n := (interp_inhOf_of (S := intP) (σ := σI) (fun a => hI a)).mp hn
  obtain ⟨aF, aT, hF, hT, hne', hiF, hiT⟩ := boolLits_core hD hc hI hσI hB hσB hn'
    (hSig _ (Or.inr ⟨"true", rfl⟩)) (hSig _ (Or.inr ⟨"false", rfl⟩)) h1 h2 h3 hf1 hf2 e
  have htr : ∀ (lit : String), tr ⟨t, []⟩ (.dv (srt "Bool") lit) = litP lit := by
    intro lit; rw [tr, trSort_srt]; rfl
  refine ⟨σB, aF, aT, fun a => by rw [trSort_srt]; exact hB a, hσB, fun m => ?_, fun m => ?_, hne', hiF, hiT⟩
  · rw [htr]; exact hF m
  · rw [htr]; exact hT m

end
end LitsText157

/-- **Each of the five sentences is the pattern `LitsText157` writes for it** (kernel):
INT-KORE.eq-int-true-left (138), INT-KORE.neq-int-false-left (133), INT-KORE.eq-int-false-rigth
(147), and the functional sentences of `_==Int_` (49) and `_=/=Int_` (46). -/
theorem lit_sents :
    (trS U.ax138).pat = LitsText157.sentPat LitsText157.eqIntTrueLeftAx ∧
    (trS U.ax133).pat = LitsText157.sentPat LitsText157.neqIntFalseLeftAx ∧
    (trS U.ax147).pat = LitsText157.sentPat LitsText157.eqIntFalseRightAx ∧
    (trS U.ax49).pat = LitsText157.sentPat (LitsText157.fnlBoolAx LitsText157.eqIntName) ∧
    (trS U.ax46).pat = LitsText157.sentPat (LitsText157.fnlBoolAx LitsText157.neqIntName) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The other sentences of the text the statement reads. -/
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

/-- **No element is both `true`'s and `false`'s** in an interpretation with definedness and the
signature that satisfies the five sentences and Int's G-nonempty item: `boolDist` from the text. -/
theorem boolDist_of_text (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig (cH H))
    (hT : ∀ φ ∈ ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat), I ⊧ᴵ φ) : I ⊧ᴵ boolDist H := by
  intro e m
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hT' : ∀ φ ∈ [(trS U.ax138).pat, (trS U.ax133).pat, (trS U.ax147).pat, (trS U.ax49).pat, (trS U.ax46).pat,
      (nonemptyItem ⟨"SortInt", [], true⟩).pat], I ⊧ᴵ φ := hT
  obtain ⟨s1, s2, s3, s4, s5⟩ := lit_sents
  obtain ⟨σB, aF, aT, -, -, haf, hat, hne, -, -⟩ := LitsText157.boolLits_of_text_sig hD hSig
    (Nat.lt_of_lt_of_le (by decide : Srt.int < nRegSorts) (Nat.le_add_right _ _) :
      Srt.int < nRegSorts + (cH H).sortNames.length) (int_name H)
    (hT' _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
    (s1 ▸ hT' _ (.head _)) (s2 ▸ hT' _ (.tail _ (.head _))) (s3 ▸ hT' _ (.tail _ (.tail _ (.head _))))
    (s4 ▸ hT' _ (.tail _ (.tail _ (.tail _ (.head _)))))
    (s5 ▸ hT' _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) [] e
  unfold boolDist
  rw [interpret_neg, interpret_conj, den_true, den_false]
  rintro ⟨h1, h2⟩
  exact hne (((haf m).mp h2).symm.trans ((hat m).mp h1))

/-- **The text entails `boolDist`**, for every H: from the five sentences, Int's G-nonempty item
and the signature. -/
theorem boolDist_from_text (H : HookParams) :
    TiePair.Texts (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat)) ∪ ΓSig (cH H) ⊧ boolDist H := by
  intro M _ I hI
  exact boolDist_of_text H (TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)) (fun φ hφ => hI φ (Or.inr hφ))
    fun φ hφ => hI φ (Or.inl (Or.inl hφ))

/-! ## W1 and W2 -/

/-- The premise `boolClosed`: every element of Bool is `true`'s or `false`'s. -/
noncomputable def BoolCl (H : HookParams) : Premises KoreAML.Sym := fun φ => φ = boolClosed (cH H)

/-- The premises of W1: sentence 157, the text's sentences `ruleAux` and signature item
`ruleSigAux` (from which `true` and `false` are apart, `boolDist_from_text`), the signature, and
`boolClosed`, the one premise beside `ΓSig` that is no sentence or signature item of the text. -/
noncomputable abbrev Pre157Cl (H : HookParams) : Premises KoreAML.Sym :=
  (TiePair.Texts ((trS U.ax157).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪ ΓSig (cH H)) ∪
    BoolCl H

/-- **W1 for the rule, under `boolClosed`**: Γ's one rule item is a consequence of sentence 157
with the text's sentences `ruleAux`, Int's G-nonempty item, the signature and `boolClosed`, for
every H. No item of `ΓDomains` is among the premises. -/
theorem rule_from_text_closed (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), Pre157Cl H ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inl (Or.inr hφ))
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  have hdist : I ⊧ᴵ boolDist H := boolDist_of_text H hD hSig
    fun φ hφ => hI φ (Or.inl (Or.inl (Or.inl (List.mem_cons_of_mem _ hφ))))
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

/-! ## The right side is defined in every model of Γ -/

/-- The generators of the right side's term: the top cell, the `k` cell, `kseq`, the injection of
Exp into KItem and the constructor `done`. -/
def rightGens : List (String × KoreAML.Gen) :=
  [("GeneratedTopCell", .ctor ⟨"Lbl'-LT-'generatedTop'-GT-'", ["KCell", "GeneratedCounterCell"], "GeneratedTopCell"⟩),
   ("KCell", .ctor ⟨"Lbl'-LT-'k'-GT-'", ["K"], "KCell"⟩),
   ("K", .ctor ⟨"kseq", ["KItem", "K"], "K"⟩),
   ("KItem", .inj "Exp"),
   ("Exp", .ctor ⟨"Lbldone", [], "Exp"⟩)]

/-- Γ has the Cons-Fun item of each (kernel). -/
theorem right_funs : TieRuleCutG.funsInGB c rightGens = true := by decide +kernel

/-- The right side's term is built of the text's variables and of those generators (kernel). -/
theorem right_built : TieRuleCutG.builtGB rightGens fT0 (cfg (ap "Lbldone" [])) "GeneratedTopCell" = true := by
  decide +kernel

theorem sorts_numbered : Srt.bool < nRegSorts + c.sortNames.length ∧ topCellSort < nRegSorts + c.sortNames.length ∧
    c.sortName Srt.bool = "Bool" ∧ c.sortName topCellSort = "GeneratedTopCell" := by decide +kernel

/-- **The premise `⌈R⌉` of `rule_w2_closed` holds in every model of Γ**, for every H: where the
guards of the text's variables hold, the right side holds one element, by the Cons-Fun items of its
generators, so `⌈R⌉` holds of every element of the top cell's sort, which the `requires` of the
text's left side (an `\equals` at that sort) keeps its elements in. -/
theorem right_defined (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT0, (guardOf (tableOf [] p0) k).interpret I e m) (a : M)
    (ha : (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a) :
    (tr ⟨tableOf [] p0, []⟩ ceilR).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have ha' : (tr ⟨tableOf [] p0, []⟩ (.and tC [cfg (ap "Lblgo" [xP]),
      .equals (srt "Bool") (srt "GeneratedTopCell") (.not (srt "Bool") gtX) (.dv (srt "Bool") "true")])).interpret I e a := ha
  have h1 := (interp_and (List.cons_ne_nil _ _)).mp ha' _ (List.mem_cons_of_mem _ List.mem_cons_self)
  exact TieRuleCutG.rightDefined_top hI sorts_numbered.2.1
    (show (cH H).sortName topCellSort = "GeneratedTopCell" from sorts_numbered.2.2.2)
    ((TieRuleCutG.funsInGB_withHooks c H rightGens).trans right_funs) right_built e m hg a
    (TieRuleCutG.equals_top hI sorts_numbered.1 (show (cH H).sortName Srt.bool = "Bool" from sorts_numbered.2.2.1)
      sorts_numbered.2.1 (show (cH H).sortName topCellSort = "GeneratedTopCell" from sorts_numbered.2.2.2) h1)

/-- **W2 for the rule, under `boolClosed`, without the premise `⌈R⌉`**: sentence 157 holds in
every model of Γ that satisfies `boolClosed`, for every H. -/
theorem rule_w2_closed_noprem (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hcl : I ⊧ᴵ boolClosed (cH H)) : I ⊧ᴵ (trS U.ax157).pat := by
  intro e m
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
  exact TieRuleLhs.lhs_entails hD free_sub hg e m fun hgs a ha =>
    left_sup H hD hc hSig hdist hcl _ e a ha (right_defined H hI e m hgs a ha)

/-! ## Sentence 157 at values, with no closure of Bool -/

/-- Γ's variable X. -/
def xX : Kore.EVar := KoreAML.evar "VarV0" (srt "Int")

/-- The sentence's variable `X` is free in it and has the index of Γ's variable at the argument of
`go`. -/
theorem x_index : KoreAML.VarKey.evar "VarX" (srt "Int") ∈ (freeOf [] U.ax157.ax.pattern).eraseDups ∧
    (tableOf U.ax157.ax.sortVars U.ax157.ax.pattern).ev (.evar "VarX" (srt "Int")) =
      (tableOf [] p0).ev (evarKey xX) := by decide +kernel

/-- `X >Int 0` as a library term over the one variable. -/
def gtT : Term := .app intGt [.var 0, .dv Srt.int (.int 0)]
def gtVars : LibEv.Vars := [("VarV0", Srt.int)]

theorem gt_kore_all : (fun H : HookParams => LibEv.kore (cH H) gtVars gtT) = fun _ => gtX := by kernel_rfl
theorem gt_srt (H : HookParams) : LibEv.srt? (cH H) gtVars gtT = some Srt.bool := by
  simp only [gtT, LibEv.srt?, LibEv.srts?, Semantics.sortOf_withHooks _ _ noRaw]
  decide +kernel
theorem gt_key (H : HookParams) : LibEv.vkey (cH H) gtVars 0 = evarKey xX := by
  show LibEv.vkey c gtVars 0 = _; decide +kernel
theorem shapesOK_c : c.shapesOK = true := by decide +kernel
theorem sortOf_false (H : HookParams) : (cH H).sortOf (KCore.bool false) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sortOf_true (H : HookParams) : (cH H).sortOf (KCore.bool true) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- The one sort named `Int` is the registry's. -/
theorem int_of_name (S : Srt) (h : srt (c.sortName S) = srt "Int") : S = Srt.int := by
  by_cases hS : S < nRegSorts + c.sortNames.length
  · exact (by decide +kernel : ∀ S ∈ List.range (nRegSorts + c.sortNames.length),
      srt (c.sortName S) = srt "Int" → S = Srt.int) S (List.mem_range.mpr hS) h
  · exfalso
    have hlt : ¬ S < nRegSorts := fun h' => hS (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
    have hge : c.sortNames.length ≤ S - nRegSorts :=
      Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.le_of_not_lt hS)
    have he : c.sortName S = "" := by
      unfold Semantics.sortName
      simp only [hlt, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
    rw [he] at h
    exact absurd h (by decide)

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **`X >Int 0` at a value of X holds nothing, or is `true`'s element, or is `false`'s**: a term
over the variable, a domain value and an interpreted symbol, of sort Bool, denotes the element of
its value or nothing (`LibEv.den_val`: the graph of `>Int` in `ΓDomains`), and a value of Bool is
`true` or `false`. -/
theorem gt_at_value (H : HookParams) (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) {v : GroundTerm}
    (hv : (cH H).sortOf v = some Srt.int)
    (hden : (den (cH H) v).interpret I e (e.evalEvar ((tableOf [] p0).ev (evarKey xX)))) :
    (∀ m, ¬ (tr ⟨tableOf [] p0, []⟩ gtX).interpret I e m) ∨
      ∃ b : Bool, ∀ m, (tr ⟨tableOf [] p0, []⟩ gtX).interpret I e m ↔ (den (cH H) (KCore.bool b)).interpret I e m := by
  obtain ⟨a0, ha0, -⟩ := den_single hI hv e
  have hlen : gtVars.length = 1 := rfl
  have hσ : ∀ i p, gtVars[i]? = some p → ∃ w, [(0, v)].lookup i = some w ∧ (cH H).sortOf w = some p.2 := by
    intro i p hp
    have hi : i < gtVars.length := (List.getElem?_eq_some_iff.mp hp).1
    rw [hlen] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    obtain rfl : ("VarV0", Srt.int) = p := Option.some.inj hp
    exact ⟨v, rfl, hv⟩
  have hag : ∀ i w, i < gtVars.length → [(0, v)].lookup i = some w →
      ∀ m, m = e.evalEvar ((tableOf [] p0).ev (LibEv.vkey (cH H) gtVars i)) ↔ (den (cH H) w).interpret I e m := by
    intro i w hi hw m
    rw [hlen] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    cases (show some v = some w from hw)
    rw [gt_key, ha0, (ha0 _).mp hden]
  obtain ⟨hval, hsrt⟩ := LibEv.den_val (coreOKH H) hI hσ hag gtT (gt_srt H)
  rw [congrFun gt_kore_all H] at hval
  cases hw : LibEv.val (cH H) [(0, v)] gtT with
  | none =>
    left; intro m h
    rw [hval, hw] at h; exact h
  | some w =>
    have hws := hsrt w hw
    rw [Semantics.sortOf_withHooks _ _ noRaw] at hws
    obtain ⟨b, rfl⟩ := shape_bool shapesOK_c hws
    exact Or.inr ⟨b, fun m => by rw [hval, hw]; rfl⟩

/-- **At a value of X, the text's left side with `⌈R⌉` is inside Γ's**, in every model of Γ, with
no closure of Bool. `X >Int 0` is `true`'s element, `false`'s, or holds nothing (`gt_at_value`).
The text's condition says `true` holds exactly the elements of Bool outside `X >Int 0`. Where
`X >Int 0` holds nothing, that set holds `false`'s element, which is not `true`'s. Where it is
`true`'s element, that set does not hold it. Where it is `false`'s, Γ's condition
`X >Int 0 = false` holds. -/
theorem left_sup_values (H : HookParams) (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M)
    (hat : AtValues (cH H) I e U.ax157.ax) (a : M)
    (h : (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a) (hR : (tr ⟨tableOf [] p0, []⟩ ceilR).interpret I e a) :
    (tr ⟨tableOf [] p0, []⟩ L0).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  have hSC : ∀ b, (trSort (tableOf [] p0) tC).interpret I e b ↔ b = σ := by unfold tC; rw [trSort_srt]; exact hσ1
  obtain ⟨σB, aF, aT, hSB, hσB, haf, haT, hne, hif, hit⟩ :=
    TieReqBool.boolTwo hD hSig hDom (sortOf_false H) (sortOf_true H) ((den_false H).trans (tr_dv ..))
      ((den_true H).trans (tr_dv ..)) (tableOf [] p0) e
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarX" (srt "Int") x_index.1
  rw [x_index.2] at hden
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  unfold Ltext0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have h1 := h (eqB (.not (srt "Bool") gtX) "true") (by simp)
  have h1' := h1
  rw [eqB_tr, interp_sEquals hD hc hSB hSC hσB hσ2] at h1'
  obtain ⟨ha, hn⟩ := h1'
  have hnot : ∀ b, Inh I σB b → ((tr ⟨tableOf [] p0, []⟩ (.not (srt "Bool") gtX)).interpret I e b ↔
      ¬ (tr ⟨tableOf [] p0, []⟩ gtX).interpret I e b) := by
    intro b hb
    rw [tr, interp_sNot]
    exact ⟨fun h => h.1, fun h => ⟨h, (interp_inhOf_of hSB).mpr hb⟩⟩
  have hcond : (tr ⟨tableOf [] p0, []⟩ (eqB gtX "false")).interpret I e a := by
    rw [eqB_tr, interp_sEquals hD hc hSB hSC hσB hσ2]
    refine ⟨ha, fun b hb => ?_⟩
    rcases gt_at_value H hI e hv hden with hemp | ⟨bb, hbb⟩
    · exact absurd ((haT aF).mp ((hn aF hif).mp ((hnot aF hif).mpr (hemp aF)))) hne
    · cases bb with
      | true =>
        have hg : (tr ⟨tableOf [] p0, []⟩ gtX).interpret I e aT := by
          rw [hbb aT, den_true H, tr_dv, ← tr_dv (t := tableOf [] p0)]; exact (haT aT).mpr rfl
        exact absurd hg ((hnot aT hit).mp ((hn aT hit).mpr ((haT aT).mpr rfl)))
      | false => rw [hbb b, den_false H, tr_dv, tr_dv]
  unfold L0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h _ (List.mem_cons_self ..)
  · exact top_of_cond H hD hc hSig _ e a h1
  · exact hcond
  · exact hR

end

/-- **Sentence 157 is entailed at values** (`EntailsAtValues`), for every H, with no closure of
Bool: at a value of X the text's left side is inside Γ's (`left_sup_values`, with `⌈R⌉` by
`right_defined`), and Γ's item gives the sentence. -/
theorem rule157_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax157 (trS U.ax157).pat := by
  intro M _ I hI e hat m
  have hD := defOK hI
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  rw [item_eq] at hg
  rw [trS157]
  exact TieRuleLhs.lhs_entails hD free_sub hg e m fun hgs a ha =>
    left_sup_values H hI e hat a ha (right_defined H hI e m hgs a ha)

/-! ## The premise `boolClosed` does not empty the statements -/


def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  (FnFacts.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)
    (show c.params.all (fun k => !k.raw) = true by decide +kernel)).obligations (openDecidedH H)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

theorem litSort_bool (H : HookParams) : (cH H).litSort Srt.bool = true :=
  (by decide +kernel : c.litSort Srt.bool = true)

open Faithful.Model in
/-- **Γ with the step's closure has a model that satisfies `boolClosed`, for every H**: the value
model at its own step, whose elements of Bool are the two literals' (`boolClosed_modelClT`). -/
theorem closed_model (H : HookParams) : ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γ (cH H) ∪ Γstep (cH H))) ∧ (I ⊧ᴵ boolClosed (cH H)) := by
  have h := coreOKH H
  have h' := Semantics.coreOK_iff_ex.mp h
  have hf := fnHypH H
  have hm : HypModelCore (cH H) := hypModel_of_fnHyp h hf
  exact ⟨_, inferInstance, _, stdI_V_model_coreEx hm
    (fun fn hfn cl hcl =>
      have hcp := (Semantics.sortedOKClEx_parts (Semantics.sortedOKClEx_of_sortedOKEx
        (Semantics.coreOKEx_parts h').1)).2.1 fn hfn cl hcl
      ⟨hcp.1, (Semantics.clausePlainOpenEx_parts hcp.2).1, (Semantics.clausePlainOpenEx_parts hcp.2).2.1⟩)
    (clausePreDecided_of_fnHyp h hf) (clausePostDecided_of_fnHypCEx h' hf) hf.2.2.2.2.2,
    boolClosed_modelClT hm (litSort_bool H)⟩


end KCore.TieE3MlReqNot157

#check @KCore.TieE3MlReqNot157.rule_text0
#check @KCore.TieE3MlReqNot157.boolDist_mem
#check @KCore.TieE3MlReqNot157.cond_iff
#check @KCore.TieE3MlReqNot157.left_sub
#check @KCore.TieE3MlReqNot157.left_sup
#check @KCore.TieE3MlReqNot157.rule_from_text_closed
#check @KCore.TieE3MlReqNot157.rule_w2_closed
#check @KCore.TieE3MlReqNot157.right_defined
#check @KCore.TieE3MlReqNot157.rule_w2_closed_noprem
#print axioms KCore.TieE3MlReqNot157.rule_text0
#print axioms KCore.TieE3MlReqNot157.boolDist_mem
#print axioms KCore.TieE3MlReqNot157.cond_iff
#print axioms KCore.TieE3MlReqNot157.rule_from_text_closed
#print axioms KCore.TieE3MlReqNot157.rule_w2_closed
#print axioms KCore.TieE3MlReqNot157.rule_w2_closed_noprem
#check @KCore.TieE3MlReqNot157.lit_sents
#check @KCore.TieE3MlReqNot157.ruleSigAux_text
#check @KCore.TieE3MlReqNot157.boolDist_from_text
#check @KCore.TieE3MlReqNot157.left_sup_values
#check @KCore.TieE3MlReqNot157.rule157_at_values
#check @KCore.TieE3MlReqNot157.closed_model
#print axioms KCore.TieE3MlReqNot157.lit_sents
#print axioms KCore.TieE3MlReqNot157.ruleSigAux_text
#print axioms KCore.TieE3MlReqNot157.boolDist_from_text
#print axioms KCore.TieE3MlReqNot157.rule157_at_values
#print axioms KCore.TieE3MlReqNot157.closed_model
