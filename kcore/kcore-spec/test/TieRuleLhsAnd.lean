/-
  `KoreAML.rule_and_pred` and `KoreAML.rule_and_as` at the three fixtures whose rule holds a
  conjunction at a term position of its left side under applications, each read by `Parse.parse`
  through `Parse.lhsAndCut` (`ReadingNote.lhsAndCut`). Run from the package root, after the
  library: `lake env lean -j1 test/TieRuleLhsAnd.lean`.

  - `Ceil` (e3-ml-rule-lhs-ceil-ctor, `go(X) #And #Ceil(go(X)) => done`, f2-examples/mllhsceil)
    and `Equals` (e3-ml-rule-lhs-equals, `go(X) #And {X #Equals 1} => done`,
    f2-examples/mllhseq): the rule with the position holding `go(X)` and `pre` the predicate
    (`ceil go(X)`, resp. `X = 1`), the rule the reader reads (`read`). `left_eq`: Γ's axiom of the
    rule, `prioRuleK c rz`, is `\rewrites(K[t] ∧ ⊤ ∧ P' ∧ ⌈R⌉, R)`, t the term at the position
    (`inj{Exp,KItem}(go(X))`), P' the predicate at the top cell's sort, R the right side.
    `left_text`, `left_tie`: the theorem's pattern `K[t ∧ P] ∧ ⊤`, P the predicate at KItem, is the
    left argument of the text's `\rewrites`. `tie`: `rule_and_pred`: `K[t] ∧ ⊤ ∧ P'` is
    `K[t ∧ P] ∧ ⊤`, the two predicates being one truth value at their sorts (`interp_sCeil`:
    go(X) has an element; `interp_sEquals`: X and 1 have the same elements of Int). `at_rule`:
    Γ's left side is the text's left side and `⌈R⌉`.
    The sentence (157 of each user module, `U.ax157`), for every H: Γ's axiom `p0` is
    `\rewrites(Lg, R)`, `Lg` := `K[t] ∧ ⊤ ∧ P' ∧ ⌈R⌉` (`p0_parts`), and the sentence is the item of
    `\rewrites(left, R)` at `p0`'s table (`rule_text0`, kernel). `left_iff`: `K[t] ∧ ⊤ ∧ P'` is `left`
    at that table in a model of the signature, at a valuation where every element of t is in KItem
    (and, `Ceil`, every element of go(X) in Exp): `and_pred_inTop`, `rule_and_pred`'s statement with
    the top cell's sort read from the `requires` `\top`; the sorts denote sorts by `ΓSig`
    (`TieRuleConnText.sort_sig`). `terms_in`: in a model of Γ, where X's guard holds, the
    inclusions hold (`condTerm_inh`: go's result sort from the signature, the injection's from its
    constructor item). `rule_w2` (W2): in a model of Γ the sentence holds where `⌈R⌉` holds wherever
    the text's left side holds (under the guards). `rule_from_text_in` (W1, under the inclusions):
    in a model of the sentence and `ΓSig` in which the inclusions hold under the guards, Γ's rule
    item holds. The inclusions are premises there: they are not derived from `ΓSig` here
    (`condTerm_inh` reads the injection's result sort from Γ's constructor item), and at an element
    of `inj{Exp,KItem}(go(X))` outside KItem, which is not one of `t ∧ P`, P a predicate at KItem,
    the sentence's left side is smaller than Γ's.
  - `Var` (e3-ml-rule-lhs-and, `c(X #And d(_, b())) => X`, f2-examples/mllhsandv): the rule with
    the position holding `d(G, b()) #as X` (`read`), whose pattern is `\and{Exp}(d(G, b()), X)`.
    `left_eq`: Γ's axiom is `\rewrites(K[d(G, b()) ∧ X] ∧ ⊤ ∧ ⌈R⌉, R)`. `left_text`, `left_tie`:
    `K[X ∧ d(G, b())] ∧ ⊤` is the left argument of the text's `\rewrites`. `tie`: `rule_and_as`:
    the two left sides have the same elements. `at_rule`: Γ's left side is the text's and `⌈R⌉`.
    The sentence (104 of the user module, `U.ax104`), for every H: it is the item of
    `\rewrites(left, R)` at the table of Γ's axiom `p0`, the indices of G and X exchanged
    (`rule_text0`, kernel). `rule_from_text` (W1): Γ's rule item is a consequence of the sentence
    alone. `rule_w2` (W2): in a model of Γ the sentence holds where `⌈R⌉`, the conjunct Γ's left
    side adds, holds wherever the text's left side holds (under the guards).
  - Γ's axiom and the text's sentence have the same right side and no variable of Γ's left side is
    bound beyond the rule's own, so Γ's axiom `∀x̄. (L' ∧ ⌈R⌉ → •R)` is the text's
    `∀x̄. (L → •R)` with the premise `⌈R⌉` every rule's axiom carries (`Var`: `rule_from_text`,
    `rule_w2`; `Ceil`, `Equals`: `rule_from_text_in`, `rule_w2`).
  - `right_defined`, `rule_w2_noprem` (each of the three): the premise `⌈R⌉` of `rule_w2` holds in
    every model of Γ where the guards hold (R is built of the text's variables, constructors and
    `inj{Exp,KItem}`, each with its Cons-Fun item in Γ: `TieRuleCutG.rightDefined_top`), so Γ
    entails the sentence, for every H.
  - `rule_from_text_aux` (`Ceil`, `Equals`; W1 from the text, without the inclusions as premises):
    Γ's rule item is a consequence of the sentence, `ΓSig` and one item of the text's signature that
    `ΓSig` does not hold, the arity item of the text's declaration `symbol inj{From, To}(From) : To`
    (`ruleSigAux`, `ruleSigAux_text`; `injArity_pat`: it is `TieFRSig.injArityP`). `terms_in_inj`:
    in a model of definedness, `ΓSig` and that item, where X's guard holds, every term lies in its
    sort (`TieFRSig.sig_of_core_inj`): go's arity (`ΓSig`) puts the elements of `go(X)` in Exp, and
    the arity of `inj` at Exp, KItem puts those of `inj{Exp,KItem}(go(X))` in KItem. `ΓSig` holds no
    item for `inj`; the text's signature does. The text's subsort sentence of Exp, KItem is not a
    premise: it equates `inj{Exp,KItem}(x)` with an element at the sort KItem, and an equation at
    KItem says nothing of an element outside KItem, so it does not give the inclusion alone.
  - The theorems hold at any table and leave as premises what `rule_and_pred` lists of the table
    and the interpretation: definedness, the sorts' patterns, every element of t in KItem, every
    element of `K[t]` in the top cell's sort, and (Ceil) every element of go(X) in Exp. The
    statements on the sentences (`rule_text0`, `left_iff`, `rule_from_text`, `rule_from_text_in`,
    `rule_w2`) are at the table of Γ's axiom.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

deriving instance DecidableEq for KoreAML.SymbolDecl

open KCore KCore.Faithful KoreAML ML

namespace TieRuleLhsAnd

def topC : Kore.KSort := srt "GeneratedTopCell"
def kitemS : Kore.KSort := srt "KItem"

/-- The context of the `k` cell's first item: `<generatedTop>(<k>(kseq(·, k)), counter)`. -/
def itemCtx (inner : KoreCutCtx) (k counter : Kore.Pattern) : KoreCutCtx :=
  .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] [] (.app ⟨⟨"kseq"⟩⟩ [] [] inner [k]) []) [counter]

/-- The `\rewrites` axiom at the place i of the text's last module: its left and right arguments. -/
def rewritesAt (k : Kore.Definition) (i : Nat) : Option (Kore.Pattern × Kore.Pattern) :=
  match k.modules.getLast?.bind (·.sentences[i]?) with
  | some (.axiom a) => match a.pattern with
    | .rewrites _ l r => some (l, r)
    | _ => none
  | _ => none

/-- `∧` of three is `∧` of the first two and the third. -/
theorem and3_iff {M : Type} {I : Interpretation KoreAML.Sym M} (ctx : Ctx) (C : Kore.KSort)
    (x y d : Kore.Pattern) (e : Valuation M) (m : M) :
    (tr ctx (.and C [x, y, d])).interpret I e m ↔
      (tr ctx (.and C [x, y])).interpret I e m ∧ (tr ctx d).interpret I e m := by
  simp only [tr, trAndList, interp_sAnd, and_assoc]

/-- `∧` of four is `∧` of the first three and the fourth. -/
theorem and4_iff {M : Type} {I : Interpretation KoreAML.Sym M} (ctx : Ctx) (C : Kore.KSort)
    (x y q d : Kore.Pattern) (e : Valuation M) (m : M) :
    (tr ctx (.and C [x, y, q, d])).interpret I e m ↔
      (tr ctx (.and C [x, y, q])).interpret I e m ∧ (tr ctx d).interpret I e m := by
  simp only [tr, trAndList, interp_sAnd, and_assoc]

/-- `K[t] ∧ E ∧ P'` is `K[t ∧ P] ∧ E` where `K[t ∧ P]` is `K[t] ∧ P'`. -/
theorem and_pred_reassoc {M : Type} {I : Interpretation KoreAML.Sym M} (ctx : Ctx) (C S : Kore.KSort)
    (K : KoreCutCtx) (t P P' E : Kore.Pattern) (e : Valuation M) (m : M)
    (h : (tr ctx (K.fill (.and S [t, P]))).interpret I e m ↔ (tr ctx (.and C [K.fill t, P'])).interpret I e m) :
    (tr ctx (.and C [K.fill t, E, P'])).interpret I e m ↔
      (tr ctx (.and C [K.fill (.and S [t, P]), E])).interpret I e m := by
  have e1 : tr ctx (.and C [K.fill t, E, P']) = sAnd (tr ctx (K.fill t)) (sAnd (tr ctx E) (tr ctx P')) := rfl
  have e2 : tr ctx (.and C [K.fill (.and S [t, P]), E]) = sAnd (tr ctx (K.fill (.and S [t, P]))) (tr ctx E) := rfl
  have e3 : tr ctx (.and C [K.fill t, P']) = sAnd (tr ctx (K.fill t)) (tr ctx P') := rfl
  rw [e3, interp_sAnd] at h
  rw [e1, e2, interp_sAnd, interp_sAnd, interp_sAnd, h]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨h1, h2, h3⟩⟩

/-- **A predicate conjoined at a position under applications, the outer sort read from E**:
`K[t] ∧ E ∧ P'` is `K[t ∧ P] ∧ E`, where P is p at every element of the sort σ and P' is p at every
element of the sort σ', every element of t is in σ and every element of E is in σ'. -/
theorem and_pred_inTop {M : Type} {I : Interpretation KoreAML.Sym M} (ctx : Ctx) (K : KoreCutCtx)
    (hK : K.noAlias ctx = true) (S C : Kore.KSort) (t P P' E : Kore.Pattern) (e : Valuation M) {σ σ' : M}
    (p : Prop)
    (hP : ∀ a, Inh I σ a → ((tr ctx P).interpret I e a ↔ p))
    (hP' : ∀ m, Inh I σ' m → ((tr ctx P').interpret I e m ↔ p))
    (hin : ∀ a, (tr ctx t).interpret I e a → Inh I σ a)
    (hEin : ∀ m, (tr ctx E).interpret I e m → Inh I σ' m) (m : M) :
    (tr ctx (.and C [K.fill t, E, P'])).interpret I e m ↔
      (tr ctx (.and C [K.fill (.and S [t, P]), E])).interpret I e m := by
  have e1 : tr ctx (.and C [K.fill t, E, P']) = sAnd (tr ctx (K.fill t)) (sAnd (tr ctx E) (tr ctx P')) := rfl
  have e2 : tr ctx (.and C [K.fill (.and S [t, P]), E]) = sAnd (tr ctx (K.fill (.and S [t, P]))) (tr ctx E) := rfl
  have hl : tr ctx (.and S [t, P]) = sAnd (tr ctx t) (tr ctx P) := by simp only [tr, trAndList]
  rw [e1, e2, interp_sAnd, interp_sAnd, interp_sAnd, tr_cutCtx ctx (.and S [t, P]) K hK, hl,
    cutCtx_fill_and_pred (fun a ha => hP a (hin a ha)) (K.toCut ctx) m, ← tr_cutCtx ctx t K hK]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, (hP' m (hEin m h2)).mp h3⟩, h2⟩,
    fun ⟨⟨h1, hp⟩, h2⟩ => ⟨h1, h2, (hP' m (hEin m h2)).mpr hp⟩⟩

namespace Ceil

kore_term kore from "f2-examples/mllhsceil.kompile.kore"
definition_of defn from "f2-examples/mllhsceil.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

example : c.sortName 32 = "Exp" ∧ c.sortName 0 = "K" ∧ c.sortName 19 = "GeneratedCounterCell" ∧
    c.symName 385 = "Lbldone" ∧ c.symName 386 = "Lblgo" := by decide +kernel

def cfg (x : Term) : Term := .app 71 [.app 383 [.app 0 [.inj 32 1 x, .var 1]], .var 2]

/-- `go(X) => done` with `pre := ceil go(X)`, X:Int the first variable. -/
def rz : Rule :=
  { vars := [Srt.int, 0, 19], lhs := cfg (.app 386 [.var 0]), req := none, rhs := cfg (.app 385 []),
    ens := none, prio := 50, pre := .ceil 32 (.app 386 [.var 0]) }

/-- The reader reads the text's rule as `rz` (`Parse.parse`, through `lhsAndCut`). -/
theorem read : c.rules = [rz] := rfl

def goX : Kore.Pattern := ap "Lblgo" [ev "VarV0" (srt "Int")]
/-- The term at the position. -/
def t : Kore.Pattern := injP "Exp" "KItem" goX
/-- The predicate as the text writes it, at KItem. -/
def P : Kore.Pattern := .ceil (srt "Exp") kitemS goX
/-- The predicate as `pre` writes it, at the top cell's sort. -/
def P' : Kore.Pattern := .ceil (srt "Exp") topC goX
def E : Kore.Pattern := .top topC
def K : KoreCutCtx := itemCtx .hole (ev "VarV1" (srt "K")) (ev "VarV2" (srt "GeneratedCounterCell"))
/-- The rule's right side, `<k> done </k>`. -/
def R : Kore.Pattern := .and topC [K.fill (injP "Exp" "KItem" (ap "Lbldone" [])), E]

/-- The theorem's right pattern: the left side with the conjunction in its position. -/
def left : Kore.Pattern := .and topC [K.fill (.and kitemS [t, P]), E]

theorem right_eq : ruleRight c rz = R := by decide +kernel

/-- Γ's axiom of the rule: `\rewrites(K[t] ∧ ⊤ ∧ P' ∧ ⌈R⌉, R)`. -/
theorem left_eq : prioRuleK c rz = .rewrites topC (.and topC [K.fill t, E, P', .ceil topC topC R]) R := by
  decide +kernel

/-- The text's spelling of the canonical names of the rule's variables. -/
def spell (n : String) (_ : Kore.KSort) : String :=
  if n == "VarV0" then "VarX" else if n == "VarV1" then "Var'Unds'DotVar1"
  else if n == "VarV2" then "Var'Unds'DotVar0" else n

theorem left_text : some (renVars spell (fun n _ => n) left) = (rewritesAt kore 295).map (·.1) := by
  decide +kernel

theorem left_tie (l : Kore.Pattern) (h : (rewritesAt kore 295).map (·.1) = some l) :
    tr ⟨tableOf [] l, []⟩ l = tr ⟨tableOf [] left, []⟩ left := by
  have hl : l = renVars spell (fun n _ => n) left := by
    have := left_text; rw [h] at this; exact (Option.some.inj this).symm
  rw [hl]
  exact tr_occurrence_order spell (fun n _ => n) [] [] left (by decide +kernel)

/-- **`rule_and_pred` at the fixture's left side**: `K[t] ∧ ⊤ ∧ ⌈go(X)⌉` is the text's left side
`K[t ∧ ⌈go(X)⌉] ∧ ⊤`, under the theorem's premises at a table without aliases. -/
theorem tie {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (tbl : VarTable) (e : Valuation M) {σx σk σ' : M}
    (hX : ∀ a, (trSort tbl (srt "Exp")).interpret I e a ↔ a = σx)
    (hK : ∀ a, (trSort tbl kitemS).interpret I e a ↔ a = σk)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσx : IsSort I σx) (hσk : IsSort I σk) (hσ' : IsSort I σ')
    (hgo : ∀ a, (tr ⟨tbl, []⟩ goX).interpret I e a → Inh I σx a)
    (hin : ∀ a, (tr ⟨tbl, []⟩ t).interpret I e a → Inh I σk a)
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill t)).interpret I e m → Inh I σ' m) (m : M) :
    (tr ⟨tbl, []⟩ (.and topC [K.fill t, E, P'])).interpret I e m ↔
      (tr ⟨tbl, []⟩ left).interpret I e m := by
  have hP : ∀ a, Inh I σk a → ((tr ⟨tbl, []⟩ P).interpret I e a ↔ ∃ b, (tr ⟨tbl, []⟩ goX).interpret I e b) :=
    fun a ha => by
      show (sCeil (trSort tbl (srt "Exp")) (trSort tbl kitemS) (tr ⟨tbl, []⟩ goX)).interpret I e a ↔ _
      rw [interp_sCeil hD hc hX hK hσx hσk hgo a]
      exact ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩
  have hP' : ∀ m, Inh I σ' m → ((tr ⟨tbl, []⟩ P').interpret I e m ↔ ∃ b, (tr ⟨tbl, []⟩ goX).interpret I e b) :=
    fun m hm => by
      show (sCeil (trSort tbl (srt "Exp")) (trSort tbl topC) (tr ⟨tbl, []⟩ goX)).interpret I e m ↔ _
      rw [interp_sCeil hD hc hX hC hσx hσ' hgo m]
      exact ⟨fun h => h.1, fun h => ⟨h, hm⟩⟩
  exact and_pred_reassoc ⟨tbl, []⟩ topC kitemS K t P P' E e m
    (rule_and_pred ⟨tbl, []⟩ K rfl kitemS topC t P P' e _ hP hP' hin hout m)

/-- **Γ's left side is the text's left side with `⌈R⌉`**. -/
theorem at_rule {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (tbl : VarTable) (e : Valuation M) {σx σk σ' : M}
    (hX : ∀ a, (trSort tbl (srt "Exp")).interpret I e a ↔ a = σx)
    (hK : ∀ a, (trSort tbl kitemS).interpret I e a ↔ a = σk)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσx : IsSort I σx) (hσk : IsSort I σk) (hσ' : IsSort I σ')
    (hgo : ∀ a, (tr ⟨tbl, []⟩ goX).interpret I e a → Inh I σx a)
    (hin : ∀ a, (tr ⟨tbl, []⟩ t).interpret I e a → Inh I σk a)
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill t)).interpret I e m → Inh I σ' m) (m : M) :
    (tr ⟨tbl, []⟩ (.and topC [K.fill t, E, P', .ceil topC topC R])).interpret I e m ↔
      (tr ⟨tbl, []⟩ left).interpret I e m ∧ (tr ⟨tbl, []⟩ (.ceil topC topC R)).interpret I e m := by
  rw [and4_iff, tie hD hc tbl e hX hK hC hσx hσk hσ' hgo hin hout m]

/-! ## The rule's sentence (157), for every H: W1 under the term's sort, and W2 -/

user_axioms U from "f2-examples/mllhsceil.kompile.kore" module "E3-ML-RULE-LHS-CEIL-CTOR"

noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c rz

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

/-- Γ's left side: `K[t] ∧ ⊤ ∧ P' ∧ ⌈R⌉`. -/
def Lg : Kore.Pattern := .and topC [K.fill t, E, P', .ceil topC topC R]

theorem p0_parts : TieRuleLhs.rwParts p0 = some (topC, Lg, R) := by decide +kernel

/-- The free variables of the text's form. -/
def fT : List VarKey := (freeOf [] (.rewrites topC left R)).eraseDups

/-- **The text's sentence 157 is the item of `\rewrites{C}(left, R)` at the table of Γ's axiom**
(kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT topC left R) [] =
    some (trS U.ax157).pat := by
  decide +kernel
theorem fT_free0 : fT.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem free_sub0 : ∀ k ∈ (freeOf [] p0).eraseDups, k ∈ fT := by decide +kernel
theorem x_free0 : VarKey.evar "VarV0" (srt "Int") ∈ fT := by decide +kernel

/-- The terms as the reading's terms: `go(X)` and `inj{Exp,KItem}(go(X))` over the rule's variables. -/
theorem terms_kore : Term.kore c (canonVars c rz.vars) (.app 386 [.var 0]) = goX ∧
    Term.kore c (canonVars c rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0])) = t ∧
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) rz.vars (.app 386 [.var 0]) = some 32 ∧
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) rz.vars (.inj 32 Srt.kitem (.app 386 [.var 0])) = some Srt.kitem ∧
    canonKey c rz.vars 0 = .evar "VarV0" (srt "Int") := by
  decide +kernel

/-- The two terms' patterns do not read the interpretation of the hooks. -/
theorem terms_koreF :
    (fun H : HookParams => (Term.kore (c.withHooks H) (canonVars (c.withHooks H) rz.vars) (.app 386 [.var 0]),
      Term.kore (c.withHooks H) (canonVars (c.withHooks H) rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0])))) =
    fun _ => (Term.kore c (canonVars c rz.vars) (.app 386 [.var 0]),
      Term.kore c (canonVars c rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0]))) := by
  kernel_rfl

theorem terms_koreH (H : HookParams) :
    Term.kore (cH H) (canonVars (cH H) rz.vars) (.app 386 [.var 0]) =
      Term.kore c (canonVars c rz.vars) (.app 386 [.var 0]) ∧
    Term.kore (cH H) (canonVars (cH H) rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0])) =
      Term.kore c (canonVars c rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0])) :=
  ⟨congrArg Prod.fst (congrFun terms_koreF H), congrArg Prod.snd (congrFun terms_koreF H)⟩

/-- **Γ's left side without `⌈R⌉` is the text's left side**, at the table of Γ's axiom, in a model
of the signature, at a valuation where every element of `go(X)` is in Exp and every element of the
term at the position in KItem: `and_pred_inTop`, the outer sort read from the `requires` `\top`. -/
theorem left_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (e : Valuation M)
    (hgo : ∀ a, (tr ⟨tableOf [] p0, []⟩ goX).interpret I e a →
      (inhOf (trSort (tableOf [] p0) (srt "Exp"))).interpret I e a)
    (hin : ∀ a, (tr ⟨tableOf [] p0, []⟩ t).interpret I e a →
      (inhOf (trSort (tableOf [] p0) kitemS)).interpret I e a) (m : M) :
    (tr ⟨tableOf [] p0, []⟩ (.and topC [K.fill t, E, P'])).interpret I e m ↔
      (tr ⟨tableOf [] p0, []⟩ left).interpret I e m := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  obtain ⟨σx, hσx, hX, -⟩ := TieRuleConnText.sort_sig hD hSig (s := 32)
    (by decide +kernel : (32 : Srt) < nRegSorts + c.sortNames.length)
    (show (cH H).sortName 32 = "Exp" from (by decide +kernel : c.sortName 32 = "Exp"))
  obtain ⟨σk, hσk, hK, -⟩ := TieRuleConnText.sort_sig hD hSig (s := Srt.kitem)
    (by decide +kernel : Srt.kitem < nRegSorts + c.sortNames.length)
    (show (cH H).sortName Srt.kitem = "KItem" from (by decide +kernel : c.sortName Srt.kitem = "KItem"))
  obtain ⟨σ', hσ', hC, -⟩ := TieRuleConnText.sort_sig hD hSig (s := topCellSort)
    (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
    (show (cH H).sortName topCellSort = "GeneratedTopCell" from
      (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell"))
  have hK' : ∀ a, (trSort (tableOf [] p0) kitemS).interpret I e a ↔ a = σk := hK _ e
  have hC' : ∀ a, (trSort (tableOf [] p0) topC).interpret I e a ↔ a = σ' := hC _ e
  have hgo' : ∀ a, (tr ⟨tableOf [] p0, []⟩ goX).interpret I e a → Inh I σx a :=
    fun a ha => (interp_inhOf_of (hX _ e)).mp (hgo a ha)
  have hin' : ∀ a, (tr ⟨tableOf [] p0, []⟩ t).interpret I e a → Inh I σk a :=
    fun a ha => (interp_inhOf_of (hK _ e)).mp (hin a ha)
  have hP : ∀ a, Inh I σk a → ((tr ⟨tableOf [] p0, []⟩ P).interpret I e a ↔
      ∃ b, (tr ⟨tableOf [] p0, []⟩ goX).interpret I e b) :=
    fun a ha => by
      show (sCeil (trSort (tableOf [] p0) (srt "Exp")) (trSort (tableOf [] p0) kitemS)
        (tr ⟨tableOf [] p0, []⟩ goX)).interpret I e a ↔ _
      rw [interp_sCeil hD hc (hX _ e) hK' hσx hσk hgo' a]
      exact ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩
  have hP' : ∀ m, Inh I σ' m → ((tr ⟨tableOf [] p0, []⟩ P').interpret I e m ↔
      ∃ b, (tr ⟨tableOf [] p0, []⟩ goX).interpret I e b) :=
    fun m hm => by
      show (sCeil (trSort (tableOf [] p0) (srt "Exp")) (trSort (tableOf [] p0) topC)
        (tr ⟨tableOf [] p0, []⟩ goX)).interpret I e m ↔ _
      rw [interp_sCeil hD hc (hX _ e) hC' hσx hσ' hgo' m]
      exact ⟨fun h => h.1, fun h => ⟨h, hm⟩⟩
  exact and_pred_inTop ⟨tableOf [] p0, []⟩ K rfl kitemS topC t P P' E e _ hP hP' hin'
    (fun m hm => TieRuleConnText.top_inh hD (hC _ e) m hm) m

/-- **In a model of Γ, where X's guard holds**, every element of `go(X)` is in Exp and every element
of `inj{Exp,KItem}(go(X))` in KItem (`condTerm_inh`: the symbols' result sorts, from Γ's items of
the signature and of the constructors). -/
theorem terms_in (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (e : Valuation M) (m : M) (hg : ∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) :
    (∀ a, (tr ⟨tableOf [] p0, []⟩ goX).interpret I e a →
      (inhOf (trSort (tableOf [] p0) (srt "Exp"))).interpret I e a) ∧
    (∀ a, (tr ⟨tableOf [] p0, []⟩ t).interpret I e a →
      (inhOf (trSort (tableOf [] p0) kitemS)).interpret I e a) := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hgw : genWf (cH H) = true := (faithCoreOK_parts (Semantics.coreOK_parts (coreOKH H)).2.1).2.1
  obtain ⟨hk1, hk2, hs1, hs2, hkey⟩ := terms_kore
  have hx := hg _ x_free0
  rw [interp_guard_evar hD, trSort_srt] at hx
  have hvars : ∀ i ∈ varOccs (.app 386 [.var 0]),
      InS I ((cH H).sortName (rz.vars.getD i 0)) (e.evalEvar ((tableOf [] p0).ev (canonKey (cH H) rz.vars i))) := by
    intro i hi
    have : i = 0 := by simpa [varOccs, varOccsList] using hi
    subst this
    show InS I (c.sortName (rz.vars.getD 0 0)) (e.evalEvar ((tableOf [] p0).ev (canonKey c rz.vars 0)))
    rw [hkey]
    exact (inS_iff e).mp hx
  obtain ⟨τx, -, hτx⟩ := srt_den hI (s := 32) (by decide +kernel : (32 : Srt) < nRegSorts + c.sortNames.length)
  obtain ⟨τk, -, hτk⟩ := srt_den hI (s := Srt.kitem)
    (by decide +kernel : Srt.kitem < nRegSorts + c.sortNames.length)
  have h1 := condTerm_inh hI hgw (tbl := tableOf [] p0) (e := e) hτx
    (show sortOfTerm ((cH H).rhsCtx ((cH H).fns.map Fn.sig)) rz.vars (.app 386 [.var 0]) = some 32 from hs1) hvars
  have h2 := condTerm_inh hI hgw (tbl := tableOf [] p0) (e := e) hτk
    (show sortOfTerm ((cH H).rhsCtx ((cH H).fns.map Fn.sig)) rz.vars (.inj 32 Srt.kitem (.app 386 [.var 0])) =
      some Srt.kitem from hs2)
    (fun i hi => hvars i (by simpa [varOccs, varOccsList] using hi))
  rw [(terms_koreH H).1, hk1] at h1
  rw [(terms_koreH H).2, hk2] at h2
  exact ⟨fun a ha => (interp_inhOf_of (hτx _ e)).mpr (h1 a ha), fun a ha => (interp_inhOf_of (hτk _ e)).mpr (h2 a ha)⟩

/-- **W1 for the rule, under the term's sort**: in a model of sentence 157 and the signature in
which, where the guards hold, every element of `go(X)` is in Exp and every element of the term at
the position in KItem, Γ's rule item holds, for every H. (The two inclusions hold in every model of
Γ, `terms_in`; they are not derived from the signature alone here.) -/
theorem rule_from_text_in (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP (TiePair.Texts [(trS U.ax157).pat] ∪ ΓSig (cH H)))
    (hT : ∀ (e : Valuation M) (m : M),
      (∀ k ∈ (freeOf [] p0).eraseDups, (guardOf (tableOf [] p0) k).interpret I e m) →
        (∀ a, (tr ⟨tableOf [] p0, []⟩ goX).interpret I e a →
          (inhOf (trSort (tableOf [] p0) (srt "Exp"))).interpret I e a) ∧
        (∀ a, (tr ⟨tableOf [] p0, []⟩ t).interpret I e a →
          (inhOf (trSort (tableOf [] p0) kitemS)).interpret I e a)) :
    ∀ it ∈ ruleItems (cH H), I ⊧ᴵ it.pat := by
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  rw [List.mem_singleton.mp hit]
  exact TieRuleConnText.rule_w1_sides hD p0_parts rule_text0 fT_free0
    (hI _ (Or.inl (Or.inl (List.mem_singleton_self _))))
    (fun e m hg x hx => (left_iff H hD hSig e (hT e m hg).1 (hT e m hg).2 x).mp ((and4_iff _ _ _ _ _ _ _ _).mp hx).1)
    (fun e m _ x hx => hx)

/-- **W2 for the rule, with the guard**: in a model of Γ, sentence 157 holds where, at each
valuation at which the guards of its variables hold, `⌈R⌉` (the conjunct Γ's left side adds) holds
wherever the text's left side holds, for every H. -/
theorem rule_w2 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (hR : ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) →
      ∀ x, (tr ⟨tableOf [] p0, []⟩ left).interpret I e x →
        (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).interpret I e x) :
    I ⊧ᴵ (trS U.ax157).pat := by
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  exact TieRuleConnText.rule_w2_sides hD p0_parts rule_text0 free_sub0 hg
    (fun e m hgs x hx => (and4_iff _ _ _ _ _ _ _ _).mpr
      ⟨(left_iff H hD hSig e (terms_in H hI e m hgs).1 (terms_in H hI e m hgs).2 x).mpr hx, hR e m hgs x hx⟩)
    (fun e m _ x hx => hx)

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

/-- The right side's term is built of the text's variables and of those generators, at arguments
of their sorts (kernel). -/
theorem right_built : TieRuleCutG.builtGB rightGens fT (K.fill (injP "Exp" "KItem" (ap "Lbldone" []))) "GeneratedTopCell" = true := by
  decide +kernel

/-- **The premise of `rule_w2` holds in every model of Γ**, for every H: where the guards of the
text's variables hold, the right side holds one element, by the Cons-Fun items of its generators,
so `⌈R⌉` holds of every element of the top cell's sort, which the `\top` of the text's left side
keeps its elements in. -/
theorem right_defined (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) (a : M)
    (ha : (tr ⟨tableOf [] p0, []⟩ left).interpret I e a) :
    (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have ha' : (tr ⟨tableOf [] p0, []⟩ (.and topC [K.fill (.and kitemS [t, P]), E])).interpret I e a := ha
  exact TieRuleCutG.rightDefined_top hI
    (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
    (show (cH H).sortName topCellSort = "GeneratedTopCell" from
      (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell"))
    ((TieRuleCutG.funsInGB_withHooks c H rightGens).trans right_funs) right_built e m hg a
    ((interp_and (List.cons_ne_nil _ _)).mp ha' E (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **W2 for the rule, without a premise**: sentence 157 holds in every model of Γ, for every H
(`rule_w2` with `right_defined`). -/
theorem rule_w2_noprem (H : HookParams) : Γ (cH H) ⊧ (trS U.ax157).pat :=
  fun {_} _ {_} hI => rule_w2 H hI (right_defined H hI)

/-- go's signature, Int to Exp. -/
def kgo : KCore.CtorSig := ⟨386, [Srt.int], 32⟩
theorem kgo_mem (H : HookParams) : kgo ∈ kernelSyms (cH H) := (by decide +kernel : kgo ∈ kernelSyms c)
/-- go's arity item: go of elements of Int holds elements of Exp only. -/
theorem kgo_arity_c : (symArityItem c kgo).pat =
    (sym (.symbol "Lblgo") ⬝ inhOf (sortP "Int") ⊆⊆ inhOf (sortP "Exp")) := by decide +kernel
kernel_rfl kgo_arity_withHooks : ∀ H : HookParams, (symArityItem (c.withHooks H) kgo).pat = (symArityItem c kgo).pat
theorem kgo_arity (H : HookParams) : (symArityItem (cH H) kgo).pat =
    (sym (.symbol "Lblgo") ⬝ inhOf (sortP "Int") ⊆⊆ inhOf (sortP "Exp")) :=
  (kgo_arity_withHooks H).trans kgo_arity_c

/-- The text's declaration `symbol inj{From, To}(From) : To [sortInjection{}()]`. -/
def injDecl : SymbolDecl :=
  ⟨"inj", [⟨⟨⟨"From"⟩⟩⟩, ⟨⟨⟨"To"⟩⟩⟩], [.var ⟨⟨⟨"From"⟩⟩⟩], .var ⟨⟨⟨"To"⟩⟩⟩, false, ["sortInjection"]⟩

theorem injDecl_mem : injDecl ∈ kore.symbolDecls := by decide +kernel

/-- Its arity item is `TieFRSig.injArityP`: at two sorts, what `inj` builds of an element of the
first lies in the second. -/
theorem injArity_pat : (arityItem injDecl).pat = TieFRSig.injArityP := TieFRSig.injArityP_shape _ _

/-- The rule sentence. -/
noncomputable def ruleText : List AxiomDecl := [U.ax157]

/-- The other sentences of the text the statement reads: none. -/
noncomputable def ruleAux : List AxiomDecl := []

/-- The item of the text's signature the statement reads, which `ΓSig` does not hold: the arity
item of the declaration of `inj`. -/
def ruleSigAux : List Item := [arityItem injDecl]

/-- Each item of `ruleSigAux` is an item of the signature of the text's theory. -/
theorem ruleSigAux_text : ∀ it ∈ ruleSigAux, it ∈ (Theory.ofDefinition kore).signature := by
  intro it hit
  rw [List.mem_singleton.mp hit]
  simp only [Theory.ofDefinition, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨_, injDecl_mem, rfl⟩)))

/-- **In a model of definedness, the signature and `inj`'s arity item, where X's guard holds**,
every element of `go(X)` is in Exp and every element of `inj{Exp,KItem}(go(X))` in KItem: each term
lies in its sort (`TieFRSig.sig_of_core_inj`: go's result sort from its arity item in `ΓSig`, the
injection's target sort from `inj`'s arity item at the subsort pair Exp, KItem). -/
theorem terms_in_inj (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (hA : I ⊧ᴵ TieFRSig.injArityP) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ (freeOf [] p0).eraseDups, (guardOf (tableOf [] p0) k).interpret I e m) :
    (∀ a, (tr ⟨tableOf [] p0, []⟩ goX).interpret I e a →
      (inhOf (trSort (tableOf [] p0) (srt "Exp"))).interpret I e a) ∧
    (∀ a, (tr ⟨tableOf [] p0, []⟩ t).interpret I e a →
      (inhOf (trSort (tableOf [] p0) kitemS)).interpret I e a) := by
  have hT : TermsInSort (cH H) I := (TieFRSig.sig_of_core_inj (coreOKH H) hD hSig hA).2
  obtain ⟨hk1, hk2, hs1, hs2, hkey⟩ := terms_kore
  have hx := hg _ (List.contains_iff_mem.mp (List.all_eq_true.mp fT_free0 _ x_free0))
  rw [interp_guard_evar hD, trSort_srt] at hx
  have hvars : ∀ i ∈ varOccs (.inj 32 Srt.kitem (.app 386 [.var 0])),
      InS I ((cH H).sortName (rz.vars.getD i 0)) (e.evalEvar ((tableOf [] p0).ev (canonKey (cH H) rz.vars i))) := by
    intro i hi
    have : i = 0 := by simpa [varOccs, varOccsList] using hi
    subst this
    show InS I (c.sortName (rz.vars.getD 0 0)) (e.evalEvar ((tableOf [] p0).ev (canonKey c rz.vars 0)))
    rw [hkey]
    exact (inS_iff e).mp hx
  have h1 : ∀ a, (tr ⟨tableOf [] p0, []⟩ (Term.kore (cH H) (canonVars (cH H) rz.vars) (.app 386 [.var 0]))).interpret I e a →
      InS I ((cH H).sortName 32) a :=
    hT (show sortOfTerm ((cH H).rhsCtx ((cH H).fns.map Fn.sig)) rz.vars (.app 386 [.var 0]) = some 32 from hs1)
      (by decide +kernel : (32 : Srt) < nRegSorts + c.sortNames.length)
      (fun i hi => hvars i (by simpa [varOccs, varOccsList] using hi))
  have h2 : ∀ a, (tr ⟨tableOf [] p0, []⟩
      (Term.kore (cH H) (canonVars (cH H) rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0])))).interpret I e a →
      InS I ((cH H).sortName Srt.kitem) a :=
    hT (show sortOfTerm ((cH H).rhsCtx ((cH H).fns.map Fn.sig)) rz.vars (.inj 32 Srt.kitem (.app 386 [.var 0])) =
      some Srt.kitem from hs2)
      (by decide +kernel : Srt.kitem < nRegSorts + c.sortNames.length) hvars
  rw [(terms_koreH H).1, hk1, show (cH H).sortName 32 = "Exp" from (by decide +kernel : c.sortName 32 = "Exp")] at h1
  rw [(terms_koreH H).2, hk2, show (cH H).sortName Srt.kitem = "KItem" from
    (by decide +kernel : c.sortName Srt.kitem = "KItem")] at h2
  exact ⟨fun a ha => by rw [trSort_srt]; exact (inS_iff e).mpr (h1 a ha),
    fun a ha => by rw [kitemS, trSort_srt]; exact (inS_iff e).mpr (h2 a ha)⟩

/-- **W1 for the rule, from the text**: Γ's one rule item is a consequence of sentence 157 with the
arity item of the text's declaration of `inj` (`ruleSigAux`, an item of the text's signature that
`ΓSig` does not hold) and `ΓSig`, for every H. The arity item puts every element of
`inj{Exp,KItem}(go(X))` in KItem (`terms_in_inj`); the text's subsort sentence of Exp, KItem is not
read (it equates the injection with an element at KItem only). -/
theorem rule_from_text_aux (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText,
    TiePair.Texts ((trS ad).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  refine ⟨U.ax157, List.mem_singleton_self _, ?_⟩
  intro M _ I hI
  have hT : I ⊧ᴵP (TiePair.Texts [(trS U.ax157).pat] ∪ ΓSig (cH H)) := by
    intro φ hφ
    rcases hφ with (hm | hd) | hs
    · exact hI φ (Or.inl (Or.inl (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hm)))))
    · exact hI φ (Or.inl (Or.inr hd))
    · exact hI φ (Or.inr hs)
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hA : I ⊧ᴵ TieFRSig.injArityP := by
    rw [← injArity_pat]
    exact hI _ (Or.inl (Or.inl (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  exact rule_from_text_in H hT (fun e m hg => terms_in_inj H hD (fun φ hφ => hI φ (Or.inr hφ)) hA e m hg) it hit

/-- info: 'TieRuleLhsAnd.Ceil.rule_from_text_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_from_text_in
/-- info: 'TieRuleLhsAnd.Ceil.rule_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_w2
#check @left_iff
#check @terms_in
#check @rule_from_text_in
#check @rule_w2
/-- info: 'TieRuleLhsAnd.Ceil.rule_w2_noprem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_w2_noprem
/-- info: 'TieRuleLhsAnd.Ceil.rule_from_text_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_from_text_aux
#check @right_defined
#check @rule_w2_noprem
#check @ruleSigAux_text
#check @terms_in_inj
#check @rule_from_text_aux

end Ceil

namespace Equals

kore_term kore from "f2-examples/mllhseq.kompile.kore"
definition_of defn from "f2-examples/mllhseq.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

example : c.sortName 32 = "Exp" ∧ c.sortName 0 = "K" ∧ c.sortName 19 = "GeneratedCounterCell" ∧
    c.symName 385 = "Lbldone" ∧ c.symName 386 = "Lblgo" := by decide +kernel

def cfg (x : Term) : Term := .app 71 [.app 383 [.app 0 [.inj 32 1 x, .var 1]], .var 2]

/-- `go(X) => done` with `pre := X = 1`, X:Int the first variable. -/
def rz : Rule :=
  { vars := [Srt.int, 0, 19], lhs := cfg (.app 386 [.var 0]), req := none, rhs := cfg (.app 385 []),
    ens := none, prio := 50, pre := .equals Srt.int (.var 0) (.dv Srt.int (.int 1)) }

/-- The reader reads the text's rule as `rz` (`Parse.parse`, through `lhsAndCut`). -/
theorem read : c.rules = [rz] := rfl

def x : Kore.Pattern := ev "VarV0" (srt "Int")
def one : Kore.Pattern := .dv (srt "Int") "1"
def t : Kore.Pattern := injP "Exp" "KItem" (ap "Lblgo" [x])
/-- The predicate as the text writes it, at KItem. -/
def P : Kore.Pattern := .equals (srt "Int") kitemS x one
/-- The predicate as `pre` writes it, at the top cell's sort. -/
def P' : Kore.Pattern := .equals (srt "Int") topC x one
def E : Kore.Pattern := .top topC
def K : KoreCutCtx := itemCtx .hole (ev "VarV1" (srt "K")) (ev "VarV2" (srt "GeneratedCounterCell"))
def R : Kore.Pattern := .and topC [K.fill (injP "Exp" "KItem" (ap "Lbldone" [])), E]

def left : Kore.Pattern := .and topC [K.fill (.and kitemS [t, P]), E]

theorem right_eq : ruleRight c rz = R := by decide +kernel

/-- Γ's axiom of the rule: `\rewrites(K[t] ∧ ⊤ ∧ P' ∧ ⌈R⌉, R)`. -/
theorem left_eq : prioRuleK c rz = .rewrites topC (.and topC [K.fill t, E, P', .ceil topC topC R]) R := by
  decide +kernel

def spell (n : String) (_ : Kore.KSort) : String :=
  if n == "VarV0" then "VarX" else if n == "VarV1" then "Var'Unds'DotVar1"
  else if n == "VarV2" then "Var'Unds'DotVar0" else n

theorem left_text : some (renVars spell (fun n _ => n) left) = (rewritesAt kore 295).map (·.1) := by
  decide +kernel

theorem left_tie (l : Kore.Pattern) (h : (rewritesAt kore 295).map (·.1) = some l) :
    tr ⟨tableOf [] l, []⟩ l = tr ⟨tableOf [] left, []⟩ left := by
  have hl : l = renVars spell (fun n _ => n) left := by
    have := left_text; rw [h] at this; exact (Option.some.inj this).symm
  rw [hl]
  exact tr_occurrence_order spell (fun n _ => n) [] [] left (by decide +kernel)

/-- **`rule_and_pred` at the fixture's left side**: `K[t] ∧ ⊤ ∧ (X = 1)` is the text's left side
`K[t ∧ (X = 1)] ∧ ⊤`, under the theorem's premises at a table without aliases. -/
theorem tie {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (tbl : VarTable) (e : Valuation M) {σi σk σ' : M}
    (hI : ∀ a, (trSort tbl (srt "Int")).interpret I e a ↔ a = σi)
    (hK : ∀ a, (trSort tbl kitemS).interpret I e a ↔ a = σk)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσi : IsSort I σi) (hσk : IsSort I σk) (hσ' : IsSort I σ')
    (hin : ∀ a, (tr ⟨tbl, []⟩ t).interpret I e a → Inh I σk a)
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill t)).interpret I e m → Inh I σ' m) (m : M) :
    (tr ⟨tbl, []⟩ (.and topC [K.fill t, E, P'])).interpret I e m ↔
      (tr ⟨tbl, []⟩ left).interpret I e m := by
  have hP : ∀ a, Inh I σk a → ((tr ⟨tbl, []⟩ P).interpret I e a ↔
      ∀ b, Inh I σi b → ((tr ⟨tbl, []⟩ x).interpret I e b ↔ (tr ⟨tbl, []⟩ one).interpret I e b)) :=
    fun a ha => by
      show (sEquals (trSort tbl (srt "Int")) (trSort tbl kitemS) (tr ⟨tbl, []⟩ x) (tr ⟨tbl, []⟩ one)).interpret I e a ↔ _
      rw [interp_sEquals hD hc hI hK hσi hσk a]
      exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  have hP' : ∀ m, Inh I σ' m → ((tr ⟨tbl, []⟩ P').interpret I e m ↔
      ∀ b, Inh I σi b → ((tr ⟨tbl, []⟩ x).interpret I e b ↔ (tr ⟨tbl, []⟩ one).interpret I e b)) :=
    fun m hm => by
      show (sEquals (trSort tbl (srt "Int")) (trSort tbl topC) (tr ⟨tbl, []⟩ x) (tr ⟨tbl, []⟩ one)).interpret I e m ↔ _
      rw [interp_sEquals hD hc hI hC hσi hσ' m]
      exact ⟨fun h => h.2, fun h => ⟨hm, h⟩⟩
  exact and_pred_reassoc ⟨tbl, []⟩ topC kitemS K t P P' E e m
    (rule_and_pred ⟨tbl, []⟩ K rfl kitemS topC t P P' e _ hP hP' hin hout m)

/-- **Γ's left side is the text's left side with `⌈R⌉`**. -/
theorem at_rule {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (tbl : VarTable) (e : Valuation M) {σi σk σ' : M}
    (hI : ∀ a, (trSort tbl (srt "Int")).interpret I e a ↔ a = σi)
    (hK : ∀ a, (trSort tbl kitemS).interpret I e a ↔ a = σk)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσi : IsSort I σi) (hσk : IsSort I σk) (hσ' : IsSort I σ')
    (hin : ∀ a, (tr ⟨tbl, []⟩ t).interpret I e a → Inh I σk a)
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill t)).interpret I e m → Inh I σ' m) (m : M) :
    (tr ⟨tbl, []⟩ (.and topC [K.fill t, E, P', .ceil topC topC R])).interpret I e m ↔
      (tr ⟨tbl, []⟩ left).interpret I e m ∧ (tr ⟨tbl, []⟩ (.ceil topC topC R)).interpret I e m := by
  rw [and4_iff, tie hD hc tbl e hI hK hC hσi hσk hσ' hin hout m]

/-! ## The rule's sentence (157), for every H: W1 under the term's sort, and W2 -/

user_axioms U from "f2-examples/mllhseq.kompile.kore" module "E3-ML-RULE-LHS-EQUALS"

noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c rz

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

/-- Γ's left side: `K[t] ∧ ⊤ ∧ P' ∧ ⌈R⌉`. -/
def Lg : Kore.Pattern := .and topC [K.fill t, E, P', .ceil topC topC R]

theorem p0_parts : TieRuleLhs.rwParts p0 = some (topC, Lg, R) := by decide +kernel

/-- The free variables of the text's form. -/
def fT : List VarKey := (freeOf [] (.rewrites topC left R)).eraseDups

/-- **The text's sentence 157 is the item of `\rewrites{C}(left, R)` at the table of Γ's axiom**
(kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT topC left R) [] =
    some (trS U.ax157).pat := by
  decide +kernel
theorem fT_free0 : fT.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem free_sub0 : ∀ k ∈ (freeOf [] p0).eraseDups, k ∈ fT := by decide +kernel
theorem x_free0 : VarKey.evar "VarV0" (srt "Int") ∈ fT := by decide +kernel

/-- The term at the position as the reading's term, `inj{Exp,KItem}(go(X))` over the rule's variables. -/
theorem terms_kore : Term.kore c (canonVars c rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0])) = t ∧
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) rz.vars (.inj 32 Srt.kitem (.app 386 [.var 0])) = some Srt.kitem ∧
    canonKey c rz.vars 0 = .evar "VarV0" (srt "Int") := by
  decide +kernel

/-- The term's pattern does not read the interpretation of the hooks. -/
theorem terms_koreF :
    (fun H : HookParams =>
      Term.kore (c.withHooks H) (canonVars (c.withHooks H) rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0]))) =
    fun _ => Term.kore c (canonVars c rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0])) := by
  kernel_rfl

/-- **Γ's left side without `⌈R⌉` is the text's left side**, at the table of Γ's axiom, in a model
of the signature, at a valuation where every element of the term at the position is in KItem:
`and_pred_inTop`, the outer sort read from the `requires` `\top`. -/
theorem left_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (e : Valuation M)
    (hin : ∀ a, (tr ⟨tableOf [] p0, []⟩ t).interpret I e a →
      (inhOf (trSort (tableOf [] p0) kitemS)).interpret I e a) (m : M) :
    (tr ⟨tableOf [] p0, []⟩ (.and topC [K.fill t, E, P'])).interpret I e m ↔
      (tr ⟨tableOf [] p0, []⟩ left).interpret I e m := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  obtain ⟨σi, hσi, hInt, -⟩ := TieRuleConnText.sort_sig hD hSig (s := Srt.int)
    (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
    (show (cH H).sortName Srt.int = "Int" from (by decide +kernel : c.sortName Srt.int = "Int"))
  obtain ⟨σk, hσk, hK, -⟩ := TieRuleConnText.sort_sig hD hSig (s := Srt.kitem)
    (by decide +kernel : Srt.kitem < nRegSorts + c.sortNames.length)
    (show (cH H).sortName Srt.kitem = "KItem" from (by decide +kernel : c.sortName Srt.kitem = "KItem"))
  obtain ⟨σ', hσ', hC, -⟩ := TieRuleConnText.sort_sig hD hSig (s := topCellSort)
    (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
    (show (cH H).sortName topCellSort = "GeneratedTopCell" from
      (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell"))
  have hK' : ∀ a, (trSort (tableOf [] p0) kitemS).interpret I e a ↔ a = σk := hK _ e
  have hC' : ∀ a, (trSort (tableOf [] p0) topC).interpret I e a ↔ a = σ' := hC _ e
  have hin' : ∀ a, (tr ⟨tableOf [] p0, []⟩ t).interpret I e a → Inh I σk a :=
    fun a ha => (interp_inhOf_of (hK _ e)).mp (hin a ha)
  have hP : ∀ a, Inh I σk a → ((tr ⟨tableOf [] p0, []⟩ P).interpret I e a ↔
      ∀ b, Inh I σi b → ((tr ⟨tableOf [] p0, []⟩ x).interpret I e b ↔ (tr ⟨tableOf [] p0, []⟩ one).interpret I e b)) :=
    fun a ha => by
      show (sEquals (trSort (tableOf [] p0) (srt "Int")) (trSort (tableOf [] p0) kitemS)
        (tr ⟨tableOf [] p0, []⟩ x) (tr ⟨tableOf [] p0, []⟩ one)).interpret I e a ↔ _
      rw [interp_sEquals hD hc (hInt _ e) hK' hσi hσk a]
      exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  have hP' : ∀ m, Inh I σ' m → ((tr ⟨tableOf [] p0, []⟩ P').interpret I e m ↔
      ∀ b, Inh I σi b → ((tr ⟨tableOf [] p0, []⟩ x).interpret I e b ↔ (tr ⟨tableOf [] p0, []⟩ one).interpret I e b)) :=
    fun m hm => by
      show (sEquals (trSort (tableOf [] p0) (srt "Int")) (trSort (tableOf [] p0) topC)
        (tr ⟨tableOf [] p0, []⟩ x) (tr ⟨tableOf [] p0, []⟩ one)).interpret I e m ↔ _
      rw [interp_sEquals hD hc (hInt _ e) hC' hσi hσ' m]
      exact ⟨fun h => h.2, fun h => ⟨hm, h⟩⟩
  exact and_pred_inTop ⟨tableOf [] p0, []⟩ K rfl kitemS topC t P P' E e _ hP hP' hin'
    (fun m hm => TieRuleConnText.top_inh hD (hC _ e) m hm) m

/-- **In a model of Γ, where X's guard holds**, every element of `inj{Exp,KItem}(go(X))` is in KItem
(`condTerm_inh`: the symbols' result sorts, from Γ's items of the signature and of the
constructors). -/
theorem terms_in (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (e : Valuation M) (m : M) (hg : ∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) :
    ∀ a, (tr ⟨tableOf [] p0, []⟩ t).interpret I e a →
      (inhOf (trSort (tableOf [] p0) kitemS)).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hgw : genWf (cH H) = true := (faithCoreOK_parts (Semantics.coreOK_parts (coreOKH H)).2.1).2.1
  obtain ⟨hk2, hs2, hkey⟩ := terms_kore
  have hx := hg _ x_free0
  rw [interp_guard_evar hD, trSort_srt] at hx
  have hvars : ∀ i ∈ varOccs (.inj 32 Srt.kitem (.app 386 [.var 0])),
      InS I ((cH H).sortName (rz.vars.getD i 0)) (e.evalEvar ((tableOf [] p0).ev (canonKey (cH H) rz.vars i))) := by
    intro i hi
    have : i = 0 := by simpa [varOccs, varOccsList] using hi
    subst this
    show InS I (c.sortName (rz.vars.getD 0 0)) (e.evalEvar ((tableOf [] p0).ev (canonKey c rz.vars 0)))
    rw [hkey]
    exact (inS_iff e).mp hx
  obtain ⟨τk, -, hτk⟩ := srt_den hI (s := Srt.kitem)
    (by decide +kernel : Srt.kitem < nRegSorts + c.sortNames.length)
  have h2 := condTerm_inh hI hgw (tbl := tableOf [] p0) (e := e) hτk
    (show sortOfTerm ((cH H).rhsCtx ((cH H).fns.map Fn.sig)) rz.vars (.inj 32 Srt.kitem (.app 386 [.var 0])) =
      some Srt.kitem from hs2) hvars
  rw [show Term.kore (cH H) (canonVars (cH H) rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0])) =
    Term.kore c (canonVars c rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0])) from congrFun terms_koreF H, hk2] at h2
  exact fun a ha => (interp_inhOf_of (hτk _ e)).mpr (h2 a ha)

/-- **W1 for the rule, under the term's sort**: in a model of sentence 157 and the signature in
which, where the guards hold, every element of the term at the position is in KItem, Γ's rule item
holds, for every H. (The inclusion holds in every model of Γ, `terms_in`; it is not derived from
the signature alone here.) -/
theorem rule_from_text_in (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP (TiePair.Texts [(trS U.ax157).pat] ∪ ΓSig (cH H)))
    (hT : ∀ (e : Valuation M) (m : M),
      (∀ k ∈ (freeOf [] p0).eraseDups, (guardOf (tableOf [] p0) k).interpret I e m) →
        ∀ a, (tr ⟨tableOf [] p0, []⟩ t).interpret I e a →
          (inhOf (trSort (tableOf [] p0) kitemS)).interpret I e a) :
    ∀ it ∈ ruleItems (cH H), I ⊧ᴵ it.pat := by
  intro it hit
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  rw [List.mem_singleton.mp hit]
  exact TieRuleConnText.rule_w1_sides hD p0_parts rule_text0 fT_free0
    (hI _ (Or.inl (Or.inl (List.mem_singleton_self _))))
    (fun e m hg x hx => (left_iff H hD hSig e (hT e m hg) x).mp ((and4_iff _ _ _ _ _ _ _ _).mp hx).1)
    (fun e m _ x hx => hx)

/-- **W2 for the rule, with the guard**: in a model of Γ, sentence 157 holds where, at each
valuation at which the guards of its variables hold, `⌈R⌉` (the conjunct Γ's left side adds) holds
wherever the text's left side holds, for every H. -/
theorem rule_w2 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (hR : ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) →
      ∀ x, (tr ⟨tableOf [] p0, []⟩ left).interpret I e x →
        (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).interpret I e x) :
    I ⊧ᴵ (trS U.ax157).pat := by
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  exact TieRuleConnText.rule_w2_sides hD p0_parts rule_text0 free_sub0 hg
    (fun e m hgs x hx => (and4_iff _ _ _ _ _ _ _ _).mpr
      ⟨(left_iff H hD hSig e (terms_in H hI e m hgs) x).mpr hx, hR e m hgs x hx⟩)
    (fun e m _ x hx => hx)

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

/-- The right side's term is built of the text's variables and of those generators, at arguments
of their sorts (kernel). -/
theorem right_built : TieRuleCutG.builtGB rightGens fT (K.fill (injP "Exp" "KItem" (ap "Lbldone" []))) "GeneratedTopCell" = true := by
  decide +kernel

/-- **The premise of `rule_w2` holds in every model of Γ**, for every H: where the guards of the
text's variables hold, the right side holds one element, by the Cons-Fun items of its generators,
so `⌈R⌉` holds of every element of the top cell's sort, which the `\top` of the text's left side
keeps its elements in. -/
theorem right_defined (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) (a : M)
    (ha : (tr ⟨tableOf [] p0, []⟩ left).interpret I e a) :
    (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have ha' : (tr ⟨tableOf [] p0, []⟩ (.and topC [K.fill (.and kitemS [t, P]), E])).interpret I e a := ha
  exact TieRuleCutG.rightDefined_top hI
    (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
    (show (cH H).sortName topCellSort = "GeneratedTopCell" from
      (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell"))
    ((TieRuleCutG.funsInGB_withHooks c H rightGens).trans right_funs) right_built e m hg a
    ((interp_and (List.cons_ne_nil _ _)).mp ha' E (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **W2 for the rule, without a premise**: sentence 157 holds in every model of Γ, for every H
(`rule_w2` with `right_defined`). -/
theorem rule_w2_noprem (H : HookParams) : Γ (cH H) ⊧ (trS U.ax157).pat :=
  fun {_} _ {_} hI => rule_w2 H hI (right_defined H hI)

/-- go's signature, Int to Exp. -/
def kgo : KCore.CtorSig := ⟨386, [Srt.int], 32⟩
theorem kgo_mem (H : HookParams) : kgo ∈ kernelSyms (cH H) := (by decide +kernel : kgo ∈ kernelSyms c)
/-- go's arity item: go of elements of Int holds elements of Exp only. -/
theorem kgo_arity_c : (symArityItem c kgo).pat =
    (sym (.symbol "Lblgo") ⬝ inhOf (sortP "Int") ⊆⊆ inhOf (sortP "Exp")) := by decide +kernel
kernel_rfl kgo_arity_withHooks : ∀ H : HookParams, (symArityItem (c.withHooks H) kgo).pat = (symArityItem c kgo).pat
theorem kgo_arity (H : HookParams) : (symArityItem (cH H) kgo).pat =
    (sym (.symbol "Lblgo") ⬝ inhOf (sortP "Int") ⊆⊆ inhOf (sortP "Exp")) :=
  (kgo_arity_withHooks H).trans kgo_arity_c

/-- The text's declaration `symbol inj{From, To}(From) : To [sortInjection{}()]`. -/
def injDecl : SymbolDecl :=
  ⟨"inj", [⟨⟨⟨"From"⟩⟩⟩, ⟨⟨⟨"To"⟩⟩⟩], [.var ⟨⟨⟨"From"⟩⟩⟩], .var ⟨⟨⟨"To"⟩⟩⟩, false, ["sortInjection"]⟩

theorem injDecl_mem : injDecl ∈ kore.symbolDecls := by decide +kernel

/-- Its arity item is `TieFRSig.injArityP`: at two sorts, what `inj` builds of an element of the
first lies in the second. -/
theorem injArity_pat : (arityItem injDecl).pat = TieFRSig.injArityP := TieFRSig.injArityP_shape _ _

/-- The rule sentence. -/
noncomputable def ruleText : List AxiomDecl := [U.ax157]

/-- The other sentences of the text the statement reads: none. -/
noncomputable def ruleAux : List AxiomDecl := []

/-- The item of the text's signature the statement reads, which `ΓSig` does not hold: the arity
item of the declaration of `inj`. -/
def ruleSigAux : List Item := [arityItem injDecl]

/-- Each item of `ruleSigAux` is an item of the signature of the text's theory. -/
theorem ruleSigAux_text : ∀ it ∈ ruleSigAux, it ∈ (Theory.ofDefinition kore).signature := by
  intro it hit
  rw [List.mem_singleton.mp hit]
  simp only [Theory.ofDefinition, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨_, injDecl_mem, rfl⟩)))

/-- **In a model of definedness, the signature and `inj`'s arity item, where X's guard holds**,
every element of `inj{Exp,KItem}(go(X))` is in KItem: the term lies in its sort
(`TieFRSig.sig_of_core_inj`: go's result sort from its arity item in `ΓSig`, the injection's target
sort from `inj`'s arity item at the subsort pair Exp, KItem). -/
theorem terms_in_inj (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (hA : I ⊧ᴵ TieFRSig.injArityP) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ (freeOf [] p0).eraseDups, (guardOf (tableOf [] p0) k).interpret I e m) :
    ∀ a, (tr ⟨tableOf [] p0, []⟩ t).interpret I e a →
      (inhOf (trSort (tableOf [] p0) kitemS)).interpret I e a := by
  have hT : TermsInSort (cH H) I := (TieFRSig.sig_of_core_inj (coreOKH H) hD hSig hA).2
  obtain ⟨hk2, hs2, hkey⟩ := terms_kore
  have hx := hg _ (List.contains_iff_mem.mp (List.all_eq_true.mp fT_free0 _ x_free0))
  rw [interp_guard_evar hD, trSort_srt] at hx
  have hvars : ∀ i ∈ varOccs (.inj 32 Srt.kitem (.app 386 [.var 0])),
      InS I ((cH H).sortName (rz.vars.getD i 0)) (e.evalEvar ((tableOf [] p0).ev (canonKey (cH H) rz.vars i))) := by
    intro i hi
    have : i = 0 := by simpa [varOccs, varOccsList] using hi
    subst this
    show InS I (c.sortName (rz.vars.getD 0 0)) (e.evalEvar ((tableOf [] p0).ev (canonKey c rz.vars 0)))
    rw [hkey]
    exact (inS_iff e).mp hx
  have h2 : ∀ a, (tr ⟨tableOf [] p0, []⟩
      (Term.kore (cH H) (canonVars (cH H) rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0])))).interpret I e a →
      InS I ((cH H).sortName Srt.kitem) a :=
    hT (show sortOfTerm ((cH H).rhsCtx ((cH H).fns.map Fn.sig)) rz.vars (.inj 32 Srt.kitem (.app 386 [.var 0])) =
      some Srt.kitem from hs2)
      (by decide +kernel : Srt.kitem < nRegSorts + c.sortNames.length) hvars
  rw [show Term.kore (cH H) (canonVars (cH H) rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0])) =
    Term.kore c (canonVars c rz.vars) (.inj 32 Srt.kitem (.app 386 [.var 0])) from congrFun terms_koreF H, hk2,
    show (cH H).sortName Srt.kitem = "KItem" from (by decide +kernel : c.sortName Srt.kitem = "KItem")] at h2
  exact fun a ha => by rw [kitemS, trSort_srt]; exact (inS_iff e).mpr (h2 a ha)

/-- **W1 for the rule, from the text**: Γ's one rule item is a consequence of sentence 157 with the
arity item of the text's declaration of `inj` (`ruleSigAux`, an item of the text's signature that
`ΓSig` does not hold) and `ΓSig`, for every H. The arity item puts every element of
`inj{Exp,KItem}(go(X))` in KItem (`terms_in_inj`); the text's subsort sentence of Exp, KItem is not
read (it equates the injection with an element at KItem only). -/
theorem rule_from_text_aux (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText,
    TiePair.Texts ((trS ad).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  refine ⟨U.ax157, List.mem_singleton_self _, ?_⟩
  intro M _ I hI
  have hT : I ⊧ᴵP (TiePair.Texts [(trS U.ax157).pat] ∪ ΓSig (cH H)) := by
    intro φ hφ
    rcases hφ with (hm | hd) | hs
    · exact hI φ (Or.inl (Or.inl (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hm)))))
    · exact hI φ (Or.inl (Or.inr hd))
    · exact hI φ (Or.inr hs)
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hA : I ⊧ᴵ TieFRSig.injArityP := by
    rw [← injArity_pat]
    exact hI _ (Or.inl (Or.inl (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  exact rule_from_text_in H hT (fun e m hg => terms_in_inj H hD (fun φ hφ => hI φ (Or.inr hφ)) hA e m hg) it hit

/-- info: 'TieRuleLhsAnd.Equals.rule_from_text_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_from_text_in
/-- info: 'TieRuleLhsAnd.Equals.rule_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_w2
#check @left_iff
#check @terms_in
#check @rule_from_text_in
#check @rule_w2
/-- info: 'TieRuleLhsAnd.Equals.rule_w2_noprem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_w2_noprem
/-- info: 'TieRuleLhsAnd.Equals.rule_from_text_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_from_text_aux
#check @right_defined
#check @rule_w2_noprem
#check @ruleSigAux_text
#check @terms_in_inj
#check @rule_from_text_aux

end Equals

namespace Var

kore_term kore from "f2-examples/mllhsandv.kompile.kore"
definition_of defn from "f2-examples/mllhsandv.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

example : c.sortName 32 = "Exp" ∧ c.sortName 0 = "K" ∧ c.sortName 19 = "GeneratedCounterCell" ∧
    c.symName 386 = "Lblb" ∧ c.symName 387 = "Lblc" ∧ c.symName 388 = "Lbld" := by decide +kernel

def cfg (x : Term) : Term := .app 71 [.app 383 [.app 0 [.inj 32 1 x, .var 2]], .var 3]

/-- `c(d(G, b()) #as X) => X`, G:Exp the first variable, X:Exp the second. -/
def rz : Rule :=
  { vars := [32, 32, 0, 19], lhs := cfg (.app 387 [.as (.app 388 [.var 0, .app 386 []]) 1]), req := none,
    rhs := cfg (.var 1), ens := none, prio := 50 }

/-- The reader reads the text's rule as `rz` (`Parse.parse`, through `lhsAndCut`). -/
theorem read : c.rules = [rz] := rfl

def S : Kore.KSort := srt "Exp"
def x : Kore.EVar := evar "VarV1" S
def p : Kore.Pattern := ap "Lbld" [ev "VarV0" S, ap "Lblb" []]
def E : Kore.Pattern := .top topC
def K : KoreCutCtx := itemCtx (.app ⟨⟨"inj"⟩⟩ [S, kitemS] [] (.app ⟨⟨"Lblc"⟩⟩ [] [] .hole []) [])
    (ev "VarV2" (srt "K")) (ev "VarV3" (srt "GeneratedCounterCell"))
def R : Kore.Pattern := .and topC [itemCtx .hole (ev "VarV2" (srt "K")) (ev "VarV3" (srt "GeneratedCounterCell"))
    |>.fill (injP "Exp" "KItem" (.var (.evar x))), E]

/-- The theorem's right pattern: the left side with `X ∧ p` in its position. -/
def left : Kore.Pattern := .and topC [K.fill (.and S [.var (.evar x), p]), E]

theorem right_eq : ruleRight c rz = R := by decide +kernel

/-- Γ's axiom of the rule: `\rewrites(K[p ∧ X] ∧ ⊤ ∧ ⌈R⌉, R)`, `p #as X` translated. -/
theorem left_eq : prioRuleK c rz =
    .rewrites topC (.and topC [K.fill (.and S [p, .var (.evar x)]), E, .ceil topC topC R]) R := by
  decide +kernel

def spell (n : String) (_ : Kore.KSort) : String :=
  if n == "VarV0" then "Var'Unds'Gen0" else if n == "VarV1" then "VarX"
  else if n == "VarV2" then "Var'Unds'DotVar1" else if n == "VarV3" then "Var'Unds'DotVar0" else n

theorem left_text : some (renVars spell (fun n _ => n) left) = (rewritesAt kore 200).map (·.1) := by
  decide +kernel

theorem left_tie (l : Kore.Pattern) (h : (rewritesAt kore 200).map (·.1) = some l) :
    tr ⟨tableOf [] l, []⟩ l = tr ⟨tableOf [] left, []⟩ left := by
  have hl : l = renVars spell (fun n _ => n) left := by
    have := left_text; rw [h] at this; exact (Option.some.inj this).symm
  rw [hl]
  exact tr_occurrence_order spell (fun n _ => n) [] [] left (by decide +kernel)

/-- **`rule_and_as` at the fixture's left side**: `K[p ∧ X] ∧ ⊤` is the text's left side
`K[X ∧ p] ∧ ⊤`, at every table and interpretation. -/
theorem tie {M : Type} {I : Interpretation KoreAML.Sym M} (tbl : VarTable) (e : Valuation M) (m : M) :
    (tr ⟨tbl, []⟩ (.and topC [K.fill (.and S [p, .var (.evar x)]), E])).interpret I e m ↔
      (tr ⟨tbl, []⟩ left).interpret I e m := by
  have e1 : ∀ φ : Kore.Pattern, tr ⟨tbl, []⟩ (.and topC [φ, E]) = sAnd (tr ⟨tbl, []⟩ φ) (tr ⟨tbl, []⟩ E) :=
    fun _ => rfl
  show (tr ⟨tbl, []⟩ (.and topC [K.fill (.and S [p, .var (.evar x)]), E])).interpret I e m ↔
    (tr ⟨tbl, []⟩ (.and topC [K.fill (.and S [.var (.evar x), p]), E])).interpret I e m
  rw [e1, e1, interp_sAnd, interp_sAnd, rule_and_as ⟨tbl, []⟩ K rfl S x p e m]

/-- **Γ's left side is the text's left side with `⌈R⌉`**. -/
theorem at_rule {M : Type} {I : Interpretation KoreAML.Sym M} (tbl : VarTable) (e : Valuation M) (m : M) :
    (tr ⟨tbl, []⟩ (.and topC [K.fill (.and S [p, .var (.evar x)]), E, .ceil topC topC R])).interpret I e m ↔
      (tr ⟨tbl, []⟩ left).interpret I e m ∧ (tr ⟨tbl, []⟩ (.ceil topC topC R)).interpret I e m := by
  rw [and3_iff, tie tbl e m]

/-! ### The rule's sentence (104), for every H: W1 and W2 -/

user_axioms U from "f2-examples/mllhsandv.kompile.kore" module "E3-ML-RULE-LHS-AND"

noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c rz

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

theorem p0_parts : TieRuleLhs.rwParts p0 =
    some (topC, .and topC [K.fill (.and S [p, .var (.evar x)]), E, .ceil topC topC R], R) := by
  unfold p0; rw [left_eq]; rfl

/-- The free variables of the text's form. -/
def fT : List VarKey := (freeOf [] (.rewrites topC left R)).eraseDups

/-- **The text's sentence 104 is the item of `\rewrites{C}(left, R)` at the table of Γ's axiom**
(kernel, under the exchange of the indices of G and X, which the text holds in the other order). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT topC left R) [(1, 5), (2, 1), (5, 2)] =
    some (trS U.ax104).pat := by
  decide +kernel
theorem fT_free0 : fT.all (fun k => (freeOf [] p0).eraseDups.contains k) = true := by decide +kernel
theorem free_sub0 : ∀ k ∈ (freeOf [] p0).eraseDups, k ∈ fT := by decide +kernel

/-- **W1 for the rule, and the converse for `ruleItems`**: Γ's one rule item is a consequence of
sentence 104, for every H: every element of Γ's left side is one of the text's (`at_rule`). -/
theorem rule_from_text (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), TiePair.Texts [(trS U.ax104).pat] ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq, List.mem_singleton] at hit
  subst hit
  have hD : DefOK I := TiePair.defOK_texts hI
  exact TieRuleLhs.rule_w1 hD p0_parts rule_text0 fT_free0 (hI _ (Or.inl (List.mem_singleton_self _)))
    fun e _ _ a ha => ((at_rule (tableOf [] p0) e a).mp ha).1

/-- **W2 for the rule, with the guard**: in a model of Γ, sentence 104 holds where, at each
valuation at which the guards of its variables hold, `⌈R⌉` (the conjunct Γ's left side adds) holds
wherever the text's left side holds, for every H. -/
theorem rule_w2 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (hR : ∀ (e : Valuation M) (m : M), (∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) →
      ∀ a, (tr ⟨tableOf [] p0, []⟩ left).interpret I e a →
        (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).interpret I e a) :
    I ⊧ᴵ (trS U.ax104).pat := by
  have hD := defOK hI
  have hit : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have hg : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, hit, rfl⟩)))
  exact TieRuleConnText.rule_w2_sides hD p0_parts rule_text0 free_sub0 hg
    (fun e m hgs a ha => (at_rule (tableOf [] p0) e a).mpr ⟨ha, hR e m hgs a ha⟩) (fun _ _ _ _ h => h)

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The generators of the right side's term: the top cell, the `k` cell, `kseq`, the injection of
Exp into KItem. -/
def rightGens : List (String × KoreAML.Gen) :=
  [("GeneratedTopCell", .ctor ⟨"Lbl'-LT-'generatedTop'-GT-'", ["KCell", "GeneratedCounterCell"], "GeneratedTopCell"⟩),
   ("KCell", .ctor ⟨"Lbl'-LT-'k'-GT-'", ["K"], "KCell"⟩),
   ("K", .ctor ⟨"kseq", ["KItem", "K"], "K"⟩),
   ("KItem", .inj "Exp")]

/-- Γ has the Cons-Fun item of each (kernel). -/
theorem right_funs : TieRuleCutG.funsInGB c rightGens = true := by decide +kernel

/-- The right side's term is built of the text's variables and of those generators, at arguments
of their sorts (kernel). -/
theorem right_built : TieRuleCutG.builtGB rightGens fT ((itemCtx .hole (ev "VarV2" (srt "K")) (ev "VarV3" (srt "GeneratedCounterCell"))).fill (injP "Exp" "KItem" (.var (.evar x)))) "GeneratedTopCell" = true := by
  decide +kernel

/-- **The premise of `rule_w2` holds in every model of Γ**, for every H: where the guards of the
text's variables hold, the right side holds one element, by the Cons-Fun items of its generators,
so `⌈R⌉` holds of every element of the top cell's sort, which the `\top` of the text's left side
keeps its elements in. -/
theorem right_defined (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT, (guardOf (tableOf [] p0) k).interpret I e m) (a : M)
    (ha : (tr ⟨tableOf [] p0, []⟩ left).interpret I e a) :
    (tr ⟨tableOf [] p0, []⟩ (.ceil topC topC R)).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have ha' : (tr ⟨tableOf [] p0, []⟩ (.and topC [K.fill (.and S [.var (.evar x), p]), E])).interpret I e a := ha
  exact TieRuleCutG.rightDefined_top hI
    (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
    (show (cH H).sortName topCellSort = "GeneratedTopCell" from
      (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell"))
    ((TieRuleCutG.funsInGB_withHooks c H rightGens).trans right_funs) right_built e m hg a
    ((interp_and (List.cons_ne_nil _ _)).mp ha' E (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **W2 for the rule, without a premise**: sentence 104 holds in every model of Γ, for every H
(`rule_w2` with `right_defined`). -/
theorem rule_w2_noprem (H : HookParams) : Γ (cH H) ⊧ (trS U.ax104).pat :=
  fun {_} _ {_} hI => rule_w2 H hI (right_defined H hI)

/-- info: 'TieRuleLhsAnd.Var.rule_w2_noprem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_w2_noprem
#check @right_defined
#check @rule_w2_noprem

end Var

end TieRuleLhsAnd

#check @TieRuleLhsAnd.Ceil.read
#check @TieRuleLhsAnd.Ceil.left_eq
#check @TieRuleLhsAnd.Ceil.left_tie
#check @TieRuleLhsAnd.Ceil.tie
#check @TieRuleLhsAnd.Ceil.at_rule
#check @TieRuleLhsAnd.Equals.read
#check @TieRuleLhsAnd.Equals.left_eq
#check @TieRuleLhsAnd.Equals.left_tie
#check @TieRuleLhsAnd.Equals.tie
#check @TieRuleLhsAnd.Equals.at_rule
#check @TieRuleLhsAnd.Var.read
#check @TieRuleLhsAnd.Var.left_eq
#check @TieRuleLhsAnd.Var.left_tie
#check @TieRuleLhsAnd.Var.tie
#check @TieRuleLhsAnd.Var.at_rule
#print axioms TieRuleLhsAnd.Ceil.tie
#print axioms TieRuleLhsAnd.Ceil.left_tie
#print axioms TieRuleLhsAnd.Equals.tie
#print axioms TieRuleLhsAnd.Equals.left_tie
#print axioms TieRuleLhsAnd.Var.tie
#print axioms TieRuleLhsAnd.Var.left_tie
#check @TieRuleLhsAnd.Var.rule_text0
#check @TieRuleLhsAnd.Var.rule_from_text
#check @TieRuleLhsAnd.Var.rule_w2
#print axioms TieRuleLhsAnd.Var.rule_from_text
#print axioms TieRuleLhsAnd.Var.rule_w2
