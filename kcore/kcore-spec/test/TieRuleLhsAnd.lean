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
    `rule_w2`; `Ceil`, `Equals`: argued from `at_rule`, no statement at the level of the sentences'
    validity is written here).
  - The theorems hold at any table and leave as premises what `rule_and_pred` lists of the table
    and the interpretation: definedness, the sorts' patterns, every element of t in KItem, every
    element of `K[t]` in the top cell's sort, and (Ceil) every element of go(X) in Exp. Nothing here
    relates the table of Γ's axiom to the table of the text's sentence beyond `left_tie`'s renaming
    and `Var`'s `rule_text0`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

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
