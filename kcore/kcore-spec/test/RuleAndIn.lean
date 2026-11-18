/-
  `KoreAML.rule_and_in` and `KoreAML.rule_and_var` at the two fixtures whose rule's right side holds
  `t #And u` of two terms under applications. Run from the package root, after the library:
  `lake env lean -j1 test/RuleAndIn.lean`.

  - `Fresh` (e3-ml-rule-rhs-and-term, `go(X) => f(X) #And g(X)`, f2-examples/mlandt): `rz` is the
    rule with the position cut by a fresh existential variable Z:Int, `post := Z ∈ f(X) ∧ Z ∈ g(X)`,
    the rule the reader reads (`read`: `andTermsCut`).
    `left_eq`: `ruleRight c rz` is the theorem's left pattern (the context K of the position, the
    `ensures` `\top`). `right_text`: the theorem's right pattern, its canonical names spelled as the
    text spells them, is the right argument of the text's `\rewrites`; `right_tie`: so the two have
    one translation under their own tables (`tr_occurrence_order`). `tie`: `rule_and_in` at these.
  - `Var` (e3-ml-rule-rhs-and-ctor, `c(X) => X #And a`, f2-examples/mlandc): `rv` is the rule with
    the position holding X and `post := X ∈ a`, the rule the reader reads (`read`); `left_eq`, `right_text`, `right_tie`, `tie` for
    `rule_and_var`.
  - The two theorems are stated at one table for both patterns. `Fresh.tables`: in the rule's
    sentence (`prioRuleK c rz`) every variable of the text's right side is met in the left side,
    before Z, so its table gives them the indices the table of the sentence without the cut gives
    them. A rule whose right side holds a variable first met after Z (one the left side does not
    bind) has two tables that differ by a permutation of those variables: that case is not covered
    by a statement here.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Faithful KoreAML ML

namespace RuleAndIn

def topC : Kore.KSort := srt "GeneratedTopCell"

/-- The context of the `k` cell's first item at the sort X: `<generatedTop>(<k>(kseq(inj{X,
KItem}(·), k)), counter)`. -/
def cellCtx (X : String) (k counter : Kore.Pattern) : KoreCutCtx :=
  .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] []
      (.app ⟨⟨"kseq"⟩⟩ [] [] (.app ⟨⟨"inj"⟩⟩ [srt X, srt "KItem"] [] .hole []) [k]) []) [counter]

/-- The right argument of the `\rewrites` axiom at the place i of the text's last module. -/
def rewritesRight (k : Kore.Definition) (i : Nat) : Option Kore.Pattern :=
  match k.modules.getLast?.bind (·.sentences[i]?) with
  | some (.axiom a) => match a.pattern with
    | .rewrites _ _ r => some r
    | _ => none
  | _ => none

/-- The text's spelling of the three canonical names of the rule's variables. -/
def spell (n : String) (_ : Kore.KSort) : String :=
  if n == "VarV0" then "VarX" else if n == "VarV1" then "Var'Unds'DotVar1"
  else if n == "VarV2" then "Var'Unds'DotVar0" else n

namespace Fresh

kore_term kore from "f2-examples/mlandt.kompile.kore"
definition_of defn from "f2-examples/mlandt.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

example : c.sortName 3 = "Int" ∧ c.sortName 0 = "K" ∧ c.sortName 19 = "GeneratedCounterCell" ∧
    c.symName 388 = "Lblf" ∧ c.symName 389 = "Lblg" ∧ c.symName 386 = "Lblgo" := by decide +kernel

def cfg (s : Srt) (x : Term) : Term := .app 71 [.app 383 [.app 0 [.inj s 1 x, .var 1]], .var 2]

/-- `go(X) => ?Z` with `post := Z ∈ f(X) ∧ Z ∈ g(X)`, Z:Int the fourth variable. -/
def rz : Rule :=
  { vars := [3, 0, 19, 3], lhs := cfg 32 (.app 386 [.var 0]), req := none, rhs := cfg 3 (.var 3), ens := none,
    prio := 50, exs := [3],
    post := .and (.mem 3 (.var 3) (.app 388 [.var 0])) (.mem 3 (.var 3) (.app 389 [.var 0])) }

/-- The reader reads the text's rule as `rz` (`Parse.ruleBody` through the cut). -/
theorem read : c.rules = [rz] := rfl

def S : Kore.KSort := srt "Int"
def z : Kore.EVar := evar "VarV3" S
def x : Kore.Pattern := ev "VarV0" S
def t : Kore.Pattern := ap "Lblf" [x]
def u : Kore.Pattern := ap "Lblg" [x]
def E : Kore.Pattern := .top topC
def K : KoreCutCtx := cellCtx "Int" (ev "VarV1" (srt "K")) (ev "VarV2" (srt "GeneratedCounterCell"))

/-- The theorem's right pattern: the right side with the conjunction in its position. -/
def right : Kore.Pattern := .and topC [K.fill (.and S [t, u]), E]

theorem left_eq : ruleRight c rz =
    .exist topC z (.and topC [K.fill (.var (.evar z)), E,
      .and topC [.in S topC (.var (.evar z)) t, .in S topC (.var (.evar z)) u]]) := by decide +kernel

theorem right_text : some (renVars spell (fun n _ => n) right) = rewritesRight kore 298 := by
  decide +kernel

theorem right_tie (r : Kore.Pattern) (h : rewritesRight kore 298 = some r) :
    tr ⟨tableOf [] r, []⟩ r = tr ⟨tableOf [] right, []⟩ right := by
  have hr : r = renVars spell (fun n _ => n) right := by
    have := right_text; rw [h] at this; exact (Option.some.inj this).symm
  rw [hr]
  exact tr_occurrence_order spell (fun n _ => n) [] [] right (by decide +kernel)

/-- **`rule_and_in` at the fixture**: `ruleRight c rz` is the right side with the conjunction in
its position, under the theorem's premises at a table without aliases. -/
theorem tie {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ⟨tbl, []⟩ (tbl.ev (evarKey z)))
    (ht : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ t))
    (hu : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ u))
    (hE : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ E))
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hin : ∀ a, (tr ⟨tbl, []⟩ (.and S [t, u])).interpret I e a → Inh I σ a)
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill (.and S [t, u]))).interpret I e m → Inh I σ' m) (m : M) :
    (tr ⟨tbl, []⟩ (ruleRight c rz)).interpret I e m ↔ (tr ⟨tbl, []⟩ right).interpret I e m := by
  rw [left_eq]
  exact rule_and_in hD hc ⟨tbl, []⟩ K rfl S topC z rfl t u E e hsides ht hu hE hSz hCz hS hC hσ hσ' hin hout m

/-- The rule's sentence without the cut, over the canonical names: its left side and the right
side with the conjunction in its position. -/
noncomputable def plain : Kore.Pattern :=
  .rewrites topC (.and topC [Term.kore c (canonVars c rz.vars) rz.lhs, .top topC]) right

/-- The table of the rule's sentence and the table of the sentence without the cut give each
variable of the right side one index: each is met in the left side, before Z. -/
theorem tables : ∀ k ∈ varsOf right,
    (tableOf [] (prioRuleK c rz)).index k = (tableOf [] plain).index k := by decide +kernel

end Fresh

namespace Var

kore_term kore from "f2-examples/mlandc.kompile.kore"
definition_of defn from "f2-examples/mlandc.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

example : c.sortName 32 = "Exp" ∧ c.sortName 0 = "K" ∧ c.sortName 19 = "GeneratedCounterCell" ∧
    c.symName 385 = "Lbla" ∧ c.symName 387 = "Lblc" := by decide +kernel

def cfg (x : Term) : Term := .app 71 [.app 383 [.app 0 [.inj 32 1 x, .var 1]], .var 2]

/-- `c(X) => X` with `post := X ∈ a`. -/
def rv : Rule :=
  { vars := [32, 0, 19], lhs := cfg (.app 387 [.var 0]), req := none, rhs := cfg (.var 0), ens := none,
    prio := 50, post := .mem 32 (.var 0) (.app 385 []) }

/-- The reader reads the text's rule as `rv` (`Parse.ruleBody` through the cut). -/
theorem read : c.rules = [rv] := rfl

def S : Kore.KSort := srt "Exp"
def v : Kore.EVar := evar "VarV0" S
def u : Kore.Pattern := ap "Lbla" []
def E : Kore.Pattern := .top topC
def K : KoreCutCtx := cellCtx "Exp" (ev "VarV1" (srt "K")) (ev "VarV2" (srt "GeneratedCounterCell"))

/-- The theorem's right pattern: the right side with the conjunction in its position. -/
def right : Kore.Pattern := .and topC [K.fill (.and S [.var (.evar v), u]), E]

theorem left_eq : ruleRight c rv =
    .and topC [K.fill (.var (.evar v)), E, .in S topC (.var (.evar v)) u] := by decide +kernel

theorem right_text : some (renVars spell (fun n _ => n) right) = rewritesRight kore 200 := by
  decide +kernel

theorem right_tie (r : Kore.Pattern) (h : rewritesRight kore 200 = some r) :
    tr ⟨tableOf [] r, []⟩ r = tr ⟨tableOf [] right, []⟩ right := by
  have hr : r = renVars spell (fun n _ => n) right := by
    have := right_text; rw [h] at this; exact (Option.some.inj this).symm
  rw [hr]
  exact tr_occurrence_order spell (fun n _ => n) [] [] right (by decide +kernel)

/-- **`rule_and_var` at the fixture**: `ruleRight c rv` is the right side with the conjunction in
its position, under the theorem's premises at a table without aliases. -/
theorem tie {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hv : Inh I σ (e.evalEvar (tbl.ev (evarKey v))))
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill (.var (.evar v)))).interpret I e m → Inh I σ' m) (m : M) :
    (tr ⟨tbl, []⟩ (ruleRight c rv)).interpret I e m ↔ (tr ⟨tbl, []⟩ right).interpret I e m := by
  rw [left_eq]
  exact rule_and_var hD hc ⟨tbl, []⟩ K rfl S topC v u E e hS hC hσ hσ' hv hout m

end Var

end RuleAndIn
