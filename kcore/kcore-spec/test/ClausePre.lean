/-
  A clause with a predicate in its premise (`Clause.pre`): CN-4 §4.9's expectation, on a semantics
  built by hand against the existing field `Clause.pre` (Core.lean, `structure Clause`). The
  statements are written as propositions (`expect…`) and each is proved: those on the sentences
  (`exclusion_pre`, `sentence_pre`, `sentence1_pre`), `coreOK` (`coreOK_ok`), and those on `Eval`'s
  results (`u_results`, `g_at0`, `g_at2`); `expect_ok` is the whole.
  Run from the package root: `lake env lean -j1 test/ClausePre.lean`. Kernel-checked.

  The semantics `c`, two functions over Int:
  - `u(X:Int) => X ensures X >Int 0` (`uCl`). Its one clause matches every Int, so at `x ≤ 0` the
    clause decides and its `ensures` is not `true`: `u(x)` has no value there (`Eval.ensFails`:
    `rhs ∧ ⊥` is empty), and the rest is not read; at `x > 0`, `u(x)` is `x`. `>Int` is a hook of
    the registry, total on Int, so this holds under every interpretation of the parameters
    (`expectU`).
  - `g(X:Int)` with two clauses: `gCl1`, `pre := ⌈u(X)⌉`, `rhs := 1`, of priority 50, and `gCl2`,
    `rhs := 0`, of priority 200.

  What the text of `g` states, read as a matching-logic theory (CN-4 §4.9, "What each text
  states"): the first clause's sentence is `⊤ ∧ X0 ∈ X ∧ ⌈u(X)⌉ → g(X0) = 1`, the second's
  `¬ ∃X'. (⊤ ∧ X0 ∈ X' ∧ ⌈u(X')⌉) ∧ ⊤ ∧ X0 ∈ X → g(X0) = 0`. So:
  - at 0, `⌈u(0)⌉` is false (u(0) has no value): the first clause does not apply, the second's
    premise holds, `g(0) = 0`, and nothing else (`expectAt0`);
  - at 2, `⌈u(2)⌉` is true (u(2) is 2): the first clause applies, `g(2) = 1`, and the second's
    premise is false there, so nothing else (`expectAt2`).
  In `Eval`'s terms after e3 (CN-4 §4.9's first Lean block): at 0, `gCl1` fails by `ReqFails.pre`
  (`Holds … (.ceil Srt.int (u(X))) false`, by `Holds.ceil` at the result `none`), so `gCl2`
  decides; at 2, `gCl1` meets `hpre` (`Holds.ceil` at `some 2`) and decides, and `gCl2` is blocked
  since `gCl1` does not fail.

  `clausesPlain` admits `gCl1` (a predicate in the premise, conditions that need no witness), so
  `coreOK` holds (`clausesPlain_ok`, `coreOK_ok`: `expectCore`). The sentences
  carry the predicate (`withPre`, Emit.lean, in `exclusion`, `clauseEquation` and
  `competingEquation`): the second clause's sentence negates `∃X'. ((⊤ ∧ X0 ∈ X') ∧ ⌈u(X')⌉)`
  (`exclusion_pre`, `sentence_pre`), which is not the text without the predicate
  (`exclusion_ne_plain`).

  The results at every Int x: `u(x)` is x where x > 0 and has no value elsewhere (`evalU_mk`,
  `evalU_inv`, under every interpretation of the parameters), `⌈u(X)⌉` has the truth value x > 0
  and no other (`holdsPre_mk`, `holdsPre_inv`), and `g(x)` is 1 where x > 0 and 0 elsewhere, and
  nothing else (`evalG_mk`, `evalG_inv`). So `c` meets `FnDet`, `FnSolves`, `ClausePreDecided` and
  `OpenLaws`, and `Γ` has a model (`consistent`, by `consistent_of`).

  The lemmas for a clause with a predicate, at `g`, none through a `\top` predicate
  (`not_preTop`): `eval_den4ClPre` in every model of `Γc c` with its hypotheses `hcls`, `hneg` and
  `hpreR` discharged (`hcls_c`, `hneg_c`, `hpreR_c`; `den_g`, `den_g0`, `den_g2`), `gCl1` being a
  clause `hpreR` and `hneg` are read at (`gCl1_read`); and in the value model `satFnsGoalPre`
  (`satFns`), `sat_clauseEqPre` at `gCl1` (`sat_gCl1`) and `sat_competingEqPre` at `gCl2` under the
  negation of `gCl1`'s exclusion (`sat_gCl2`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace ClausePre

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)
open Faithful (canonVars canonClausePres eqnSentence competingPremise clauseEquation competingEquation
  prioEquation lowerClauses fnEquationsK)
open KoreAML (R)

/-- An integer literal, as a term and as a value. -/
def iT (i : Int) : Term := .dv Srt.int (.int i)
def iv (i : Int) : GroundTerm := .dv Srt.int (.int i)

/-- The symbols after the four cell symbols: u, g. -/
def U : Sym := nRegSyms + 4
def G : Sym := nRegSyms + 5

/-- `u(X)`, X the variable 0. -/
def uX : Term := .app U [.var 0]

/-- `u(X) => X ensures X >Int 0`. -/
def uCl : Clause := ⟨[Srt.int], [.var 0], none, .var 0, some (.app intGt [.var 0, iT 0]), 50, false, [], .top, .top⟩
def uFn : Fn := ⟨U, [Srt.int], Srt.int, [uCl], false⟩

/-- `⌈u(X)⌉`. -/
def pre1 : Cond := .ceil Srt.int uX

/-- `g(X) => 1` where `⌈u(X)⌉`, of priority 50. -/
def gCl1 : Clause := ⟨[Srt.int], [.var 0], none, iT 1, none, 50, false, [], pre1, .top⟩
/-- `g(X) => 0`, of priority 200. -/
def gCl2 : Clause := ⟨[Srt.int], [.var 0], none, iT 0, none, 200, false, [], .top, .top⟩
def gFn : Fn := ⟨G, [Srt.int], Srt.int, [gCl1, gCl2], false⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblu", "Lblg"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [uFn, gFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

/-! ## What is decided today -/

/-- The names: `u`, `g`, and the registry's `>Int`. -/
theorem names : c.symName U = "Lblu" ∧ c.symName G = "Lblg" ∧ c.symName intGt = "Lbl'Unds-GT-'Int'Unds'" ∧
    c.sortName Srt.int = "Int" := by decide +kernel

theorem lookups : c.lookupFn U = some uFn ∧ c.lookupFn G = some gFn := ⟨rfl, rfl⟩

/-- `>Int` is a hook, not a constructor, a parameter or an overload; `u` and `g` are none of these
(what `EvalTerm.hook` and `EvalTerm.call` ask). -/
theorem kinds : isHook intGt = true ∧ c.isCtor intGt = false ∧
    c.isCtor U = false ∧ isHook U = false ∧ c.isParam U = false ∧ c.isOvl U = false ∧
    c.isCtor G = false ∧ isHook G = false ∧ c.isParam G = false ∧ c.isOvl G = false := by decide +kernel

/-- `>Int` at 0 and at 2, against 0: `false` and `true` (Hooks.lean), so `u(0)`'s `ensures` is not
`true` and `u(2)`'s is. -/
theorem gt_at : c.hookRes intGt [iv 0, iv 0] = some (some (bool false)) ∧
    c.hookRes intGt [iv 2, iv 0] = some (some (bool true)) := by decide +kernel

/-- `gCl1` is of a smaller priority than `gCl2` and not `aside`: it is `gCl2`'s one competitor, and
has none itself. -/
theorem lower : lowerClauses gFn gCl2 = [gCl1] ∧ lowerClauses gFn gCl1 = [] := ⟨rfl, rfl⟩

/-- `gCl1`'s predicate is well sorted over its variables (the conjunct `clauseSorted` gains, CN-4
§4.9), and reads the variable its pattern binds (X, once from the pattern and once from the
predicate in `leftVars`): no open condition variable. -/
theorem pre_ok : c.condOK gCl1.vars gCl1.pre = true ∧ gCl1.condVars = [0] ∧ gCl1.leftVars = [0, 0] ∧
    gCl1.openCondVars = [] := by
  decide +kernel

/-- CN-4 §4.9's final text of what `clausesPlain` asks of one clause (to run): no `\exists`
variable, a `\top` right-side predicate, and the conjunct on open condition variables; the
premise predicate `pre` is admitted. -/
def clauseE3 (c : Semantics) (cl : Clause) : Bool :=
  cl.exs.isEmpty && cl.post.isTop &&
  (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false)

/-- `sortedOK` without `clausesPlain`. -/
def sortedRest (c : Semantics) : Bool :=
  c.subsortsOK && c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) &&
    c.rules.all c.ruleSorted && c.rulesPlain && c.paramsPlain

/-- `coreOK` without `sortedOK`. -/
def coreRest (c : Semantics) : Bool :=
  c.faithCoreOK && c.hooksApart && c.predsApart && c.idsOK && c.overloadsOK

/-- `sortedOK` is `sortedRest` with `clausesPlain`. -/
theorem sortedOK_eq (c : Semantics) : c.sortedOK = (sortedRest c && c.clausesPlain) := by
  simp only [Semantics.sortedOK, sortedRest, Bool.and_assoc, Bool.and_comm c.clausesPlain]

/-- `coreOK` is `sortedOK` with `coreRest`. -/
theorem coreOK_eq (c : Semantics) : c.coreOK = (c.sortedOK && coreRest c) := by
  simp only [Semantics.coreOK, coreRest, Bool.and_assoc]

/-- Every condition of `coreOK` but `clausesPlain` holds. -/
theorem sortedRest_ok : sortedRest c = true := by decide +kernel
theorem coreRest_ok : coreRest c = true := by decide +kernel
/-- Every clause meets CN-4 §4.9's final clause conjunct. -/
theorem clauseE3_ok : c.fns.all (fun f => f.clauses.all (clauseE3 c)) = true := by decide +kernel
/-- `clausesPlain` admits `gCl1`: its predicate is not `\top` and its conditions need no witness. -/
theorem clausesPlain_ok : c.clausesPlain = true := by decide +kernel
/-- So `coreOK` holds. -/
theorem coreOK_ok : c.coreOK = true := by
  rw [coreOK_eq, sortedOK_eq, clausesPlain_ok, sortedRest_ok, coreRest_ok]; rfl

/-! ## The second clause's sentence -/

/-- g's argument sorts by name, and the variables of each clause (one, X:Int) as the sentences
name them. -/
def gArgs : List String := gFn.args.map c.sortName
def vs1 : List KoreAML.Var := canonVars c gCl1.vars
def vs2 : List KoreAML.Var := canonVars c gCl2.vars

/-- The landed premise of `gCl1` under its own variables: `⊤ ∧ X0 ∈ X'`. -/
def prem1 : Kore.Pattern := premise gArgs (gCl1.req.map (Term.kore c vs1)) (Term.koreList c vs1 gCl1.pats)

/-- `gCl1`'s exclusion without its predicate, `∃X'. (⊤ ∧ X0 ∈ X')`: the text before the sentences
read `Clause.pre`, and the text of a clause like `gCl1` whose `pre` is `\top`. -/
def exclNow : Kore.Pattern := KoreAML.existsAll R (vs1.map KoreAML.Var.kore) prem1

/-- `gCl1`'s exclusion with its predicate (CN-4 §4.9, `withPre` at a `pre` that is not `\top`, in
`exclusion`): `∃X'. ((⊤ ∧ X0 ∈ X') ∧ ⌈u(X')⌉)`. -/
def exclPre : Kore.Pattern :=
  KoreAML.existsAll R (vs1.map KoreAML.Var.kore) (.and R [prem1, Cond.kore c vs1 R gCl1.pre])

/-- `gCl2`'s sentence over the exclusion `e` of `gCl1`: `¬ (e ∨ ⊥) ∧ (⊤ ∧ X0 ∈ X) → g(X0) = 0 ∧ ⊤`
(`gCl2`'s own premise is the landed one: its `pre` is `\top`, CN-4 §4.9 `withPre`). -/
def sentence2 (e : Kore.Pattern) : Kore.Sentence :=
  eqnSentence c gFn (competingPremise gArgs [e] (gCl2.req.map (Term.kore c vs2)) (Term.koreList c vs2 gCl2.pats))
    (Term.kore c vs2 gCl2.rhs) (reqPat (srtOf c gFn.result) (gCl2.ens.map (Term.kore c vs2)))

/-- The predicate as the sentence writes it: `\ceil{SortInt{}, R}(Lblu(X'))`, X' the clause's
variable. -/
theorem pre_kore : Cond.kore c vs1 R gCl1.pre =
    .ceil (KoreAML.srt "Int") R (.app ⟨⟨"Lblu"⟩⟩ [] [KoreAML.varAt vs1 0]) := by rfl

/-- **Expected** (proved: `exclusion_pre`): `gCl1`'s exclusion carries its predicate. -/
def expectExclusion : Prop := exclusion c gFn gCl1 (canonClausePres gCl1) = exclPre

/-- `gCl1`'s exclusion is `exclPre`: `∃X'. ((⊤ ∧ X0 ∈ X') ∧ ⌈u(X')⌉)` (`withPre` at a `pre` that is
not `\top`). -/
theorem exclusion_pre : expectExclusion := by unfold expectExclusion; rfl

/-- The exclusion with the predicate is not the one without it (`exclNow`). -/
theorem exclusion_ne_plain : exclusion c gFn gCl1 (canonClausePres gCl1) ≠ exclNow := by
  rw [show exclusion c gFn gCl1 (canonClausePres gCl1) = exclPre from exclusion_pre]; decide +kernel

/-- With `gCl1`'s predicate `\top` in place of `⌈u(X)⌉` the exclusion is `exclNow`, the text
without a predicate (`withPre` at `\top`). -/
theorem exclusion_top_plain :
    exclusion c gFn { gCl1 with pre := .top } (canonClausePres { gCl1 with pre := .top }) = exclNow := by rfl

/-- **Expected** (proved: `sentence_pre`): `Γ`'s sentence for the second clause (`prioEquation`, an
element of `fnEquationsK c gFn`, so of `fnItems` and `ΓFns`) carries the negated existential
`¬ ∃X'. (X0 ∈ X' ∧ ⌈u(X')⌉)`. -/
def expectSentence : Prop :=
  prioEquation c gFn gCl2 = sentence2 exclPre ∧ prioEquation c gFn gCl2 ∈ fnEquationsK c gFn

/-- `Γ`'s sentence for the second clause negates `exclPre`, and is one of `g`'s equations. -/
theorem sentence_pre : expectSentence :=
  ⟨by rfl, List.mem_map.mpr ⟨gCl2, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl⟩⟩

/-- **Expected** (proved: `sentence1_pre`): the first clause's sentence has the premise
`(⊤ ∧ X0 ∈ X) ∧ ⌈u(X)⌉`. -/
def expectSentence1 : Prop :=
  prioEquation c gFn gCl1 =
    eqnSentence c gFn (.and R [prem1, Cond.kore c vs1 R gCl1.pre])
      (Term.kore c vs1 gCl1.rhs) (reqPat (srtOf c gFn.result) (gCl1.ens.map (Term.kore c vs1)))

/-- The first clause's sentence has the premise `(⊤ ∧ X0 ∈ X) ∧ ⌈u(X)⌉`. -/
theorem sentence1_pre : expectSentence1 := by unfold expectSentence1; rfl

/-! ## The emitted equations (`Emit.clauseAx`)

The text `kcore` writes for a clause (`clauseAx`, read by `fnEquations`) has the premise `Γ`'s
sentence for it has: `gCl1`'s own equation states `g(X0) = 1` under `(⊤ ∧ X0 ∈ X) ∧ ⌈u(X)⌉`, the
body `gCl2`'s `[owise]` premise negates under `∃X'` (`exclPre`). Before `clauseAx` read
`Clause.pre` the first was `⊤ ∧ X0 ∈ X → g(X0) = 1` beside the second's
`¬ ∃X'. ((⊤ ∧ X0 ∈ X') ∧ ⌈u(X')⌉)`: at 0 both premises hold and the text states `g(0) = 1` and
`g(0) = 0`. The presentation is the canonical one (`canonFnPres`, `canonClausePres`); `p` bears on
the attributes only. -/

/-- `gCl1`'s emitted equation has the premise `(⊤ ∧ X0 ∈ X) ∧ ⌈u(X)⌉`, the premise of `Γ`'s
sentence for it (`sentence1_pre`). -/
theorem clauseAx_pre (p : Presentation) :
    clauseAx c p gFn (Faithful.canonFnPres gFn) gCl1 (canonClausePres gCl1) =
      KoreAML.equationAx "Lblg" gArgs "Int" (.and R [prem1, Cond.kore c vs1 R gCl1.pre])
        (Term.kore c vs1 gCl1.rhs) (reqPat (srtOf c gFn.result) (gCl1.ens.map (Term.kore c vs1)))
        (metaAttrs p (canonClausePres gCl1).info none none) := by rfl

/-- With `gCl1`'s predicate `\top` the emitted equation has the premise `⊤ ∧ X0 ∈ X` alone
(`clauseAx_top`): the text before `clauseAx` read `Clause.pre`. -/
theorem clauseAx_top_plain (p : Presentation) :
    clauseAx c p gFn (Faithful.canonFnPres gFn) { gCl1 with pre := .top } (canonClausePres gCl1) =
      KoreAML.equationAx "Lblg" gArgs "Int" prem1
        (Term.kore c vs1 gCl1.rhs) (reqPat (srtOf c gFn.result) (gCl1.ens.map (Term.kore c vs1)))
        (metaAttrs p (canonClausePres gCl1).info none none) := by
  rw [clauseAx_top rfl]; rfl

/-- The two differ: the predicate is in the emitted premise. -/
theorem clauseAx_pre_ne_plain (p : Presentation) :
    clauseAx c p gFn (Faithful.canonFnPres gFn) gCl1 (canonClausePres gCl1) ≠
      clauseAx c p gFn (Faithful.canonFnPres gFn) { gCl1 with pre := .top } (canonClausePres gCl1) := by
  rw [clauseAx_pre, clauseAx_top_plain]
  intro h
  have h' : some (Kore.Pattern.and R [prem1, Cond.kore c vs1 R gCl1.pre]) = some prem1 :=
    congrArg (fun s => match s with
      | Kore.Sentence.axiom ax => (match ax.pattern with | .implies _ a _ => some a | _ => none)
      | _ => none) h
  exact absurd h' (by decide +kernel)

/-- `gCl2`'s emitted `[owise]` equation negates `exclPre`, the exclusion of `gCl1` with its
predicate, over its own premise `⊤ ∧ X0 ∈ X` (its `pre` is `\top`): the premise of `Γ`'s sentence
for it (`sentence_pre`, `sentence2 exclPre`). -/
theorem clauseAx_owise (p : Presentation) :
    clauseAx c p gFn (Faithful.canonFnPres gFn) gCl2 (canonClausePres gCl2) =
      KoreAML.equationAx "Lblg" gArgs "Int"
        (competingPremise gArgs [exclPre] (gCl2.req.map (Term.kore c vs2)) (Term.koreList c vs2 gCl2.pats))
        (Term.kore c vs2 gCl2.rhs) (reqPat (srtOf c gFn.result) (gCl2.ens.map (Term.kore c vs2)))
        (sortAttrs (metaAttrs p (canonClausePres gCl2).info none none ++ [KoreAML.attr "owise"])) := by rfl

/-! ## The results -/

/-- `f`'s result at `[iv x]` in `d` is `r` and only `r`. -/
def OnlyResult (d : Semantics) (f : Sym) (x : Int) (r : Option GroundTerm) : Prop :=
  Eval d f [iv x] r ∧ ∀ r', Eval d f [iv x] r' → r' = r

/-- **Expected** (proved: `coreOK_ok`): `coreOK` holds. -/
def expectCore : Prop := c.coreOK = true

/-- **Expected** (proved: `u_results`): `u(0)` has no value, by `Eval.ensFails`, and `u(2)` is
2, under every interpretation of the parameters. -/
def expectU : Prop :=
  ∀ H : HookParams, OnlyResult (c.withHooks H) U 0 none ∧ OnlyResult (c.withHooks H) U 2 (some (iv 2))

/-- **Expected** (proved: `g_at0`): `g(0)` is 0 and nothing else: `⌈u(0)⌉` is false, so
the first clause fails (`ReqFails.pre`) and the second decides. -/
def expectAt0 : Prop := OnlyResult c G 0 (some (iv 0))

/-- **Expected** (proved: `g_at2`): `g(2)` is 1 and nothing else: `⌈u(2)⌉` is true, so
the first clause decides (`hpre`) and blocks the second. -/
def expectAt2 : Prop := OnlyResult c G 2 (some (iv 1))

/-- The expectation of CN-4 §4.9, whole. -/
def expect : Prop :=
  expectCore ∧ expectU ∧ expectAt0 ∧ expectAt2 ∧ expectExclusion ∧ expectSentence ∧ expectSentence1


/-! ## `u`'s results, under every interpretation of the parameters -/

theorem ifT {α : Type} {p : Prop} [Decidable p] (h : p) {a b : α} : (if p then a else b) = a := by simp [h]
theorem ifF {α : Type} {p : Prop} [Decidable p] (h : ¬ p) {a b : α} : (if p then a else b) = b := by simp [h]

/-- `c` under the interpretation `H` of the parameters; `c` itself is `cH c.hooks`. -/
abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem lookupsH (H : HookParams) : (cH H).lookupFn U = some uFn ∧ (cH H).lookupFn G = some gFn := ⟨rfl, rfl⟩

/-- `kinds` under `H`: none of these reads the interpretation. -/
theorem kindsH (H : HookParams) : (cH H).isCtor intGt = false ∧ (cH H).isOvl intGt = false ∧
    (cH H).isCtor U = false ∧ (cH H).isParam U = false ∧ (cH H).isOvl U = false :=
  (by decide +kernel : c.isCtor intGt = false ∧ c.isOvl intGt = false ∧
    c.isCtor U = false ∧ c.isParam U = false ∧ c.isOvl U = false)

theorem match0 {d : Semantics} {σ : Subst} {vs : List GroundTerm} (h : PatVals d σ [.var 0] vs) :
    ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
  rw [PatVals.nil_inv hs]
  exact ⟨v, rfl, PatVal.var_inv hv⟩

/-- The substitution that gives the one variable the value `v`. -/
def sg (v : GroundTerm) : Subst := [(0, v)]

theorem sg_sortedAt {d : Semantics} {v : GroundTerm} (hv : d.sortOf v = some Srt.int) (is : List Nat) :
    d.WellSortedAt [Srt.int] is (sg v) := by
  intro i _ s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨v, rfl, hv⟩
  | succ i => simp at hs

theorem sg_sorted {d : Semantics} {v : GroundTerm} (hv : d.sortOf v = some Srt.int) : d.WellSorted [Srt.int] (sg v) := by
  intro i s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨v, rfl, hv⟩
  | succ i => simp at hs

theorem sg_match {d : Semantics} (v : GroundTerm) : PatVals d (sg v) [.var 0] [v] := .cons (.var rfl) .nil

theorem iv_sort (d : Semantics) (x : Int) : d.sortOf (iv x) = some Srt.int := sortOf_int x

/-- `>Int` at an Int against 0, under every interpretation: the registry's hook has a value. -/
theorem gt_res (H : HookParams) (x : Int) :
    (cH H).hookRes intGt [iv x, iv 0] = some (some (bool (decide (x > 0)))) :=
  Semantics.hookRes_of_value (by rw [Det.hook_intGt]; rfl)

theorem allSome2 (a b : GroundTerm) : allSome [some a, some b] = some [a, b] := rfl
theorem allSome1 (a : GroundTerm) : allSome [some a] = some [a] := rfl

/-- `X >Int 0` has the result `x > 0` where X is the Int x. -/
theorem evalGt_mk (H : HookParams) {σ : Subst} {x : Int} (hl : σ.lookup 0 = some (iv x)) :
    EvalTerm (cH H) σ (.app intGt [.var 0, iT 0]) (some (bool (decide (x > 0)))) :=
  .hook (kindsH H).1 kinds.1 (.cons .var (.cons .dv .nil))
    (fun vs hvs => by
      rw [hl] at hvs
      have hv : vs = [iv x, iv 0] := Option.some.inj (hvs.symm.trans (allSome2 _ _))
      subst hv; exact gt_res H x)
    (fun hn => by rw [hl] at hn; exact absurd (hn.symm.trans (allSome2 _ _)) (by simp))

/-- `X >Int 0` has no other result. -/
theorem evalGt_inv {H : HookParams} {σ : Subst} {x : Int} (hl : σ.lookup 0 = some (iv x))
    {w : Option GroundTerm} (h : EvalTerm (cH H) σ (.app intGt [.var 0, iT 0]) w) :
    w = some (bool (decide (x > 0))) := by
  cases h with
  | ctor hk _ => exact absurd ((kindsH H).1.symm.trans hk) (by simp)
  | hook _ _ hts hh _ =>
    cases hts with
    | cons h1 hs =>
      cases hs with
      | cons h2 hs2 =>
        cases hs2; cases h1; cases h2
        rw [hl] at hh
        have := (hh _ (allSome2 _ _)).symm.trans (gt_res H x)
        exact (Option.some.inj this)
  | param _ hhk _ _ _ => exact absurd (kinds.1.symm.trans hhk) (by simp)
  | call _ hhk _ _ _ _ => exact absurd (kinds.1.symm.trans hhk) (by simp)
  | callUndef _ hhk _ _ _ => exact absurd (kinds.1.symm.trans hhk) (by simp)
  | ovl _ ho _ _ => exact absurd ((kindsH H).2.1.symm.trans ho) (by simp)
  | ovlFn _ ho _ _ _ _ _ => exact absurd ((kindsH H).2.1.symm.trans ho) (by simp)

theorem gt_true {x : Int} (h : some (bool true) = some (bool (decide (x > 0)))) : x > 0 :=
  of_decide_eq_true (by
    have : bool true = bool (decide (x > 0)) := Option.some.inj h
    simpa [bool] using this.symm)

theorem uCl_of {cl : Clause} (h : cl ∈ uFn.clauses) : cl = uCl := by simpa [uFn] using h

/-- `u` at the Int x: x where x > 0, and no value elsewhere. -/
def uRes (x : Int) : Option GroundTerm := if x > 0 then some (iv x) else none

/-- **`u(x)` has the result `uRes x`**: its clause decides at every Int, with its `ensures` `true`
where x > 0 (`Eval.clause`) and `false` elsewhere (`Eval.ensFails`). -/
theorem evalU_mk (H : HookParams) (x : Int) : Eval (cH H) U [iv x] (uRes x) := by
  have hprio : ∀ cl' ∈ uFn.clauses, cl'.aside = false → cl'.prio < uCl.prio → Fails (cH H) [iv x] cl' :=
    fun cl' hcl' _ hlt => by rw [uCl_of hcl'] at hlt; exact absurd hlt (Nat.lt_irrefl _)
  have hg := evalGt_mk H (σ := sg (iv x)) (x := x) rfl
  by_cases hx : x > 0
  · rw [uRes, ifT hx]
    rw [decide_eq_true hx] at hg
    exact .clause (fn := uFn) (cl := uCl) (σ := sg (iv x)) (lookupsH H).1 (List.mem_singleton_self _)
      (sg_sorted (iv_sort _ x)) (sg_match _) (fun t ht => nomatch ht) .top hprio rfl .var
      (fun t ht => by cases ht; exact hg) .top
  · rw [uRes, ifF hx]
    rw [decide_eq_false hx] at hg
    exact .ensFails (fn := uFn) (cl := uCl) (σ := sg (iv x)) (lookupsH H).1 (List.mem_singleton_self _)
      (sg_sorted (iv_sort _ x)) (sg_match _) (fun t ht => nomatch ht) .top hprio rfl rfl hg
      (by intro h; cases h)

/-- **`u(x)` has no other result.** -/
theorem evalU_inv {H : HookParams} {x : Int} {r : Option GroundTerm} (h : Eval (cH H) U [iv x] r) :
    r = uRes x := by
  cases h with
  | clause hfn hcl hσ hm _ _ _ _ hrhs hens _ =>
    obtain rfl := Option.some.inj ((lookupsH H).1.symm.trans hfn)
    obtain rfl := uCl_of hcl
    obtain ⟨w, hw, hl⟩ := match0 hm
    cases hw
    have hg := evalGt_inv hl (hens _ rfl)
    have hx : x > 0 := gt_true hg
    rw [uRes, ifT hx, ← hl]
    exact EvalTerm.var_inv hrhs
  | rest hfn hnone =>
    obtain rfl := Option.some.inj ((lookupsH H).1.symm.trans hfn)
    cases hnone uCl (List.mem_singleton_self _) with
    | intro h =>
      cases h (sg (iv x)) (sg_sortedAt (iv_sort _ x) _) (sg_match _) with
      | intro ht _ _ => cases ht
      | pre hp => exact absurd hp.top_eq (by simp)
  | ensFails hfn hcl hσ hm _ _ _ _ ht he hw =>
    obtain rfl := Option.some.inj ((lookupsH H).1.symm.trans hfn)
    obtain rfl := uCl_of hcl
    obtain ⟨w', hw', hl⟩ := match0 hm
    cases hw'
    cases ht
    have hg := evalGt_inv hl he
    by_cases hx : x > 0
    · rw [decide_eq_true hx] at hg; exact absurd hg hw
    · rw [uRes, ifF hx]
  | clauseEx hfn hcl _ _ _ _ _ hne _ _ _ _ =>
    obtain rfl := Option.some.inj ((lookupsH H).1.symm.trans hfn)
    obtain rfl := uCl_of hcl
    exact absurd rfl hne
  | exNone hfn hcl hne _ _ _ _ _ _ _ =>
    obtain rfl := Option.some.inj ((lookupsH H).1.symm.trans hfn)
    obtain rfl := uCl_of hcl
    exact absurd rfl hne

/-- **`u(0)` has no value and `u(2)` is 2, and nothing else, under every interpretation of the
parameters.** -/
theorem u_results : expectU := fun H =>
  ⟨⟨evalU_mk H 0, fun _ h => evalU_inv h⟩, ⟨evalU_mk H 2, fun _ h => evalU_inv h⟩⟩

/-! ## `g`'s results -/

/-- `u(X)` has the result `uRes x` where X is the Int x. -/
theorem evalUX_mk {σ : Subst} {x : Int} (hl : σ.lookup 0 = some (iv x)) :
    EvalTerm c σ (.app U [.var 0]) (uRes x) :=
  .call (vs := [iv x]) kinds.2.2.1 kinds.2.2.2.1 (.cons .var .nil) (by rw [hl]; rfl) (evalU_mk c.hooks x)
    kinds.2.2.2.2.1

/-- `u(X)` has no other result. -/
theorem evalUX_inv {σ : Subst} {x : Int} (hl : σ.lookup 0 = some (iv x)) {r : Option GroundTerm}
    (h : EvalTerm c σ (.app U [.var 0]) r) : r = uRes x := by
  cases h with
  | ctor hk _ => exact absurd (kinds.2.2.1.symm.trans hk) (by simp)
  | hook _ hhk _ _ _ => exact absurd (kinds.2.2.2.1.symm.trans hhk) (by simp)
  | param _ _ hp _ _ => exact absurd (kinds.2.2.2.2.1.symm.trans hp) (by simp)
  | call _ _ hts hvs hf _ =>
    cases hts with
    | cons h1 hs =>
      cases hs; cases h1
      rw [hl] at hvs
      obtain rfl := Option.some.inj (hvs.symm.trans (allSome1 _))
      exact evalU_inv (H := c.hooks) hf
  | callUndef _ _ hts hvs _ =>
    cases hts with
    | cons h1 hs =>
      cases hs; cases h1
      rw [hl] at hvs
      exact absurd (hvs.symm.trans (allSome1 _)) (by simp)
  | ovl _ ho _ _ => exact absurd (kinds.2.2.2.2.2.1.symm.trans ho) (by simp)
  | ovlFn _ ho _ _ _ _ _ => exact absurd (kinds.2.2.2.2.2.1.symm.trans ho) (by simp)

/-- **`⌈u(X)⌉` has the truth value `x > 0`** where X is the Int x. -/
theorem holdsPre_mk {σ : Subst} {x : Int} (hl : σ.lookup 0 = some (iv x)) :
    Holds c 1 σ pre1 (decide (x > 0)) := by
  have he := evalUX_mk hl
  by_cases hx : x > 0
  · rw [uRes, ifT hx] at he; rw [decide_eq_true hx]; exact .ceil he
  · rw [uRes, ifF hx] at he; rw [decide_eq_false hx]; exact .ceil he

/-- **`⌈u(X)⌉` has no other truth value.** -/
theorem holdsPre_inv {σ : Subst} {x : Int} (hl : σ.lookup 0 = some (iv x)) {b : Bool}
    (h : Holds c 1 σ (.ceil Srt.int (.app U [.var 0])) b) : b = decide (x > 0) := by
  cases h with
  | ceil he =>
    rw [evalUX_inv hl he, uRes]
    by_cases hx : x > 0
    · rw [ifT hx, decide_eq_true hx]; rfl
    · rw [ifF hx, decide_eq_false hx]; rfl

theorem gCl_of {cl : Clause} (h : cl ∈ gFn.clauses) : cl = gCl1 ∨ cl = gCl2 := by simpa [gFn] using h

/-- `g` at the Int x: 1 where x > 0, and 0 elsewhere. -/
def gRes (x : Int) : GroundTerm := if x > 0 then iv 1 else iv 0

/-- **`g(x)` has the result `gRes x`**: where x > 0 the first clause's predicate is true and it
decides; elsewhere the predicate is false at every match (`ReqFails.pre`), the first clause fails
and the second decides. -/
theorem evalG_mk (x : Int) : Eval c G [iv x] (some (gRes x)) := by
  by_cases hx : x > 0
  · rw [gRes, ifT hx]
    have hp := holdsPre_mk (σ := sg (iv x)) (x := x) rfl
    rw [decide_eq_true hx] at hp
    exact .clause (fn := gFn) (cl := gCl1) (σ := sg (iv x)) lookups.2 (List.mem_cons_self ..)
      (sg_sorted (iv_sort _ x)) (sg_match _) (fun t ht => nomatch ht) hp
      (fun cl' hcl' _ hlt => by
        rcases gCl_of hcl' with rfl | rfl
        · exact absurd hlt (Nat.lt_irrefl _)
        · exact absurd hlt (by decide))
      rfl .dv (fun t ht => nomatch ht) .top
  · rw [gRes, ifF hx]
    exact .clause (fn := gFn) (cl := gCl2) (σ := sg (iv x)) lookups.2
      (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      (sg_sorted (iv_sort _ x)) (sg_match _) (fun t ht => nomatch ht) .top
      (fun cl' hcl' _ hlt => by
        rcases gCl_of hcl' with rfl | rfl
        · refine .intro fun σ _ hm => .pre ?_
          obtain ⟨w, hw, hl⟩ := match0 hm
          cases hw
          have hp := holdsPre_mk hl
          rwa [decide_eq_false hx] at hp
        · exact absurd hlt (Nat.lt_irrefl _))
      rfl .dv (fun t ht => nomatch ht) .top

/-- **`g(x)` has no other result.** -/
theorem evalG_inv {x : Int} {r : Option GroundTerm} (h : Eval c G [iv x] r) : r = some (gRes x) := by
  cases h with
  | clause hfn hcl hσ hm _ hpre hprio _ hrhs _ _ =>
    obtain rfl := Option.some.inj (lookups.2.symm.trans hfn)
    rcases gCl_of hcl with rfl | rfl
    · obtain ⟨w, hw, hl⟩ := match0 hm
      cases hw
      have hx : x > 0 := of_decide_eq_true (holdsPre_inv hl hpre).symm
      rw [gRes, ifT hx]
      exact EvalTerm.dv_inv hrhs
    · have hx : ¬ x > 0 := by
        cases hprio gCl1 (List.mem_cons_self ..) rfl (by decide) with
        | intro hf =>
          cases hf (sg (iv x)) (sg_sortedAt (iv_sort _ x) _) (sg_match _) with
          | intro ht _ _ => cases ht
          | pre hp => exact of_decide_eq_false (holdsPre_inv (σ := sg (iv x)) rfl hp).symm
      rw [gRes, ifF hx]
      exact EvalTerm.dv_inv hrhs
  | rest hfn hnone =>
    obtain rfl := Option.some.inj (lookups.2.symm.trans hfn)
    cases hnone gCl2 (List.mem_cons_of_mem _ (List.mem_singleton_self _)) with
    | intro h =>
      cases h (sg (iv x)) (sg_sortedAt (iv_sort _ x) _) (sg_match _) with
      | intro ht _ _ => cases ht
      | pre hp => exact absurd hp.top_eq (by simp)
  | ensFails hfn hcl _ _ _ _ _ _ ht _ _ =>
    obtain rfl := Option.some.inj (lookups.2.symm.trans hfn)
    rcases gCl_of hcl with rfl | rfl <;> cases ht
  | clauseEx hfn hcl _ _ _ _ _ hne _ _ _ _ =>
    obtain rfl := Option.some.inj (lookups.2.symm.trans hfn)
    rcases gCl_of hcl with rfl | rfl <;> exact absurd rfl hne
  | exNone hfn hcl hne _ _ _ _ _ _ _ =>
    obtain rfl := Option.some.inj (lookups.2.symm.trans hfn)
    rcases gCl_of hcl with rfl | rfl <;> exact absurd rfl hne

/-- **`g(0)` is 0 and nothing else.** -/
theorem g_at0 : expectAt0 := ⟨evalG_mk 0, fun _ h => evalG_inv h⟩

/-- **`g(2)` is 1 and nothing else.** -/
theorem g_at2 : expectAt2 := ⟨evalG_mk 2, fun _ h => evalG_inv h⟩

/-- **The expectation of CN-4 §4.9 holds.** -/
theorem expect_ok : expect :=
  ⟨coreOK_ok, u_results, g_at0, g_at2, exclusion_pre, sentence_pre, sentence1_pre⟩

/-! ## `FnDet`, `FnSolves` and the predicates' truth values -/

theorem mem_fns {fn : Fn} (h : fn ∈ c.fns) : fn = uFn ∨ fn = gFn := by simpa [c] using h

/-- A clause over the one variable X whose pattern is X is coherent with itself: two matches at
one argument give X one value. -/
theorem coherent_self {cl : Clause} (hp : cl.pats = [.var 0]) (hex : cl.exs = [])
    (hr : (varOccs cl.rhs).all (· == 0) = true)
    (he : ((cl.ens.map varOccs).getD []).all (· == 0) = true) : Coherent c cl cl := by
  intro vs σ σ' ha ha' _ _ _ _ _
  have h1 := ha.2.1; have h2 := ha'.2.1
  rw [hp] at h1 h2
  obtain ⟨v, rfl, hl⟩ := match0 h1
  obtain ⟨w, hw, hl'⟩ := match0 h2
  cases hw
  refine .inl ⟨hex, hex, rfl, rfl, fun i hi => ?_, fun t ht i hi => ?_⟩
  · have := beq_iff_eq.mp (List.all_eq_true.mp hr i hi)
    rw [this, hl, hl']
  · rw [ht] at he
    have := beq_iff_eq.mp (List.all_eq_true.mp he i hi)
    rw [this, hl, hl']

/-- The clauses that compete are coherent: `g`'s two clauses are of two priorities and neither is
`aside`, so each clause competes with itself only. -/
theorem coherent : CoherentAll c :=
  Faithful.coherentAll_ofCl
    (fun fn hfn cl cl' hp hprio => by
      rcases mem_fns hfn with rfl | rfl
      · simp [uFn, pairs] at hp
      · have : cl = gCl1 ∧ cl' = gCl2 := by simpa [gFn, pairs] using hp
        obtain ⟨rfl, rfl⟩ := this
        exact absurd hprio (by decide))
    (fun fn hfn cl hcl => by
      rcases mem_fns hfn with rfl | rfl
      · obtain rfl := uCl_of hcl
        exact (matchIndependent_iff_noExs rfl).mpr (coherent_self rfl rfl (by decide) (by decide))
      · rcases gCl_of hcl with rfl | rfl <;>
          exact (matchIndependent_iff_noExs rfl).mpr (coherent_self rfl rfl (by decide) (by decide)))

/-- **Every function of `c` has at most one result.** -/
theorem fnDet : FnDet c := fnDet_of_coherent coherent

/-- A value of the sort Int is an Int literal. -/
theorem int_shape {v : GroundTerm} (h : c.sortOf v = some Srt.int) : ∃ x, v = iv x :=
  shape_int (by decide +kernel) h

/-- What a σ well sorted on a clause's one variable X:Int that matches gives: X is an Int x, and
the argument list is `[x]`. -/
theorem match_int {σ : Subst} {vs : List GroundTerm} (hσ : c.WellSortedAt [Srt.int] [0] σ)
    (hm : PatVals c σ [.var 0] vs) : ∃ x, σ.lookup 0 = some (iv x) ∧ vs = [iv x] := by
  obtain ⟨w, hl, hw⟩ := hσ 0 (List.mem_singleton_self _) Srt.int rfl
  obtain ⟨w', rfl, hl'⟩ := match0 hm
  rw [hl] at hl'; cases hl'
  obtain ⟨x, rfl⟩ := int_shape hw
  exact ⟨x, hl, rfl⟩

/-- **Evaluation solves the equations of `c`.** Where `g`'s second clause decides as the model
reads it, the first does not apply: its predicate, which has a truth value, is false, so the first
clause fails and `Eval` gives the second's value. -/
theorem fnSolves : FnSolves c := by
  intro fn hfn vs _ cl hcl σ hdec v
  rcases mem_fns hfn with rfl | rfl
  · obtain rfl := uCl_of hcl
    have hσ := (wellSortedAt_univ rfl).mp hdec.1.1
    obtain ⟨x, hl, rfl⟩ := match_int (hσ.at _) hdec.1.2.1
    refine Iff.trans ?_ (Clause.gives_iff_noExs (cl := uCl) rfl rfl hσ v).symm
    constructor
    · intro h
      have hr := evalU_inv (H := c.hooks) h
      by_cases hx : x > 0
      · rw [uRes, ifT hx] at hr; cases hr
        refine ⟨?_, fun t ht => ?_⟩
        · have := EvalTerm.var (c := c) (σ := σ) (i := 0); rw [hl] at this; exact this
        · cases ht; have := evalGt_mk c.hooks hl; rw [decide_eq_true hx] at this; exact this
      · rw [uRes, ifF hx] at hr; cases hr
    · rintro ⟨hr, he⟩
      have hv : some v = some (iv x) := (EvalTerm.var_inv hr).trans hl
      cases hv
      have hx : x > 0 := gt_true (evalGt_inv (H := c.hooks) hl (he _ rfl))
      have := evalU_mk c.hooks x; rw [uRes, ifT hx] at this; exact this
  · rcases gCl_of hcl with rfl | rfl
    · have hσ := (wellSortedAt_univ rfl).mp hdec.1.1
      obtain ⟨x, hl, rfl⟩ := match_int (hσ.at _) hdec.1.2.1
      have hx : x > 0 := of_decide_eq_true (holdsPre_inv hl hdec.1.2.2.2).symm
      have hg := evalG_mk x; rw [gRes, ifT hx] at hg
      refine Iff.trans ?_ (Clause.gives_iff_noExs (cl := gCl1) rfl rfl hσ v).symm
      constructor
      · intro h
        cases fnDet _ _ _ _ h hg
        exact ⟨.dv, fun t ht => nomatch ht⟩
      · rintro ⟨hr, -⟩
        cases (EvalTerm.dv_inv hr : some v = some (iv 1))
        exact hg
    · have hσ := (wellSortedAt_univ rfl).mp hdec.1.1
      obtain ⟨x, hl, rfl⟩ := match_int (hσ.at _) hdec.1.2.1
      have hx : ¬ x > 0 := fun hx => by
        have hp := holdsPre_mk (σ := sg (iv x)) (x := x) rfl
        rw [decide_eq_true hx] at hp
        exact hdec.2 gCl1 (List.mem_cons_self ..) rfl (by decide) (sg (iv x)) (sg_sortedAt (iv_sort _ x) _)
          (sg_match _) ⟨fun t ht => (nomatch ht), hp⟩
      have hg := evalG_mk x; rw [gRes, ifF hx] at hg
      refine Iff.trans ?_ (Clause.gives_iff_noExs (cl := gCl2) rfl rfl hσ v).symm
      constructor
      · intro h
        cases fnDet _ _ _ _ h hg
        exact ⟨.dv, fun t ht => nomatch ht⟩
      · rintro ⟨hr, -⟩
        cases (EvalTerm.dv_inv hr : some v = some (iv 0))
        exact hg

/-- **Each clause's predicate has a truth value where its patterns match** (`ClausePreDecided`):
`⌈u(X)⌉` is true or false at every Int, `u` having a result there. -/
theorem clausePreDecided : ClausePreDecided c := by
  intro fn hfn cl hcl σ vs hσ hm
  rcases mem_fns hfn with rfl | rfl
  · obtain rfl := uCl_of hcl; exact ⟨true, .top⟩
  · rcases gCl_of hcl with rfl | rfl
    · obtain ⟨x, hl, -⟩ := match_int (fun i hi => hσ i (by simp [gCl1, Clause.leftVars, Clause.condVars, varOccsList, varOccs, pre1, uX, varOccsCond] at hi ⊢; omega)) hm
      exact ⟨_, holdsPre_mk hl⟩
    · exact ⟨true, .top⟩

theorem openLaws : OpenLaws c := openLaws_of_plain (by decide +kernel)

/-- **`Γ` of `c` has a model**: `consistent_of` at a definition one of whose clauses has a
predicate that is not `\top`. -/
theorem consistent : Consistent c := consistent_of c coreOK_ok fnDet fnSolves clausePreDecided
  (clausePostDecided_of_isTop (by decide +kernel)) openLaws

/-! ## The predicate lemmas at `g`

The lemmas for a clause with a predicate in its premise, at `g`: `gCl1`'s predicate is `⌈u(X)⌉`,
not `\top`, so none of them is read here through a clause whose predicate is `\top`
(`Semantics.clausesPreTop` is false at `c`: `not_preTop`). -/

theorem not_preTop : c.clausesPreTop = false := by decide +kernel

section Tie

open Faithful HoldsShape ML

variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

/-- No clause of `c` has conditions that need a witness. -/
theorem noWitness : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c := by
  intro fn hfn cl hcl h
  have h0 : c.fns.all (fun f => f.clauses.all fun cl => !cl.needsWitness c) = true := by decide +kernel
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h0 fn hfn) cl hcl
  rw [h] at h1; cases h1

/-- `hcls` of `eval_den4ClPre` at `c`: each clause's facts with its predicate well sorted. -/
theorem hcls_c : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∃ L, HeadsOK c L ∧ ClauseOpenFactsP c fn L cl :=
  clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK_noExs (Semantics.coreOK_parts coreOK_ok).1 (Semantics.fnsNoExs_of_all (by decide +kernel)))

/-- `hpreR` of `eval_den4ClPre` at `c`: every model of `Γc c` reads `gCl1`'s predicate. -/
theorem hpreR_c (hIc : I ⊧ᴵP Γc c) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre ≠ .top → PreRead c I cl :=
  preReadAll_of_core coreOK_ok hIc

/-- `hneg` of `eval_den4ClPre` at `c`: `gCl1`, which `gCl2`'s sentence negates, has an empty
exclusion where it fails. -/
theorem hneg_c (hIc : I ⊧ᴵP Γc c) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmptyCl c I fn cl := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core coreOK_ok
  haveI : OvlOK c := hno
  exact neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK_noExs hok (Semantics.fnsNoExs_of_all (by decide +kernel))) hsr (Semantics.coreOK_parts coreOK_ok).2.1 hph
    noWitness (hpreR_c hIc)

theorem gFn_all : gFn ∈ c.allFns := List.mem_append_left _ (by simp [c])

/-- `gCl1` is one of the clauses `hpreR` and `hneg` are read at: its predicate is not `\top`, and
`gCl2` negates it. -/
theorem gCl1_read (hIc : I ⊧ᴵP Γc c) : PreRead c I gCl1 ∧ ExclEmptyCl c I gFn gCl1 :=
  ⟨hpreR_c hIc gFn gFn_all gCl1 (List.mem_cons_self ..) (fun h => Cond.noConfusion (show Cond.ceil Srt.int uX = Cond.top from h)),
    hneg_c hIc gFn gFn_all gCl1 (List.mem_cons_self ..)
      ⟨gCl2, List.mem_cons_of_mem _ (List.mem_singleton_self _), by decide⟩⟩

/-- **`eval_den4ClPre` at `g`**: in every model of `Γc c`, `g` applied to the element of an Int x
is what its result denotes, 1 where x > 0 and 0 elsewhere. -/
theorem den_g (hIc : I ⊧ᴵP Γc c) (x : Int) (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c G (GroundTerm.koreList c [iv x]))).interpret I e m ↔
      Res c I e (some (gRes x)) m := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core coreOK_ok
  haveI : OvlOK c := hno
  exact eval_den4ClPre (fun φ hφ => hIc φ (Or.inl hφ)) hnn (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)) hph
    hcls_c (hneg_c hIc) (hpreR_c hIc) (evalG_mk x) lookups.2
    (sortsOf_const (es := [iv x]) fun e he => by rw [List.mem_singleton.mp he]; exact iv_sort c x) e m

/-- At 0 through the second clause, whose sentence negates the first's exclusion with its
predicate; at 2 through the first, whose premise holds the predicate. -/
theorem den_g0 (hIc : I ⊧ᴵP Γc c) (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c G (GroundTerm.koreList c [iv 0]))).interpret I e m ↔ Res c I e (some (iv 0)) m :=
  den_g hIc 0 e m

theorem den_g2 (hIc : I ⊧ᴵP Γc c) (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c G (GroundTerm.koreList c [iv 2]))).interpret I e m ↔ Res c I e (some (iv 1)) m :=
  den_g hIc 2 e m

end Tie

section ModelSide

open Faithful Faithful.Model ML

theorem hypModel : HypModelCore c := hypModel_of_fn coreOK_ok fnDet fnSolves

theorem preOK_c : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.condOK cl.vars cl.pre = true := by
  intro fn hfn cl hcl
  have h0 : c.fns.all (fun f => f.clauses.all fun cl => c.condOK cl.vars cl.pre) = true := by decide +kernel
  exact List.all_eq_true.mp (List.all_eq_true.mp h0 fn hfn) cl hcl

/-- `hdec` of the model lemmas at `c`. -/
theorem preDec_c : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, ∀ σ ws, c.WellSorted cl.vars σ → PatVals c σ cl.pats ws →
    (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b :=
  fun fn hfn cl hcl σ ws hσ hm _ => clausePreDecided fn hfn cl hcl σ ws (hσ.at _) hm

/-- **`satFnsGoalPre` at `c`**: the value model satisfies the functions' equations with their
predicates. -/
theorem satFns : SatFnsGoal c := satFnsGoalPre hypModel (Semantics.fnsNoExs_of_all (by decide +kernel)) preOK_c preDec_c

theorem gFn_mem : gFn ∈ c.fns := by simp [c]
theorem gCl1_mem : gCl1 ∈ gFn.clauses := List.mem_cons_self ..
theorem gCl2_mem : gCl2 ∈ gFn.clauses := List.mem_cons_of_mem _ (List.mem_singleton_self _)

/-- **`sat_clauseEqPre` at `gCl1`**, a clause with the predicate `⌈u(X)⌉` and no competitor: its
equation holds in the value model. -/
theorem sat_gCl1 (T : GroundTerm → GroundTerm → Prop) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
      (withPre c (canonVars c gCl1.vars) gCl1 (clausePrem c gFn gCl1))
      (fnConcl c gFn (Term.kore c (canonVars c gCl1.vars) gCl1.rhs)
        (reqPat (srtOf c gFn.result) (gCl1.ens.map (Term.kore c (canonVars c gCl1.vars))))), []⟩ : Kore.Axiom)⟩).pat :=
  AtT.sat_clauseEqPre hypModel gFn_all (clause_eqnFactsPre hypModel gFn_all gCl1_mem rfl (preOK_c _ gFn_mem _ gCl1_mem))
    (preDec_c _ gFn_mem _ gCl1_mem)
    fun σ ws hws happ => eval_of_decides hypModel gFn_all gCl1_mem rfl hws ⟨happ, fun cl' hcl' _ hlt => by
      rcases gCl_of hcl' with rfl | rfl
      · exact absurd hlt (Nat.lt_irrefl _)
      · exact absurd hlt (by decide)⟩

/-- **`sat_competingEqPre` at `gCl2`**, under the negation of `gCl1`'s exclusion with its
predicate: its equation holds in the value model. -/
theorem sat_gCl2 (T : GroundTerm → GroundTerm → Prop) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
      (.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf ([gCl1].map fun cl' => exclusion c gFn cl' (canonClausePres cl'))),
        withPre c (canonVars c gCl2.vars) gCl2 (clausePrem c gFn gCl2)])
      (fnConcl c gFn (Term.kore c (canonVars c gCl2.vars) gCl2.rhs)
        (reqPat (srtOf c gFn.result) (gCl2.ens.map (Term.kore c (canonVars c gCl2.vars))))), []⟩ : Kore.Axiom)⟩).pat :=
  AtT.sat_competingEqPre hypModel gFn_all (clause_eqnFactsPre hypModel gFn_all gCl2_mem rfl (preOK_c _ gFn_mem _ gCl2_mem))
    (preDec_c _ gFn_mem _ gCl2_mem)
    (fun cl' hcl' => by
      obtain rfl : cl' = gCl1 := by simpa using hcl'
      exact (clause_eqnFactsPre hypModel gFn_all gCl1_mem rfl (preOK_c _ gFn_mem _ gCl1_mem)).toExclFactsPre)
    fun σ ws hws happ hfails => eval_of_decides hypModel gFn_all gCl2_mem rfl hws ⟨happ, fun cl' hcl' _ hlt σ' hw hp' => by
      rcases gCl_of hcl' with rfl | rfl
      · exact hfails gCl1 (List.mem_singleton_self _) σ' hw hp'
      · exact absurd hlt (Nat.lt_irrefl _)⟩

end ModelSide

end ClausePre

end KCore

/-- info: 'KCore.ClausePre.expect_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClausePre.expect_ok
/-- info: 'KCore.ClausePre.fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClausePre.fnDet
/-- info: 'KCore.ClausePre.fnSolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClausePre.fnSolves
/-- info: 'KCore.ClausePre.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClausePre.consistent
/-- info: 'KCore.ClausePre.gCl1_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClausePre.gCl1_read
/-- info: 'KCore.ClausePre.den_g0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClausePre.den_g0
/-- info: 'KCore.ClausePre.den_g2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClausePre.den_g2
/-- info: 'KCore.ClausePre.satFns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClausePre.satFns
/-- info: 'KCore.ClausePre.sat_gCl1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClausePre.sat_gCl1
/-- info: 'KCore.ClausePre.sat_gCl2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClausePre.sat_gCl2
