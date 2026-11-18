/-
  A clause with a predicate in its premise (`Clause.pre`): CN-4 §4.9's expectation, on a semantics
  built by hand against the existing field `Clause.pre` (Core.lean, `structure Clause`). The
  statements are written as propositions (`expect…`): those on the sentences (`expectExclusion`,
  `expectSentence`, `expectSentence1`) are proved here since the sentences read `Clause.pre`
  (`exclusion_pre`, `sentence_pre`, `sentence1_pre`), and `expectCore` is proved (`coreOK_ok`);
  the statements on `Eval`'s results (`expectU`, `expectAt0`, `expectAt2`) are elaborated, not
  proved.
  Run from the package root: `lake env lean -j1 test/ClausePre.lean`.
  Kernel-checked (`decide +kernel`): only what does not depend on a clause's `pre` being read.

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
  (`exclusion_ne_plain`). `expectU`, `expectAt0` and `expectAt2` are stated and not proved here.
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

/-! ## The emitted equations (`Emit.clauseAx`, e3.clauseAx-pre)

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

/-- **Expected** (to run, e3.admit): `coreOK` holds. -/
def expectCore : Prop := c.coreOK = true

/-- **Expected** (to run; reads no `pre`): `u(0)` has no value, by `Eval.ensFails`, and `u(2)` is
2, under every interpretation of the parameters. -/
def expectU : Prop :=
  ∀ H : HookParams, OnlyResult (c.withHooks H) U 0 none ∧ OnlyResult (c.withHooks H) U 2 (some (iv 2))

/-- **Expected** (to run, e3.clause-pre-eval): `g(0)` is 0 and nothing else: `⌈u(0)⌉` is false, so
the first clause fails (`ReqFails.pre`) and the second decides. -/
def expectAt0 : Prop := OnlyResult c G 0 (some (iv 0))

/-- **Expected** (to run, e3.clause-pre-eval): `g(2)` is 1 and nothing else: `⌈u(2)⌉` is true, so
the first clause decides (`hpre`) and blocks the second. -/
def expectAt2 : Prop := OnlyResult c G 2 (some (iv 1))

/-- The expectation of CN-4 §4.9, whole. -/
def expect : Prop :=
  expectCore ∧ expectU ∧ expectAt0 ∧ expectAt2 ∧ expectExclusion ∧ expectSentence ∧ expectSentence1

end ClausePre

end KCore
