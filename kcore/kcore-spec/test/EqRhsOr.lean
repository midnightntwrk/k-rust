/-
  An equation with `\or` on its right side, of a function declared `total`: the expectations of
  fixture `e3-ml-eq-rhs-or-total` (test/constructs/fixtures), derived from its sentence, written as
  propositions on semantics built by hand (`expect…`, elaborated here, to be proved; their
  `coreOK` conjunct is `coreOK_now`). Run from the package root:
  `lake env lean -j1 test/EqRhsOr.lean`. Kernel-checked (`decide +kernel`): for `Fx` and `Pt`, every
  condition of `coreOK` but `clausesPlain` (`sortedRest_ok`, `coreRest_ok`), CN-4 §4.9's final
  clause conjunct (`clauseE3_ok`), `clausesPlain` itself, which admits h's predicates since no
  condition of h's clauses needs a witness (`clausesPlain_now`), so `coreOK` (`coreOK_now`), and
  that `ok`, which asks every clause's predicate `\top`, refuses them (`clausesPreTop_now`,
  `ok_now`); for `D`, where Z stands.

  The sentence (kore.txt `//@ 344`, `rule h(X) => f(X) #Or g(X)`, h `total`):
    X0 ∈ X → h(X0) = (f(X) ∨ g(X)) ∧ ⊤
  and kompile writes h's functional sentence `∃Val. Val = h(K0)` (`//@ 216`), so h(x) is one element
  at every x. Read with that sentence, the right side is one element where it is not empty: where
  `f(x)` and `g(x)` are both defined they are that element, where one is defined it is that one's,
  where neither is the right side is empty, against h's functional sentence. So:
  - f and g agree at x: the value there;
  - one undefined at x: the other's value;
  - both defined and different at x: the text has no model; `Eval` has both results, so not `FnDet`;
  - neither defined at x: the text has no model; `Eval` gives `none`, so `FnHyp`'s second conjunct
    (a total function has a value) is false.
  The reading (n+1 clauses of one priority, the alternatives `a₁ := f(X)`, `a₂ := g(X)`):
    `pre := ⌈aₖ⌉`, `rhs := aₖ` for each k, and `pre := ¬⌈a₁⌉ ∧ ¬⌈a₂⌉`, `rhs := a₁`, `ens := false`
  (`hCl1`, `hCl2`, `hCl3`). Its clause equations state `⌈aₖ⌉ → h(X0) = aₖ` and `h(X0) = ⊥` where
  neither is defined; with h's functional sentence they are the sentence.

  Two semantics of the three clauses:
  - `Fx`: f and g as the fixture writes them, `f(X) => X` and `g(X) => 0 -Int X`, both total. They
    agree at 0 only; at every other x both are defined and differ.
  - `Pt`: f and g partial, each undefined through its `ensures` (as `Eval.ensFails` reads it):
    `f(X) => X ensures X >=Int 0` and `g(X) => 0 -Int X ensures X <=Int 1 andBool -1 <=Int X`. At 0
    they agree (0), at 1 they differ (1 and -1), at 2 only f is defined (2), at -1 only g (1), at
    -2 neither.
  The fixture's text has f and g total; `Pt` is not its reading, only the clauses of h are.

  The amendment D shape (`D`): `k(X) => (X -Int Z) #Or X`, Z bound by no pattern. Split as above,
  Z would stand in the first clause's `pre` and so among its open condition variables
  (`openCondVars`); at Int (unconfined) CN-4 §4.9's final clause conjunct refuses the clause, with
  no reason naming the shape (`D.clauseE3_1`). `Parse.frRead` refuses the equation itself,
  `manyValuedRightSide`, naming Z as a variable of an alternative that the arguments do not bind
  (test/RhsReader.lean, `eqD`), so these clauses are hand-built only.
  `c.clausesPlain` is false of the three clauses (`D.clausesPlain_now`), at Z's sort: no clause
  has a condition that needs a witness (`D.needsWitness_none`), so their predicates, none of them
  `\top` (`D.pre_now`), are admitted, and the first clause fails the final conjunct. Where Z is of
  Bool, which is confined (`DB`, the shape `k(X) => (X andBool Z) #Or X`), the final conjunct
  admits the three clauses (`DB.clauseE3_ok`) and so does `clausesPlain` (`DB.clausesPlain_now`).

  Reader expectations, to run on the fixtures with that reader: `e3-ml-eq-rhs-or-total` read as
  `Fx`'s clauses of h; `e3-ml-eq-rhs-or` (h not `total`) refused `manyValuedRightSide`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace EqRhsOr

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-- An integer literal, as a term and as a value. -/
def iT (i : Int) : Term := .dv Srt.int (.int i)
def iv (i : Int) : GroundTerm := .dv Srt.int (.int i)

/-- The literal `false`. -/
def falseT : Term := .dv Srt.bool (.bool false)

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

/-- The symbols after the four cell symbols: f, g, h. -/
def F : Sym := nRegSyms + 4
def G : Sym := nRegSyms + 5
def H : Sym := nRegSyms + 6

/-- `f(X)` and `g(X)`, X the variable 0. -/
def fX : Term := .app F [.var 0]
def gX : Term := .app G [.var 0]

/-- `⌈f(X)⌉` and `⌈g(X)⌉`. -/
def pre1 : Cond := .ceil Srt.int fX
def pre2 : Cond := .ceil Srt.int gX

/-- `h(X) => f(X)` where `⌈f(X)⌉`. -/
def hCl1 : Clause := ⟨[Srt.int], [.var 0], none, fX, none, 50, false, [], pre1, .top⟩
/-- `h(X) => g(X)` where `⌈g(X)⌉`. -/
def hCl2 : Clause := ⟨[Srt.int], [.var 0], none, gX, none, 50, false, [], pre2, .top⟩
/-- `h(X) => f(X) ensures false` where neither is defined. -/
def hCl3 : Clause := ⟨[Srt.int], [.var 0], none, fX, some falseT, 50, false, [],
  .and (.not pre1) (.not pre2), .top⟩

/-- h, declared `total`. -/
def hFn : Fn := ⟨H, [Srt.int], Srt.int, [hCl1, hCl2, hCl3], true⟩

/-- The three clauses are what the reading function's builder (`Parse.frClauses`,
KcoreSpec/ReadFns.lean) gives for the alternatives `f(X)`, `g(X)`, neither with a predicate of its
own; test/RhsReader.lean runs the reading function on the fixture's text. -/
theorem frClauses_h :
    Parse.frClauses Srt.int [Srt.int] [.var 0] none 50 false [(fX, []), (gX, [])] = [hCl1, hCl2, hCl3] := rfl

/-- The semantics with f's and g's functions given. -/
def sem (fFn gFn : Fn) : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg", "Lblh"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fFn, gFn, hFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

/-- `FnHyp`'s second conjunct: a function declared `total` has a value at every argument list of
its sorts. -/
def TotalHasValue (c : Semantics) : Prop :=
  ∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v)

/-- h's result at `[iv x]` is `r` and only `r`. -/
def OnlyResult (c : Semantics) (x : Int) (r : Option GroundTerm) : Prop :=
  Eval c H [iv x] r ∧ ∀ r', Eval c H [iv x] r' → r' = r

/-! ## `Fx`: the fixture's f and g -/

namespace Fx

/-- `f(X) => X`, total. -/
def fFn : Fn := ⟨F, [Srt.int], Srt.int, [⟨[Srt.int], [.var 0], none, .var 0, none, 50, false, [], .top, .top⟩], true⟩
/-- `g(X) => 0 -Int X`, total. -/
def gFn : Fn := ⟨G, [Srt.int], Srt.int,
  [⟨[Srt.int], [.var 0], none, .app intSub [iT 0, .var 0], none, 50, false, [], .top, .top⟩], true⟩

def c : Semantics := sem fFn gFn

theorem sortedRest_ok : sortedRest c = true := by decide +kernel
theorem coreRest_ok : coreRest c = true := by decide +kernel
/-- Every clause meets CN-4 §4.9's final clause conjunct. -/
theorem clauseE3_ok : c.fns.all (fun f => f.clauses.all (clauseE3 c)) = true := by decide +kernel
/-- `clausesPlain` admits h's clauses: no condition of theirs needs a witness. -/
theorem clausesPlain_now : c.clausesPlain = true := by decide +kernel
/-- So `coreOK` holds. -/
theorem coreOK_now : c.coreOK = true := by
  rw [coreOK_eq, sortedOK_eq, sortedRest_ok, clausesPlain_now, coreRest_ok]; rfl
/-- h's clauses have predicates that are not `\top`, which `ok` refuses. -/
theorem clausesPreTop_now : c.clausesPreTop = false := by decide +kernel
theorem ok_now : c.ok = false := by
  cases h : c.ok
  · rfl
  · exact absurd (Semantics.preTop_of_okAll (Semantics.okAll_of_ok h)) (by rw [clausesPreTop_now]; decide)

/-- **Expected** (to run): `coreOK` holds; at 0 the one value 0; at every other x both x and -x
and no other result; so not `FnDet`, not `FnHyp`; `Γc` has no model, as the text has none. -/
def expect : Prop :=
  c.coreOK = true ∧
  OnlyResult c 0 (some (iv 0)) ∧
  (∀ x : Int, x ≠ 0 → Eval c H [iv x] (some (iv x)) ∧ Eval c H [iv x] (some (iv (-x))) ∧
    ∀ r, Eval c H [iv x] r → r = some (iv x) ∨ r = some (iv (-x))) ∧
  ¬ FnDet c ∧ ¬ FnHyp c ∧ ¬ Consistent c

end Fx

/-! ## `Pt`: f and g partial -/

namespace Pt

/-- `f(X) => X ensures X >=Int 0`. -/
def fFn : Fn := ⟨F, [Srt.int], Srt.int,
  [⟨[Srt.int], [.var 0], none, .var 0, some (.app intGe [.var 0, iT 0]), 50, false, [], .top, .top⟩], false⟩
/-- `g(X) => 0 -Int X ensures X <=Int 1 andBool -1 <=Int X`. -/
def gFn : Fn := ⟨G, [Srt.int], Srt.int,
  [⟨[Srt.int], [.var 0], none, .app intSub [iT 0, .var 0],
    some (.app boolAnd [.app intLe [.var 0, iT 1], .app intLe [iT (-1), .var 0]]), 50, false, [], .top, .top⟩], false⟩

def c : Semantics := sem fFn gFn

theorem sortedRest_ok : sortedRest c = true := by decide +kernel
theorem coreRest_ok : coreRest c = true := by decide +kernel
theorem clauseE3_ok : c.fns.all (fun f => f.clauses.all (clauseE3 c)) = true := by decide +kernel
theorem clausesPlain_now : c.clausesPlain = true := by decide +kernel
theorem coreOK_now : c.coreOK = true := by
  rw [coreOK_eq, sortedOK_eq, sortedRest_ok, clausesPlain_now, coreRest_ok]; rfl
theorem clausesPreTop_now : c.clausesPreTop = false := by decide +kernel
theorem ok_now : c.ok = false := by
  cases h : c.ok
  · rfl
  · exact absurd (Semantics.preTop_of_okAll (Semantics.okAll_of_ok h)) (by rw [clausesPreTop_now]; decide)

/-- **Expected** (to run): `coreOK` holds. -/
def expectCore : Prop := c.coreOK = true

/-- **Expected** (to run): where f and g agree (0), that value. -/
def expectAgree : Prop := OnlyResult c 0 (some (iv 0))

/-- **Expected** (to run): where one is undefined, the other's value: at 2 (g undefined) f's 2, at
-1 (f undefined) g's 1. -/
def expectOneUndefined : Prop := OnlyResult c 2 (some (iv 2)) ∧ OnlyResult c (-1) (some (iv 1))

/-- **Expected** (to run): where both are defined and differ (1), both results and no other, so
not `FnDet`; `Γc` has no model (`h(1) = f(1) = 1` and `h(1) = g(1) = -1`). -/
def expectDiffer : Prop :=
  Eval c H [iv 1] (some (iv 1)) ∧ Eval c H [iv 1] (some (iv (-1))) ∧
  (∀ r, Eval c H [iv 1] r → r = some (iv 1) ∨ r = some (iv (-1))) ∧ ¬ FnDet c ∧ ¬ Consistent c

/-- **Expected** (to run): where neither is defined (-2), `none` by the last clause, and only it;
so `FnHyp`'s second conjunct is false (h is declared `total`). -/
def expectNeither : Prop := OnlyResult c (-2) none ∧ ¬ TotalHasValue c

end Pt

/-! ## `D`: amendment D's shape, a variable of one alternative that no pattern binds -/

namespace D

/-- `k`, the one function. -/
def K : Sym := nRegSyms + 4

/-- `X -Int Z` (X the variable 0, Z the variable 1) and `X`. -/
def a1 : Term := .app intSub [.var 0, .var 1]
def a2 : Term := .var 0

def p1 : Cond := .ceil Srt.int a1
def p2 : Cond := .ceil Srt.int a2

/-- The three clauses F6's split would give `k(X) => (X -Int Z) #Or X`. -/
def cl1 : Clause := ⟨[Srt.int, Srt.int], [.var 0], none, a1, none, 50, false, [], p1, .top⟩
def cl2 : Clause := ⟨[Srt.int, Srt.int], [.var 0], none, a2, none, 50, false, [], p2, .top⟩
def cl3 : Clause := ⟨[Srt.int, Srt.int], [.var 0], none, a1, some falseT, 50, false, [],
  .and (.not p1) (.not p2), .top⟩

def kFn : Fn := ⟨K, [Srt.int], Srt.int, [cl1, cl2, cl3], true⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblk"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [kFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

/-- Z (the variable 1) is an open condition variable of the first and last clauses, beside X,
which the pattern binds; Int is not confined. -/
theorem openCondVars_Z : cl1.openCondVars = [1] ∧ cl3.openCondVars = [1] ∧ cl2.openCondVars = [] ∧
    cl1.reqOpen = true ∧ cl1.reqClosed = false ∧ c.confined Srt.int = false := by decide +kernel

/-- CN-4 §4.9's final clause conjunct refuses the first clause (and the last), with no reason
naming the shape; the second, whose `pre` reads X only, passes. -/
theorem clauseE3_1 : clauseE3 c cl1 = false ∧ clauseE3 c cl3 = false ∧ clauseE3 c cl2 = true := by
  decide +kernel

/-- No clause has a condition that needs a witness, so `clausesPlain` admits their predicates. -/
theorem needsWitness_none : cl1.needsWitness c = false ∧ cl2.needsWitness c = false ∧
    cl3.needsWitness c = false := by decide +kernel

/-- `clausesPlain` refuses the definition at Z's sort: the first clause fails the final
conjunct (`clauseE3_1`). -/
theorem clausesPlain_now : c.clausesPlain = false := by decide +kernel

theorem pre_now : cl1.pre.isTop = false ∧ cl2.pre.isTop = false ∧ cl3.pre.isTop = false ∧
    cl2.openCondVars = [] := by decide +kernel

end D

/-! ## `DB`: the same shape with Z of a confined sort -/

namespace DB

/-- `X andBool Z` (X the variable 0, Z the variable 1) and `X`. -/
def a1 : Term := .app boolAnd [.var 0, .var 1]
def a2 : Term := .var 0

def p1 : Cond := .ceil Srt.bool a1
def p2 : Cond := .ceil Srt.bool a2

/-- The three clauses the split would give `k(X) => (X andBool Z) #Or X`, X and Z of Bool. -/
def cl1 : Clause := ⟨[Srt.bool, Srt.bool], [.var 0], none, a1, none, 50, false, [], p1, .top⟩
def cl2 : Clause := ⟨[Srt.bool, Srt.bool], [.var 0], none, a2, none, 50, false, [], p2, .top⟩
def cl3 : Clause := ⟨[Srt.bool, Srt.bool], [.var 0], none, a1, some falseT, 50, false, [],
  .and (.not p1) (.not p2), .top⟩

def kFn : Fn := ⟨D.K, [Srt.bool], Srt.bool, [cl1, cl2, cl3], true⟩

def c : Semantics := { D.c with fns := [kFn] }

/-- Z is an open condition variable of the first and last clauses as at Int; Bool is confined. -/
theorem openCondVars_Z : cl1.openCondVars = [1] ∧ cl3.openCondVars = [1] ∧ cl2.openCondVars = [] ∧
    c.confined Srt.bool = true := by decide +kernel

/-- The final clause conjunct admits the three clauses: Z's sort is confined. -/
theorem clauseE3_ok : clauseE3 c cl1 = true ∧ clauseE3 c cl2 = true ∧ clauseE3 c cl3 = true := by
  decide +kernel

/-- `clausesPlain` admits the three clauses: their open condition variable Z is of a confined
sort, and none needs a witness. -/
theorem clausesPlain_now : c.clausesPlain = true := by decide +kernel

end DB

end EqRhsOr

end KCore

/-- info: 'KCore.EqRhsOr.sortedOK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.sortedOK_eq
/-- info: 'KCore.EqRhsOr.coreOK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.coreOK_eq
/-- info: 'KCore.EqRhsOr.Fx.sortedRest_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Fx.sortedRest_ok
/-- info: 'KCore.EqRhsOr.Fx.coreRest_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Fx.coreRest_ok
/-- info: 'KCore.EqRhsOr.Fx.clauseE3_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Fx.clauseE3_ok
/-- info: 'KCore.EqRhsOr.Fx.clausesPlain_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Fx.clausesPlain_now
/-- info: 'KCore.EqRhsOr.Fx.coreOK_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Fx.coreOK_now
/-- info: 'KCore.EqRhsOr.Fx.ok_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Fx.ok_now
/-- info: 'KCore.EqRhsOr.Pt.sortedRest_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Pt.sortedRest_ok
/-- info: 'KCore.EqRhsOr.Pt.coreRest_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Pt.coreRest_ok
/-- info: 'KCore.EqRhsOr.Pt.clauseE3_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Pt.clauseE3_ok
/-- info: 'KCore.EqRhsOr.Pt.clausesPlain_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Pt.clausesPlain_now
/-- info: 'KCore.EqRhsOr.Pt.coreOK_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Pt.coreOK_now
/-- info: 'KCore.EqRhsOr.Pt.ok_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Pt.ok_now
/-- info: 'KCore.EqRhsOr.D.openCondVars_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.D.openCondVars_Z
/-- info: 'KCore.EqRhsOr.D.clauseE3_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.D.clauseE3_1
/-- info: 'KCore.EqRhsOr.D.clausesPlain_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.D.clausesPlain_now
/-- info: 'KCore.EqRhsOr.DB.clauseE3_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.DB.clauseE3_ok
/-- info: 'KCore.EqRhsOr.DB.clausesPlain_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.DB.clausesPlain_now
