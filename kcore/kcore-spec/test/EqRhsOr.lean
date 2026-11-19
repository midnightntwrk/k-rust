/-
  An equation with `\or` on its right side, of a function declared `total`: the expectations of
  fixture `e3-ml-eq-rhs-or-total` (test/constructs/fixtures), derived from its sentence, written as
  propositions on semantics built by hand (`expect…`) and proved (`Fx.expect_holds`,
  `Pt.expectCore_holds`, `Pt.expectAgree_holds`, `Pt.expectOneUndefined_holds`,
  `Pt.expectDiffer_holds`, `Pt.expectNeither_holds`): h's results at x are f's and g's there
  (`evalH_inv`, `evalH_f`, `evalH_g`, `evalH_none`), and where two differ `Γc` has no model
  (`Fx.no_model`, `Pt.no_model`: h(1) would denote the elements of 1 and -1, which are apart). Run from the package root:
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

  The reader (`runOr`, on the kompiled texts): `e3-ml-eq-rhs-or-total` is read with h's clauses
  `hCl1`, `hCl2`, `hCl3` and `Fx`'s functions (the text's numbering of f, g, h is `sem`'s);
  `e3-ml-eq-rhs-or` (h not `total`) and `e3-ml-eq-rhs-or-many` (nine alternatives) are refused
  `manyValuedRightSide`, with their whole details. By the kernel, the reader's clauses of h on that
  text are `Parse.frClauses`' (test/ReaderWire.lean `Stages.cls2_frClauses`), which `frClauses_h`
  equates with `hCl1`, `hCl2`, `hCl3`.
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


/-! ## The expectations, proved

h's results at an integer x are read from f's and g's there (`evalH_inv`, `evalH_f`, `evalH_g`,
`evalH_none`), each of f and g having one result at x (`Uniq`); f's and g's from their one clause
(`eval1_iff`). -/

section Results

variable {c : Semantics}

/-- The substitution that gives X the value v. -/
def sg (v : GroundTerm) : Subst := [(0, v)]

theorem sg_sorted (x : Int) : c.WellSorted [Srt.int] (sg (iv x)) := by
  intro i s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨iv x, rfl, rmS_sortOf_int c x⟩
  | succ i => simp at hs

theorem sg_sortedAt (x : Int) (is : List Nat) : c.WellSortedAt [Srt.int] is (sg (iv x)) :=
  fun i _ s hs => sg_sorted x i s hs

theorem sg_match (v : GroundTerm) : PatVals c (sg v) [.var 0] [v] := .cons (.var rfl) .nil

theorem match0 {σ : Subst} {vs : List GroundTerm} (h : PatVals c σ [.var 0] vs) :
    ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
  rw [PatVals.nil_inv hs]
  exact ⟨v, rfl, PatVal.var_inv hv⟩

/-- f, g or h's symbol is a function's: no constructor, hook, parameter or overloading symbol. -/
def IsFn (c : Semantics) (k : Sym) : Prop :=
  c.isCtor k = false ∧ isHook k = false ∧ c.isParam k = false ∧ c.isOvl k = false

/-- The one result of a term under σ, X being x. -/
def Uniq (c : Semantics) (σ : Subst) (t : Term) (r : Option GroundTerm) : Prop :=
  ∀ w, EvalTerm c σ t w ↔ w = r

theorem uniq_var {σ : Subst} {x : Int} (hl : σ.lookup 0 = some (iv x)) : Uniq c σ (.var 0) (some (iv x)) :=
  fun _ => ⟨fun h => (EvalTerm.var_inv h).trans hl, fun h => h ▸ hl ▸ .var⟩

theorem uniq_dv {σ : Subst} (s : Srt) (l : Lit) : Uniq c σ (.dv s l) (some (.dv s l)) :=
  fun _ => ⟨fun h => EvalTerm.dv_inv h, fun h => h ▸ .dv⟩

/-- A hooked symbol of two arguments, each with one result: the hook's result. -/
theorem uniq_hook2 {f : Sym} (hc : c.isCtor f = false) (hh : isHook f = true) (ho : c.isOvl f = false)
    {σ : Subst} {t u : Term} {a b : GroundTerm} {r : Option GroundTerm}
    (ht : Uniq c σ t (some a)) (hu : Uniq c σ u (some b)) (hr : c.hookRes f [a, b] = some r) :
    Uniq c σ (.app f [t, u]) r := by
  intro w
  constructor
  · intro h
    cases h with
    | ctor hk _ => exact absurd (hc.symm.trans hk) (by simp)
    | hook _ _ hts hres _ =>
      cases hts with
      | cons h1 hs =>
        cases hs with
        | cons h2 hs' =>
          cases hs'
          obtain rfl := (ht _).mp h1
          obtain rfl := (hu _).mp h2
          exact Option.some.inj ((hres [a, b] rfl).symm.trans hr)
    | param _ hhk _ _ _ => exact absurd (hh.symm.trans hhk) (by simp)
    | call _ hhk _ _ _ _ => exact absurd (hh.symm.trans hhk) (by simp)
    | callUndef _ hhk _ _ _ => exact absurd (hh.symm.trans hhk) (by simp)
    | ovl _ hov _ _ => exact absurd (ho.symm.trans hov) (by simp)
    | ovlFn _ hov _ _ _ _ _ => exact absurd (ho.symm.trans hov) (by simp)
  · rintro rfl
    exact .hook hc hh (.cons ((ht _).mpr rfl) (.cons ((hu _).mpr rfl) .nil))
      (fun vs hvs => by
        have : vs = [a, b] := Option.some.inj hvs.symm
        subst this; exact hr)
      (fun hn => nomatch hn)

/-- A function applied to X: the function's result at x. -/
theorem app_mk {k : Sym} (hk : IsFn c k) {σ : Subst} {x : Int} {r : Option GroundTerm}
    (hl : σ.lookup 0 = some (iv x)) (he : Eval c k [iv x] r) : EvalTerm c σ (.app k [.var 0]) r :=
  .call hk.1 hk.2.1 (.cons .var .nil) (by rw [hl]; rfl) he hk.2.2.1

theorem app_inv {k : Sym} (hk : IsFn c k) {σ : Subst} {x : Int} {r : Option GroundTerm}
    (hl : σ.lookup 0 = some (iv x)) (h : EvalTerm c σ (.app k [.var 0]) r) : Eval c k [iv x] r := by
  cases h with
  | ctor hc _ => exact absurd (hk.1.symm.trans hc) (by simp)
  | hook _ hh _ _ _ => exact absurd (hk.2.1.symm.trans hh) (by simp)
  | param _ _ hp _ _ => exact absurd (hk.2.2.1.symm.trans hp) (by simp)
  | call _ _ hts hvs hf _ =>
    cases hts with
    | cons h1 hs =>
      cases hs; cases h1
      rw [hl] at hvs
      obtain rfl := Option.some.inj hvs.symm
      exact hf
  | callUndef _ _ hts hvs _ =>
    cases hts with
    | cons h1 hs =>
      cases hs; cases h1
      rw [hl] at hvs
      exact nomatch hvs
  | ovl _ ho _ _ => exact absurd (hk.2.2.2.symm.trans ho) (by simp)
  | ovlFn _ ho _ _ _ _ _ => exact absurd (hk.2.2.2.symm.trans ho) (by simp)

/-- `⌈k(X)⌉` is whether k has a value at x. -/
theorem ceil_inv {k : Sym} (hk : IsFn c k) {σ : Subst} {x : Int} {rk : Option GroundTerm}
    (hl : σ.lookup 0 = some (iv x)) (hu : ∀ r, Eval c k [iv x] r ↔ r = rk) {n : Nat} {s : Srt} {b : Bool}
    (h : Holds c n σ (.ceil s (.app k [.var 0])) b) : b = rk.isSome := by
  cases h with
  | ceil e => rw [(hu _).mp (app_inv hk hl e)]

theorem ceil_mk {k : Sym} (hk : IsFn c k) {σ : Subst} {x : Int} {rk : Option GroundTerm}
    (hl : σ.lookup 0 = some (iv x)) (hu : ∀ r, Eval c k [iv x] r ↔ r = rk) (n : Nat) (s : Srt) :
    Holds c n σ (.ceil s (.app k [.var 0])) rk.isSome :=
  .ceil (app_mk hk hl ((hu rk).mpr rfl))

/-- `¬p ∧ ¬q` has the truth value of its two negations. -/
theorem andNot_inv {n : Nat} {σ : Subst} {p q : Cond} {b : Bool} (h : Holds c n σ (.and (.not p) (.not q)) b) :
    ∃ b1 b2, Holds c n σ p b1 ∧ Holds c n σ q b2 ∧ b = (!b1 && !b2) := by
  cases h with
  | and h1 h2 =>
    cases h1 with
    | not h1 =>
      cases h2 with
      | not h2 => exact ⟨_, _, h1, h2, rfl⟩

/-- A function's one clause over the Int variable X: `X => rhs ensures ens`, of priority 50. -/
def cl1 (rhs : Term) (ens : Option Term) : Clause := ⟨[Srt.int], [.var 0], none, rhs, ens, 50, false, [], .top, .top⟩

/-- **A function of one clause** has, at x, the right side's result where the `ensures` is true
(or absent), and no value where it is false. -/
theorem eval1_iff {k : Sym} {fn : Fn} (hk : c.lookupFn k = some fn) {rhs : Term} {ens : Option Term}
    (hcls : fn.clauses = [cl1 rhs ens]) {x : Int} {rr : Option GroundTerm} {ok : Bool}
    (hrhs : ∀ σ : Subst, σ.lookup 0 = some (iv x) → Uniq c σ rhs rr)
    (hens : ∀ σ : Subst, σ.lookup 0 = some (iv x) → ∀ t, ens = some t → Uniq c σ t (some (bool ok)))
    (hnone : ens = none → ok = true) :
    ∀ r, Eval c k [iv x] r ↔ r = (if ok then rr else none) := by
  have hmem : cl1 rhs ens ∈ fn.clauses := by rw [hcls]; exact List.mem_singleton_self _
  have hcl : ∀ {cl}, cl ∈ fn.clauses → cl = cl1 rhs ens := fun h => by rw [hcls] at h; exact List.mem_singleton.mp h
  have hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < (cl1 rhs ens).prio → Fails c [iv x] cl' :=
    fun cl' h _ hlt => by rw [hcl h] at hlt; exact absurd hlt (Nat.lt_irrefl _)
  intro r
  constructor
  · intro h
    cases h with
    | clause hfn hc _ hm _ _ _ _ hr hen _ =>
      obtain rfl := Option.some.inj (hk.symm.trans hfn)
      obtain rfl := hcl hc
      obtain ⟨w, hw, hl⟩ := match0 hm
      cases hw
      have hok : ok = true := by
        cases he : ens with
        | none => exact hnone he
        | some t =>
          have := ((hens _ hl t he) _).mp (hen t he)
          cases ok
          · exact absurd this (by decide)
          · rfl
      subst hok
      exact (hrhs _ hl _).mp hr
    | rest hfn hn =>
      obtain rfl := Option.some.inj (hk.symm.trans hfn)
      cases hn _ hmem with
      | intro hf =>
        cases hf (sg (iv x)) (sg_sortedAt x _) (sg_match _) with
        | intro ht _ _ => exact nomatch ht
        | pre hp => cases hp
    | ensFails hfn hc _ hm _ _ _ _ ht he hw =>
      obtain rfl := Option.some.inj (hk.symm.trans hfn)
      obtain rfl := hcl hc
      obtain ⟨w, hw', hl⟩ := match0 hm
      cases hw'
      have := ((hens _ hl _ ht) _).mp he
      subst this
      cases ok
      · rfl
      · exact absurd rfl hw
    | clauseEx hfn hc _ _ _ _ _ hne _ _ _ _ =>
      obtain rfl := Option.some.inj (hk.symm.trans hfn)
      obtain rfl := hcl hc
      exact absurd rfl hne
    | exNone hfn hc hne _ _ _ _ _ _ _ =>
      obtain rfl := Option.some.inj (hk.symm.trans hfn)
      obtain rfl := hcl hc
      exact absurd rfl hne
  · rintro rfl
    cases ok with
    | true =>
      exact .clause hk hmem (sg_sorted x) (sg_match _) (fun t ht => nomatch ht) .top hprio rfl
        ((hrhs _ rfl _).mpr rfl) (fun t ht => ((hens _ rfl t ht) _).mpr rfl) .top
    | false =>
      cases he : ens with
      | none => exact absurd (hnone he) (by decide)
      | some t =>
        exact .ensFails (cl := cl1 rhs ens) hk hmem (sg_sorted x) (sg_match _) (fun t ht => nomatch ht) .top hprio rfl
          he (((hens _ rfl t he) _).mpr rfl) (by decide)

/-- h's clauses. -/
theorem hFn_clauses : hFn.clauses = [hCl1, hCl2, hCl3] := rfl

theorem hprio {x : Int} {cl : Clause} (hcl : cl ∈ hFn.clauses) :
    ∀ cl' ∈ hFn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c [iv x] cl' := by
  intro cl' hcl' _ hlt
  simp only [hFn_clauses, List.mem_cons, List.not_mem_nil, or_false] at hcl hcl'
  rcases hcl with rfl | rfl | rfl <;> rcases hcl' with rfl | rfl | rfl <;> exact absurd hlt (by decide)

variable (hH : c.lookupFn H = some hFn) (hF : IsFn c F) (hG : IsFn c G) {x : Int} {rf rg : Option GroundTerm}
  (hf : ∀ r, Eval c F [iv x] r ↔ r = rf) (hg : ∀ r, Eval c G [iv x] r ↔ r = rg)
include hH hF hG hf hg

/-- **h's results at x**: f's value where f has one, g's where g has one, and none where neither
has one. -/
theorem evalH_inv {r : Option GroundTerm} (h : Eval c H [iv x] r) :
    (rf.isSome ∧ r = rf) ∨ (rg.isSome ∧ r = rg) ∨ (rf = none ∧ rg = none ∧ r = none) := by
  cases h with
  | clause hfn hcl _ hm _ hpre _ _ hrhs hens _ =>
    obtain rfl := Option.some.inj (hH.symm.trans hfn)
    simp only [hFn_clauses, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl | rfl <;> obtain ⟨w, hw, hl⟩ := match0 hm <;> cases hw
    · exact .inl ⟨(ceil_inv hF hl hf hpre).symm, (hf _).mp (app_inv hF hl hrhs)⟩
    · exact .inr (.inl ⟨(ceil_inv hG hl hg hpre).symm, (hg _).mp (app_inv hG hl hrhs)⟩)
    · exact absurd (EvalTerm.dv_inv (hens _ rfl)) (by decide)
  | rest hfn hn =>
    obtain rfl := Option.some.inj (hH.symm.trans hfn)
    have f1 : ReqFails c (sg (iv x)) hCl1 :=
      match hn hCl1 (by simp [hFn_clauses]) with | .intro hf' => hf' _ (sg_sortedAt x _) (sg_match _)
    have f2 : ReqFails c (sg (iv x)) hCl2 :=
      match hn hCl2 (by simp [hFn_clauses]) with | .intro hf' => hf' _ (sg_sortedAt x _) (sg_match _)
    have f3 : ReqFails c (sg (iv x)) hCl3 :=
      match hn hCl3 (by simp [hFn_clauses]) with | .intro hf' => hf' _ (sg_sortedAt x _) (sg_match _)
    have h1 : rf.isSome = false := by
      cases f1 with
      | intro ht _ _ => exact nomatch ht
      | pre hp => exact (ceil_inv hF rfl hf hp).symm
    have h2 : rg.isSome = false := by
      cases f2 with
      | intro ht _ _ => exact nomatch ht
      | pre hp => exact (ceil_inv hG rfl hg hp).symm
    cases f3 with
    | intro ht _ _ => exact nomatch ht
    | pre hp =>
      obtain ⟨b1, b2, hp1, hp2, hb⟩ := andNot_inv hp
      rw [ceil_inv hF rfl hf hp1, ceil_inv hG rfl hg hp2, h1, h2] at hb
      exact absurd hb (by decide)
  | ensFails hfn hcl _ hm _ hpre _ _ ht _ _ =>
    obtain rfl := Option.some.inj (hH.symm.trans hfn)
    simp only [hFn_clauses, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl | rfl
    · exact nomatch ht
    · exact nomatch ht
    · obtain ⟨w, hw, hl⟩ := match0 hm
      cases hw
      obtain ⟨b1, b2, hp1, hp2, hb⟩ := andNot_inv hpre
      rw [ceil_inv hF hl hf hp1, ceil_inv hG hl hg hp2] at hb
      cases hrf : rf <;> cases hrg : rg <;> rw [hrf, hrg] at hb <;>
        first | exact .inr (.inr ⟨rfl, rfl, rfl⟩) | simp at hb
  | clauseEx hfn hcl _ _ _ _ _ hne _ _ _ _ =>
    obtain rfl := Option.some.inj (hH.symm.trans hfn)
    simp only [hFn_clauses, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl | rfl <;> exact absurd rfl hne
  | exNone hfn hcl hne _ _ _ _ _ _ _ =>
    obtain rfl := Option.some.inj (hH.symm.trans hfn)
    simp only [hFn_clauses, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl | rfl <;> exact absurd rfl hne

omit hG hg in
/-- Where f has the value a at x, h has it, by the first clause. -/
theorem evalH_f {a : GroundTerm} (ha : rf = some a) : Eval c H [iv x] (some a) := by
  have hp := ceil_mk hF (σ := sg (iv x)) rfl hf 1 Srt.int
  rw [ha] at hp
  exact .clause (cl := hCl1) hH (by simp [hFn_clauses]) (sg_sorted x) (sg_match _) (fun t ht => nomatch ht) hp
    (hprio (by simp [hFn_clauses])) rfl (app_mk hF rfl ((hf _).mpr ha.symm)) (fun t ht => nomatch ht) .top

omit hF hf in
/-- Where g has the value b at x, h has it, by the second clause. -/
theorem evalH_g {b : GroundTerm} (hb : rg = some b) : Eval c H [iv x] (some b) := by
  have hp := ceil_mk hG (σ := sg (iv x)) rfl hg 1 Srt.int
  rw [hb] at hp
  exact .clause (cl := hCl2) hH (by simp [hFn_clauses]) (sg_sorted x) (sg_match _) (fun t ht => nomatch ht) hp
    (hprio (by simp [hFn_clauses])) rfl (app_mk hG rfl ((hg _).mpr hb.symm)) (fun t ht => nomatch ht) .top

/-- Where neither has a value at x, h has none, by the last clause's `ensures` false. -/
theorem evalH_none (h1 : rf = none) (h2 : rg = none) : Eval c H [iv x] none := by
  have hp := Holds.and (Holds.not (ceil_mk hF (σ := sg (iv x)) rfl hf 1 Srt.int))
    (Holds.not (ceil_mk hG (σ := sg (iv x)) rfl hg 1 Srt.int))
  rw [h1, h2] at hp
  exact .ensFails (cl := hCl3) hH (by simp [hFn_clauses]) (sg_sorted x) (sg_match _) (fun t ht => nomatch ht) hp
    (hprio (by simp [hFn_clauses])) rfl rfl .dv (by decide)

end Results

/-! ### `Fx` -/

namespace Fx

theorem lookupH : c.lookupFn H = some hFn := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupF : c.lookupFn F = some fFn := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn G = some gFn := by rw [Semantics.lookupFn_eq]; rfl
theorem isFnF : IsFn c F := by unfold IsFn; decide +kernel
theorem isFnG : IsFn c G := by unfold IsFn; decide +kernel
theorem kindsSub : c.isCtor intSub = false ∧ isHook intSub = true ∧ c.isOvl intSub = false := by decide +kernel

/-- f(x) is x. -/
theorem evalF (x : Int) : ∀ r, Eval c F [iv x] r ↔ r = some (iv x) := fun r => by
  simpa using eval1_iff (ok := true) lookupF rfl (fun σ hl => uniq_var hl) (fun _ _ t ht => nomatch ht) (fun _ => rfl) r

/-- g(x) is 0 - x. -/
theorem evalG (x : Int) : ∀ r, Eval c G [iv x] r ↔ r = some (iv (0 - x)) := fun r => by
  simpa using eval1_iff (ok := true) (rr := some (iv (0 - x))) lookupG rfl
    (fun σ hl => uniq_hook2 kindsSub.1 kindsSub.2.1 kindsSub.2.2 (uniq_dv _ _) (uniq_var hl) rfl)
    (fun _ _ t ht => nomatch ht) (fun _ => rfl) r

theorem evalH_inv' {x : Int} {r : Option GroundTerm} (h : Eval c H [iv x] r) :
    r = some (iv x) ∨ r = some (iv (-x)) := by
  rcases evalH_inv lookupH isFnF isFnG (evalF x) (evalG x) h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨h1, -, -⟩
  · exact .inl rfl
  · exact .inr (by rw [Int.zero_sub])
  · exact absurd h1 (by simp)

theorem evalH_x (x : Int) : Eval c H [iv x] (some (iv x)) := evalH_f lookupH isFnF (evalF x) rfl
theorem evalH_negx (x : Int) : Eval c H [iv x] (some (iv (-x))) := by
  rw [← Int.zero_sub]; exact evalH_g lookupH isFnG (evalG x) rfl

theorem not_fnDet : ¬ FnDet c := fun h => absurd (h H [iv 1] _ _ (evalH_x 1) (evalH_negx 1)) (by decide)

theorem not_fnHyp : ¬ FnHyp c := fun h => not_fnDet (fnModel_of_fnHyp coreOK_now h).1

theorem noWitCl : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = false := by decide +kernel

open ML Faithful in
/-- **`Γc` has no model**: h(1) would denote the element of 1, its result by the first clause, and
the element of -1, its result by the second, which are apart. -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γc c) := by
  intro M _ I hIc
  obtain ⟨hok, hsr, -, -, hph, -, -, -, hno⟩ := hypSound_of_core coreOK_now
  haveI : OvlOK c := hno
  have F := HoldsShape.nodeFacts_of_core coreOK_now hIc
  have hden := fun (r : Option GroundTerm) (hev : Eval c H [iv 1] r) (e : Valuation M) (m : M) =>
    Faithful.eval_den4_coreCl hIc (Semantics.sortedOKCl_of_sortedOK_noExs hok (Semantics.fnsNoExs_of_all (by decide +kernel))) hsr (Semantics.coreOK_parts coreOK_now).2.1 hph
      (fun fn hfn cl hcl hw => absurd hw (by rw [noWitCl fn hfn cl hcl]; decide))
      (HoldsShape.preReadAll_of_core coreOK_now hIc) hev lookupH (by decide +kernel) e m
  let e : Valuation M := ⟨fun _ => default, fun _ _ => False⟩
  obtain ⟨a, ha, -⟩ := F.val (rmS_sortOf_int c 1) [] e
  have h1 := (hden _ (evalH_x 1) e a).mpr ((ha a).mpr rfl)
  have h2 := (hden _ (evalH_negx 1) e a).mp h1
  have := F.apart (rmS_sortOf_int c 1) (rmS_sortOf_int c (-1)) e a ((ha a).mpr rfl) h2
  simp [int] at this

theorem not_consistent : ¬ Consistent c := fun ⟨M, hM, I, hI⟩ =>
  no_model M hM I (fun φ hφ => hI φ (Or.inl hφ))

/-- **`expect` holds.** -/
theorem expect_holds : expect := by
  refine ⟨coreOK_now, ⟨evalH_x 0, fun r h => ?_⟩, fun x _ => ⟨evalH_x x, evalH_negx x, fun r h => evalH_inv' h⟩,
    not_fnDet, not_fnHyp, not_consistent⟩
  rcases evalH_inv' h with rfl | rfl <;> simp

end Fx

/-! ### `Pt` -/

namespace Pt

theorem lookupH : c.lookupFn H = some hFn := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupF : c.lookupFn F = some fFn := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn G = some gFn := by rw [Semantics.lookupFn_eq]; rfl
theorem isFnF : IsFn c F := by unfold IsFn; decide +kernel
theorem isFnG : IsFn c G := by unfold IsFn; decide +kernel
theorem kinds2 (f : Sym) (hf : f = intSub ∨ f = intGe ∨ f = intLe ∨ f = boolAnd) :
    c.isCtor f = false ∧ isHook f = true ∧ c.isOvl f = false := by
  rcases hf with rfl | rfl | rfl | rfl <;> decide +kernel

/-- f(x) is x where x ≥ 0, and has no value elsewhere. -/
theorem evalF (x : Int) : ∀ r, Eval c F [iv x] r ↔ r = if decide (x ≥ 0) then some (iv x) else none :=
  eval1_iff lookupF rfl (fun σ hl => uniq_var hl)
    (fun σ hl t ht => by
      cases ht
      have k := kinds2 intGe (by simp)
      exact uniq_hook2 k.1 k.2.1 k.2.2 (uniq_var hl) (uniq_dv _ _) rfl)
    (fun h => nomatch h)

/-- g(x) is -x where -1 ≤ x ≤ 1, and has no value elsewhere. -/
theorem evalG (x : Int) : ∀ r, Eval c G [iv x] r ↔
    r = if (decide (x ≤ 1) && decide (-1 ≤ x)) then some (iv (0 - x)) else none :=
  eval1_iff lookupG rfl
    (fun σ hl => by
      have k := kinds2 intSub (by simp)
      exact uniq_hook2 k.1 k.2.1 k.2.2 (uniq_dv _ _) (uniq_var hl) rfl)
    (fun σ hl t ht => by
      cases ht
      have ka := kinds2 boolAnd (by simp)
      have kl := kinds2 intLe (by simp)
      exact uniq_hook2 ka.1 ka.2.1 ka.2.2 (uniq_hook2 kl.1 kl.2.1 kl.2.2 (uniq_var hl) (uniq_dv _ _) rfl)
        (uniq_hook2 kl.1 kl.2.1 kl.2.2 (uniq_dv _ _) (uniq_var hl) rfl) rfl)
    (fun h => nomatch h)

theorem expectCore_holds : expectCore := coreOK_now

theorem res (x : Int) {r : Option GroundTerm} (h : Eval c H [iv x] r) :
    ((if decide (x ≥ 0) then some (iv x) else none).isSome ∧ r = if decide (x ≥ 0) then some (iv x) else none) ∨
    ((if (decide (x ≤ 1) && decide (-1 ≤ x)) then some (iv (0 - x)) else none).isSome ∧
      r = if (decide (x ≤ 1) && decide (-1 ≤ x)) then some (iv (0 - x)) else none) ∨
    ((if decide (x ≥ 0) then some (iv x) else none) = none ∧
      (if (decide (x ≤ 1) && decide (-1 ≤ x)) then some (iv (0 - x)) else none) = none ∧ r = none) :=
  evalH_inv lookupH isFnF isFnG (evalF x) (evalG x) h

theorem expectAgree_holds : expectAgree := by
  refine ⟨evalH_f lookupH isFnF (evalF 0) (by decide), fun r h => ?_⟩
  rcases res 0 h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨h1, -, -⟩
  · decide
  · decide
  · exact absurd h1 (by decide)

theorem expectOneUndefined_holds : expectOneUndefined := by
  refine ⟨⟨evalH_f lookupH isFnF (evalF 2) (by decide), fun r h => ?_⟩,
    ⟨evalH_g lookupH isFnG (evalG (-1)) (by decide), fun r h => ?_⟩⟩
  · rcases res 2 h with ⟨-, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -, -⟩
    · decide
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
  · rcases res (-1) h with ⟨h1, -⟩ | ⟨-, rfl⟩ | ⟨-, h2, -⟩
    · exact absurd h1 (by decide)
    · decide
    · exact absurd h2 (by decide)

theorem eval1 : Eval c H [iv 1] (some (iv 1)) := evalH_f lookupH isFnF (evalF 1) (by decide)
theorem evalm1 : Eval c H [iv 1] (some (iv (-1))) := evalH_g lookupH isFnG (evalG 1) (by decide)

theorem noWitCl : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = false := by decide +kernel

open ML Faithful in
/-- **`Γc` has no model**: h(1) would denote the elements of 1 and of -1. -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γc c) := by
  intro M _ I hIc
  obtain ⟨hok, hsr, -, -, hph, -, -, -, hno⟩ := hypSound_of_core coreOK_now
  haveI : OvlOK c := hno
  have F := HoldsShape.nodeFacts_of_core coreOK_now hIc
  have hden := fun (r : Option GroundTerm) (hev : Eval c H [iv 1] r) (e : Valuation M) (m : M) =>
    Faithful.eval_den4_coreCl hIc (Semantics.sortedOKCl_of_sortedOK_noExs hok (Semantics.fnsNoExs_of_all (by decide +kernel))) hsr (Semantics.coreOK_parts coreOK_now).2.1 hph
      (fun fn hfn cl hcl hw => absurd hw (by rw [noWitCl fn hfn cl hcl]; decide))
      (HoldsShape.preReadAll_of_core coreOK_now hIc) hev lookupH (by decide +kernel) e m
  let e : Valuation M := ⟨fun _ => default, fun _ _ => False⟩
  obtain ⟨a, ha, -⟩ := F.val (rmS_sortOf_int c 1) [] e
  have h1 := (hden _ eval1 e a).mpr ((ha a).mpr rfl)
  have h2 := (hden _ evalm1 e a).mp h1
  have := F.apart (rmS_sortOf_int c 1) (rmS_sortOf_int c (-1)) e a ((ha a).mpr rfl) h2
  simp [int] at this

theorem expectDiffer_holds : expectDiffer := by
  refine ⟨eval1, evalm1, fun r h => ?_, fun h => absurd (h H [iv 1] _ _ eval1 evalm1) (by decide),
    fun ⟨M, hM, I, hI⟩ => no_model M hM I (fun φ hφ => hI φ (Or.inl hφ))⟩
  rcases res 1 h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨h1, -, -⟩
  · exact .inl (by decide)
  · exact .inr (by decide)
  · exact absurd h1 (by decide)

theorem expectNeither_holds : expectNeither := by
  have hn : Eval c H [iv (-2)] none := evalH_none lookupH isFnF isFnG (evalF (-2)) (evalG (-2)) (by decide) (by decide)
  have honly : ∀ r, Eval c H [iv (-2)] r → r = none := fun r h => by
    rcases res (-2) h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, rfl⟩
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · rfl
  refine ⟨⟨hn, honly⟩, fun ht => ?_⟩
  obtain ⟨v, hv⟩ := ht hFn (by simp [c, sem]) rfl [iv (-2)] (by decide +kernel)
  exact absurd (honly _ hv) (by simp)

end Pt


/-! ## The fixtures through the reader

On the kompiled texts (from the cache `kfix.py` keeps): `e3-ml-eq-rhs-or-total` gives h the clauses
`hCl1`, `hCl2`, `hCl3` (`Parse.clauses?`), and the definition `parse` reads from it has `Fx`'s three
functions (f, g and h, in the text's numbering, which is `sem`'s); `e3-ml-eq-rhs-or` (h without its
`functional` sentence) and `e3-ml-eq-rhs-or-many` (nine alternatives) are refused
`manyValuedRightSide`, each with its whole detail. The reader's clauses of h are `Parse.frClauses`'
by the kernel in test/ReaderWire.lean (`Stages.cls2_frClauses`, on `f2-examples/mleqort`, the same
text). -/

section Fixtures

/-- The cache of kompiled fixture texts, as test/constructs/kfix.py names it. -/
def cacheDir : IO String := do
  let get := fun (n : String) => do
    match ← IO.getEnv n with
    | some d => pure (if d.isEmpty then none else some d)
    | none => pure none
  if let some d ← get "KCORE_KFIX_CACHE" then return d
  if let some d ← get "XDG_CACHE_HOME" then return s!"{d}/kcore-kfix"
  let home := (← get "HOME").getD "."
  return s!"{home}/.cache/kcore-kfix"

/-- The kompiled text of fixture `n`, its `BUILTIN/` and `FIXTURE/` paths restored to made-up
directories (as `kfix.py accounts` restores them before reading). -/
def load (n : String) : IO Kore.Definition := do
  let t ← IO.FS.readFile s!"test/constructs/fixtures/{n}/kompile.txt"
  let some l := (t.splitOn "\n").find? (·.startsWith "definition.kore sha256: ")
    | throw (IO.userError s!"{n}: kompile.txt names no sha256")
  let sha := (l.splitOn ": ").getD 1 ""
  let raw ← IO.FS.readFile s!"{← cacheDir}/{sha}.kore"
  let raw := ((raw.replace "BUILTIN/" "/made-up-k/include/kframework/builtin/").replace "FIXTURE/" "/made-up-fx/").replace
    "FIXTURE" "/made-up-fx"
  match Kore.parseDefinition raw with
  | .ok k => pure k
  | .error e => throw (IO.userError s!"{n}: KORE read error {e}")

/-- The reader on fixture `n`: the clauses of `fn`'s equations, whether they are h's three, and
`parse`'s verdict, with whether the functions read are `Fx`'s. -/
def runOr (n fn : String) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  let S := Parse.scan m.sentences
  match Parse.envOf m S with
  | .error f => IO.println s!"{n}: envOf fails {f.reason.name}"
  | .ok E =>
    for e in S.eqs.filter (·.fn == fn) do
      match Parse.clauses? E.N E.src e none with
      | .ok xs => IO.println s!"{n} {fn}: {xs.length} clauses; hCl1, hCl2, hCl3: {reprStr (xs.map (·.1)) == reprStr [hCl1, hCl2, hCl3]}"
      | .error f => IO.println s!"{n} {fn}: refused {f.reason.name} ({f.detail})"
  match Parse.parse k with
  | .error r => IO.println s!"  parse: refused {r.reason.name} ({r.detail})"
  | .ok d => IO.println s!"  parse: read; coreOK {d.sem.coreOK}; the functions are Fx's: {reprStr d.sem.fns == reprStr Fx.c.fns}"

/--
info: e3-ml-eq-rhs-or-total Lblh: 3 clauses; hCl1, hCl2, hCl3: true
  parse: read; coreOK true; the functions are Fx's: true
e3-ml-eq-rhs-or Lblh: refused manyValuedRightSide (\or: the sentence gives the function every element of each side; the text holds no functional sentence of the function, so where the sides differ that is more than one element, which no clause states)
  parse: refused manyValuedRightSide (\or: the sentence gives the function every element of each side; the text holds no functional sentence of the function, so where the sides differ that is more than one element, which no clause states)
e3-ml-eq-rhs-or-many Lblk: refused manyValuedRightSide (\or: 9 alternatives, more than 8)
  parse: refused manyValuedRightSide (\or: 9 alternatives, more than 8)
-/
#guard_msgs in
#eval show IO Unit from do
  runOr "e3-ml-eq-rhs-or-total" "Lblh"
  runOr "e3-ml-eq-rhs-or" "Lblh"
  runOr "e3-ml-eq-rhs-or-many" "Lblk"

end Fixtures

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
/-- info: 'KCore.EqRhsOr.Fx.expect_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Fx.expect_holds
/-- info: 'KCore.EqRhsOr.Fx.no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Fx.no_model
/-- info: 'KCore.EqRhsOr.Pt.expectAgree_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Pt.expectAgree_holds
/-- info: 'KCore.EqRhsOr.Pt.expectOneUndefined_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Pt.expectOneUndefined_holds
/-- info: 'KCore.EqRhsOr.Pt.expectDiffer_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Pt.expectDiffer_holds
/-- info: 'KCore.EqRhsOr.Pt.expectNeither_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.EqRhsOr.Pt.expectNeither_holds
