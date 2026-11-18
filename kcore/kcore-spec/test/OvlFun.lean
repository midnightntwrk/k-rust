/-
  Overloads by functions: semantics built by hand from the fixtures' kompiled sentences, the facts
  that hold of them now, and the expectations the function-overload construct is to meet, as
  propositions to prove (`expect`, `expectOvlfun`, `expectLhs` in each namespace, elaborated here, proved by the tickets that build the
  construct). Run from the package root: `lake env lean -j1 test/OvlFun.lean`.

  Each semantics has the configuration `<generatedTop>(<k>(K), C)`, its own sorts numbered from
  `nRegSorts` and its own symbols from `nRegSyms` (the sort predicates first, then constructors,
  functions and overloading symbols). Every condition of `coreOK` but `overloadsOK` holds of each
  but `lhs` (`others_…`), and so does `overloadsOK`, which admits an overload by a function
  (`Admit.ovls_…`), hence `coreOK` (`Admit.coreOK_…`); `lhs` fails `sortedOK` and `ovlPatsOK`.
  `overloadsOK` refuses the chain whose larger symbol does not list the function it reaches
  (`Admit.chain_false`: every other leaf holds) and two functions meeting under one overloading
  symbol (`Admit.two_refused`: `ovlCoherent` alone fails).

  - `e5` (test/constructs/fixtures/e5-ovl-fun): `plusExp : Exp Exp → Exp` (`anywhere`, sentence
    `symbol LblplusExp`), the function `plusInt : Int Int → Int` (`function`, not total) with the
    equation `plusInt(X0, X1) = X0 +Int X1`, Int < Exp, and the overload equation
    `plusExp(inj X0, inj X1) = inj(plusInt(X0, X1))` (`symbol-overload`). Expected: `coreOK`,
    `FnHyp`, `Consistent`, and `plusExp(inj 1, inj 2)` evaluates to `inj 3`. Also to settle (prove,
    or record as argued): the text's no-confusion sentence of `plusExp` and its overload equation,
    with the injectivity of `inj{Int,Exp}` and `1 ≠ 2`, have no model (`plusExp(inj 1, inj 2)` and
    `plusExp(inj 2, inj 1)` are both `inj 3`); this is a fact of the text, not of `Γ`, and the
    account's note states it only as a condition.
  - `ovlfun` (f2-examples/ovlfun.k): `capGas : Gas → Gas` overloads the total function
    `capN : N → N`, N < Gas, `capN(z #as G0) = G0`, and the rule `run(G) => done(cap(G))`. Expected:
    `capGas(inj z)` evaluates to `inj z`; `coreOK`, `FnHyp`, `Consistent`.
  - `keep` (e5-ovl-fun-keep): the overload keeps the result sort: `capN : N → Gas` total,
    `capN(z) = inf`, the overload equation `capGas(inj X0) = capN(X0)` (no injection on the right).
    Expected: `capGas(inj z)` evaluates to `inf`; `coreOK`, `FnHyp`, `Consistent`.
  - `lhs` (e5-ovl-fun-lhs): `ovlfun`'s signature with the rule `run(cap(G)) => done(G)`: `capGas`
    in a left side. The left side is not sorted over `patCtxNF`, so `sortedOK` is false
    (`sorted_lhs`), and `ovlPatsOK` is false (`fnOvl_facts`); expected: `coreOK` false.
  - `chain b` (REVIEW-CN4 finding B): `plusExp : Exp Exp → Exp` over the function `plusInt`,
    `plusBig : Big Big → Big` over `plusExp` (and `plusInt` where `b`), Int < Exp < Big. Without
    `plusInt` in `plusBig`'s list, `plusBig` is not function-overloaded (`fnOvlSyms`); with it,
    it is, and a left side applying it is refused (`ruleSorted`, `ovlPatsOK`). Expected: `coreOK` false without
    it; `coreOK`, `FnHyp`, `Consistent` with it.
  - `conf over` (REVIEW-CN4 finding A): `fS : A → S` overloads the result-keeping function
    `fB : B → S`, B < A, `fB(X) = fB(X)` (no value at `b`), the total `p : S → Bool`, `p(_) = true`,
    and the rules `x => y requires p(H)` (H of S, not bound by the left side) and `x => z` with
    priority 200. S is not confined (`confined_S`), by the conjunct of `confinedAt` on a generator
    that overloads a function: with `fS` overloading nothing, S is confined (`confined_S_control`).
    Expected: `coreOK`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OvlFun

/-! ## The configuration -/

/-- `<generatedTop>`, `<k>`, the counter and their optional sorts, with the k cell's sort `kc`
(the cell's optional sort `kc + 1`) and its constructor `kl` (`noKCell` `kl + 1`). -/
def cellSorts (kc : Srt) : List Srt := [Srt.top, Srt.topFrag, kc, kc + 1, Srt.counter, Srt.counterOpt]
def cellCtors (kc : Srt) (kl : Sym) : List CtorSig :=
  [⟨topLabel, [kc, Srt.counter], Srt.top⟩, ⟨topFragLabel, [kc + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨kl, [Srt.k], kc⟩, ⟨kl + 1, [], kc + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts (kc : Srt) : List (Srt × Srt) := [(kc, kc + 1), (Srt.counter, Srt.counterOpt)]

/-- The library: Int and Bool below KItem, `#KConfigValue`. -/
def lib0 : Lib := { sortsBelowKItem := [Srt.int, Srt.bool], ctors := [⟨kconfigValue, [Srt.k], Srt.kitem⟩] }

/-- `<generatedTop>(<k>(kseq(inj{s,KItem}(t), dotk)), C)`, C the variable `cnt`. -/
def cfg (kl : Sym) (s : Srt) (t : Term) (cnt : Nat) : Term :=
  .app topLabel [.app kl [.app kseq [.inj s Srt.kitem t, .app dotk []]], .var cnt]

def intT (i : Int) : Term := .dv Srt.int (.int i)

/-- Every condition of `coreOK` but `overloadsOK`. -/
def others (c : Semantics) : Bool := c.sortedOK && c.faithCoreOK && c.hooksApart && c.predsApart && c.idsOK

open Faithful Faithful.Model in
/-- The conditions of `others` but the two of `faithCoreOK` that compare names (`namesApartK`,
`itesApart`), each of which the kernel decides here within a few GiB on its own. -/
def light (c : Semantics) : Bool :=
  c.sortedOK && c.hooksApart && c.predsApart && c.idsOK && namesNumbered c && genWf c && collSortsOK c &&
    collsOK c && patHeadsOK c && LitsApart c && sortsNumbered c && kindsApart c && ctorsOnce c && fnsApart c

open Faithful Faithful.Model in
theorem others_of {c : Semantics} (h : light c = true) (hn : namesApartFast c = true) (hi : itesApart c = true) :
    others c = true := by
  unfold light at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  unfold others Semantics.faithCoreOK
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, namesApartK_of_fast hn, hi, Bool.and_self]

/-! ## e5-ovl-fun -/

namespace E5

def expS : Srt := nRegSorts
def kl : Sym := nRegSyms + 3
def plusInt : Sym := nRegSyms + 5
def plusExp : Sym := nRegSyms + 6

def plusIntFn : Fn :=
  ⟨plusInt, [Srt.int, Srt.int], Srt.int,
    [{ vars := [Srt.int, Srt.int], pats := [.var 0, .var 1], req := none,
       rhs := .app intAdd [.var 0, .var 1], ens := none }], false⟩

def c : Semantics :=
  { lib := lib0
    sortNames := ["Exp", "KCell", "KCellOpt"]
    symNames := ["LblisExp", "LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "LblplusInt",
      "LblplusExp"]
    userSorts := [Srt.top, Srt.topFrag, expS, expS + 1, expS + 2, Srt.counter, Srt.counterOpt]
    ctors := cellCtors (expS + 1) kl
    fns := [plusIntFn]
    userSubsorts := (Srt.int, expS) :: cellSubsorts (expS + 1)
    pgmSort := Srt.k
    rules := []
    ovls := [⟨⟨plusExp, [expS, expS], expS⟩, [plusInt]⟩] }

theorem light_ok : light c = true := by rw [light]; decide_cheap

open Faithful.Model in
theorem names_ok : namesApartFast c = true := by decide +kernel

open Faithful.Model in
theorem ites_ok : itesApart c = true := by decide_cheap

theorem others_ok : others c = true := others_of light_ok names_ok ites_ok

theorem fnOvl_facts : c.fnOvlSyms = [plusExp] ∧ c.ovlPatsOK = true ∧ c.isOvl plusExp = true := by
  decide +kernel

/-- `consItemsK` writes the functionality and the injectivity of `plusExp` at uncovered arguments
(one item of each rule, `plusExp` being the one function-overloaded symbol), and neither at every
argument. -/
theorem cons_items :
    ((Faithful.consItemsK c).filter (·.rule == "Cons-Fun-Unc")).length = 1 ∧
    ((Faithful.consItemsK c).filter (·.rule == "Cons-Inj-Unc")).length = 1 ∧
    ((Faithful.consItemsK c).any fun it =>
      it.pat == (KoreAML.Cons.funItem "Exp" (Gen.toK c (.ctor ⟨plusExp, [expS, expS], expS⟩))).pat ||
      it.pat == (KoreAML.Cons.injItem "Exp" (Gen.toK c (.ctor ⟨plusExp, [expS, expS], expS⟩))).pat) = false := by
  decide +kernel

/-- `ovlOver` reads the function's signature, which `ovlByFn` tells from a constructor's; the
arguments `inj{Int,Exp}(1), inj{Int,Exp}(2)` are covered and `norm` leaves the application as it is
(no function on values gives `1 + 2`), which is no value (`sortOf`). -/
theorem norm_facts :
    c.ovlOver ⟨⟨plusExp, [expS, expS], expS⟩, [plusInt]⟩ = [⟨plusInt, [Srt.int, Srt.int], Srt.int⟩] ∧
    c.ovlByFn ⟨plusInt, [Srt.int, Srt.int], Srt.int⟩ = true ∧
    c.uncovered plusExp [.inj Srt.int expS (.dv Srt.int (.int 1)), .inj Srt.int expS (.dv Srt.int (.int 2))] = false ∧
    c.norm plusExp [.inj Srt.int expS (.dv Srt.int (.int 1)), .inj Srt.int expS (.dv Srt.int (.int 2))] =
      .ctor plusExp [.inj Srt.int expS (.dv Srt.int (.int 1)), .inj Srt.int expS (.dv Srt.int (.int 2))] ∧
    c.sortOf (.ctor plusExp [.inj Srt.int expS (.dv Srt.int (.int 1)), .inj Srt.int expS (.dv Srt.int (.int 2))]) = none := by
  decide +kernel

/-- The function overload `plusInt` covers `inj{Int,Exp}(1), inj{Int,Exp}(2)` (`fnCover`), and no
function overload covers two arguments that are no injections from Int. -/
theorem fnCover_facts :
    c.fnCover plusExp [.inj Srt.int expS (.dv Srt.int (.int 1)), .inj Srt.int expS (.dv Srt.int (.int 2))] =
      some ⟨plusInt, [Srt.int, Srt.int], Srt.int⟩ ∧
    c.fnCover plusExp [.ctor plusExp [], .ctor plusExp []] = none ∧
    c.fnCover plusInt [.dv Srt.int (.int 1), .dv Srt.int (.int 2)] = none := by
  decide +kernel

/-- The uncovered items of `plusExp` are guarded by the function's argument sorts. -/
theorem cons_covs :
    ((Faithful.consItemsK c).any fun it =>
      it.pat == (KoreAML.Cons.funUncItem "Exp" (Gen.toK c (.ctor ⟨plusExp, [expS, expS], expS⟩)) [["Int", "Int"]]).pat) = true ∧
    ((Faithful.consItemsK c).any fun it =>
      it.pat == (KoreAML.Cons.injUncItem "Exp" (Gen.toK c (.ctor ⟨plusExp, [expS, expS], expS⟩)) [["Int", "Int"]]).pat) = true := by
  decide +kernel

/-- `plusExp(inj{Int,Exp}(1), inj{Int,Exp}(2))`. -/
def app12 : Term := .app plusExp [.inj Srt.int expS (intT 1), .inj Srt.int expS (intT 2)]

def expect : Prop :=
  c.coreOK = true ∧ FnHyp c ∧ Consistent c ∧
    EvalTerm c [] app12 (some (.inj Srt.int expS (.dv Srt.int (.int 3))))

end E5

/-! ## ovlfun and e5-ovl-fun-lhs -/

namespace Cap

def gasS : Srt := nRegSorts
def nS : Srt := nRegSorts + 1
def pgmS : Srt := nRegSorts + 2
def kl : Sym := nRegSyms + 5
def done : Sym := nRegSyms + 7
def inf : Sym := nRegSyms + 8
def run : Sym := nRegSyms + 9
def z : Sym := nRegSyms + 10
def capN : Sym := nRegSyms + 11
def capGas : Sym := nRegSyms + 12

/-- `capN : N → N`, total, with the text's equation `capN(z #as G0) = G0`. -/
def capNFn : Fn :=
  ⟨capN, [nS], nS, [{ vars := [nS], pats := [.as (.app z []) 0], req := none, rhs := .var 0, ens := none }], true⟩

/-- `<k> run(G) => done(cap(G)) </k>` (ovlfun) -/
def rWrap : Rule :=
  { vars := [gasS, Srt.counter], lhs := cfg kl pgmS (.app run [.var 0]) 1, req := none,
    rhs := cfg kl pgmS (.app done [.app capGas [.var 0]]) 1, ens := none, prio := 50 }

/-- `<k> run(cap(G)) => done(G) </k>` (e5-ovl-fun-lhs) -/
def rLhs : Rule :=
  { vars := [gasS, Srt.counter], lhs := cfg kl pgmS (.app run [.app capGas [.var 0]]) 1, req := none,
    rhs := cfg kl pgmS (.app done [.var 0]) 1, ens := none, prio := 50 }

def sem (r : Rule) : Semantics :=
  { lib := lib0
    sortNames := ["Gas", "N", "Pgm", "KCell", "KCellOpt"]
    symNames := ["LblisGas", "LblisN", "LblisPgm", "LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'",
      "LblnoKCell", "Lbldone", "Lblinf", "Lblrun", "Lblz", "LblcapN", "LblcapGas"]
    userSorts := [Srt.top, Srt.topFrag, gasS, nS, pgmS, pgmS + 1, pgmS + 2, Srt.counter, Srt.counterOpt]
    ctors := cellCtors (pgmS + 1) kl ++
      [⟨done, [gasS], pgmS⟩, ⟨inf, [], gasS⟩, ⟨run, [gasS], pgmS⟩, ⟨z, [], nS⟩]
    fns := [capNFn]
    userSubsorts := (nS, gasS) :: cellSubsorts (pgmS + 1)
    pgmSort := pgmS
    rules := [r]
    ovls := [⟨⟨capGas, [gasS], gasS⟩, [capN]⟩] }

/-- ovlfun. -/
def ovlfun : Semantics := sem rWrap
/-- e5-ovl-fun-lhs. -/
def lhs : Semantics := sem rLhs

theorem light_ovlfun : light ovlfun = true := by rw [light]; decide_cheap

open Faithful.Model in
theorem names_ovlfun : namesApartFast ovlfun = true := by decide +kernel

open Faithful.Model in
theorem ites_ovlfun : itesApart ovlfun = true := by decide_cheap

theorem others_ovlfun : others ovlfun = true := others_of light_ovlfun names_ovlfun ites_ovlfun

/-- The rule's left side applies `capGas`, which `patCtxNF` holds no signature of. -/
theorem sorted_lhs : lhs.sortedOK = false := by decide +kernel

open Faithful.Model in
theorem names_lhs : namesApartFast lhs = true := by decide +kernel

open Faithful.Model in
theorem ites_lhs : itesApart lhs = true := by decide_cheap

/-- `capGas` is function-overloaded; it is refused in `lhs`'s left side, not in `ovlfun`'s right. -/
theorem fnOvl_facts : ovlfun.fnOvlSyms = [capGas] ∧ ovlfun.ovlPatsOK = true ∧ lhs.ovlPatsOK = false := by
  decide +kernel

/-- `consItemsK` writes the functionality and the injectivity of `capGas` and its distinctness from
each other generator of Gas (the constructor `inf`, whose overload closure does not meet `capGas`'s,
and the injection from N) at uncovered arguments, and none of them at every argument. -/
theorem cons_items :
    ((Faithful.consItemsK ovlfun).filter (·.rule == "Cons-Fun-Unc")).length = 1 ∧
    ((Faithful.consItemsK ovlfun).filter (·.rule == "Cons-Inj-Unc")).length = 1 ∧
    ((Faithful.consItemsK ovlfun).filter (·.rule == "Cons-Dist-Unc")).length = 2 ∧
    ((Faithful.consItemsK ovlfun).any fun it =>
      it.pat == (KoreAML.Cons.funItem "Gas" (Gen.toK ovlfun (.ctor ⟨capGas, [gasS], gasS⟩))).pat ||
      it.pat == (KoreAML.Cons.injItem "Gas" (Gen.toK ovlfun (.ctor ⟨capGas, [gasS], gasS⟩))).pat ||
      it.pat == (KoreAML.Cons.distItem "Gas" (Gen.toK ovlfun (.ctor ⟨inf, [], gasS⟩))
        (Gen.toK ovlfun (.ctor ⟨capGas, [gasS], gasS⟩))).pat) = false ∧
    ovlfun.distGuarded (.ctor ⟨inf, [], gasS⟩) (.ctor ⟨capGas, [gasS], gasS⟩) = true := by
  decide +kernel

/-- `capGas` at `inf`, which no overload covers, is its raw application, a value of Gas; at
`inj{N,Gas}(z)`, which the function `capN` covers, `norm` leaves the application as it is, and it is
no value. -/
theorem norm_facts :
    ovlfun.uncovered capGas [.ctor inf []] = true ∧
    ovlfun.norm capGas [.ctor inf []] = .ctor capGas [.ctor inf []] ∧
    ovlfun.sortOf (.ctor capGas [.ctor inf []]) = some gasS ∧
    ovlfun.uncovered capGas [.inj nS gasS (.ctor z [])] = false ∧
    ovlfun.norm capGas [.inj nS gasS (.ctor z [])] = .ctor capGas [.inj nS gasS (.ctor z [])] ∧
    ovlfun.sortOf (.ctor capGas [.inj nS gasS (.ctor z [])]) = none := by
  decide +kernel

/-- The function overload `capN` covers `inj{N,Gas}(z)` (`fnCover`); no function overload covers
`inf`. -/
theorem fnCover_facts :
    (ovlfun.fnCover capGas [.inj nS gasS (.ctor z [])]).map (·.name) = some capN ∧
    ovlfun.fnCover capGas [.ctor inf []] = none := by
  decide +kernel

/-- `capGas(inj{N,Gas}(z))`. -/
def capZ : Term := .app capGas [.inj nS gasS (.app z [])]

def expectOvlfun : Prop :=
  ovlfun.coreOK = true ∧ FnHyp ovlfun ∧ Consistent ovlfun ∧
    EvalTerm ovlfun [] capZ (some (.inj nS gasS (.ctor z [])))

def expectLhs : Prop := lhs.coreOK = false

end Cap

/-! ## e5-ovl-fun-keep -/

namespace Keep

def gasS : Srt := nRegSorts
def nS : Srt := nRegSorts + 1
def kl : Sym := nRegSyms + 4
def inf : Sym := nRegSyms + 6
def z : Sym := nRegSyms + 7
def capN : Sym := nRegSyms + 8
def capGas : Sym := nRegSyms + 9

/-- `capN : N → Gas`, total, `capN(z) = inf`. -/
def capNFn : Fn :=
  ⟨capN, [nS], gasS, [{ vars := [], pats := [.app z []], req := none, rhs := .app inf [], ens := none }], true⟩

def c : Semantics :=
  { lib := lib0
    sortNames := ["Gas", "N", "KCell", "KCellOpt"]
    symNames := ["LblisGas", "LblisN", "LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell",
      "Lblinf", "Lblz", "LblcapN", "LblcapGas"]
    userSorts := [Srt.top, Srt.topFrag, gasS, nS, nS + 1, nS + 2, Srt.counter, Srt.counterOpt]
    ctors := cellCtors (nS + 1) kl ++ [⟨inf, [], gasS⟩, ⟨z, [], nS⟩]
    fns := [capNFn]
    userSubsorts := (nS, gasS) :: cellSubsorts (nS + 1)
    pgmSort := Srt.k
    rules := []
    ovls := [⟨⟨capGas, [gasS], gasS⟩, [capN]⟩] }

theorem light_ok : light c = true := by rw [light]; decide_cheap

open Faithful.Model in
theorem names_ok : namesApartFast c = true := by decide +kernel

open Faithful.Model in
theorem ites_ok : itesApart c = true := by decide_cheap

theorem others_ok : others c = true := others_of light_ok names_ok ites_ok

theorem fnOvl_facts : c.fnOvlSyms = [capGas] ∧ c.ovlPatsOK = true := by decide +kernel

def capZ : Term := .app capGas [.inj nS gasS (.app z [])]

def expect : Prop :=
  c.coreOK = true ∧ FnHyp c ∧ Consistent c ∧ EvalTerm c [] capZ (some (.ctor inf []))

end Keep

/-! ## The three-level chain (REVIEW-CN4 finding B) -/

namespace Chain

def expS : Srt := nRegSorts
def bigS : Srt := nRegSorts + 1
def kl : Sym := nRegSyms + 4
def plusInt : Sym := nRegSyms + 6
def plusExp : Sym := nRegSyms + 7
def plusBig : Sym := nRegSyms + 8

/-- `plusBig` overloads `plusExp`, and `plusInt` where `b`. -/
def c (b : Bool) : Semantics :=
  { lib := lib0
    sortNames := ["Exp", "Big", "KCell", "KCellOpt"]
    symNames := ["LblisExp", "LblisBig", "LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell",
      "LblplusInt", "LblplusExp", "LblplusBig"]
    userSorts := [Srt.top, Srt.topFrag, expS, bigS, bigS + 1, bigS + 2, Srt.counter, Srt.counterOpt]
    ctors := cellCtors (bigS + 1) kl
    fns := [⟨plusInt, [Srt.int, Srt.int], Srt.int,
      [{ vars := [Srt.int, Srt.int], pats := [.var 0, .var 1], req := none,
         rhs := .app intAdd [.var 0, .var 1], ens := none }], false⟩]
    userSubsorts := [(Srt.int, expS), (expS, bigS)] ++ cellSubsorts (bigS + 1)
    pgmSort := Srt.k
    rules := []
    ovls := [⟨⟨plusExp, [expS, expS], expS⟩, [plusInt]⟩,
      ⟨⟨plusBig, [bigS, bigS], bigS⟩, if b then [plusExp, plusInt] else [plusExp]⟩] }

/-- `<k> plusBig(X, Y) => X </k>`, with X, Y of Big at `inj{Big,KItem}`. -/
def rBig : Rule :=
  { vars := [bigS, bigS, Srt.counter], lhs := cfg kl bigS (.app plusBig [.var 0, .var 1]) 2, req := none,
    rhs := cfg kl bigS (.var 0) 2, ens := none, prio := 50 }

theorem light_false : light (c false) = true := by rw [light]; decide_cheap

open Faithful.Model in
theorem names_false : namesApartFast (c false) = true := by decide +kernel

open Faithful.Model in
theorem ites_false : itesApart (c false) = true := by decide_cheap

theorem others_false : others (c false) = true := others_of light_false names_false ites_false

theorem light_true : light (c true) = true := by rw [light]; decide_cheap

open Faithful.Model in
theorem names_true : namesApartFast (c true) = true := by decide +kernel

open Faithful.Model in
theorem ites_true : itesApart (c true) = true := by decide_cheap

theorem others_true : others (c true) = true := others_of light_true names_true ites_true

/-- Without `plusInt` in its list `plusBig` is not function-overloaded; with it, it is, and a left
side applying it is refused. -/
theorem fnOvl_facts : (c false).fnOvlSyms = [plusExp] ∧ (c true).fnOvlSyms = [plusExp, plusBig] ∧
    (c false).ovlPatsOK = true ∧ (c true).ovlPatsOK = true ∧
    ({ c false with rules := [rBig] }).ovlPatsOK = true ∧ ({ c true with rules := [rBig] }).ovlPatsOK = false := by
  decide +kernel

def expect : Prop :=
  (c false).coreOK = false ∧ (c true).coreOK = true ∧ FnHyp (c true) ∧ Consistent (c true) ∧
    ({ c true with rules := [rBig] }).ovlPatsOK = false

end Chain

/-! ## A confined-looking sort with a function-overloaded generator (REVIEW-CN4 finding A) -/

namespace Conf

def aS : Srt := nRegSorts
def bS : Srt := nRegSorts + 1
def sS : Srt := nRegSorts + 2
def pgmS : Srt := nRegSorts + 3
def kl : Sym := nRegSyms + 6
def b : Sym := nRegSyms + 8
def x : Sym := nRegSyms + 9
def y : Sym := nRegSyms + 10
def z : Sym := nRegSyms + 11
def fB : Sym := nRegSyms + 12
def p : Sym := nRegSyms + 13
def fS : Sym := nRegSyms + 14

/-- `fB : B → S` (function), `fB(X) = fB(X)`. -/
def fBFn : Fn :=
  ⟨fB, [bS], sS, [{ vars := [bS], pats := [.var 0], req := none, rhs := .app fB [.var 0], ens := none }], false⟩

/-- `p : S → Bool` (function, total), `p(_) = true`. -/
def pFn : Fn :=
  ⟨p, [sS], Srt.bool, [{ vars := [sS], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool true), ens := none }],
    true⟩

/-- `<k> x => y </k> requires p(H)`, H of S not in the left side. -/
def rY : Rule :=
  { vars := [Srt.counter, sS], lhs := cfg kl pgmS (.app x []) 0, req := some (.app p [.var 1]),
    rhs := cfg kl pgmS (.app y []) 0, ens := none, prio := 50 }

/-- `<k> x => z </k>` `[owise]`. -/
def rZ : Rule :=
  { vars := [Srt.counter], lhs := cfg kl pgmS (.app x []) 0, req := none,
    rhs := cfg kl pgmS (.app z []) 0, ens := none, prio := 200 }

/-- `fS` overloads `over`: `[fB]` is the text's. -/
def c (over : List Sym) : Semantics :=
  { lib := lib0
    sortNames := ["A", "B", "S", "Pgm", "KCell", "KCellOpt"]
    symNames := ["LblisA", "LblisB", "LblisS", "LblisPgm", "LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'",
      "LblnoKCell", "Lblb", "Lblx", "Lbly", "Lblz", "LblfB", "Lblp", "LblfS"]
    userSorts := [Srt.top, Srt.topFrag, aS, bS, sS, pgmS, pgmS + 1, pgmS + 2, Srt.counter, Srt.counterOpt]
    ctors := cellCtors (pgmS + 1) kl ++ [⟨b, [], bS⟩, ⟨x, [], pgmS⟩, ⟨y, [], pgmS⟩, ⟨z, [], pgmS⟩]
    fns := [fBFn, pFn]
    userSubsorts := (bS, aS) :: cellSubsorts (pgmS + 1)
    pgmSort := pgmS
    rules := [rY, rZ]
    ovls := [⟨⟨fS, [aS], sS⟩, over⟩] }

theorem light_ok : light (c [fB]) = true := by rw [light]; decide_cheap

open Faithful.Model in
theorem names_ok : namesApartFast (c [fB]) = true := by decide +kernel

open Faithful.Model in
theorem ites_ok : itesApart (c [fB]) = true := by decide_cheap

theorem others_ok : others (c [fB]) = true := others_of light_ok names_ok ites_ok

theorem fnOvl_facts : (c [fB]).fnOvlSyms = [fS] ∧ (c [fB]).ovlPatsOK = true := by decide +kernel

/-- S is not confined: its one generator `fS` overloads the function `fB`. -/
theorem confined_S : (c [fB]).confined sS = false ∧ (c [fB]).confined aS = true ∧ (c [fB]).confined bS = true := by
  decide +kernel

/-- With `fS` overloading nothing, S is confined: the `false` above is that conjunct's. -/
theorem confined_S_control : (c []).confined sS = true := by decide +kernel

def expect : Prop := (c [fB]).coreOK = true ∧ (c [fB]).confined sS = false

end Conf

/-- info: 'OvlFun.others_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms others_of
/-- info: 'OvlFun.E5.light_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms E5.light_ok
/-- info: 'OvlFun.E5.names_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms E5.names_ok
/-- info: 'OvlFun.E5.ites_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms E5.ites_ok
/-- info: 'OvlFun.E5.others_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms E5.others_ok
/-- info: 'OvlFun.E5.fnOvl_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms E5.fnOvl_facts
/-- info: 'OvlFun.Cap.light_ovlfun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.light_ovlfun
/-- info: 'OvlFun.Cap.names_ovlfun' depends on axioms: [propext] -/
#guard_msgs in #print axioms Cap.names_ovlfun
/-- info: 'OvlFun.Cap.ites_ovlfun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.ites_ovlfun
/-- info: 'OvlFun.Cap.others_ovlfun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.others_ovlfun
/-- info: 'OvlFun.Cap.sorted_lhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.sorted_lhs
/-- info: 'OvlFun.Cap.names_lhs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Cap.names_lhs
/-- info: 'OvlFun.Cap.ites_lhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.ites_lhs
/-- info: 'OvlFun.Cap.fnOvl_facts' does not depend on any axioms -/
#guard_msgs in #print axioms Cap.fnOvl_facts
/-- info: 'OvlFun.Keep.light_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Keep.light_ok
/-- info: 'OvlFun.Keep.names_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Keep.names_ok
/-- info: 'OvlFun.Keep.ites_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Keep.ites_ok
/-- info: 'OvlFun.Keep.others_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Keep.others_ok
/-- info: 'OvlFun.Keep.fnOvl_facts' does not depend on any axioms -/
#guard_msgs in #print axioms Keep.fnOvl_facts
/-- info: 'OvlFun.Chain.light_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chain.light_false
/-- info: 'OvlFun.Chain.names_false' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chain.names_false
/-- info: 'OvlFun.Chain.ites_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chain.ites_false
/-- info: 'OvlFun.Chain.others_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chain.others_false
/-- info: 'OvlFun.Chain.light_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chain.light_true
/-- info: 'OvlFun.Chain.names_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chain.names_true
/-- info: 'OvlFun.Chain.ites_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chain.ites_true
/-- info: 'OvlFun.Chain.others_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chain.others_true
/-- info: 'OvlFun.Chain.fnOvl_facts' does not depend on any axioms -/
#guard_msgs in #print axioms Chain.fnOvl_facts
/-- info: 'OvlFun.Conf.light_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Conf.light_ok
/-- info: 'OvlFun.Conf.names_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Conf.names_ok
/-- info: 'OvlFun.Conf.ites_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Conf.ites_ok
/-- info: 'OvlFun.Conf.others_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Conf.others_ok
/-- info: 'OvlFun.Conf.fnOvl_facts' does not depend on any axioms -/
#guard_msgs in #print axioms Conf.fnOvl_facts
/-- info: 'OvlFun.Conf.confined_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Conf.confined_S
/-- info: 'OvlFun.Conf.confined_S_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Conf.confined_S_control

/-! ## The value model at `capGas`, a function among its overloads -/

namespace Cap

open Faithful Faithful.Model ML

def capGasO : OvlSig := ⟨⟨capGas, [gasS], gasS⟩, [capN]⟩
def capNSig : CtorSig := ⟨capN, [nS], nS⟩

/-- What the model's cases read of `capGas` holds of `ovlfun`, whose `capGas` overloads the
function `capN`. -/
theorem ovlAt_capGas : OvlAtF ovlfun capGasO :=
  { names := namesApartK_spec (namesApartK_of_fast names_ovlfun)
    mem := by decide +kernel
    lookup := by decide +kernel
    isOvl := by decide +kernel
    sorts := by decide +kernel
    over := by decide +kernel }

/-- The function overload covering a value of N lifted to Gas is `capN`'s: `capGas` overloads
nothing else. -/
theorem capN_cover (as : List GroundTerm) (h : ovlfun.sortsOf as = some capNSig.args) :
    ovlfun.fnCover capGasO.sig.name (liftAll capNSig.args capGasO.sig.args as) = some capNSig :=
  fnCover_of_unique_ovlF (o := capGasO) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (covers_liftAll_ovlF (by decide +kernel) h)
    (fun kg' hkg' _ _ => by
      have : ovlfun.ovlOver capGasO = [capNSig] := by decide +kernel
      rw [this] at hkg'; simpa using hkg')

/-- **In the value model of `ovlfun`** (at any transition), `capGas(inj{N,Gas}(z))` has the
values of `capN(z)` injected into Gas, and no other. -/
theorem model_capZ (x : Elem) :
    result ovlfun capGasO.sig [.inj nS gasS (.ctor z [])] x ↔
      ∃ v, x = .val (lift nS gasS v) ∧ Eval ovlfun capN [.ctor z []] (some v) :=
  result_ovlFn (o := capGasO) (kg := capNSig) (by decide +kernel) (by decide +kernel) (by decide +kernel) x

/-- **The value model of `ovlfun` satisfies the three items `Γ` writes of `capGas`**: its overload
equation over the function `capN`, and its functionality and injectivity at uncovered arguments.
Nothing is asked of `capN`. -/
theorem model_capGas_items (T : GroundTerm → GroundTerm → Prop) :
    (stdI_T ovlfun T ⊧ᴵ (KoreAML.Cons.ovlEqItem (toK ovlfun capGasO.sig) (toK ovlfun capNSig)).pat) ∧
    (stdI_T ovlfun T ⊧ᴵ (KoreAML.Cons.funUncItem (ovlfun.sortName gasS) (Gen.toK ovlfun (.ctor capGasO.sig))
      ((ovlfun.ovlOver capGasO).map fun kg => kg.args.map ovlfun.sortName)).pat) ∧
    (stdI_T ovlfun T ⊧ᴵ (KoreAML.Cons.injUncItem (ovlfun.sortName gasS) (Gen.toK ovlfun (.ctor capGasO.sig))
      ((ovlfun.ovlOver capGasO).map fun kg => kg.args.map ovlfun.sortName)).pat) :=
  ⟨AtT.sat_ovlEq_ovlF ovlAt_capGas (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (irrefl_of_all (by decide +kernel)) capN_cover,
    AtT.sat_funUnc_ovlF ovlAt_capGas, AtT.sat_injUnc_ovlF ovlAt_capGas⟩

/-- The three items are the ones `consItemsK ovlfun` holds for `capGas`. -/
theorem model_capGas_items_mem :
    ((Faithful.consItemsK ovlfun).any fun it =>
      it.pat == (KoreAML.Cons.ovlEqItem (toK ovlfun capGasO.sig) (toK ovlfun capNSig)).pat) = true ∧
    ((Faithful.consItemsK ovlfun).any fun it =>
      it.pat == (KoreAML.Cons.funUncItem (ovlfun.sortName gasS) (Gen.toK ovlfun (.ctor capGasO.sig))
        ((ovlfun.ovlOver capGasO).map fun kg => kg.args.map ovlfun.sortName)).pat) = true ∧
    ((Faithful.consItemsK ovlfun).any fun it =>
      it.pat == (KoreAML.Cons.injUncItem (ovlfun.sortName gasS) (Gen.toK ovlfun (.ctor capGasO.sig))
        ((ovlfun.ovlOver capGasO).map fun kg => kg.args.map ovlfun.sortName)).pat) = true := by
  decide +kernel

/-- **The value model of `ovlfun` satisfies the two distinctness items `Γ` writes of `capGas`**,
both at uncovered arguments: against the constructor `inf` and against the injection from N. -/
theorem model_capGas_dist (T : GroundTerm → GroundTerm → Prop) :
    (stdI_T ovlfun T ⊧ᴵ (KoreAML.Cons.distUncItem (ovlfun.sortName gasS) (Gen.toK ovlfun (.ctor ⟨inf, [], gasS⟩))
      (Gen.toK ovlfun (.ctor capGasO.sig)) (Model.ovlArgsOf ovlfun (.ctor ⟨inf, [], gasS⟩))
      (Model.ovlArgsOf ovlfun (.ctor capGasO.sig))).pat) ∧
    (stdI_T ovlfun T ⊧ᴵ (KoreAML.Cons.distUncItem (ovlfun.sortName gasS) (Gen.toK ovlfun (.ctor capGasO.sig))
      (Gen.toK ovlfun (.inj nS)) (Model.ovlArgsOf ovlfun (.ctor capGasO.sig)) (Model.ovlArgsOf ovlfun (.inj nS))).pat) :=
  ⟨AtT.sat_distUnc_ovlF ovlAt_capGas.names
      (AtT.genAt_ctor_ovlF ovlAt_capGas.names (k := ⟨inf, [], gasS⟩) (by decide +kernel) (by decide +kernel) gasS)
      (AtT.genAt_ovlF ovlAt_capGas gasS)
      (fun vs ws _ _ _ _ he => absurd (GroundTerm.ctor.inj he).1 (by decide)),
    AtT.sat_distUnc_ovlF ovlAt_capGas.names (AtT.genAt_ovlF ovlAt_capGas gasS)
      (AtT.genAt_inj_ovlF ovlAt_capGas.names (a := nS) (N := gasS) (by decide +kernel) (by decide +kernel))
      (fun vs ws _ _ _ _ he => by
        generalize ws.headD (.ctor 0 []) = w at he
        cases w <;> simp [injNormal] at he)⟩

/-- The two items are the ones `consItemsK ovlfun` holds for `capGas`. -/
theorem model_capGas_dist_mem :
    ((Faithful.consItemsK ovlfun).any fun it =>
      it.pat == (KoreAML.Cons.distUncItem (ovlfun.sortName gasS) (Gen.toK ovlfun (.ctor ⟨inf, [], gasS⟩))
        (Gen.toK ovlfun (.ctor capGasO.sig)) (Model.ovlArgsOf ovlfun (.ctor ⟨inf, [], gasS⟩))
        (Model.ovlArgsOf ovlfun (.ctor capGasO.sig))).pat) = true ∧
    ((Faithful.consItemsK ovlfun).any fun it =>
      it.pat == (KoreAML.Cons.distUncItem (ovlfun.sortName gasS) (Gen.toK ovlfun (.ctor capGasO.sig))
        (Gen.toK ovlfun (.inj nS)) (Model.ovlArgsOf ovlfun (.ctor capGasO.sig)) (Model.ovlArgsOf ovlfun (.inj nS))).pat) = true := by
  decide +kernel

/-! ## Evaluation at a covered application, and the declarations' facts -/

/-- The clause of `capN`: `capN(z #as G0) = G0`. -/
def capNCl : Clause := { vars := [nS], pats := [.as (.app z []) 0], req := none, rhs := .var 0, ens := none }

/-- **`capN(z)` evaluates to `z`**, by its one clause. -/
theorem eval_capN_z : Eval ovlfun capN [.ctor z []] (some (.ctor z [])) :=
  .clause (fn := capNFn) (cl := capNCl) (σ := [(0, .ctor z [])])
    (by rw [Semantics.lookupFn_eq]; rfl) (List.mem_cons_self ..)
    (fun i s' h => by
      cases i with
      | zero => cases h; exact ⟨.ctor z [], rfl, by decide +kernel⟩
      | succ i => simp [capNCl] at h)
    (.cons (.as (.ctor (by decide +kernel) .nil) rfl) .nil) (fun t ht => by cases ht) .top
    (fun cl' h _ hlt => by
      have : cl' = capNCl := by simpa [capNFn, capNCl] using h
      subst this
      exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t ht => by cases ht) .top

/-- **A covered application evaluates to the function's value, injected** (`EvalTerm.ovlFn`):
`capGas(inj{N,Gas}(z))` evaluates to `inj{N,Gas}(z)`, the value of `capN(z)` in Gas. -/
theorem evalTerm_capZ : EvalTerm ovlfun [] capZ (some (.inj nS gasS (.ctor z []))) :=
  EvalTerm.ovlFn (rs := [some (.inj nS gasS (.ctor z []))]) (vs := [.inj nS gasS (.ctor z [])])
    (o := capGasO) (kg := capNSig) (r := some (.ctor z []))
    (by decide +kernel) (by decide +kernel)
    (.cons (.inj (.ctor (f := z) (rs := []) (by decide +kernel) .nil)) .nil) rfl
    (by decide +kernel) (by decide +kernel) eval_capN_z

/-- **The facts the laws of `norm` read of the declarations hold of `ovlfun`**, whose `capGas`
overloads the function `capN`: they exclude no function among the overloads. -/
theorem fnFacts_ovlfun : OvlLaws.OvlFnFacts ovlfun where
  isOvl := by decide +kernel
  over := by decide +kernel
  coh := by decide +kernel
  closed := fun o ho kg hkg o' ho' => by
    have he : ovlfun.ovls = [capGasO] := by decide +kernel
    rw [he] at ho
    obtain rfl := List.mem_singleton.mp ho
    have hov : ovlfun.ovlOver capGasO = [capNSig] := by decide +kernel
    rw [hov] at hkg
    obtain rfl := List.mem_singleton.mp hkg
    have hn : ovlfun.lookupOvl capNSig.name = none := by decide +kernel
    rw [hn] at ho'
    cases ho'

/-- info: 'OvlFun.Cap.evalTerm_capZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evalTerm_capZ
/-- info: 'OvlFun.Cap.fnFacts_ovlfun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnFacts_ovlfun
/-- info: 'OvlFun.Cap.model_capGas_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_capGas_dist
/-- info: 'OvlFun.Cap.model_capGas_items' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_capGas_items
/-- info: 'OvlFun.Cap.model_capZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_capZ

end Cap

/-! ## `overloadsOK` and `coreOK` of the semantics above -/

namespace Admit

open Faithful.OvlLibCtorWitness (ov1 ov2 ov3 ov4 ov5 ov6 ov7 ov8 ov9)

theorem coreOK_of {c : Semantics} (h : others c = true) (ho : c.overloadsOK = true) : c.coreOK = true := by
  show (others c && c.overloadsOK) = true
  rw [h, ho]; rfl

/-- `overloadsOK` admits the overload of `plusExp` by the function `plusInt`. -/
theorem ovls_e5 : E5.c.overloadsOK = true := by decide +kernel
theorem coreOK_e5 : E5.c.coreOK = true := coreOK_of E5.others_ok ovls_e5

/-- `overloadsOK` admits the overload of `capGas` by the function `capN`. -/
theorem ovls_ovlfun : Cap.ovlfun.overloadsOK = true := by decide +kernel
theorem coreOK_ovlfun : Cap.ovlfun.coreOK = true := coreOK_of Cap.others_ovlfun ovls_ovlfun

/-- A left side applying the function-overloaded `capGas` is refused, by `sortedOK` and by
`overloadsOK` (`ovlPatsOK`). -/
theorem ovls_lhs : Cap.lhs.overloadsOK = false := by decide +kernel
theorem coreOK_lhs : Cap.expectLhs := by
  show Cap.lhs.coreOK = false
  simp [Semantics.coreOK, Cap.sorted_lhs]

/-- `overloadsOK` admits the overload that keeps the result sort. -/
theorem ovls_keep : Keep.c.overloadsOK = true := by decide +kernel
theorem coreOK_keep : Keep.c.coreOK = true := coreOK_of Keep.others_ok ovls_keep

/-- The chain whose larger symbol lists the function. -/
theorem ovls_chain : (Chain.c true).overloadsOK = true := by decide +kernel
theorem coreOK_chain : (Chain.c true).coreOK = true := coreOK_of Chain.others_true ovls_chain

/-- **The chain whose larger symbol does not list the function it reaches is refused, by that
conjunct alone**: `plusBig` reaches `plusInt` through `plusExp` and does not list it; every other
leaf of `overloadsOK` holds, and every other condition of `coreOK` (`Chain.others_false`). So the
conjunct is implied by no other. -/
theorem chain_false : (Chain.c false).overloadsOK = false ∧ ov9 (Chain.c false) = false ∧
    ov1 (Chain.c false) = true ∧ ov2 (Chain.c false) = true ∧ ov3 (Chain.c false) = true ∧
    ov4 (Chain.c false) = true ∧ ov5 (Chain.c false) = true ∧ ov6 (Chain.c false) = true ∧
    ov7 (Chain.c false) = true ∧ ov8 (Chain.c false) = true ∧ (Chain.c false).ovlPatsOK = true := by
  decide +kernel

theorem coreOK_chain_false : (Chain.c false).coreOK = false := by
  show (others (Chain.c false) && (Chain.c false).overloadsOK) = false
  rw [chain_false.1, Bool.and_false]

/-- The witness module of this conjunct (`Faithful.OvlClosedWitness`, whose `Γ` has no model) is
this chain with its function's clause taken away. -/
theorem closed_witness_eq : Faithful.OvlClosedWitness.c =
    { Chain.c false with fns := [⟨Chain.plusInt, [Srt.int, Srt.int], Srt.int, [], false⟩] } := rfl

/-- The overload of `fS` by the result-keeping function `fB`. -/
theorem ovls_conf : (Conf.c [Conf.fB]).overloadsOK = true := by decide +kernel
theorem coreOK_conf : Conf.expect :=
  ⟨coreOK_of Conf.others_ok ovls_conf, Conf.confined_S.1⟩

/-- `E5.c` with a second function `Int Int → Int` among the overloads of `plusExp`. -/
def two : Semantics :=
  { E5.c with
    fns := [E5.plusIntFn, { E5.plusIntFn with label := E5.plusExp + 1 }]
    ovls := [⟨⟨E5.plusExp, [E5.expS, E5.expS], E5.expS⟩, [E5.plusInt, E5.plusExp + 1]⟩] }

/-- **Two functions that cover one argument list under one overloading symbol are refused, by
`ovlCoherent` alone**: a function's signature has nothing below it along the overloads but
itself, so no symbol covers the arguments lying in both. Every other leaf of `overloadsOK`
holds. -/
theorem two_refused : two.overloadsOK = false ∧ ov8 two = false ∧
    ov1 two = true ∧ ov2 two = true ∧ ov3 two = true ∧ ov4 two = true ∧ ov5 two = true ∧
    ov6 two = true ∧ ov7 two = true ∧ ov9 two = true ∧ two.ovlPatsOK = true := by
  decide +kernel

/-- What the laws of the normal forms read (`OvlFnFacts`), from `coreOK`, at a semantics with a
function among the overloads. -/
theorem fnFacts_e5 : OvlLaws.OvlFnFacts E5.c :=
  ((ovlOK_of_core coreOK_e5).hyp
    (NamesApart.subsorts_trans_of (Semantics.coreOK_parts coreOK_e5).2.2.2.2 (Semantics.coreOK_parts coreOK_e5).1)).fnFacts

/-- info: 'OvlFun.Admit.coreOK_e5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreOK_e5
/-- info: 'OvlFun.Admit.coreOK_ovlfun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreOK_ovlfun
/-- info: 'OvlFun.Admit.coreOK_lhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreOK_lhs
/-- info: 'OvlFun.Admit.coreOK_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreOK_keep
/-- info: 'OvlFun.Admit.coreOK_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreOK_chain
/-- info: 'OvlFun.Admit.chain_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms chain_false
/-- info: 'OvlFun.Admit.coreOK_conf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreOK_conf
/-- info: 'OvlFun.Admit.two_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms two_refused
/-- info: 'OvlFun.Admit.fnFacts_e5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnFacts_e5

end Admit

end OvlFun
