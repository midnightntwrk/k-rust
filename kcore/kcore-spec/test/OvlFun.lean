/-
  Overloads by functions: semantics built by hand from the fixtures' kompiled sentences, the facts
  that hold of them now, and the expectations the function-overload construct meets, as
  propositions (`expect`, `expectOvlfun`, `expectLhs`, `expectCut` in each namespace), each proved
  here (`E5.expect_e5`, `Cap.expect_ovlfun`, `Admit.coreOK_lhs`, `Keep.expect_keep`, `Chain.expect_chain`,
  `Admit.coreOK_conf`, `Cap.expect_cut`). Run from the package root: `lake env lean -j1 test/OvlFun.lean`.

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
    `FnHyp`, `Consistent`, and `plusExp(inj 1, inj 2)` evaluates to `inj 3` (`E5.expect_e5`). Argued, not
    kernel-checked: the text has no model. Its no-confusion sentence of `plusExp` (kore.txt line 78)
    and its overload equation (line 86), with `inj{Int,Exp}` functional and injective and `1 ≠ 2`,
    are not enough: they hold where `plusInt` is empty or injective. With `plusInt(1, 2)` and
    `plusInt(2, 1)` both `3` (the text's equation of `plusInt` and the value of `+Int`), the
    overload equation makes `plusExp(inj 1, inj 2)` and `plusExp(inj 2, inj 1)` both `inj 3`, so
    their conjunction is `inj 3`, while the no-confusion sentence puts it inside
    `plusExp(inj 1 ∧ inj 2, inj 2 ∧ inj 1)`, which is empty. This is a fact of the text, not of
    `Γ`, and the account's note states it only as a condition.
  - `ovlfun` (f2-examples/ovlfun.k): `capGas : Gas → Gas` overloads the total function
    `capN : N → N`, N < Gas, `capN(z #as G0) = G0`, and the rule `run(G) => done(cap(G))`. Expected:
    `capGas(inj z)` evaluates to `inj z`; `coreOK`, `FnHyp`, `Consistent` (`Cap.expect_ovlfun`; the
    one fact `FnHyp` names is the totality of `capN`, proved from N holding `z` only). Argued, not
    kernel-checked: the text has a model, `capN` being total, injective on the one value of N and
    `inj z` being no application of the constructor `inf`; kernel-checked is that `Γ` has one
    (`Consistent`), with the items of `capGas` at uncovered arguments (`Cap.model_capGas_items`).
  - `keep` (e5-ovl-fun-keep): the overload keeps the result sort: `capN : N → Gas` total,
    `capN(z) = inf`, the overload equation `capGas(inj X0) = capN(X0)` (no injection on the right).
    Expected: `capGas(inj z)` evaluates to `inf`; `coreOK`, `FnHyp`, `Consistent` (`Keep.expect_keep`).
  - `lhs` (e5-ovl-fun-lhs): `ovlfun`'s signature with the rule `run(cap(G)) => done(G)`: `capGas`
    in a left side. The left side is not sorted over `patCtxNF`, so `sortedOK` is false
    (`sorted_lhs`), and `ovlPatsOK` is false (`fnOvl_facts`); expected: `coreOK` false (`Admit.coreOK_lhs`). The
    fixture's kompiled text is not this semantics: its rule is read with a variable in place of the
    application and the membership as its predicate, which is `cutSem`.
  - `cutSem` (e5-ovl-fun-lhs as the reader reads it, test/OvlCutRule.lean): `ovlfun`'s signature
    with the rule `run(V) => done(G)`, `pre := V ∈ capGas(G)`. G is held by the right side under
    `done` (arm A, `rulePlainPP`, so `rulesPlain` admits it without `memHeld`), and no witness is
    asked (V is bound, so the conditions are not closed). Expected (`Cap.expect_cut`): `coreOK`,
    `FnHyp` (the totality of `capN`), `complete_hyp`'s conclusion `CompleteC`; `Step` from
    `run(inj z)` to `done(inj z)` (G := `inj z`, covered: `capGas(inj z) = inj(capN(z))`), from
    `run(capGas(inf))` to `done(inf)` (G := `inf`, uncovered), and no step from `run(inf)` (no value
    of Gas has `capGas` of it equal to `inf`: `Cap.no_step_inf`).
  - `keepRun` (e5-ovl-fun-keep-run): `cutSem` with `capN : N → Gas`, `capN(z) = inf`: `run(inf)`
    steps to `done(inj z)`, the covered application being `inf` (`Cap.step_keepRun`).
  - `Dbl` (e5-ovl-fun-lhs-int, CN-4b §3.2): `dblExp : Exp → Exp` over the total function
    `dblInt : Int → Int`, `dblInt(I) = 2 *Int I`, Int < Exp, the cut rule `run(V) => done(0)`,
    `pre := V ∈ dblExp(E)`, beside `run(_) => done(1)` `[owise]`. Int and Exp are not confined, so
    `dblExp` is not `ovlHeld` and E is held by nothing, the cut included (`Dbl.not_held`: `memHeld`
    is false at E): the cut rule fails `rulesPlain` at E under
    `dblExp`, in both conjuncts (`Dbl.text_refused`; the reader's `openRequires` naming E and
    `dblExp` is test/OvlCutRule.lean's), so `coreOK` is false (`Dbl.coreOK_text`), and without the
    `[owise]` rule it still fails the arms (`Dbl.zeroAlone_refused`). Alone and with `=> done(E)`
    (`done` taking Exp, built by hand: no fixture has this text) it is admitted by arm A, and
    `coreOK` holds (`Dbl.alone_admitted`, `Dbl.coreOK_alone`).
  - `chain b` (REVIEW-CN4 finding B): `plusExp : Exp Exp → Exp` over the function `plusInt`,
    `plusBig : Big Big → Big` over `plusExp` (and `plusInt` where `b`), Int < Exp < Big. Without
    `plusInt` in `plusBig`'s list, `plusBig` is not function-overloaded (`fnOvlSyms`); with it,
    it is, and a left side applying it is refused (`ruleSorted`, `ovlPatsOK`). Expected: `coreOK` false without
    it; `coreOK`, `FnHyp`, `Consistent` with it (`Chain.expect_chain`).
  - `conf over` (REVIEW-CN4 finding A): `fS : A → S` overloads the result-keeping function
    `fB : B → S`, B < A, `fB(X) = fB(X)` (no value at `b`), the total `p : S → Bool`, `p(_) = true`,
    and the rules `x => y requires p(H)` (H of S, not bound by the left side) and `x => z` with
    priority 200. S is not confined (`confined_S`), by the conjunct of `confinedAt` on a generator
    that overloads a function: with `fS` overloading nothing, S is confined (`confined_S_control`).
    Expected: `coreOK`, and S not confined (`Admit.coreOK_conf`).
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

/-! ## e5-ovl-fun: the functions' hypotheses, the covered application, and what was expected -/

namespace E5

open Det

theorem noRaw_e5 : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem confined_named : c.readsConfined = false := by decide +kernel
theorem valued_e5 : c.rightValued = true := by decide +kernel
theorem term_named : c.rankObligations [plusInt] ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP [plusInt] [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

/-- **`FnHyp` of e5-ovl-fun**: no fact is named; `plusInt` is not `[total]` and calls `+Int` only. -/
theorem fnHyp_e5 : FnHyp c :=
  fnHyp_of_fnObligations (ord := [plusInt]) (tp := []) Admit.coreOK_e5 (Semantics.rightHeld_of_valued valued_e5) ParamsTotal.nil
    ⟨fun f hf => by rw [term_named] at hf; exact absurd hf List.not_mem_nil,
     fun f hf => by rw [total_named] at hf; exact absurd hf List.not_mem_nil,
     fun f hf => by rw [agree_named] at hf; exact absurd hf List.not_mem_nil,
     fun p hp => by rw [match_named] at hp; exact absurd hp List.not_mem_nil,
     openDecided_of_readsConfined confined_named, openLaws_of_plain noRaw_e5⟩

/-- **`Consistent`** of e5-ovl-fun. -/
theorem consistent_e5 : Consistent c := consistent_of_fnHyp _ Admit.coreOK_e5 fnHyp_e5

def plusIntSig : CtorSig := ⟨plusInt, [Srt.int, Srt.int], Srt.int⟩
def plusExpO : OvlSig := ⟨⟨plusExp, [expS, expS], expS⟩, [plusInt]⟩
def plusIntCl : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0, .var 1], req := none, rhs := .app intAdd [.var 0, .var 1], ens := none }

/-- **`plusInt(1, 2)` evaluates to `3`**, by its one clause and the value of `+Int`. -/
theorem eval_plusInt_12 : Eval c plusInt [.dv Srt.int (.int 1), .dv Srt.int (.int 2)] (some (.dv Srt.int (.int 3))) :=
  .clause (fn := plusIntFn) (cl := plusIntCl) (σ := [(0, .dv Srt.int (.int 1)), (1, .dv Srt.int (.int 2))])
    (by rw [Semantics.lookupFn_eq]; rfl) (List.mem_cons_self ..)
    (fun i s' h => by
      match i, h with
      | 0, h => cases h; exact ⟨_, rfl, by decide +kernel⟩
      | 1, h => cases h; exact ⟨_, rfl, by decide +kernel⟩
      | i + 2, h => simp [plusIntCl] at h)
    (.cons (.var rfl) (.cons (.var rfl) .nil)) (fun t ht => by cases ht) .top
    (fun cl' h _ hlt => by
      have : cl' = plusIntCl := by simpa [plusIntFn, plusIntCl] using h
      subst this
      exact absurd hlt (Nat.lt_irrefl _))
    rfl
    (.hook (rs := [some (.dv Srt.int (.int 1)), some (.dv Srt.int (.int 2))]) (by decide +kernel) (by decide +kernel)
      (.cons .var (.cons .var .nil))
      (fun vs h => by cases h; exact Semantics.hookRes_of_value (by decide +kernel))
      (fun h => by cases h))
    (fun t ht => by cases ht) .top

/-- **The covered application evaluates to the function's value, injected** (`EvalTerm.ovlFn`):
`plusExp(inj{Int,Exp}(1), inj{Int,Exp}(2))` evaluates to `inj{Int,Exp}(3)`. -/
theorem evalTerm_app12 : EvalTerm c [] app12 (some (.inj Srt.int expS (.dv Srt.int (.int 3)))) :=
  EvalTerm.ovlFn (rs := [some (.inj Srt.int expS (.dv Srt.int (.int 1))), some (.inj Srt.int expS (.dv Srt.int (.int 2)))])
    (vs := [.inj Srt.int expS (.dv Srt.int (.int 1)), .inj Srt.int expS (.dv Srt.int (.int 2))])
    (o := plusExpO) (kg := plusIntSig) (r := some (.dv Srt.int (.int 3)))
    (by decide +kernel) (by decide +kernel)
    (.cons (.inj .dv) (.cons (.inj .dv) .nil)) rfl
    (by decide +kernel) (by decide +kernel) eval_plusInt_12

/-- **What was expected of e5-ovl-fun.** -/
theorem expect_e5 : expect := ⟨Admit.coreOK_e5, fnHyp_e5, consistent_e5, evalTerm_app12⟩

/-- info: 'OvlFun.E5.fnHyp_e5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnHyp_e5
/-- info: 'OvlFun.E5.consistent_e5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consistent_e5
/-- info: 'OvlFun.E5.evalTerm_app12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evalTerm_app12
/-- info: 'OvlFun.E5.expect_e5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expect_e5

end E5
/-! ## The three-level chain: the functions' hypotheses, and what was expected -/

namespace Chain

open Det

theorem noRaw_chain : ∀ k ∈ (c true).params, k.raw = false := by decide +kernel
theorem confined_chain : (c true).readsConfined = false := by decide +kernel
theorem valued_chain : (c true).rightValued = true := by decide +kernel
theorem term_chain : (c true).rankObligations [plusInt] ++ (c true).decObligationsL = [] := by decide +kernel
theorem total_chain : (c true).totalObligationsRP [plusInt] [] = [] := by decide +kernel
theorem agree_chain : (c true).agreeObligationsI = [] := by decide +kernel
theorem match_chain : (c true).matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

/-- **`FnHyp` of the chain whose larger symbol lists the function**: no fact is named. -/
theorem fnHyp_chain : FnHyp (c true) :=
  fnHyp_of_fnObligations (ord := [plusInt]) (tp := []) Admit.coreOK_chain
    (Semantics.rightHeld_of_valued valued_chain) ParamsTotal.nil
    ⟨fun f hf => by rw [term_chain] at hf; exact absurd hf List.not_mem_nil,
     fun f hf => by rw [total_chain] at hf; exact absurd hf List.not_mem_nil,
     fun f hf => by rw [agree_chain] at hf; exact absurd hf List.not_mem_nil,
     fun p hp => by rw [match_chain] at hp; exact absurd hp List.not_mem_nil,
     openDecided_of_readsConfined confined_chain, openLaws_of_plain noRaw_chain⟩

/-- **`Consistent`** of that chain. -/
theorem consistent_chain : Consistent (c true) := consistent_of_fnHyp _ Admit.coreOK_chain fnHyp_chain

/-- **What was expected of the chain**: refused without the function in the larger symbol's list;
with it, `coreOK`, `FnHyp` and `Consistent`, and the larger symbol refused in a left side. -/
theorem expect_chain : expect :=
  ⟨Admit.coreOK_chain_false, Admit.coreOK_chain, fnHyp_chain, consistent_chain, fnOvl_facts.2.2.2.2.2⟩

/-- info: 'OvlFun.Chain.fnHyp_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnHyp_chain
/-- info: 'OvlFun.Chain.consistent_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consistent_chain
/-- info: 'OvlFun.Chain.expect_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expect_chain

end Chain

/-! ## ovlfun and e5-ovl-fun-keep: the functions' hypotheses, and what was expected -/

/-- A sort whose one generator is a constant holds that constant only: no other constructor, no
overloading symbol and no raw parameter ends at it, nothing is below it, and it has neither
literals nor collections. -/
theorem onlyConst_ftf {c : Semantics} {s : Srt} {k0 : CtorSig} (ha : k0.args = [])
    (hk : ∀ k ∈ c.ctorSigs, k.result = s → k = k0)
    (ho : ∀ o ∈ c.ovls, o.sig.result ≠ s)
    (hp : ∀ k ∈ c.params, k.raw = false)
    (hsub : ∀ p ∈ c.subsorts, p.2 ≠ s)
    (hdv : ∀ lit, dvOK c.lib s lit = false)
    (hcoll : c.collOf s = none)
    {v : GroundTerm} (h : c.sortOf v = some s) : v = .ctor k0.name [] := by
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp h with ⟨k, hk', hs, hr⟩ | ⟨-, o, hlo, -, -, hr⟩ | ⟨-, -, k, hko, -⟩
    · obtain ⟨hm, hn⟩ := lookupSig_spec hk'
      have := hk k hm hr.symm
      subst this
      rw [ha] at hs
      rw [sortsOf_inv_nil hs, hn]
    · obtain ⟨-, i, hi, he, -⟩ := OvlLaws.lookupOvl_spec hlo
      exact absurd hr.symm (ho o (he ▸ List.getElem_mem hi))
    · obtain ⟨hm, hraw, -⟩ := Semantics.lookupOpen_spec _ hko
      rw [hp k hm] at hraw; cases hraw
  | inj a b t =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact absurd rfl (hsub _ (List.contains_iff_mem.mp hc.1.1))
    · cases h
  | dv s' lit =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc; cases h; rw [hdv lit] at hc; cases hc
    · cases h
  | map s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_map_sort h
    rw [hcoll] at hc; cases hc
  | set s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_set_sort h
    rw [hcoll] at hc; cases hc
  | list s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_list_sort h
    rw [hcoll] at hc; cases hc

/-- A sort that is no carrier of literals has none. -/
theorem noLit_ftf {l : Lib} {s : Srt}
    (h : (l.carrier s == Srt.int || l.carrier s == Srt.bool || l.carrier s == Srt.kconfigVar ||
      l.carrier s == Srt.string || l.tokenSorts.contains (l.carrier s) || l.carrier s == Srt.bytes ||
      l.byteSorts.contains (l.carrier s) || l.carrier s == Srt.float) = false) (lit : Lit) :
    dvOK l s lit = false := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  cases lit <;> simp only [dvOK, h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_and, Bool.or_self]

namespace Cap

open Det

theorem noRaw_ovlfun : ∀ k ∈ ovlfun.params, k.raw = false := by decide +kernel
theorem confined_ovlfun : ovlfun.readsConfined = false := by decide +kernel
theorem valued_ovlfun : ovlfun.rightValued = true := by decide +kernel
theorem term_ovlfun : ovlfun.rankObligations [capN] ++ ovlfun.decObligationsL = [] := by decide +kernel
theorem total_ovlfun : ovlfun.totalObligationsRP [capN] [] = [capN] := by decide +kernel
theorem agree_ovlfun : ovlfun.agreeObligationsI = [] := by decide +kernel
theorem match_ovlfun : ovlfun.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

/-- N holds `z` only. -/
theorem val_N {v : GroundTerm} (h : ovlfun.sortOf v = some nS) : v = .ctor z [] :=
  onlyConst_ftf (k0 := ⟨z, [], nS⟩) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (noLit_ftf (by decide +kernel)) (by decide +kernel) h

/-- **`capN` is `Total`**: its one clause decides at `z`, the one value of N. -/
theorem total_capN : Total ovlfun capN := fun fn' hfn' vs hvs => by
  have hfn : ovlfun.lookupFn capN = some capNFn := by rw [Semantics.lookupFn_eq]; rfl
  obtain rfl : fn' = capNFn := Option.some.inj (hfn'.symm.trans hfn)
  obtain ⟨w, ws', rfl, hw, hws⟩ := sortsOf_inv_cons (show ovlfun.sortsOf vs = some [nS] from hvs)
  cases sortsOf_inv_nil hws
  cases val_N hw
  exact ⟨_, eval_capN_z⟩

/-- **`FnHyp`**: the one fact named is the totality of `capN`. -/
theorem fnHyp_ovlfun : FnHyp ovlfun :=
  fnHyp_of_fnObligations (ord := [capN]) (tp := []) Admit.coreOK_ovlfun
    (Semantics.rightHeld_of_valued valued_ovlfun) ParamsTotal.nil
    ⟨fun f hf => by rw [term_ovlfun] at hf; exact absurd hf List.not_mem_nil,
     fun f hf => by rw [total_ovlfun] at hf; rw [List.mem_singleton.mp hf]; exact total_capN,
     fun f hf => by rw [agree_ovlfun] at hf; exact absurd hf List.not_mem_nil,
     fun p hp => by rw [match_ovlfun] at hp; exact absurd hp List.not_mem_nil,
     openDecided_of_readsConfined confined_ovlfun, openLaws_of_plain noRaw_ovlfun⟩

/-- **`Consistent`.** -/
theorem consistent_ovlfun : Consistent ovlfun := consistent_of_fnHyp _ Admit.coreOK_ovlfun fnHyp_ovlfun

/-- **What was expected of ovlfun.** -/
theorem expect_ovlfun : expectOvlfun := ⟨Admit.coreOK_ovlfun, fnHyp_ovlfun, consistent_ovlfun, evalTerm_capZ⟩

/-- info: 'OvlFun.Cap.expect_ovlfun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expect_ovlfun

end Cap

namespace Keep

open Det

theorem noRaw_keep : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem confined_keep : c.readsConfined = false := by decide +kernel
theorem valued_keep : c.rightValued = true := by decide +kernel
theorem term_keep : c.rankObligations [capN] ++ c.decObligationsL = [] := by decide +kernel
theorem total_keep : c.totalObligationsRP [capN] [] = [capN] := by decide +kernel
theorem agree_keep : c.agreeObligationsI = [] := by decide +kernel
theorem match_keep : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

def capGasO : OvlSig := ⟨⟨capGas, [gasS], gasS⟩, [capN]⟩
def capNSig : CtorSig := ⟨capN, [nS], gasS⟩
def capNCl : Clause := { vars := [], pats := [.app z []], req := none, rhs := .app inf [], ens := none }

/-- **`capN(z)` evaluates to `inf`**, by its one clause. -/
theorem eval_capN_z : Eval c capN [.ctor z []] (some (.ctor inf [])) :=
  .clause (fn := capNFn) (cl := capNCl) (σ := [])
    (by rw [Semantics.lookupFn_eq]; rfl) (List.mem_cons_self ..)
    (fun i s' h => by simp [capNCl] at h)
    (.cons (.ctor (by decide +kernel) .nil) .nil) (fun t ht => by cases ht) .top
    (fun cl' h _ hlt => by
      have : cl' = capNCl := by simpa [capNFn, capNCl] using h
      subst this
      exact absurd hlt (Nat.lt_irrefl _))
    rfl (.ctor (f := inf) (rs := []) (by decide +kernel) .nil) (fun t ht => by cases ht) .top

/-- N holds `z` only. -/
theorem val_N {v : GroundTerm} (h : c.sortOf v = some nS) : v = .ctor z [] :=
  onlyConst_ftf (k0 := ⟨z, [], nS⟩) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (noLit_ftf (by decide +kernel)) (by decide +kernel) h

/-- **`capN` is `Total`**: its one clause decides at `z`, the one value of N. -/
theorem total_capN : Total c capN := fun fn' hfn' vs hvs => by
  have hfn : c.lookupFn capN = some capNFn := by rw [Semantics.lookupFn_eq]; rfl
  obtain rfl : fn' = capNFn := Option.some.inj (hfn'.symm.trans hfn)
  obtain ⟨w, ws', rfl, hw, hws⟩ := sortsOf_inv_cons (show c.sortsOf vs = some [nS] from hvs)
  cases sortsOf_inv_nil hws
  cases val_N hw
  exact ⟨_, eval_capN_z⟩

/-- **`FnHyp`**: the one fact named is the totality of `capN`. -/
theorem fnHyp_keep : FnHyp c :=
  fnHyp_of_fnObligations (ord := [capN]) (tp := []) Admit.coreOK_keep
    (Semantics.rightHeld_of_valued valued_keep) ParamsTotal.nil
    ⟨fun f hf => by rw [term_keep] at hf; exact absurd hf List.not_mem_nil,
     fun f hf => by rw [total_keep] at hf; rw [List.mem_singleton.mp hf]; exact total_capN,
     fun f hf => by rw [agree_keep] at hf; exact absurd hf List.not_mem_nil,
     fun p hp => by rw [match_keep] at hp; exact absurd hp List.not_mem_nil,
     openDecided_of_readsConfined confined_keep, openLaws_of_plain noRaw_keep⟩

/-- **`Consistent`.** -/
theorem consistent_keep : Consistent c := consistent_of_fnHyp _ Admit.coreOK_keep fnHyp_keep

/-- **A covered application evaluates to the function's value, in its own sort** (`EvalTerm.ovlFn`):
`capGas(inj{N,Gas}(z))` evaluates to `inf`, the value of `capN(z)`, which is of Gas. -/
theorem evalTerm_capZ : EvalTerm c [] capZ (some (.ctor inf [])) :=
  EvalTerm.ovlFn (rs := [some (.inj nS gasS (.ctor z []))]) (vs := [.inj nS gasS (.ctor z [])])
    (o := capGasO) (kg := capNSig) (r := some (.ctor inf []))
    (by decide +kernel) (by decide +kernel)
    (.cons (.inj (.ctor (f := z) (rs := []) (by decide +kernel) .nil)) .nil) rfl
    (by decide +kernel) (by decide +kernel) eval_capN_z

/-- **What was expected of e5-ovl-fun-keep.** -/
theorem expect_keep : expect := ⟨Admit.coreOK_keep, fnHyp_keep, consistent_keep, evalTerm_capZ⟩

/-- info: 'OvlFun.Keep.expect_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expect_keep

end Keep

/-! ## e5-ovl-fun-lhs read through the cut -/

/-- A membership holds where both sides evaluate to one value. -/
theorem holds_mem_pto {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {v : GroundTerm}
    (h : EvalTerm c σ t (some v)) (h' : EvalTerm c σ u (some v)) : Holds c n σ (.mem s t u) true := by
  have := Holds.mem (n := n) (s := s) h h'
  simpa [sameResult, cmp_eq_iff.mpr rfl] using this

/-- What a membership's truth value is made of. -/
theorem holds_mem_inv_pto {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {b : Bool}
    (h : Holds c n σ (.mem s t u) b) :
    ∃ r r', EvalTerm c σ t r ∧ EvalTerm c σ u r' ∧ b = (r.isSome && sameResult r r') := by
  generalize hp : Cond.mem s t u = p at h
  cases h with
  | mem h h' => cases hp; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hp

theorem sameResult_some_pto {v w : GroundTerm} (h : sameResult (some v) (some w) = true) : v = w :=
  cmp_eq_iff.mp (by simpa [sameResult] using h)

namespace Cap

open Det

/-- `<k> run(cap(G)) => done(G) </k>` as the reader reads e5-ovl-fun-lhs (test/OvlCutRule.lean
prints it): `run(V) => done(G)` with `pre := V ∈ capGas(G)`, its variables G, the counter cell and
V. -/
def rCut : Rule :=
  { vars := [gasS, Srt.counter, gasS], lhs := cfg kl pgmS (.app run [.var 2]) 1, req := none,
    rhs := cfg kl pgmS (.app done [.var 0]) 1, ens := none, prio := 50,
    pre := .mem gasS (.var 2) (.app capGas [.var 0]) }

/-- e5-ovl-fun-lhs with its rule cut. -/
def cutSem : Semantics := sem rCut

/-- The cut rule's left side applies no function-overloaded symbol; G (the variable 0), which it
does not bind, is held by the right side under the constructor `done`, so the arms admit it by
arm A, under constructors only (`rulePlainPP`); Gas is not confined; V is bound and in `pre`, so
the conditions are not closed and no witness is asked (`needsWitness`). -/
theorem cut_facts : cutSem.ovlPatsOK = true ∧ rCut.opens = [0] ∧ (ctorOccs cutSem rCut.rhs).contains 0 = true ∧
    cutSem.confined gasS = false ∧ rCut.reqClosed = false ∧ cutSem.rulePlainPP rCut = true ∧
    cutSem.rulesPlain = true ∧ (∀ r ∈ cutSem.rules, r.needsWitness cutSem = false) ∧
    (∀ fn ∈ cutSem.fns, ∀ cl ∈ fn.clauses, cl.needsWitness cutSem = false) := by
  decide +kernel

theorem light_cut : light cutSem = true := by rw [light]; decide_cheap

open Faithful.Model in
theorem names_cut : namesApartFast cutSem = true := by decide +kernel

open Faithful.Model in
theorem ites_cut : itesApart cutSem = true := by decide_cheap

theorem others_cut : others cutSem = true := others_of light_cut names_cut ites_cut

/-- `overloadsOK` admits the cut rule: its left side no longer applies `capGas`. -/
theorem ovls_cut : cutSem.overloadsOK = true := by decide +kernel

theorem coreOK_cut : cutSem.coreOK = true := Admit.coreOK_of others_cut ovls_cut

theorem noRaw_cut : ∀ k ∈ cutSem.params, k.raw = false := by decide +kernel
theorem valued_cut : cutSem.rightValued = true := by decide +kernel
theorem term_cut : cutSem.rankObligations [capN] ++ cutSem.decObligationsL = [] := by decide +kernel
theorem total_cut : cutSem.totalObligationsRP [capN] [] = [capN] := by decide +kernel
theorem agree_cut : cutSem.agreeObligationsI = [] := by decide +kernel
theorem match_cut : cutSem.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

/-- `capN(z)` evaluates to `z` in `cutSem`, by its one clause (`eval_capN_z` at `ovlfun`; evaluation
reads no rule, but `Eval` is stated per semantics). -/
theorem eval_capN_z_cut : Eval cutSem capN [.ctor z []] (some (.ctor z [])) :=
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

theorem total_capN_cut : Total cutSem capN := fun fn' hfn' vs hvs => by
  have hfn : cutSem.lookupFn capN = some capNFn := by rw [Semantics.lookupFn_eq]; rfl
  obtain rfl : fn' = capNFn := Option.some.inj (hfn'.symm.trans hfn)
  obtain ⟨w, ws', rfl, hw, hws⟩ := sortsOf_inv_cons (show cutSem.sortsOf vs = some [nS] from hvs)
  cases sortsOf_inv_nil hws
  cases onlyConst_ftf (k0 := ⟨z, [], nS⟩) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (noLit_ftf (by decide +kernel)) (by decide +kernel) hw
  exact ⟨_, eval_capN_z_cut⟩

/-- **`FnHyp` of the cut semantics**: the one fact named is the totality of `capN`; the open
variable G asks for no witness. -/
theorem fnHyp_cut : FnHyp cutSem :=
  fnHyp_of_fnObligations (ord := [capN]) (tp := []) coreOK_cut
    (Semantics.rightHeld_of_valued valued_cut) ParamsTotal.nil
    ⟨fun f hf => by rw [term_cut] at hf; exact absurd hf List.not_mem_nil,
     fun f hf => by rw [total_cut] at hf; rw [List.mem_singleton.mp hf]; exact total_capN_cut,
     fun f hf => by rw [agree_cut] at hf; exact absurd hf List.not_mem_nil,
     fun p hp => by rw [match_cut] at hp; exact absurd hp List.not_mem_nil,
     openDecided_of_plain cut_facts.2.2.2.2.2.2.2.1 cut_facts.2.2.2.2.2.2.2.2,
     openLaws_of_plain noRaw_cut⟩

/-- **`complete_hyp`'s conclusion holds of the cut semantics.** -/
theorem complete_cut (ref : OutFn) : CompleteC cutSem ref := complete_hyp cutSem ref coreOK_cut fnHyp_cut

theorem sound_cut : SoundC cutSem := sound_hyp cutSem coreOK_cut fnHyp_cut

/-! ### The steps -/

/-- The counter cell at 0. -/
def cnt0 : GroundTerm := .ctor counterLabel [.dv Srt.int (.int 0)]
/-- `<generatedTop>(<k>(kseq(inj{Pgm,KItem}(t), dotk)), cnt0)`. -/
def cfgV (t : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kl [.ctor kseq [.inj pgmS Srt.kitem t, .ctor dotk []]], cnt0]
def injZ : GroundTerm := .inj nS gasS (.ctor z [])
/-- `capGas(inf)`, uncovered: a value of Gas. -/
def capInf : GroundTerm := .ctor capGas [.ctor inf []]

def runZ : Config cutSem := ⟨cfgV (.ctor run [injZ]), by decide +kernel⟩
def doneZ : Config cutSem := ⟨cfgV (.ctor done [injZ]), by decide +kernel⟩
def runCapInf : Config cutSem := ⟨cfgV (.ctor run [capInf]), by decide +kernel⟩
def doneInf : Config cutSem := ⟨cfgV (.ctor done [.ctor inf []]), by decide +kernel⟩
def runInf : Config cutSem := ⟨cfgV (.ctor run [.ctor inf []]), by decide +kernel⟩

theorem syms_cut : cutSem.isCtor topLabel = true ∧ cutSem.isCtor kl = true ∧ cutSem.isCtor kseq = true ∧
    cutSem.isCtor dotk = true ∧ cutSem.isCtor run = true ∧ cutSem.isCtor done = true ∧
    cutSem.isCtor capGas = false ∧ cutSem.isOvl capGas = true ∧ isHook capGas = false ∧ cutSem.isParam capGas = false ∧
    patternHooks.contains topLabel = false ∧ patternHooks.contains kl = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains run = false := by
  decide +kernel

theorem rCut_vars : rCut.vars = [gasS, Srt.counter, gasS] := rfl

/-- σ gives each variable of the cut rule a value of its sort. -/
theorem wellSorted_cut {g v : GroundTerm} (hg : cutSem.sortOf g = some gasS) (hv : cutSem.sortOf v = some gasS) :
    cutSem.WellSorted rCut.vars [(0, g), (1, cnt0), (2, v)] := fun j s hs => by
  rw [rCut_vars] at hs
  match j, hs with
  | 0, hs => cases hs; exact ⟨_, rfl, hg⟩
  | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
  | 2, hs => cases hs; exact ⟨_, rfl, hv⟩
  | j + 3, hs => simp at hs

/-- The cut rule's left side denotes `run(v)` where V is v. -/
theorem lhs_match_cut {g v : GroundTerm} : PatVal cutSem [(0, g), (1, cnt0), (2, v)] rCut.lhs (cfgV (.ctor run [v])) :=
  .ctor syms_cut.1 (.cons (.ctor syms_cut.2.1 (.cons (.ctor syms_cut.2.2.1
    (.cons (.inj (.ctor syms_cut.2.2.2.2.1 (.cons (.var rfl) .nil))) (.cons (.ctor syms_cut.2.2.2.1 .nil) .nil))) .nil))
    (.cons (.var rfl) .nil))

/-- The cut rule's right side evaluates to `done(g)` where G is g. -/
theorem eval_rhs_cut {g v : GroundTerm} :
    EvalTerm cutSem [(0, g), (1, cnt0), (2, v)] rCut.rhs (some (cfgV (.ctor done [g]))) :=
  .ctor syms_cut.1 (.cons (.ctor syms_cut.2.1 (.cons (.ctor syms_cut.2.2.1
    (.cons (.inj (.ctor syms_cut.2.2.2.2.2.1 (.cons .var .nil))) (.cons (.ctor syms_cut.2.2.2.1 .nil) .nil))) .nil))
    (.cons .var .nil))

/-- The cut rule's step from `run(v)` to `done(g)` where `capGas(g)` evaluates to v. -/
theorem stepBy_cut {g v : GroundTerm} (hg : cutSem.sortOf g = some gasS) (hv : cutSem.sortOf v = some gasS)
    (hcap : EvalTerm cutSem [(0, g), (1, cnt0), (2, v)] (.app capGas [.var 0]) (some v))
    (x y : Config cutSem) (hx : x.val = cfgV (.ctor run [v])) (hy : y.val = cfgV (.ctor done [g])) :
    StepBy cutSem rCut [(0, g), (1, cnt0), (2, v)] x y where
  mem := List.mem_singleton_self _
  hσ := wellSorted_cut hg hv
  hmatch := hx ▸ lhs_match_cut
  hreq := fun t ht => by simp [rCut] at ht
  hpre := holds_mem_pto (.var : EvalTerm cutSem _ (.var 2) _) hcap
  heval := hy ▸ eval_rhs_cut
  hens := fun t ht => by simp [rCut] at ht
  hpost := .top
  hprio := fun r' hr' hlt => by
    rw [List.mem_singleton.mp hr'] at hlt
    exact absurd hlt (Nat.lt_irrefl _)

/-- `capGas(inj{N,Gas}(z))`, covered by `capN`, evaluates to `inj{N,Gas}(capN(z))`. -/
theorem evalTerm_capG_z :
    EvalTerm cutSem [(0, injZ), (1, cnt0), (2, injZ)] (.app capGas [.var 0]) (some injZ) :=
  EvalTerm.ovlFn (rs := [some injZ]) (vs := [injZ]) (o := capGasO) (kg := capNSig) (r := some (.ctor z []))
    syms_cut.2.2.2.2.2.2.1 syms_cut.2.2.2.2.2.2.2.1 (.cons .var .nil) rfl
    (by decide +kernel) (by decide +kernel) eval_capN_z_cut

/-- `capGas(inf)`, uncovered, evaluates to its raw application. -/
theorem evalTerm_capG_inf :
    EvalTerm cutSem [(0, .ctor inf []), (1, cnt0), (2, capInf)] (.app capGas [.var 0]) (some capInf) := by
  have h := EvalTerm.ovl (c := cutSem) (σ := [(0, .ctor inf []), (1, cnt0), (2, capInf)])
    syms_cut.2.2.2.2.2.2.1 syms_cut.2.2.2.2.2.2.2.1 (.cons (EvalTerm.var (i := 0)) .nil)
    (fun vs hvs => by
      have hvs' : some [GroundTerm.ctor inf []] = some vs := hvs
      obtain rfl : vs = [.ctor inf []] := (Option.some.inj hvs').symm
      decide +kernel)
  have hn : cutSem.norm capGas [.ctor inf []] = capInf := by decide +kernel
  rw [← hn]; exact h

/-- **`run(inj{N,Gas}(z))` steps to `done(inj{N,Gas}(z))`**: G := `inj{N,Gas}(z)`, covered, and
`capGas(inj{N,Gas}(z)) = inj{N,Gas}(capN(z)) = inj{N,Gas}(z)`. -/
theorem step_z : Step cutSem runZ doneZ :=
  step_iff_by.mpr ⟨rCut, _, stepBy_cut (by decide +kernel) (by decide +kernel) evalTerm_capG_z runZ doneZ rfl rfl⟩

/-- **`run(capGas(inf))` steps to `done(inf)`**: G := `inf`, uncovered. -/
theorem step_capInf : Step cutSem runCapInf doneInf :=
  step_iff_by.mpr ⟨rCut, _, stepBy_cut (by decide +kernel) (by decide +kernel) evalTerm_capG_inf runCapInf doneInf
    rfl rfl⟩

/-! ### No step from `run(inf)` -/

theorem lookupOvl_cut : cutSem.lookupOvl capGas = some capGasO := by decide +kernel
theorem ovlOver_cut : cutSem.ovlOver capGasO = [capNSig] := by decide +kernel

/-- `capGas`'s one overload is the function `capN`'s, so its normal form is its raw application. -/
theorem norm_capGas_cut (vs : List GroundTerm) : cutSem.norm capGas vs = .ctor capGas vs := by
  have hfn : cutSem.ovlByFn capNSig = true := by decide +kernel
  show cutSem.normN 2 capGas vs = _
  simp only [Semantics.normN, lookupOvl_cut, ovlOver_cut, List.find?_cons, List.find?_nil]
  split
  · rfl
  · rename_i kg hkg
    split at hkg
    · cases hkg; simp [hfn]
    · cases hkg

/-- The function overload covering anything is `capN`'s. -/
theorem fnCover_cut {vs : List GroundTerm} {kg : CtorSig} (h : cutSem.fnCover capGas vs = some kg) : kg = capNSig := by
  unfold Semantics.fnCover at h
  rw [lookupOvl_cut, Option.bind_some, ovlOver_cut] at h
  exact List.mem_singleton.mp (List.mem_of_find?_eq_some h)

/-- The cut rule's left side at `run(w)` gives V the value w. -/
theorem lhs_inv_cut {σ : Subst} {w : GroundTerm} (h : PatVal cutSem σ rCut.lhs (cfgV (.ctor run [w]))) :
    σ.lookup 2 = some w := by
  have hl : rCut.lhs = .app topLabel [.app kl [.app kseq [.inj pgmS Srt.kitem (.app run [.var 2]), .app dotk []]],
      .var 1] := rfl
  rw [hl] at h
  obtain ⟨-, vs, he, hs⟩ := PatVal.app_inv syms_cut.2.2.2.2.2.2.2.2.2.2.1 h syms_cut.1
  simp only [cfgV, GroundTerm.ctor.injEq, true_and] at he
  subst he
  obtain ⟨a1, as1, he1, h1, -⟩ := PatVals.cons_inv hs
  simp only [List.cons.injEq] at he1
  obtain ⟨rfl, rfl⟩ := he1
  obtain ⟨-, vs2, he2, hs2⟩ := PatVal.app_inv syms_cut.2.2.2.2.2.2.2.2.2.2.2.1 h1 syms_cut.2.1
  simp only [GroundTerm.ctor.injEq, true_and] at he2
  subst he2
  obtain ⟨a2, as2, he3, h2, -⟩ := PatVals.cons_inv hs2
  simp only [List.cons.injEq] at he3
  obtain ⟨rfl, rfl⟩ := he3
  obtain ⟨-, vs3, he4, hs3⟩ := PatVal.app_inv syms_cut.2.2.2.2.2.2.2.2.2.2.2.2.1 h2 syms_cut.2.2.1
  simp only [GroundTerm.ctor.injEq, true_and] at he4
  subst he4
  obtain ⟨a3, as3, he5, h3, -⟩ := PatVals.cons_inv hs3
  simp only [List.cons.injEq] at he5
  obtain ⟨rfl, rfl⟩ := he5
  obtain ⟨w', hw', he6⟩ := PatVal.inj_inv h3
  obtain ⟨-, vs4, rfl, hs4⟩ := PatVal.app_inv syms_cut.2.2.2.2.2.2.2.2.2.2.2.2.2 hw' syms_cut.2.2.2.2.1
  simp only [injNormal, GroundTerm.inj.injEq, GroundTerm.ctor.injEq, true_and] at he6
  subst he6
  obtain ⟨a4, as4, he7, h4, -⟩ := PatVals.cons_inv hs4
  simp only [List.cons.injEq] at he7
  obtain ⟨rfl, rfl⟩ := he7
  exact PatVal.var_inv h4

/-- `capGas(G)` at a value of G evaluates to its raw application or to an injection from N: never
to `inf`. -/
theorem capG_ne_inf {σ : Subst} {g : GroundTerm} {r' : Option GroundTerm}
    (h : EvalTerm cutSem σ (.app capGas [.var 0]) r') (hg : σ.lookup 0 = some g)
    (hb : true = ((some (GroundTerm.ctor inf [])).isSome && sameResult (some (.ctor inf [])) r')) : False := by
  generalize ht : Term.app capGas [.var 0] = t at h
  cases h with
  | ctor hc _ => cases ht; rw [syms_cut.2.2.2.2.2.2.1] at hc; cases hc
  | hook _ hhk _ _ _ => cases ht; rw [syms_cut.2.2.2.2.2.2.2.2.1] at hhk; cases hhk
  | param _ _ hp _ _ => cases ht; rw [syms_cut.2.2.2.2.2.2.2.2.2.1] at hp; cases hp
  | call _ _ _ _ hf _ =>
    cases ht
    have h' := hf.isOvl_false
    rw [syms_cut.2.2.2.2.2.2.2.1] at h'
    cases h'
  | callUndef => cases ht; simp [sameResult] at hb
  | ovl _ _ hts _ =>
    cases ht
    obtain ⟨r0, rs', rfl, h0, hn⟩ := EvalTerms.cons_inv hts
    cases EvalTerms.nil_inv hn
    rw [EvalTerm.var_inv h0, hg] at hb
    have hb' : true = (true && sameResult (some (.ctor inf [])) (some (cutSem.norm capGas [g]))) := hb
    rw [Bool.true_and, norm_capGas_cut] at hb'
    have he := sameResult_some_pto hb'.symm
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  | @ovlFn _ _ _ _ _ o kg r _ _ _ _ hlo hcov _ =>
    cases ht
    rw [lookupOvl_cut] at hlo
    cases hlo
    cases fnCover_cut hcov
    cases r with
    | none => simp [sameResult] at hb
    | some w =>
      have hb' : true = (true && sameResult (some (.ctor inf [])) (some (injNormal nS gasS w))) := hb
      rw [Bool.true_and] at hb'
      have he := sameResult_some_pto hb'.symm
      cases w <;> simp [injNormal] at he
  | _ => cases ht

/-- **No step from `run(inf)`**: V is `inf`, and no value g of Gas has `capGas(g)` equal to `inf`
(at `inj{N,Gas}(z)` it is `inj{N,Gas}(z)`, elsewhere the raw application). -/
theorem no_step_inf (y : Config cutSem) : ¬ Step cutSem runInf y := by
  intro h
  obtain ⟨r, σ, hb⟩ := step_iff_by.mp h
  obtain rfl : r = rCut := List.mem_singleton.mp hb.mem
  have hV : σ.lookup 2 = some (.ctor inf []) := lhs_inv_cut hb.hmatch
  obtain ⟨r1, r2, h1, h2, hb2⟩ := holds_mem_inv_pto (show Holds cutSem 3 σ (.mem gasS (.var 2) (.app capGas [.var 0])) true
    from hb.hpre)
  rw [EvalTerm.var_inv h1, hV] at hb2
  obtain ⟨g, hg, -⟩ := hb.hσ 0 gasS rfl
  exact capG_ne_inf h2 hg hb2

/-- **What was expected of e5-ovl-fun-lhs read through the cut.** -/
def expectCut : Prop :=
  cutSem.coreOK = true ∧ cutSem.rulePlainPP rCut = true ∧ FnHyp cutSem ∧ (∀ ref, CompleteC cutSem ref) ∧
    Step cutSem runZ doneZ ∧ Step cutSem runCapInf doneInf ∧ ∀ y, ¬ Step cutSem runInf y

theorem expect_cut : expectCut :=
  ⟨coreOK_cut, cut_facts.2.2.2.2.2.1, fnHyp_cut, complete_cut, step_z, step_capInf, no_step_inf⟩

/-! ## e5-ovl-fun-keep-run: the overload that keeps the result sort, with the cut rule -/

/-- `capN : N → Gas`, total, `capN(z) = inf` (e5-ovl-fun-keep-run), in this signature. -/
def capNKeepFn : Fn :=
  ⟨capN, [nS], gasS, [{ vars := [], pats := [.app z []], req := none, rhs := .app inf [], ens := none }], true⟩
def capNKeepCl : Clause := { vars := [], pats := [.app z []], req := none, rhs := .app inf [], ens := none }
def capNKeepSig : CtorSig := ⟨capN, [nS], gasS⟩

/-- e5-ovl-fun-keep-run: the cut semantics with `capN` keeping the result sort. -/
def keepRun : Semantics := { cutSem with fns := [capNKeepFn] }

theorem syms_keepRun : keepRun.isCtor topLabel = true ∧ keepRun.isCtor kl = true ∧ keepRun.isCtor kseq = true ∧
    keepRun.isCtor dotk = true ∧ keepRun.isCtor run = true ∧ keepRun.isCtor done = true ∧
    keepRun.isCtor capGas = false ∧ keepRun.isOvl capGas = true := by
  decide +kernel

theorem rules_keepRun : keepRun.rules = [rCut] := rfl

theorem eval_capN_keepRun : Eval keepRun capN [.ctor z []] (some (.ctor inf [])) :=
  .clause (fn := capNKeepFn) (cl := capNKeepCl) (σ := [])
    (by rw [Semantics.lookupFn_eq]; rfl) (List.mem_cons_self ..)
    (fun i s' h => by simp [capNKeepCl] at h)
    (.cons (.ctor (by decide +kernel) .nil) .nil) (fun t ht => by cases ht) .top
    (fun cl' h _ hlt => by
      have : cl' = capNKeepCl := by simpa [capNKeepFn, capNKeepCl] using h
      subst this
      exact absurd hlt (Nat.lt_irrefl _))
    rfl (.ctor (f := inf) (rs := []) (by decide +kernel) .nil) (fun t ht => by cases ht) .top

def runInfK : Config keepRun := ⟨cfgV (.ctor run [.ctor inf []]), by decide +kernel⟩
def doneZK : Config keepRun := ⟨cfgV (.ctor done [injZ]), by decide +kernel⟩

/-- **`run(inf)` steps to `done(inj{N,Gas}(z))`**: G := `inj{N,Gas}(z)`, covered, and
`capGas(inj{N,Gas}(z)) = capN(z) = inf`. -/
theorem step_keepRun : Step keepRun runInfK doneZK := by
  refine step_iff_by.mpr ⟨rCut, [(0, injZ), (1, cnt0), (2, .ctor inf [])], ?_⟩
  exact
  { mem := by rw [rules_keepRun]; exact List.mem_singleton_self _
    hσ := fun j s hs => by
      rw [rCut_vars] at hs
      match j, hs with
      | 0, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | j + 3, hs => simp at hs
    hmatch := .ctor syms_keepRun.1 (.cons (.ctor syms_keepRun.2.1 (.cons (.ctor syms_keepRun.2.2.1
      (.cons (.inj (.ctor syms_keepRun.2.2.2.2.1 (.cons (.var rfl) .nil))) (.cons (.ctor syms_keepRun.2.2.2.1 .nil) .nil)))
        .nil)) (.cons (.var rfl) .nil))
    hreq := fun t ht => by simp [rCut] at ht
    hpre := holds_mem_pto (.var : EvalTerm keepRun _ (.var 2) _)
      (EvalTerm.ovlFn (rs := [some injZ]) (vs := [injZ]) (o := capGasO) (kg := capNKeepSig)
        (r := some (.ctor inf [])) syms_keepRun.2.2.2.2.2.2.1 syms_keepRun.2.2.2.2.2.2.2 (.cons .var .nil) rfl
        (by decide +kernel) (by decide +kernel) eval_capN_keepRun)
    heval := .ctor syms_keepRun.1 (.cons (.ctor syms_keepRun.2.1 (.cons (.ctor syms_keepRun.2.2.1
      (.cons (.inj (.ctor syms_keepRun.2.2.2.2.2.1 (.cons .var .nil))) (.cons (.ctor syms_keepRun.2.2.2.1 .nil) .nil)))
        .nil)) (.cons .var .nil))
    hens := fun t ht => by simp [rCut] at ht
    hpost := .top
    hprio := fun r' hr' hlt => by
      rw [rules_keepRun] at hr'
      rw [List.mem_singleton.mp hr'] at hlt
      exact absurd hlt (Nat.lt_irrefl _) }

end Cap

/-! ## e5-ovl-fun-lhs-int: a cut whose function overload takes Int -/

namespace Dbl

def expS : Srt := nRegSorts
def pgmS : Srt := nRegSorts + 1
def kl : Sym := nRegSyms + 4
def done : Sym := nRegSyms + 6
def run : Sym := nRegSyms + 7
def dblInt : Sym := nRegSyms + 8
def dblExp : Sym := nRegSyms + 9

/-- `dblInt : Int → Int`, total, `dblInt(I) = 2 *Int I`. -/
def dblIntFn : Fn :=
  ⟨dblInt, [Srt.int], Srt.int,
    [{ vars := [Srt.int], pats := [.var 0], req := none, rhs := .app intMul [intT 2, .var 0], ens := none }], true⟩

/-- `dblExp : Exp → Exp` over `dblInt`, Int < Exp, `run : Exp → Pgm`, `done : dArg → Pgm`, and the
rules `rs`. -/
def sem (dArg : Srt) (rs : List Rule) : Semantics :=
  { lib := lib0
    sortNames := ["Exp", "Pgm", "KCell", "KCellOpt"]
    symNames := ["LblisExp", "LblisPgm", "LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell",
      "Lbldone", "Lblrun", "LbldblInt", "LbldblExp"]
    userSorts := [Srt.top, Srt.topFrag, expS, pgmS, pgmS + 1, pgmS + 2, Srt.counter, Srt.counterOpt]
    ctors := cellCtors (pgmS + 1) kl ++ [⟨done, [dArg], pgmS⟩, ⟨run, [expS], pgmS⟩]
    fns := [dblIntFn]
    userSubsorts := (Srt.int, expS) :: cellSubsorts (pgmS + 1)
    pgmSort := pgmS
    rules := rs
    ovls := [⟨⟨dblExp, [expS], expS⟩, [dblInt]⟩] }

/-- `<k> run(dbl(_:Exp)) => done(0) </k>` read through the cut: `run(V) => done(0)`,
`pre := V ∈ dblExp(E)`, E the variable 0 and V the variable 2. -/
def rZero : Rule :=
  { vars := [expS, Srt.counter, expS], lhs := cfg kl pgmS (.app run [.var 2]) 1, req := none,
    rhs := cfg kl pgmS (.app done [intT 0]) 1, ens := none, prio := 50,
    pre := .mem expS (.var 2) (.app dblExp [.var 0]) }
/-- `<k> run(_:Exp) => done(1) </k> [owise]`. -/
def rOwise : Rule :=
  { vars := [expS, Srt.counter], lhs := cfg kl pgmS (.app run [.var 0]) 1, req := none,
    rhs := cfg kl pgmS (.app done [intT 1]) 1, ens := none, prio := 200 }
/-- The same cut with the right side `done(E)`. -/
def rE : Rule := { rZero with rhs := cfg kl pgmS (.app done [.var 0]) 1 }

/-- e5-ovl-fun-lhs-int's text, its first rule cut. -/
def text : Semantics := sem Srt.int [rZero, rOwise]
/-- The cut rule without the `[owise]` rule. -/
def zeroAlone : Semantics := sem Srt.int [rZero]
/-- The cut rule with `=> done(E)` (`done` taking Exp), without the `[owise]` rule. -/
def alone : Semantics := sem expS [rE]

/-- `dblExp`'s function overload takes Int, which is not confined, and so is Exp: `dblExp` is not
`ovlHeld`, so the cut does not hold E (`memHeld`), and no symbol of `rZero`'s right side holds E. -/
theorem not_held : text.fnOvlSyms = [dblExp] ∧ text.confined Srt.int = false ∧ text.confined expS = false ∧
    text.ovlHeld dblExp = false ∧ text.holds dblExp = false ∧ memHeld text (varOccs rZero.lhs) rZero.pre 0 = false ∧
    varOccs rZero.lhs = [2, 1] ∧ rZero.opens = [0] ∧ rZero.openCondVars = [0] ∧ rZero.reqClosed = false ∧
    (heldOccs text rZero.rhs).contains 0 = false := by
  decide +kernel

/-- **e5-ovl-fun-lhs-int is refused, at E under `dblExp`**: `rZero` fails the arms (E is held by
no constructor of the right side, its sort is not confined, and the conditions are not closed) and
the competition conjunct (E is an open condition variable of an unconfined sort in a rule below
the `[owise]` rule's priority); the `[owise]` rule passes. The cut rule is well sorted and its
left side applies no function-overloaded symbol. The reader's refusal, `openRequires` naming E and
`dblExp`, is test/OvlCutRule.lean's. -/
theorem text_refused : text.rulesPlain = false ∧ text.rulePlainHO1 rZero = false ∧
    text.rulePlainHO1 rOwise = true ∧
    rZero.opens.all (fun i => (heldOccs text rZero.rhs).contains i ||
      (rZero.vars[i]?.map text.confined).getD false ||
      (rZero.condVars.contains i && rZero.reqClosed)) = false ∧
    (!rZero.reqOpen || !text.rules.any (fun r' => rZero.prio < r'.prio) ||
      rZero.openCondVars.all (fun i => (rZero.vars[i]?.map text.confined).getD false) || rZero.reqClosed) = false ∧
    text.ruleSorted rZero = true ∧ text.ovlPatsOK = true := by
  decide +kernel

theorem coreOK_text : text.coreOK = false := by
  cases h : text.coreOK
  · rfl
  · have hs := (Semantics.coreOK_parts h).1
    have hp : text.rulesPlain = true := by
      simp only [Semantics.sortedOK, Bool.and_eq_true] at hs
      exact hs.1.1.2
    rw [text_refused.1] at hp; cases hp

/-- Without the `[owise]` rule, and right side `done(0)`, the arms still refuse E. -/
theorem zeroAlone_refused : zeroAlone.rulesPlain = false ∧ zeroAlone.rulePlainHO1 rZero = false := by
  decide +kernel

/-- **Alone and with `=> done(E)`, the cut rule is admitted by arm A**: E is held by the right
side under the constructor `done`, and no rule has a larger priority. -/
theorem alone_admitted : alone.rulesPlain = true ∧ (ctorOccs alone rE.rhs).contains 0 = true ∧
    alone.rulePlainPP rE = true ∧ alone.ruleSorted rE = true ∧ alone.ovlPatsOK = true := by
  decide +kernel

theorem light_alone : light alone = true := by rw [light]; decide_cheap

open Faithful.Model in
theorem names_alone : namesApartFast alone = true := by decide +kernel

open Faithful.Model in
theorem ites_alone : itesApart alone = true := by decide_cheap

theorem others_alone : others alone = true := others_of light_alone names_alone ites_alone

theorem ovls_alone : alone.overloadsOK = true := by decide +kernel

/-- `coreOK` admits the cut rule alone with `=> done(E)`. -/
theorem coreOK_alone : alone.coreOK = true := Admit.coreOK_of others_alone ovls_alone

end Dbl

/-- info: 'OvlFun.Cap.cut_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.cut_facts
/-- info: 'OvlFun.Cap.coreOK_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.coreOK_cut
/-- info: 'OvlFun.Cap.fnHyp_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.fnHyp_cut
/-- info: 'OvlFun.Cap.complete_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.complete_cut
/-- info: 'OvlFun.Cap.sound_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.sound_cut
/-- info: 'OvlFun.Cap.step_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.step_z
/-- info: 'OvlFun.Cap.step_capInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.step_capInf
/-- info: 'OvlFun.Cap.no_step_inf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.no_step_inf
/-- info: 'OvlFun.Cap.expect_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.expect_cut
/-- info: 'OvlFun.Cap.step_keepRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cap.step_keepRun
/-- info: 'OvlFun.Dbl.not_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Dbl.not_held
/-- info: 'OvlFun.Dbl.text_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Dbl.text_refused
/-- info: 'OvlFun.Dbl.coreOK_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Dbl.coreOK_text
/-- info: 'OvlFun.Dbl.zeroAlone_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Dbl.zeroAlone_refused
/-- info: 'OvlFun.Dbl.alone_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Dbl.alone_admitted
/-- info: 'OvlFun.Dbl.coreOK_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Dbl.coreOK_alone

end OvlFun
