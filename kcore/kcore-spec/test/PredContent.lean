/-
  The equations of a sort's predicate that a text holds, against the clauses the reading gives
  that predicate (`Semantics.sortPreds`): `Parse.predEqnOK`, `Parse.predProjOK?`,
  `Parse.predEqnFaults`, the reader's choice between `sortPreds`' function and the function the
  equations define (`Parse.predFnNamesPR`, `Parse.predStdHeldPR`, `Parse.coreOf`) and the
  account's (`Parse.consumedWith`). Run from the package root:
  `lake env lean -j1 test/PredContent.lean`.

  ## Hand-written equations, in the kernel (`Hand`)

  A semantics with one own sort Foo and a constructor `pair(Foo, Foo) : Foo`; its `sortPreds` hold
  `isFoo(kseq(inj{Foo,KItem}(V), dotk)) = true` and `isFoo(K) = false` at priority 200. Equations
  of `isFoo`:
  - `std`, `isFoo(kseq(inj{Foo,KItem}(V), dotk)) = true`;
  - `pair`, `isFoo(kseq(inj{Foo,KItem}(pair(K0, K1)), dotk)) = true requires isFoo(K0) andBool
    isFoo(K1)`;
  - `ow ds`, `isFoo(K) = false [owise]` with the exclusion's disjuncts `ds`: `dStd` excludes `std`,
    `dPair` excludes `pair`.
  `decide +kernel`:
  - the text `[ow [dStd], std]`: both are sentences the reading states, no fault;
  - `pair` is none, first or second among the equations without `[owise]`;
  - `ow []` (it says `false` where `std` says `true`), `ow [dPair, dStd]` and `ow [dStd, dPair]`
    (silent where the reading says `false`), `ow [dPair]`, and `ow [dStd, dStd]` are none;
  - `ow [dStd]` in a text that holds `pair` too is one (the fault is `pair`'s alone);
  - `ow [dStd]` in a text without `std` is none: no equation of the text reads to the clause its
    disjunct excludes;
  - the faults of `[ow [dPair, dStd], pair, std]` and of `[ow [dPair, dStd], std, pair]` are the
    `[owise]` equation's and `pair`'s, `generatedEquation`; with a user source, `unaccounted`.
  - `Γ` entails `pairT`'s equation (`inst_entailed`) and the `[owise]` equation that also names it
    (`owise_inst_entailed`).
  `predEqnFaults` is (a) of the reader's choice. Where (a) and (b) hold `isFoo` stays `sortPreds`'
  function (`kept`: the standard equations, with `pairT` or without); otherwise the reader reads it
  as the function of its equations (`fnFrom`): `faults`' texts with three clauses (`read_pair`),
  `fault_user`'s refused by `fnFrom` (`exclusionShape`, `read_user`), `inst_false`'s `pairF` text
  with three clauses whose agreement is owed (`read_inst_false`), a text without the `[owise]`
  equation (b) (`missing`).

  ## A hybrid predicate read and evaluated in the kernel (`Hyb`)

  `isRes` read from the three equations kompile writes for a `hybrid` constructor: one function of
  `c.fns` of three clauses, `isRes(pair(v, v)) = true`, `isRes(pair(v, e)) = false`.

  ## The fixtures' kompiled texts (K 7.1.337 kompile's KORE, from the cache `kfix.py` keeps)

  - `c3-strict-hybrid` and `e2-frontend-effect` (`pair` declared `hybrid`: the text holds
    `isKResult(pair(K0, K1)) = true requires isKResult(K0) andBool isKResult(K1)` and the `[owise]`
    equation excludes it): read, every sentence accounted for; isKResult is a function of `c.fns`
    of three clauses, `coreOK` holds, its totality is owed, and `isKResult(pair(1, 2))` evaluates
    to true.
  - `c3-strict-hybrid` with the standard equation moved before the pair equation: the same.
  - `c3-strict-base` (the same text without `hybrid`): read, every sentence accounted for, isKResult
    `sortPreds`' function.
  - `rdr-pred-rule` (`rule isFoo(pair(_, _)) => true`, an instance `Γ` entails): isFoo stays
    `sortPreds`' function. The same text with the rule giving false: read, isFoo the function of
    its three equations, their agreement owed (the text has no model).
  - The account alone, the definition read from `c3-strict-base` and the sentences of
    `c3-strict-hybrid` in both orders: the `[owise]` equation and the pair equation are not
    accounted for, the standard equation is; none of the three is accounted for without the arm
    for the equations no function holds (`consumedWith false`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse

namespace PredContent

namespace Hand

open KoreAML (ev evar ap srt asK uidAttr attr srcAttr R)

def Foo : Srt := nRegSorts
def isFoo : Sym := nRegSyms
def pairS : Sym := nRegSyms + 1

def N : Names := { sorts := ["Foo"], syms := ["LblisFoo", "Lblpair"] }

/-- One own sort Foo, with `pair(Foo, Foo) : Foo`; no function, no rule. -/
def c : Semantics :=
  { lib := libOf [], sortNames := N.sorts, symNames := N.syms, userSorts := [Foo]
    ctors := [⟨pairS, [Foo, Foo], Foo⟩], fns := [], userSubsorts := [], pgmSort := Srt.k, rules := [] }

def tt : Kore.Pattern := .dv (srt "Bool") "true"
def ff : Kore.Pattern := .dv (srt "Bool") "false"
def item (p : Kore.Pattern) : Kore.Pattern := asK "Foo" p
def isFooP (p : Kore.Pattern) : Kore.Pattern := ap "LblisFoo" [item p]
def bothP (a b : Kore.Pattern) : Kore.Pattern := ap "Lbl'Unds'andBool'Unds'" [isFooP a, isFooP b]

def std : RawEqn := ⟨"LblisFoo", [item (ev "VarV" (srt "Foo"))], none, none, tt, [uidAttr "std"], none, false⟩

def pair : RawEqn :=
  ⟨"LblisFoo", [item (ap "Lblpair" [ev "VarK0" (srt "Foo"), ev "VarK1" (srt "Foo")])],
   some (bothP (ev "VarK0" (srt "Foo")) (ev "VarK1" (srt "Foo"))), none, tt, [uidAttr "pair"], none, false⟩

/-- A disjunct `\exists x̄. req ∧ X0 ∈ p ∧ \top`. -/
def disjunct (xs : List Kore.EVar) (req p : Kore.Pattern) : Kore.Pattern :=
  KoreAML.existsAll R xs (.and R [req, .and R [.in (srt "K") R (ev "X0" (srt "K")) p, .top R]])

def dStd : Kore.Pattern :=
  disjunct [evar "Var'Unds'Gen2" (srt "Foo")] (.top R) (item (ev "Var'Unds'Gen2" (srt "Foo")))

def dPair : Kore.Pattern :=
  let g0 := ev "Var'Unds'Gen0" (srt "Foo")
  let g1 := ev "Var'Unds'Gen1" (srt "Foo")
  disjunct [evar "Var'Unds'Gen0" (srt "Foo"), evar "Var'Unds'Gen1" (srt "Foo")]
    (.equals (srt "Bool") R (bothP g0 g1) tt) (item (ap "Lblpair" [g0, g1]))

def ow (ds : List Kore.Pattern) : RawEqn :=
  ⟨"LblisFoo", [ev "VarK" (srt "K")], none, some ds, ff, [uidAttr "ow", attr "owise"], none, false⟩

def ok (eqs : List RawEqn) (e : RawEqn) : Option Bool := predProjOK? N "" eqs c e

/-- The reading's predicate of Foo: the two clauses. -/
theorem isFoo_clauses : ((c.sortPreds.find? (·.label == isFoo)).map fun fn => fn.clauses.map (·.prio)) =
    some [50, 200] := by decide +kernel

/-- The two standard equations are the predicate's clauses. -/
theorem standard : ok [ow [dStd], std] std = some true ∧ ok [ow [dStd], std] (ow [dStd]) = some true ∧
    (predEqnFaults N "" [ow [dStd], std] c).length = 0 := by decide +kernel

/-- The pair equation is no clause of the predicate, first or second in the text. -/
theorem pair_none : ok [ow [dPair, dStd], pair, std] pair = some false ∧
    ok [ow [dPair, dStd], std, pair] pair = some false ∧ ok [ow [dStd], pair, std] pair = some false := by
  decide +kernel

/-- The standard equation is a clause beside the pair equation, in either order. -/
theorem std_beside : ok [ow [dPair, dStd], pair, std] std = some true ∧
    ok [ow [dPair, dStd], std, pair] std = some true := by decide +kernel

/-- An `[owise]` equation whose exclusion is not one disjunct for the clause before it. -/
theorem owise_none :
    ok [ow [], std] (ow []) = some false ∧
    ok [ow [dPair, dStd], pair, std] (ow [dPair, dStd]) = some false ∧
    ok [ow [dPair, dStd], std, pair] (ow [dPair, dStd]) = some false ∧
    ok [ow [dStd, dPair], pair, std] (ow [dStd, dPair]) = some false ∧
    ok [ow [dPair], pair, std] (ow [dPair]) = some false ∧
    ok [ow [dStd, dStd], std] (ow [dStd, dStd]) = some false ∧
    ok [ow [dStd]] (ow [dStd]) = some false := by decide +kernel

/-- The `[owise]` equation with the standard exclusion is the clause, whatever else the text holds. -/
theorem owise_beside : ok [ow [dStd], pair, std] (ow [dStd]) = some true := by decide +kernel

/-- The attributes of the equation a fault is at. -/
def at? (f : Fault) : List Kore.AppPattern := match f.site with
  | .attrs as => as
  | _ => []

/-- The faults of the text with the pair equation, in both orders: the `[owise]` equation's and the
pair equation's. -/
theorem faults :
    (predEqnFaults N "" [ow [dPair, dStd], pair, std] c).map (fun f => (f.reason, at? f)) =
      [(.generatedEquation, (ow []).attrs), (.generatedEquation, pair.attrs)] ∧
    (predEqnFaults N "" [ow [dPair, dStd], std, pair] c).map (fun f => (f.reason, at? f)) =
      [(.generatedEquation, (ow []).attrs), (.generatedEquation, pair.attrs)] := by
  decide +kernel

/-- Written in a user's file, the pair equation is refused `unaccounted`. -/
theorem fault_user :
    let src := srcAttr "/made-up/user.k"
    (predEqnFaults N "/made-up/user.k" [ow [dStd], { pair with attrs := pair.attrs ++ [src] }, std] c).map (·.reason) =
      [.unaccounted] := by decide +kernel

/-- An equation of another symbol is not these functions'. -/
theorem other : ok [std] { std with fn := "Lblpair" } = none := by decide +kernel

/-! ### An instance of `std` at a constructor pattern (`predInstOK`, `predInstAcc`) -/

/-- `pairT`, `isFoo(kseq(inj{Foo,KItem}(pair(K0, K1)), dotk)) = true`: `std` with the constructor
pattern `pair(K0, K1)` in V's place; `pairF` the same with `false`. -/
def pairT : RawEqn := { pair with req := none, attrs := [uidAttr "pairT"] }
def pairF : RawEqn := { pairT with rhs := ff, attrs := [uidAttr "pairF"] }

def dPairT : Kore.Pattern :=
  let g0 := ev "Var'Unds'Gen0" (srt "Foo")
  let g1 := ev "Var'Unds'Gen1" (srt "Foo")
  disjunct [evar "Var'Unds'Gen0" (srt "Foo"), evar "Var'Unds'Gen1" (srt "Foo")] (.top R) (item (ap "Lblpair" [g0, g1]))

/-- `pairT` is an instance of `std` (and `std` of itself, V in V's place); `pairF`, which gives the
other value, and `pair`, which has a `requires`, are not. -/
theorem inst : predInstOK N "" c pairT = true ∧ predInstOK N "" c pairF = false ∧
    predInstOK N "" c pair = false ∧ predInstOK N "" c std = true := by decide +kernel

/-- The text with `pairT` and its `[owise]` equation excluding it and `std`, in either order of the
disjuncts: no fault; `predProjOK?` still says neither is a clause of the predicate. -/
theorem inst_text :
    (predEqnFaults N "" [ow [dPairT, dStd], pairT, std] c).length = 0 ∧
    (predEqnFaults N "" [ow [dStd, dPairT], std, pairT] c).length = 0 ∧
    ok [ow [dPairT, dStd], pairT, std] pairT = some false ∧
    ok [ow [dPairT, dStd], pairT, std] (ow [dPairT, dStd]) = some false := by decide +kernel

/-- The text with `pairF` (a sentence contradicting the predicate's clause): both refused, as is an
`[owise]` equation that excludes `pairT` in a text without it. -/
theorem inst_false :
    (predEqnFaults N "" [ow [dPairT, dStd], pairF, std] c).map (fun f => (f.reason, at? f)) =
      [(.generatedEquation, (ow []).attrs), (.generatedEquation, pairF.attrs)] ∧
    (predEqnFaults N "" [ow [dPairT, dStd], std] c).map (·.reason) = [.generatedEquation] := by
  decide +kernel

/-- **`Γ` entails `pairT`'s equation**, for the semantics `c` (`GenEqs.predInst_entailed`). -/
theorem inst_entailed : ∃ fn ∈ c.sortPreds, c.symName fn.label = "LblisFoo" ∧ ∃ cl cp,
    clause? N "" pairT none = .ok (cl, cp) ∧
    ∀ it ∈ Faithful.kernelItems [Faithful.prioEquation c fn cl], Faithful.Γ c ⊧ it.pat :=
  GenEqs.predInst_entailed (by decide +kernel) inst.1

/-- `isFoo`, the predicate of Foo among the semantics' sort predicates. -/
def fooPred : Fn := (c.sortPreds.find? (·.label == isFoo)).getD ⟨isFoo, [], Srt.bool, [], true⟩

theorem fooPred_mem : fooPred ∈ c.sortPreds := by
  have h : (c.sortPreds.find? (·.label == isFoo)).isSome = true := by decide +kernel
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp h
  unfold fooPred; rw [hf]; exact List.mem_of_find?_eq_some hf

/-- **`Γ` entails `inst_text`'s `[owise]` equation, whose exclusion names `pairT` beside `std`**,
for the semantics `c` (`GenEqs.predOwiseInst_entailed`): without `dPairT` it reads to a clause `ow`
of `isFoo`, and `Γ` entails `ow`'s equation under the negation of any disjuncts among which are
the exclusions of the clauses before it, `dPairT` among them or not. -/
theorem owise_inst_entailed : ∃ ow ∈ fooPred.clauses, ∀ ds₀ : List Kore.Pattern,
    (∀ cl' ∈ Faithful.lowerClauses fooPred ow, exclusion c fooPred cl' (Faithful.canonClausePres cl') ∈ ds₀) →
    ∀ it ∈ Faithful.kernelItems [GenEqs.owiseWith c fooPred ds₀ ow], Faithful.Γ c ⊧ it.pat := by
  obtain ⟨-, -, -, -, -, -, ow, -, how, -, h⟩ := GenEqs.predOwiseInst_entailed fooPred_mem
    (show predOwiseInstOK N "" [ow [dPairT, dStd], pairT, std] c fooPred (ow [dPairT, dStd]) = true by decide +kernel)
  exact ⟨ow, how, h⟩

/-! ### The reader's verdict: `sortPreds`' function, or the function of the equations

`predFnNamesPR` names the own sorts' predicates whose equations are not exactly the clauses
`sortPreds` gives ((a) and (b) of `predStdHeldPR`); the reader reads each from its equations
(`fnFrom`, as `predFnsOfPR` does at its declaration), and a refusal of `fnFrom` refuses the text. -/

/-- `isFoo` read from the equations `eqs`. -/
def readFoo (msrc : String) (eqs : List RawEqn) : Rd (Fn × FnPres) :=
  fnFrom N msrc none eqs (fnClauses N msrc eqs "LblisFoo") "LblisFoo" none ["K"] "Bool" noLoc true

/-- The number of clauses of `readFoo`, where `fnFrom` reads it. -/
def readLen (msrc : String) (eqs : List RawEqn) : Option Nat := (readFoo msrc eqs).toOption.map (·.1.clauses.length)

/-- `fnFrom`'s refusal of `readFoo`, where it refuses. -/
def readRefusal (msrc : String) (eqs : List RawEqn) : Option RefusalReason :=
  match readFoo msrc eqs with
  | .ok _ => none
  | .error f => some f.reason

/-- The standard equations, with or without `pairT` (an instance `Γ` entails, as in the fixture
rdr-pred-rule): `isFoo` stays `sortPreds`' function. -/
theorem kept : predFnNamesPR N "" [ow [dStd], std] c = [] ∧
    predFnNamesPR N "" [ow [dPairT, dStd], pairT, std] c = [] ∧
    predFnNamesPR N "" [ow [dStd, dPairT], std, pairT] c = [] := by decide +kernel

/-- `faults`' texts (the pair equation, a third equation that is no instance, before or after
`std`): `isFoo` is the function of its three equations, the `[owise]` equation's two disjuncts
matched to `pair` and `std` by content. -/
theorem read_pair : predFnNamesPR N "" [ow [dPair, dStd], pair, std] c = ["LblisFoo"] ∧
    predFnNamesPR N "" [ow [dPair, dStd], std, pair] c = ["LblisFoo"] ∧
    readLen "" [ow [dPair, dStd], pair, std] = some 3 ∧ readLen "" [ow [dPair, dStd], std, pair] = some 3 := by
  decide +kernel

/-- `fault_user`'s text (the pair equation in a user's file, the `[owise]` equation excluding
`std` alone): read as the function of its equations, which `fnFrom` refuses, the exclusion naming
one of the two equations (`exclusionShape`); with the exclusion naming both, read as a function
too. (A user's equation of a sort predicate read by the whole reader, with its place: the
rdr-pred-rule texts below.) -/
theorem read_user :
    let src := srcAttr "/made-up/user.k"
    let pu := { pair with attrs := pair.attrs ++ [src] }
    predFnNamesPR N "/made-up/user.k" [ow [dStd], pu, std] c = ["LblisFoo"] ∧
    readRefusal "/made-up/user.k" [ow [dStd], pu, std] = some .exclusionShape ∧
    predFnNamesPR N "/made-up/user.k" [ow [dPair, dStd], pu, std] c = ["LblisFoo"] := by decide +kernel

/-- `inst_false`'s first text (`pairF`, `isFoo(pair(K0, K1)) = false`): read as the function of
its three equations; `pairF` and `std`, of one priority, give two values at `pair(K0, K1)`, which
`fnExclusiveOK` does not show to agree: their agreement is owed (`agreeObligations`), false
wherever Foo has an element (the text then has no model). Its second (an `[owise]` equation
excluding `pairT` in a text without it): read as a function, which `fnFrom` refuses. -/
theorem read_inst_false : predFnNamesPR N "" [ow [dPairT, dStd], pairF, std] c = ["LblisFoo"] ∧
    readLen "" [ow [dPairT, dStd], pairF, std] = some 3 ∧
    ((readFoo "" [ow [dPairT, dStd], pairF, std]).toOption.map fun (f, _) =>
      ({ c with fns := [f] } : Semantics).agreeObligations) = some [isFoo] ∧
    predFnNamesPR N "" [ow [dPairT, dStd], std] c = ["LblisFoo"] ∧
    readRefusal "" [ow [dPairT, dStd], std] = some .exclusionShape := by decide +kernel

/-- (b): a text without the `[owise]` equation, whose one equation passes (a) (no fault), states
no clause `isFoo(K) = false`: read as the function of its equation. A text without `std` fails (a)
(`owise_none`) and is read as a function, which `fnFrom` refuses. -/
theorem missing : (predEqnFaults N "" [std] c).length = 0 ∧ predStdHeldPR N "" [std] c fooPred = false ∧
    predFnNamesPR N "" [std] c = ["LblisFoo"] ∧ readLen "" [std] = some 1 ∧
    predFnNamesPR N "" [ow [dStd]] c = ["LblisFoo"] ∧ readRefusal "" [ow [dStd]] = some .exclusionShape := by
  decide +kernel

end Hand

/-! ## A hybrid predicate, read and evaluated in the kernel (`Hyb`)

Sorts Exp and Res, Res < Exp; `pair(Exp, Exp) : Exp`, `v : Res`, `e : Exp`. Equations of `isRes`
as kompile writes them for `pair` declared `hybrid`: the standard one, `isRes(kseq(inj{Exp,KItem}(
pair(K0, K1)), dotk)) = true requires isRes(K0) andBool isRes(K1)`, and the `[owise]` equation
excluding both; `isExp`'s two standard equations. `isRes` is read as the function of its three
equations, `isExp` stays `sortPreds`' function; with that function in `c.fns`, `sortPreds` builds
none for Res and `isRes(pair(v, v))` evaluates to true, `isRes(pair(v, e))` to false. -/

namespace Hyb

open KoreAML (ev evar ap srt asK uidAttr attr R)

def Exp : Srt := nRegSorts
def Res : Srt := nRegSorts + 1
def isRes : Sym := nRegSyms + 1
def pairS : Sym := nRegSyms + 2
def vS : Sym := nRegSyms + 3
def eS : Sym := nRegSyms + 4

def N : Names := { sorts := ["Exp", "Res"], syms := ["LblisExp", "LblisRes", "Lblpair", "Lblv", "Lble"] }

def c : Semantics :=
  { lib := libOf [], sortNames := N.sorts, symNames := N.syms, userSorts := [Exp, Res]
    ctors := [⟨pairS, [Exp, Exp], Exp⟩, ⟨vS, [], Res⟩, ⟨eS, [], Exp⟩], fns := [], userSubsorts := [(Res, Exp)]
    pgmSort := Srt.k, rules := [] }

def tt : Kore.Pattern := .dv (srt "Bool") "true"
def ff : Kore.Pattern := .dv (srt "Bool") "false"
def isResP (p : Kore.Pattern) : Kore.Pattern := ap "LblisRes" [asK "Exp" p]
def bothP (a b : Kore.Pattern) : Kore.Pattern := ap "Lbl'Unds'andBool'Unds'" [isResP a, isResP b]

/-- A disjunct `\exists x̄. req ∧ X0 ∈ p ∧ \top`. -/
def disjunct (xs : List Kore.EVar) (req p : Kore.Pattern) : Kore.Pattern :=
  KoreAML.existsAll R xs (.and R [req, .and R [.in (srt "K") R (ev "X0" (srt "K")) p, .top R]])

def stdExp : RawEqn := ⟨"LblisExp", [asK "Exp" (ev "VarV" (srt "Exp"))], none, none, tt, [uidAttr "stdExp"], none, false⟩
def owExp : RawEqn :=
  ⟨"LblisExp", [ev "VarK" (srt "K")], none,
   some [disjunct [evar "Var'Unds'Gen3" (srt "Exp")] (.top R) (asK "Exp" (ev "Var'Unds'Gen3" (srt "Exp")))], ff,
   [uidAttr "owExp", attr "owise"], none, false⟩

def std : RawEqn := ⟨"LblisRes", [asK "Res" (ev "VarV" (srt "Res"))], none, none, tt, [uidAttr "std"], none, false⟩
def pair : RawEqn :=
  ⟨"LblisRes", [asK "Exp" (ap "Lblpair" [ev "VarK0" (srt "Exp"), ev "VarK1" (srt "Exp")])],
   some (bothP (ev "VarK0" (srt "Exp")) (ev "VarK1" (srt "Exp"))), none, tt, [uidAttr "pair"], none, false⟩
def ow : RawEqn :=
  let g0 := ev "Var'Unds'Gen0" (srt "Exp")
  let g1 := ev "Var'Unds'Gen1" (srt "Exp")
  ⟨"LblisRes", [ev "VarK" (srt "K")], none,
   some [disjunct [evar "Var'Unds'Gen0" (srt "Exp"), evar "Var'Unds'Gen1" (srt "Exp")]
           (.equals (srt "Bool") R (bothP g0 g1) tt) (asK "Exp" (ap "Lblpair" [g0, g1])),
         disjunct [evar "Var'Unds'Gen2" (srt "Res")] (.top R) (asK "Res" (ev "Var'Unds'Gen2" (srt "Res")))], ff,
   [uidAttr "ow", attr "owise"], none, false⟩

def eqs : List RawEqn := [owExp, stdExp, ow, pair, std]

/-- `isRes` read from its equations. -/
def readRes : Rd (Fn × FnPres) :=
  fnFrom N "" none eqs (fnClauses N "" eqs "LblisRes") "LblisRes" none ["K"] "Bool" noLoc true

/-- The semantics with `isRes` the function read. -/
def cR : Semantics := match readRes with
  | .ok (f, _) => { c with fns := [f] }
  | .error _ => c

theorem moved : predFnNamesPR N "" eqs c = ["LblisRes"] := by decide +kernel

/-- One function of three clauses, under the predicate's number: the `[owise]` one last, at
priority 200; `sortPreds` builds no function of that number and still builds `isExp`'s. -/
theorem read : cR.fns.map (fun f => (f.label, f.clauses.map (·.prio))) = [(isRes, [50, 50, 200])] ∧
    (cR.sortPreds.map (·.label)).contains isRes = false ∧ (cR.sortPreds.map (·.label)).contains nRegSyms = true := by
  decide +kernel

def item (t : Term) : Term := .app kseq [.inj Exp Srt.kitem t, .app dotk []]
def v : Term := .inj Res Exp (.app vS [])
def e : Term := .app eS []

/-- `isRes(pair(v, v)) = true`, `isRes(pair(v, pair(v, v))) = true`, `isRes(pair(v, e)) = false`. -/
theorem eval :
    Exec.evalT cR 100 [] (.app isRes [item (.app pairS [v, v])]) = some (some (.dv Srt.bool (.bool true))) ∧
    Exec.evalT cR 100 [] (.app isRes [item (.app pairS [v, .app pairS [v, v]])]) =
      some (some (.dv Srt.bool (.bool true))) ∧
    Exec.evalT cR 100 [] (.app isRes [item (.app pairS [v, e])]) = some (some (.dv Srt.bool (.bool false))) := by
  decide +kernel

end Hyb

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
def load (n : String) (edit : String → String := id) : IO Kore.Definition := do
  let t ← IO.FS.readFile s!"test/constructs/fixtures/{n}/kompile.txt"
  let some l := (t.splitOn "\n").find? (·.startsWith "definition.kore sha256: ")
    | throw (IO.userError s!"{n}: kompile.txt names no sha256")
  let sha := (l.splitOn ": ").getD 1 ""
  let raw := edit (← IO.FS.readFile s!"{← cacheDir}/{sha}.kore")
  let raw := ((raw.replace "BUILTIN/" "/made-up-k/include/kframework/builtin/").replace "FIXTURE/" "/made-up-fx/").replace
    "FIXTURE" "/made-up-fx"
  match Kore.parseDefinition raw with
  | .ok k => pure k
  | .error e => throw (IO.userError s!"{n}: KORE read error {e}")

/-- The equation of the predicate `p` a sentence is, by its kind: `owise`, `pair` (its pattern
applies `pair`) or `standard`. -/
def kindOf (p : String) (s : Kore.Sentence) : Option String :=
  match s with
  | .axiom a => (rawEqn? a).bind fun e =>
    if e.fn != p then none
    else some (if e.competitors.isSome then "owise" else if ((eqnShape e).splitOn "Lblpair").length > 1 then "pair"
      else "standard")
  | _ => none

/-- The equation of `LblisKResult` a sentence is (`kindOf`). -/
def kind? (s : Kore.Sentence) : Option String := kindOf "LblisKResult" s

/-- The text with the standard equation of `isKResult` moved before the pair equation. -/
def standardFirst (k : Kore.Definition) : Kore.Definition :=
  let move := fun (ss : List Kore.Sentence) =>
    let stds := ss.filter (kind? · == some "standard")
    ss.flatMap fun s => match kind? s with
      | some "pair" => stds ++ [s]
      | some "standard" => []
      | _ => [s]
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := move m.sentences }]).getD [] }

/-- The value of `p(pair(1, 2))` in the definition `d` (`Exec.evalT`), with `p`'s argument written
`kseq(inj{Exp,KItem}(pair(inj{Int,Exp}(1), inj{Int,Exp}(2))), dotk)`. -/
def pairValue (d : Definition) (p : String) : String :=
  let c := d.sem
  match c.symNames.idxOf? p, c.symNames.idxOf? "Lblpair", c.sortNames.idxOf? "Exp" with
  | some ip, some ipair, some iexp =>
    let exp := nRegSorts + iexp
    let int := fun (i : Int) => Term.inj Srt.int exp (.dv Srt.int (.int i))
    let t := Term.app (nRegSyms + ip)
      [.app kseq [.inj exp Srt.kitem (.app (nRegSyms + ipair) [int 1, int 2]), .app dotk []]]
    match Exec.evalT c 1000 [] t with
    | some (some (.dv _ (.bool b))) => toString b
    | _ => "no value"
  | _, _, _ => "no Exp, pair or predicate"

/-- The order of the equations of the predicate `p` in the text, the reader's verdict (where it
reads the text, the predicate's reading: `sortPreds`' function, or the function of `c.fns` its
equations define, with its clauses' priorities, the functions whose agreement and whose totality
are owed, and `coreOK`), and each refusal (its reason and which equation). -/
def verdictOf (p : String) (n : String) (edit : Kore.Definition → Kore.Definition := id)
    (raw : String → String := id) : IO Unit := do
  let k := edit (← load n raw)
  let some m := k.modules.getLast? | throw (IO.userError "no module")
  let off := preludeLength k
  IO.println s!"{n}: equations of {p} in text order: {m.sentences.filterMap (kindOf p)}"
  match Parse.parse k with
  | .ok d =>
    IO.println s!"  read; read and not accounted for: {(unconsumed k d).length}"
    let c := d.sem
    match c.fns.find? (c.symName ·.label == p) with
    | some f =>
      IO.println s!"  {p}: a function of c.fns, clauses of priorities {f.clauses.map (·.prio)}; coreOK {c.coreOK}"
      IO.println s!"  agreement owed: {c.agreeObligations.map c.symName}; totality owed: {c.totalObligations.map c.symName}"
      if c.symNames.contains "Lblpair" && c.sortNames.contains "Exp" then
        IO.println s!"  {p}(pair(1, 2)) = {pairValue d p}"
    | none => IO.println s!"  {p}: sortPreds' function {(c.sortPreds.any (c.symName ·.label == p))}; coreOK {c.coreOK}"
  | .error r => IO.println s!"  refused {r.reason.name} at the {((r.index.bind fun i => m.sentences[i - off]?).bind (kindOf p)).getD "?"} equation"
  for r in refusals k do
    IO.println s!"  refusal: {r.reason.name}, the {((r.index.bind fun i => m.sentences[i - off]?).bind (kindOf p)).getD "?"} equation: {r.detail}"

/-- `verdictOf` for `isKResult`. -/
def verdict (n : String) (edit : Kore.Definition → Kore.Definition := id) : IO Unit :=
  verdictOf "LblisKResult" n edit

/-- rdr-pred-rule's text with its rule `isFoo(pair(_, _)) => true` (the equation of unique id
`36dd…`) giving false: the value `\dv{SortBool{}}("true")` between the id's two occurrences (the
comment line before the axiom and its attribute) written `false`. -/
def instFalse (raw : String) : String :=
  let uid := "36dd24750a037f8e3a9e9fd3b8b686053564d2a6952c7d73c78bca1a2e43714e"
  match raw.splitOn uid with
  | [a, b, rest] => uid.intercalate [a, b.replace "\\dv{SortBool{}}(\"true\")" "\\dv{SortBool{}}(\"false\")", rest]
  | _ => raw

/--
info: c3-strict-hybrid: equations of LblisKResult in text order: [owise, pair, standard]
  read; read and not accounted for: 0
  LblisKResult: a function of c.fns, clauses of priorities [50, 50, 200]; coreOK true
  agreement owed: []; totality owed: [LblisKResult]
  LblisKResult(pair(1, 2)) = true
c3-strict-hybrid: equations of LblisKResult in text order: [owise, standard, pair]
  read; read and not accounted for: 0
  LblisKResult: a function of c.fns, clauses of priorities [50, 50, 200]; coreOK true
  agreement owed: []; totality owed: [LblisKResult]
  LblisKResult(pair(1, 2)) = true
e2-frontend-effect: equations of LblisKResult in text order: [owise, pair, standard]
  read; read and not accounted for: 0
  LblisKResult: a function of c.fns, clauses of priorities [50, 50, 200]; coreOK true
  agreement owed: [Lblinit0, LblisKResult]; totality owed: [LblisKResult]
  LblisKResult(pair(1, 2)) = true
c3-strict-base: equations of LblisKResult in text order: [owise, standard]
  read; read and not accounted for: 0
  LblisKResult: sortPreds' function true; coreOK true
rdr-pred-rule: equations of LblisFoo in text order: [owise, standard, pair]
  read; read and not accounted for: 0
  LblisFoo: sortPreds' function true; coreOK true
rdr-pred-rule: equations of LblisFoo in text order: [owise, standard, pair]
  read; read and not accounted for: 0
  LblisFoo: a function of c.fns, clauses of priorities [50, 50, 200]; coreOK true
  agreement owed: [LblisFoo]; totality owed: []
-/
#guard_msgs in
#eval show IO Unit from do
  verdict "c3-strict-hybrid"
  verdict "c3-strict-hybrid" standardFirst
  verdict "e2-frontend-effect"
  verdict "c3-strict-base"
  verdictOf "LblisFoo" "rdr-pred-rule"
  verdictOf "LblisFoo" "rdr-pred-rule" (raw := instFalse)

/-- The account of the equations of `isKResult` of the text `n` (edited by `edit`) by the
definition read from `c3-strict-base`: `consumed`, and `consumedWith false`. -/
def account (n : String) (edit : Kore.Definition → Kore.Definition := id) : IO Unit := do
  let d ← match Parse.parse (← load "c3-strict-base") with
    | .ok d => pure d
    | .error r => throw (IO.userError s!"c3-strict-base: refused: {r.toText}")
  let k := edit (← load n)
  let some m := k.modules.getLast? | throw (IO.userError "no module")
  let S := scan m.sentences
  let E ← match envOf m S with
    | .ok E => pure E
    | .error f => throw (IO.userError s!"envOf: {f.reason.name} {f.detail}")
  for s in m.sentences do
    if let some kd := kind? s then
      IO.println s!"{n}, {kd}: accounted {consumed S E d s}, without the arm {consumedWith false S E d s}"

/--
info: c3-strict-hybrid, owise: accounted false, without the arm false
c3-strict-hybrid, pair: accounted false, without the arm false
c3-strict-hybrid, standard: accounted true, without the arm false
c3-strict-hybrid, owise: accounted false, without the arm false
c3-strict-hybrid, standard: accounted true, without the arm false
c3-strict-hybrid, pair: accounted false, without the arm false
c3-strict-base, owise: accounted true, without the arm false
c3-strict-base, standard: accounted true, without the arm false
-/
#guard_msgs in
#eval show IO Unit from do
  account "c3-strict-hybrid"
  account "c3-strict-hybrid" standardFirst
  account "c3-strict-base"

end PredContent
