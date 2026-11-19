/-
  A semantics whose sort predicate isKResult is a function of `c.fns` under the predicate's number,
  with three clauses: isKResult(pair(K0, K1)) = true requires isKResult(K0) andBool isKResult(K1);
  isKResult(inj{KResult,KItem}(V)) = true; false otherwise (priority 200). `sortPreds` builds no
  function of that number, `coreOK` holds, and evaluation applies the function's clauses.
  Its self calls decrease in weight (`decreasingOKL`, so `decObligationsL` names nothing): the call
  argument `kseq(inj(K0), dotk)` is lighter than the pattern `kseq(inj(pair(K0, K1)), dotk)`, an
  injection against an injection over a constructor. `totalOK`'s older decider `decreasingOK`
  does not see it (`totalObligations`), and no list of `FnObligations` reads that one.
  Sorts: KCell, KCellOpt, Exp, KResult; Int < KResult < Exp; pair : Exp Exp -> Exp.
  Run from the package root: `lake env lean -j1 test/PredHybrid.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.PredHybrid

def KCellS : Srt := nRegSorts
def KCellOptS : Srt := nRegSorts + 1
def Exp : Srt := nRegSorts + 2
def KRes : Srt := nRegSorts + 3
def isKR : Sym := nRegSyms + 3
def kL : Sym := nRegSyms + 4
def noK : Sym := nRegSyms + 5
def pairS : Sym := nRegSyms + 6

def cellSorts : List Srt := [Srt.top, Srt.topFrag, KCellS, KCellOptS, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [KCellS, Srt.counter], Srt.top⟩, ⟨topFragLabel, [KCellOptS, Srt.counterOpt], Srt.topFrag⟩,
   ⟨kL, [Srt.k], KCellS⟩, ⟨noK, [], KCellOptS⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]

def item (t : Term) : Term := .app kseq [.inj Exp Srt.kitem t, .app dotk []]
def tt : Term := .dv Srt.bool (.bool true)
def ff : Term := .dv Srt.bool (.bool false)

def clPair : Clause :=
  { vars := [Exp, Exp], pats := [item (.app pairS [.var 0, .var 1])]
    req := some (.app boolAnd [.app isKR [item (.var 0)], .app isKR [item (.var 1)]]), rhs := tt, ens := none }
def clStd : Clause :=
  { vars := [KRes], pats := [.app kseq [.inj KRes Srt.kitem (.var 0), .app dotk []]], req := none, rhs := tt, ens := none }
def clOw : Clause := { vars := [Srt.k], pats := [.var 0], req := none, rhs := ff, ens := none, prio := 200 }

def isKRFn : Fn := { label := isKR, args := [Srt.k], result := Srt.bool, clauses := [clPair, clStd, clOw], total := true }

def c : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
    sortNames := ["KCell", "KCellOpt", "Exp", "KResult"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisExp", "LblisKResult", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblpair"]
    userSorts := cellSorts ++ [Exp, KRes]
    ctors := cellCtors ++ [⟨pairS, [Exp, Exp], Exp⟩]
    fns := [isKRFn]
    userSubsorts := [(KCellS, KCellOptS), (Srt.counter, Srt.counterOpt), (KRes, Exp), (Srt.int, KRes), (Srt.int, Exp)]
    pgmSort := Srt.k
    rules := [] }

def int (i : Int) : Term := .inj Srt.int Exp (.dv Srt.int (.int i))
def p12 : Term := .app pairS [int 1, int 2]


/-- `sortPreds` builds no function under the predicate's number. -/
theorem no_pred : (c.sortPreds.map (·.label)).contains isKR = false := by decide +kernel
theorem core : c.coreOK = true := by decide +kernel
/-- isKResult(pair(1, 2)) = true. -/
theorem pair_result : Exec.evalT c 100 [] (.app isKR [item p12]) = some (some (.dv Srt.bool (.bool true))) := by
  decide +kernel
/-- isKResult(pair(pair(1, 2), 1)) = true. -/
theorem pair_pair : Exec.evalT c 100 [] (.app isKR [item (.app pairS [p12, int 1])]) =
    some (some (.dv Srt.bool (.bool true))) := by decide +kernel
/-- `totalOK`'s `decreasingOK` does not confirm the predicate (its self calls are at no variable of
the pattern), so `totalObligations` names it; no list of `FnObligations` reads `decreasingOK`. -/
theorem owed : c.totalObligations = [isKR] := by decide +kernel
/-- The self calls `isKResult(kseq(inj(K0), dotk))` and at K1 decrease in weight against the
pattern `kseq(inj(pair(K0, K1)), dotk)`: no function's termination is named by `decObligationsL`. -/
theorem hybrid_term : c.decObligationsL = [] ∧ c.decreasingOKL isKRFn (some 0) = true := by decide +kernel
/-- Outside the rule (not unsound): under the pattern's injection is a nested injection, which can
denote an injected value, so `argLe` does not accept the injected variable although the variable
lies on a path of the inner pattern. -/
theorem inj_nested_outside :
    c.argLe (.inj KRes Exp (.var 0)) (.inj KRes Exp (.inj Srt.int KRes (.var 0))) = false := by
  decide +kernel

/-- info: 'KCore.Faithful.PredHybrid.core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms core

/-- info: 'KCore.Faithful.PredHybrid.pair_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pair_result

/-- info: 'KCore.Faithful.PredHybrid.hybrid_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms hybrid_term

end KCore.Faithful.PredHybrid
