/-
  The helpers of the function-overload conjunct (FaithOK.lean, Core.lean), kernel-checked
  (`decide +kernel`) on hand-built terms, conditions and semantics. Run from the package root: `lake env lean -j1 test/FnOvlHelpers.lean`.

  - `Semantics.fnOvlSyms`: the overloading symbols one of whose own overloads is a function. Of the
    chain `plusBig over [plusExp]`, `plusExp over [plusInt]`, `plusInt` a function, only `plusExp`
    is one; listing `plusInt` among `plusBig`'s overloads makes `plusBig` one too. A constructor
    overload does not.
  - `Semantics.fnOvl`: a generator that is a function-overloaded overloading symbol.
  - `symOccs`: the applied symbols of a term, through `as`, injections and collection pattern
    symbols; `condPats`: the `exMatch` patterns of a condition, through `not`, both sides of
    `and`, `or`, `implies`, `ex`, `all` and an `exMatch` body, never the scrutinee or the sides of
    `ceil`, `equals`, `mem`.
  - `Semantics.ovlPatsOK`: false for `plusExp` in each of a rule's left side, `pre`, `post` and a
    clause's patterns, `pre`, `post`; true for it in a right side, a `requires`, an `ensures`, an
    `exMatch` scrutinee or a `mem`; true for `plusBig` in a left side while `plusBig` does not list
    `plusInt` (what `overloadsOK`'s closure conjunct is for).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace FnOvlHelpers

def expS : Srt := nRegSorts
def bigS : Srt := nRegSorts + 1

/-- `plusInt : Int Int → Int`, a function. -/
def plusInt : Sym := nRegSyms + 10
/-- `plusExp : Exp Exp → Exp`, overloading `plusInt`. -/
def plusExp : Sym := nRegSyms + 11
/-- `plusBig : Big Big → Big`, overloading `plusExp`. -/
def plusBig : Sym := nRegSyms + 12
/-- `lit : Int → Exp`, a constructor. -/
def lit : Sym := nRegSyms + 13
/-- `litB : Int → Big`, overloading the constructor `lit`. -/
def litB : Sym := nRegSyms + 14

def expSig : CtorSig := ⟨plusExp, [expS, expS], expS⟩
def bigSig : CtorSig := ⟨plusBig, [bigS, bigS], bigS⟩
def litBSig : CtorSig := ⟨litB, [Srt.int], bigS⟩

def plusIntFn (cls : List Clause := []) : Fn := ⟨plusInt, [Srt.int, Srt.int], Srt.int, cls, false⟩

/-- A semantics holding the chain, `plusBig` over `bigOver`, and the given rules and clauses of
`plusInt`. -/
def sem (bigOver : List Sym) (rules : List Rule := []) (cls : List Clause := []) : Semantics where
  lib := {}
  sortNames := ["Exp", "Big"]
  symNames := []
  userSorts := [expS, bigS]
  ctors := [⟨lit, [Srt.int], expS⟩]
  fns := [plusIntFn cls]
  userSubsorts := [(Srt.int, expS), (expS, bigS)]
  pgmSort := Srt.k
  rules := rules
  ovls := [⟨expSig, [plusInt]⟩, ⟨bigSig, bigOver⟩, ⟨litBSig, [lit]⟩]

/-! ## `fnOvlSyms`, `fnOvl` -/

theorem fnOvlSyms_chain : (sem [plusExp]).fnOvlSyms = [plusExp] ∧
    (sem [plusExp, plusInt]).fnOvlSyms = [plusExp, plusBig] := by
  decide +kernel

theorem fnOvl_gens : (sem [plusExp]).fnOvl (.ctor expSig) = true ∧
    (sem [plusExp]).fnOvl (.ctor bigSig) = false ∧
    (sem [plusExp, plusInt]).fnOvl (.ctor bigSig) = true ∧
    (sem [plusExp]).fnOvl (.ctor litBSig) = false ∧
    (sem [plusExp]).fnOvl (.ctor ⟨lit, [Srt.int], expS⟩) = false ∧
    (sem [plusExp]).fnOvl (.inj Srt.int) = false := by
  decide +kernel

/-! ## `symOccs` -/

def x0 : Term := .var 0
def x1 : Term := .var 1
/-- `plusExp(X0, X1)`. -/
def pe : Term := .app plusExp [x0, x1]

theorem symOccs_descends :
    symOccs pe = [plusExp] ∧
    symOccs (.app lit [.as (.inj expS bigS pe) 2]) = [lit, plusExp] ∧
    symOccs (.app mapConcat [.app mapElem [x0, .inj expS Srt.kitem pe], .app mapUnit []]) =
      [mapConcat, mapElem, plusExp, mapUnit] ∧
    symOccs (.app listConcat [.app listElem [.inj expS Srt.kitem pe], .app listUnit []]) =
      [listConcat, listElem, plusExp, listUnit] ∧
    symOccs (.app setElem [.inj expS Srt.kitem pe]) = [setElem, plusExp] ∧
    symOccs (.dv Srt.int (.int 1)) = [] ∧ symOccs x0 = [] := by
  decide +kernel

/-! ## `condPats` -/

/-- `\exists. \in(X1, plusExp(X0, X1)) ∧ body`: `plusExp(X0, X1)` its pattern, `X1` its scrutinee. -/
def em (body : Cond := .top) : Cond := .exMatch [expS] expS pe x1 body
/-- An `exMatch` with the application as its scrutinee and a variable as its pattern. -/
def emScrut : Cond := .exMatch [expS] expS x0 pe .top

def hasPe (p : Cond) : Bool := (condPats p).any fun t => (symOccs t).contains plusExp

theorem condPats_descends :
    hasPe (em) = true ∧ hasPe (.not (em)) = true ∧
    hasPe (.and (em) .top) = true ∧ hasPe (.and .top (em)) = true ∧
    hasPe (.or (em) .top) = true ∧ hasPe (.or .top (em)) = true ∧
    hasPe (.implies (em) .top) = true ∧ hasPe (.implies .top (em)) = true ∧
    hasPe (.ex expS (em)) = true ∧ hasPe (.all expS (em)) = true ∧
    hasPe (.exMatch [expS] expS x0 x1 (em)) = true := by
  decide +kernel

theorem condPats_not_terms :
    hasPe emScrut = false ∧ (condPats emScrut).map symOccs = [[]] ∧ (condPats (em)).map symOccs = [[plusExp]] ∧
    hasPe (.ceil expS pe) = false ∧ hasPe (.equals expS pe x0) = false ∧
    hasPe (.mem expS x0 pe) = false ∧ hasPe (.not (.mem expS pe x0)) = false ∧
    (condPats (.and (.ceil expS pe) .bot)).isEmpty = true := by
  decide +kernel

/-! ## `ovlPatsOK` -/

def rule (lhs : Term) (pre post : Cond := .top) (rhs : Term := x0) (req ens : Option Term := none) : Rule :=
  { vars := [expS, expS], lhs := lhs, req := req, rhs := rhs, ens := ens, prio := 50, pre := pre, post := post }

def clause (pats : List Term) (pre post : Cond := .top) (rhs : Term := .var 0) (req : Option Term := none) : Clause :=
  { vars := [Srt.int, Srt.int], pats := pats, req := req, rhs := rhs, ens := none, pre := pre, post := post }

/-- Refused in each place a pattern is matched. -/
theorem ovlPatsOK_refuses :
    (sem [plusExp] [rule pe]).ovlPatsOK = false ∧
    (sem [plusExp] [rule (.app lit [.as (.inj expS bigS pe) 2])]).ovlPatsOK = false ∧
    (sem [plusExp] [rule x0 (pre := .and .top (em))]).ovlPatsOK = false ∧
    (sem [plusExp] [rule x0 (post := .not (em))]).ovlPatsOK = false ∧
    (sem [plusExp] [] [clause [pe, x1]]).ovlPatsOK = false ∧
    (sem [plusExp] [] [clause [x0, x1] (pre := .ex expS (em))]).ovlPatsOK = false ∧
    (sem [plusExp] [] [clause [x0, x1] (post := .or .top (em))]).ovlPatsOK = false := by
  decide +kernel

/-- Admitted where the application is evaluated, not matched, and for a symbol that is not
function-overloaded. -/
theorem ovlPatsOK_admits :
    (sem [plusExp]).ovlPatsOK = true ∧
    (sem [plusExp] [rule x0 (rhs := pe) (req := some pe) (ens := some pe)]).ovlPatsOK = true ∧
    (sem [plusExp] [rule x0 (pre := emScrut) (post := .mem expS x0 pe)]).ovlPatsOK = true ∧
    (sem [plusExp] [] [clause [x0, x1] (rhs := pe) (req := some pe) (pre := .ceil expS pe)]).ovlPatsOK = true ∧
    (sem [plusExp] [rule (.app litB [x0])]).ovlPatsOK = true ∧
    (sem [plusExp] [rule (.app plusBig [x0, x1])]).ovlPatsOK = true ∧
    (sem [plusExp, plusInt] [rule (.app plusBig [x0, x1])]).ovlPatsOK = false := by
  decide +kernel

/-- info: 'FnOvlHelpers.fnOvlSyms_chain' does not depend on any axioms -/
#guard_msgs in #print axioms fnOvlSyms_chain
/-- info: 'FnOvlHelpers.fnOvl_gens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnOvl_gens
/-- info: 'FnOvlHelpers.symOccs_descends' does not depend on any axioms -/
#guard_msgs in #print axioms symOccs_descends
/-- info: 'FnOvlHelpers.condPats_descends' does not depend on any axioms -/
#guard_msgs in #print axioms condPats_descends
/-- info: 'FnOvlHelpers.condPats_not_terms' does not depend on any axioms -/
#guard_msgs in #print axioms condPats_not_terms
/-- info: 'FnOvlHelpers.ovlPatsOK_refuses' does not depend on any axioms -/
#guard_msgs in #print axioms ovlPatsOK_refuses
/-- info: 'FnOvlHelpers.ovlPatsOK_admits' does not depend on any axioms -/
#guard_msgs in #print axioms ovlPatsOK_admits

end FnOvlHelpers
