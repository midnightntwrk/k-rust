/-
  The reader refuses an equation or a rewrite axiom whose right side has an `\and{s}` or `\or{s}`
  with an operand of another sort (`Parse.rhsSorted`, `RefusalReason.rhsOperandSort`), on
  hand-written sentences: no K text kompiles to one, kompile's sort inference giving each
  connective its operands' sort. In a
  valid KORE pattern the sort of each argument of a connective is the connective's sort parameter
  (kore-syntax.md:330), so such a sentence is no valid KORE axiom.

  - `illAnd`, `\and{SortInt}(f(X), \equals{SortBool,SortFoo}(X >Int 0, true))`: the lifted
    conjunct's result sort is Foo, not Int. Refused by `clauseBody` (the landed reader) and, as an
    alternative of `\or{SortInt}`, by `frRead`.
  - `okAnd`, the same with `\equals{SortBool,SortInt}`: `clauseBody` reads the clause
    `f(X) = f(X) ensures X >Int 0`; `frRead` reads the `\or` (test/RhsReader.lean `eqA`).
  - `illOr`, `\or{SortInt}(\and{SortFoo}(f(X), …), g(X))`: an operand `\and` of sort Foo.
  - `illNested`, `f(\and{SortInt}(X, \or{SortFoo}(…)))`: under an application.
  - The same right sides on a rewrite axiom (`rule`): `ruleBodyRead` refuses `illAnd` and
    `illNested` and reads `okAnd`.
  - Under `\exists` (`exIll`, `exOk`): `exRead` and `ceRead` check the body under the binders.
  - An `\exists` as an operand (`exOpIll`, `exBodyIll`, `orIll`): of another sort than the
    connective's, or with a body of another sort than its own, refused by `clauseBody`,
    `ruleBodyRead` and `frRead`, where the readers drop it unread.
  - A `\top` or `\bottom` as an operand (`topIll`, `botIll`, `orTopIll`): of another sort than the
    connective's, refused by `clauseBody`, `ruleBodyRead` and `frRead`.
  - A binder heading the right side (`ruleEx`, `ruleEx2`, `ruleExX`, `exEqnT`) of another sort than
    the rewrite axiom's or the function's result: refused by `ruleBodyRead`, `exRead` and `ceRead`,
    the binder named.
  - The other connectives as operands (`notIll`, `notBodyIll`, `impIll`, `forallIll`, `ceilSwap`,
    `ceilOpIll`, `floorIll`, `inOpIll`, `orNotIll`): `\not{s}`, `\implies{s}`, `\forall{s}` of
    another sort than their connective's, or with an operand of another sort than s; `\ceil{S1,s}`,
    `\floor{S1,s}`, `\in{S1,s}` of another result sort s, or with an operand of another sort than
    S1. Refused by `clauseBody`, `ruleBodyRead` and `frRead`; their twins are read.
  - `\iff` and the operands of `\equals` (`iffIll`, `iffOpIll`, `eqOpIll`, `eqTrueIll`, `orEqIll`):
    `\iff{s}` of another sort than its connective's or with an operand of another sort than s;
    `\equals{S1,s}` with an operand of another sort than S1, among them the B of a lifted conjunct
    `\equals{SortBool{},s}(B, \dv{SortBool{}}("true"))`. Refused by `clauseBody`, `ruleBodyRead`
    and `frRead`; their twins are read.
  - The conjunction of the right side with its `ensures` (`ensRule`, `ensEqn`) and of the left
    side or the arguments with the `requires` (`reqRule`, `reqEqn`, `reqOwise`), of another sort
    than the axiom gives it or with an operand of another sort: faults (`bodyConjFault?`,
    `reqConjFault?`), refused `rhsOperandSort` by `classifyAxiom`; their twins have no fault.
  Kernel-checked (`decide +kernel`): the reasons, `rhsSorted` on each side, and that a read
  clause's, `frRead`'s, `exRead`'s, `ceRead`'s or `ruleBodyAnd`'s right side is `rhsSorted`
  (`clauseBody_rhsSorted`, `frRead_rhsSorted`, `exRead_rhsSorted`, `ceRead_rhsSorted`,
  `ruleBodyAnd_rhsSorted`). Run from the package root: `lake env lean -j1 test/RhsSortCheck.lean`.
-/
import KcoreSpec.ReadFns

set_option autoImplicit false

open KCore KCore.Parse

namespace RhsSortCheck

open KoreAML (ev ap srt)

/-- f, g, h are the symbols `nRegSyms + 4` to `nRegSyms + 6`, all of result sort Int; h has its
`functional` sentence (test/RhsReader.lean's `N0` without k). -/
def N0 : Names :=
  { sorts := ["KCell", "KCellOpt"]
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg", "Lblh"]
    keyFns := [(nRegSyms + 4, "Int"), (nRegSyms + 5, "Int"), (nRegSyms + 6, "Int")]
    fnlSyms := [("Lblh", false)] }

def X : Kore.Pattern := ev "VarX" (srt "Int")
def fX : Kore.Pattern := ap "Lblf" [X]
def gX : Kore.Pattern := ap "Lblg" [X]
def gt0 : Kore.Pattern := ap "Lbl'Unds-GT-'Int'Unds'" [X, .dv (srt "Int") "0"]
/-- `\equals{SortBool{},S}(b, \dv{SortBool{}}("true"))`. -/
def isTrueAt (S : Kore.KSort) (b : Kore.Pattern) : Kore.Pattern := .equals (srt "Bool") S b (.dv (srt "Bool") "true")

/-- `\and{SortInt{}}(f(X), \equals{SortBool{},SortFoo{}}(X >Int 0, true))`. -/
def illAnd : Kore.Pattern := .and (srt "Int") [fX, isTrueAt (srt "Foo") gt0]
/-- `\and{SortInt{}}(f(X), \equals{SortBool{},SortInt{}}(X >Int 0, true))`. -/
def okAnd : Kore.Pattern := .and (srt "Int") [fX, isTrueAt (srt "Int") gt0]
/-- `\or{SortInt{}}(\and{SortFoo{}}(f(X), \equals{SortBool{},SortFoo{}}(X >Int 0, true)), g(X))`. -/
def illOr : Kore.Pattern := .or (srt "Int") [.and (srt "Foo") [fX, isTrueAt (srt "Foo") gt0], gX]
/-- `f(\and{SortInt{}}(X, \or{SortFoo{}}(g(X), X)))`. -/
def illNested : Kore.Pattern := ap "Lblf" [.and (srt "Int") [X, .or (srt "Foo") [gX, X]]]

def uid : Kore.AppPattern := ⟨⟨⟨"UNIQUE'Unds'ID"⟩⟩, [], [.string "u"]⟩

def eqn (fn : String) (rhs : Kore.Pattern) : RawEqn := ⟨fn, [X], none, none, rhs, [uid], none, false⟩

def reasonOf {α : Type} : Rd α → Option RefusalReason
  | .error f => some f.reason
  | .ok _ => none

def showRd {α : Type} (what : String) (r : Rd α) : IO Unit :=
  match r with
  | .error f => IO.println s!"{what}: refused {repr f.reason} ({f.detail})"
  | .ok _ => IO.println s!"{what}: read"

/--
info: clauseBody illAnd: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \equals of sort SortFoo{})
clauseBody okAnd: read
clauseBody illOr: refused KCore.Parse.RefusalReason.rhsOperandSort (\or{SortInt{}}: an operand \and of sort SortFoo{})
clauseBody illNested: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \or of sort SortFoo{})
frRead illAnd: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \equals of sort SortFoo{})
frRead okAnd: read
-/
#guard_msgs in
#eval show IO Unit from do
  showRd "clauseBody illAnd" (clauseBody N0 "" (eqn "Lblf" illAnd) none)
  showRd "clauseBody okAnd" (clauseBody N0 "" (eqn "Lblf" okAnd) none)
  showRd "clauseBody illOr" (clauseBody N0 "" (eqn "Lblf" illOr) none)
  showRd "clauseBody illNested" (clauseBody N0 "" (eqn "Lblf" illNested) none)
  showRd "frRead illAnd" (frRead N0 (eqn "Lblh" (.or (srt "Int") [illAnd, gX])))
  showRd "frRead okAnd" (frRead N0 (eqn "Lblh" (.or (srt "Int") [okAnd, gX])))

/-- `rhsSorted` on the four sides. -/
theorem rhsSorted_hand :
    rhsSorted illAnd = false ∧ rhsSorted okAnd = true ∧ rhsSorted illOr = false ∧
    rhsSorted illNested = false ∧ rhsSorted (.or (srt "Int") [okAnd, gX]) = true := by
  decide +kernel

/-- The refusals' reason, by the landed reader (`clauseBody`) and by `frRead`. -/
theorem refused_hand :
    reasonOf (clauseBody N0 "" (eqn "Lblf" illAnd) none) = some .rhsOperandSort ∧
    reasonOf (clauseBody N0 "" (eqn "Lblf" illOr) none) = some .rhsOperandSort ∧
    reasonOf (clauseBody N0 "" (eqn "Lblf" illNested) none) = some .rhsOperandSort ∧
    reasonOf (frRead N0 (eqn "Lblh" (.or (srt "Int") [illAnd, gX]))) = some .rhsOperandSort ∧
    reasonOf (frRead N0 (eqn "Lblh" illOr)) = some .rhsOperandSort := by
  decide +kernel

/-- The well-sorted twin is read by both. -/
theorem read_hand :
    reasonOf (clauseBody N0 "" (eqn "Lblf" okAnd) none) = none ∧
    reasonOf (frRead N0 (eqn "Lblh" (.or (srt "Int") [okAnd, gX]))) = none := by
  decide +kernel

example {N : Names} {msrc : String} {e : RawEqn} {x : Clause × ClausePres}
    (h : clauseBody N msrc e none = .ok x) : rhsSorted e.rhs = true := clauseBody_rhsSorted h
example {N : Names} {e : RawEqn} {x : Option (List Clause × List KoreAML.Var)}
    (h : frRead N e = .ok x) : rhsSorted e.rhs = true := frRead_rhsSorted h

/-! ## A rewrite axiom's right side

`\rewrites{SortInt{}}(\and{SortInt{}}(X, \top{SortInt{}}()), \and{SortInt{}}(r, \top{SortInt{}}()))`
with r `illAnd` or `illNested` is refused `rhsOperandSort` by `ruleBodyRead` (through
`ruleBodyAnd`, before `hoist` lifts the conjunct); with r `okAnd` it is read, the conjunct as the
rule's `ensures`. -/

def loc : Kore.AppPattern :=
  ⟨⟨⟨"org'Stop'kframework'Stop'attributes'Stop'Location"⟩⟩, [], [.string "Location(1,1,1,1)"]⟩

def rule (r : Kore.Pattern) : Kore.Axiom :=
  ⟨[], .rewrites (srt "Int") (.and (srt "Int") [X, .top (srt "Int")]) (.and (srt "Int") [r, .top (srt "Int")]),
   [uid, loc]⟩

/--
info: ruleBodyRead illAnd: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \equals of sort SortFoo{})
ruleBodyRead illNested: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \or of sort SortFoo{})
ruleBodyRead okAnd: read
-/
#guard_msgs in
#eval show IO Unit from do
  showRd "ruleBodyRead illAnd" (ruleBodyRead N0 "" (rule illAnd))
  showRd "ruleBodyRead illNested" (ruleBodyRead N0 "" (rule illNested))
  showRd "ruleBodyRead okAnd" (ruleBodyRead N0 "" (rule okAnd))

/-- The rule reader's refusals and its reading of the twin. -/
theorem rule_hand :
    reasonOf (ruleBodyRead N0 "" (rule illAnd)) = some .rhsOperandSort ∧
    reasonOf (ruleBodyRead N0 "" (rule illNested)) = some .rhsOperandSort ∧
    reasonOf (ruleBodyRead N0 "" (rule okAnd)) = none := by
  decide +kernel

example {N : Names} {msrc : String} {a : Kore.Axiom} {l r0 : Kore.Pattern} {xs : List Kore.EVar}
    {r en : Kore.Pattern} {x : Rule × RulePres}
    (h : ruleBodyAnd N msrc a l r0 xs r en = .ok x) : rhsSorted r = true := ruleBodyAnd_rhsSorted h

/-! ## A right side under `\exists`: `exRead` and `ceRead`

f : Bool → Bool with its `functional` sentence (test/RhsReader.lean's `HandEx.N1`).
`exIll`, `f(X) = \exists{SortBool{}}(B, \and{SortBool{}}(B, \equals{SortBool{},SortFoo{}}(B, notBool X)))`:
the predicate's result sort is Foo, not Bool. Refused `rhsOperandSort` by `exRead` and `ceRead`
(the guard reads the body under the binder: `rhsSorted` does not look under `\exists`). Its twin
`exOk` at `\equals{SortBool{},SortBool{}}` (test/RhsReader.lean `HandEx.eqB`) is read by both. -/

def N1 : Names := { sorts := [], syms := ["Lblf"], keyFns := [(nRegSyms, "Bool")], fnlSyms := [("Lblf", false)] }
def bool : Kore.KSort := srt "Bool"
def XB : Kore.Pattern := ev "VarX" bool
def B : Kore.Pattern := ev "VarB" bool
def notB (p : Kore.Pattern) : Kore.Pattern := ap "LblnotBool'Unds'" [p]
def exEqn (S : Kore.KSort) : RawEqn :=
  ⟨"Lblf", [XB], none, none,
   .exist bool (KoreAML.evar "VarB" bool) (.and bool [B, .equals bool S B (notB XB)]), [], none, false⟩
def exIll : RawEqn := exEqn (srt "Foo")
def exOk : RawEqn := exEqn bool

/--
info: exRead exIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortBool{}}: an operand \equals of sort SortFoo{})
exRead exOk: read
ceRead exIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortBool{}}: an operand \equals of sort SortFoo{})
ceRead exOk: read
-/
#guard_msgs in
#eval show IO Unit from do
  showRd "exRead exIll" (exRead N1 exIll)
  showRd "exRead exOk" (exRead N1 exOk)
  showRd "ceRead exIll" (ceRead N1 exIll)
  showRd "ceRead exOk" (ceRead N1 exOk)

/-- The refusals and the twin's readings, by `exRead` and `ceRead`. -/
theorem ex_hand :
    rhsSorted exIll.rhs = true ∧ rhsSorted (peelExists exIll.rhs).2 = false ∧
    reasonOf (exRead N1 exIll) = some .rhsOperandSort ∧ reasonOf (exRead N1 exOk) = none ∧
    reasonOf (ceRead N1 exIll) = some .rhsOperandSort ∧ reasonOf (ceRead N1 exOk) = none := by
  decide +kernel

example {N : Names} {e : RawEqn} {x : Option (List Clause × List KoreAML.Var)}
    (h : exRead N e = .ok x) : rhsSorted (peelExists e.rhs).2 = true := exRead_rhsSorted h
example {N : Names} {e : RawEqn} {x : Clause × List KoreAML.Var}
    (h : ceRead N e = .ok x) : rhsSorted (peelExists e.rhs).2 = true := ceRead_rhsSorted h

/-! ## An `\exists` as an operand

An `\exists{s'}(Y, φ)` states its sort s' at its head and that φ is of sort s' (kore-syntax.md:195,
330), so `rhsOpSort` reads it as it reads an `\and`. Where the conjunction holds `\bottom` (`hoist`
marks it empty) or the alternative is empty (`dropEmptyAlts` leaves it out), the readers drop the
`\exists` without reading it, so the guard is what refuses its sort.
- `exOpIll`, `\and{SortInt{}}(\exists{SortFoo{}}(Y, f(Y)), \bottom{SortInt{}}())`: an operand
  `\exists` of sort Foo. Refused by `clauseBody` and `ruleBodyRead`; its twin `exOpOk` at
  `\exists{SortInt{}}` is read by both (the empty clause and the empty rule).
- `exBodyIll`, `\and{SortInt{}}(\exists{SortInt{}}(Y, \and{SortFoo{}}(f(Y), f(Y))), \bottom{SortInt{}}())`:
  an `\exists` of sort Int whose body is an `\and` of sort Foo.
- `orIll`, `\or{SortInt{}}(\exists{SortFoo{}}(Y, \bottom{SortFoo{}}()), f(X), g(X))` (h's
  equation, h with its `functional` sentence): an empty alternative `\exists` of sort Foo, refused
  by `frRead`; its twin `orOk` at Int is read. -/

def Y : Kore.Pattern := ev "VarY" (srt "Int")
def yv : Kore.EVar := KoreAML.evar "VarY" (srt "Int")
def fY : Kore.Pattern := ap "Lblf" [Y]
def exOpIll : Kore.Pattern := .and (srt "Int") [.exist (srt "Foo") yv fY, .bottom (srt "Int")]
def exOpOk : Kore.Pattern := .and (srt "Int") [.exist (srt "Int") yv fY, .bottom (srt "Int")]
def exBodyIll : Kore.Pattern :=
  .and (srt "Int") [.exist (srt "Int") yv (.and (srt "Foo") [fY, fY]), .bottom (srt "Int")]
def orIll : Kore.Pattern := .or (srt "Int") [.exist (srt "Foo") yv (.bottom (srt "Foo")), fX, gX]
def orOk : Kore.Pattern := .or (srt "Int") [.exist (srt "Int") yv (.bottom (srt "Int")), fX, gX]

/--
info: clauseBody exOpIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \exists of sort SortFoo{})
clauseBody exOpOk: read
clauseBody exBodyIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\exists{SortInt{}}: an operand \and of sort SortFoo{})
ruleBodyRead exOpIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \exists of sort SortFoo{})
ruleBodyRead exOpOk: read
ruleBodyRead exBodyIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\exists{SortInt{}}: an operand \and of sort SortFoo{})
frRead orIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\or{SortInt{}}: an operand \exists of sort SortFoo{})
frRead orOk: read
-/
#guard_msgs in
#eval show IO Unit from do
  showRd "clauseBody exOpIll" (clauseBody N0 "" (eqn "Lblf" exOpIll) none)
  showRd "clauseBody exOpOk" (clauseBody N0 "" (eqn "Lblf" exOpOk) none)
  showRd "clauseBody exBodyIll" (clauseBody N0 "" (eqn "Lblf" exBodyIll) none)
  showRd "ruleBodyRead exOpIll" (ruleBodyRead N0 "" (rule exOpIll))
  showRd "ruleBodyRead exOpOk" (ruleBodyRead N0 "" (rule exOpOk))
  showRd "ruleBodyRead exBodyIll" (ruleBodyRead N0 "" (rule exBodyIll))
  showRd "frRead orIll" (frRead N0 (eqn "Lblh" orIll))
  showRd "frRead orOk" (frRead N0 (eqn "Lblh" orOk))

/-- `rhsSorted` on the `\exists` operands, the refusals and the twins' readings. -/
theorem exOp_hand :
    rhsSorted exOpIll = false ∧ rhsSorted exOpOk = true ∧ rhsSorted exBodyIll = false ∧
    rhsSorted orIll = false ∧ rhsSorted orOk = true ∧
    reasonOf (clauseBody N0 "" (eqn "Lblf" exOpIll) none) = some .rhsOperandSort ∧
    reasonOf (clauseBody N0 "" (eqn "Lblf" exBodyIll) none) = some .rhsOperandSort ∧
    reasonOf (clauseBody N0 "" (eqn "Lblf" exOpOk) none) = none ∧
    reasonOf (ruleBodyRead N0 "" (rule exOpIll)) = some .rhsOperandSort ∧
    reasonOf (ruleBodyRead N0 "" (rule exBodyIll)) = some .rhsOperandSort ∧
    reasonOf (ruleBodyRead N0 "" (rule exOpOk)) = none ∧
    reasonOf (frRead N0 (eqn "Lblh" orIll)) = some .rhsOperandSort ∧
    reasonOf (frRead N0 (eqn "Lblh" orOk)) = none := by
  decide +kernel

/-! ## A `\top` or `\bottom` as an operand

`\top{s'}()` and `\bottom{s'}()` state their sort s' at their head (kore-syntax.md:330), so
`rhsOpSort` checks it as it checks an `\and`'s. Where the conjunction holds `\bottom` (`hoist`
marks it empty) or the alternative is empty (`dropEmptyAlts` leaves it out), the readers drop the
operand without reading it, so the guard is what refuses its sort.
- `topIll`, `\and{SortInt{}}(\bottom{SortInt{}}(), \top{SortBool{}}())`: an operand `\top` of sort
  Bool. Refused by `clauseBody` and `ruleBodyRead`; its twin `topOk` at `\top{SortInt{}}` is read
  by both (the empty clause and the empty rule).
- `botIll`, `\and{SortInt{}}(f(X), \bottom{SortFoo{}}())`: an operand `\bottom` of sort Foo.
- `orTopIll`, `\or{SortInt{}}(topIll, f(X), g(X))` (h's equation): the empty alternative, refused by
  `frRead`; its twin `orTopOk` with `topOk` is read. -/

def topIll : Kore.Pattern := .and (srt "Int") [.bottom (srt "Int"), .top (srt "Bool")]
def topOk : Kore.Pattern := .and (srt "Int") [.bottom (srt "Int"), .top (srt "Int")]
def botIll : Kore.Pattern := .and (srt "Int") [fX, .bottom (srt "Foo")]
def botOk : Kore.Pattern := .and (srt "Int") [fX, .bottom (srt "Int")]
def orTopIll : Kore.Pattern := .or (srt "Int") [topIll, fX, gX]
def orTopOk : Kore.Pattern := .or (srt "Int") [topOk, fX, gX]

/--
info: clauseBody topIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \top of sort SortBool{})
clauseBody topOk: read
clauseBody botIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \bottom of sort SortFoo{})
clauseBody botOk: read
ruleBodyRead topIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \top of sort SortBool{})
ruleBodyRead topOk: read
frRead orTopIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \top of sort SortBool{})
frRead orTopOk: read
-/
#guard_msgs in
#eval show IO Unit from do
  showRd "clauseBody topIll" (clauseBody N0 "" (eqn "Lblf" topIll) none)
  showRd "clauseBody topOk" (clauseBody N0 "" (eqn "Lblf" topOk) none)
  showRd "clauseBody botIll" (clauseBody N0 "" (eqn "Lblf" botIll) none)
  showRd "clauseBody botOk" (clauseBody N0 "" (eqn "Lblf" botOk) none)
  showRd "ruleBodyRead topIll" (ruleBodyRead N0 "" (rule topIll))
  showRd "ruleBodyRead topOk" (ruleBodyRead N0 "" (rule topOk))
  showRd "frRead orTopIll" (frRead N0 (eqn "Lblh" orTopIll))
  showRd "frRead orTopOk" (frRead N0 (eqn "Lblh" orTopOk))

/-- `rhsSorted` on the `\top` and `\bottom` operands, the refusals and the twins' readings. -/
theorem topOp_hand :
    rhsSorted topIll = false ∧ rhsSorted topOk = true ∧ rhsSorted botIll = false ∧
    rhsSorted botOk = true ∧ rhsSorted orTopIll = false ∧ rhsSorted orTopOk = true ∧
    reasonOf (clauseBody N0 "" (eqn "Lblf" topIll) none) = some .rhsOperandSort ∧
    reasonOf (clauseBody N0 "" (eqn "Lblf" topOk) none) = none ∧
    reasonOf (clauseBody N0 "" (eqn "Lblf" botIll) none) = some .rhsOperandSort ∧
    reasonOf (clauseBody N0 "" (eqn "Lblf" botOk) none) = none ∧
    reasonOf (ruleBodyRead N0 "" (rule topIll)) = some .rhsOperandSort ∧
    reasonOf (ruleBodyRead N0 "" (rule topOk)) = none ∧
    reasonOf (frRead N0 (eqn "Lblh" orTopIll)) = some .rhsOperandSort ∧
    reasonOf (frRead N0 (eqn "Lblh" orTopOk)) = none := by
  decide +kernel

/-! ## The binders heading a right side

A binder `\exists{T}(x, φ)` is of the sort T, and so is φ (kore-syntax.md:195, 330): the binders
heading the right side of `\rewrites{s}` are of the sort s, and those heading an equation's right
side of the function's result sort. `peelExists` removes them before the readers look at the body.
- `ruleEx T`, `\rewrites{SortInt{}}(\and(X, \top), \exists{T}(Y:Int, \and{SortInt{}}(f(Y), \top)))`:
  refused by `ruleBodyRead` at T = Foo, the binder named; read at T = Int.
- `ruleEx2 T`, the binder `\exists{T}(Z, …)` under `\exists{SortInt{}}(Y, …)`: the inner one named.
- `ruleExX`, a binder `\exists{SortFoo{}}(X:Int, …)` whose name the left side holds: named as the
  text writes it, not as `rhsApart` renames it.
- `exEqnT T`, `f(X) = \exists{T}(B:Bool, \and{SortBool{}}(B, \equals{SortBool{},SortBool{}}(B,
  notBool X)))` for f : Bool → Bool: refused by `exRead` and `ceRead` at T = Foo; at T = Bool it is
  `exOk`, read by both. -/

def zv : Kore.EVar := KoreAML.evar "VarZ" (srt "Int")
def xv : Kore.EVar := KoreAML.evar "VarX" (srt "Int")
def topI : Kore.Pattern := .top (srt "Int")

def ruleOf (rx : Kore.Pattern) : Kore.Axiom :=
  ⟨[], .rewrites (srt "Int") (.and (srt "Int") [X, topI]) rx, [uid, loc]⟩
def ruleEx (T : Kore.KSort) : Kore.Axiom := ruleOf (.exist T yv (.and (srt "Int") [fY, topI]))
def ruleEx2 (T : Kore.KSort) : Kore.Axiom :=
  ruleOf (.exist (srt "Int") yv (.exist T zv (.and (srt "Int") [ap "Lblg" [fY, ev "VarZ" (srt "Int")], topI])))
def ruleExX : Kore.Axiom := ruleOf (.exist (srt "Foo") xv (.and (srt "Int") [fX, topI]))

def exEqnT (T : Kore.KSort) : RawEqn :=
  ⟨"Lblf", [XB], none, none,
   .exist T (KoreAML.evar "VarB" bool) (.and bool [B, .equals bool bool B (notB XB)]), [], none, false⟩

/--
info: ruleBodyRead ruleEx Foo: refused KCore.Parse.RefusalReason.rhsOperandSort (\rewrites{SortInt{}}: a binder \exists{SortFoo{}}(VarY:SortInt{}, …) heading its right side)
ruleBodyRead ruleEx Int: read
ruleBodyRead ruleEx2 Foo: refused KCore.Parse.RefusalReason.rhsOperandSort (\rewrites{SortInt{}}: a binder \exists{SortFoo{}}(VarZ:SortInt{}, …) heading its right side)
ruleBodyRead ruleEx2 Int: read
ruleBodyRead ruleExX: refused KCore.Parse.RefusalReason.rhsOperandSort (\rewrites{SortInt{}}: a binder \exists{SortFoo{}}(VarX:SortInt{}, …) heading its right side)
exRead exEqnT Foo: refused KCore.Parse.RefusalReason.rhsOperandSort (Lblf: a binder \exists{SortFoo{}}(VarB:SortBool{}, …) heading its right side, not of the function's result sort Bool)
ceRead exEqnT Foo: refused KCore.Parse.RefusalReason.rhsOperandSort (Lblf: a binder \exists{SortFoo{}}(VarB:SortBool{}, …) heading its right side, not of the function's result sort Bool)
-/
#guard_msgs in
#eval show IO Unit from do
  showRd "ruleBodyRead ruleEx Foo" (ruleBodyRead N0 "" (ruleEx (srt "Foo")))
  showRd "ruleBodyRead ruleEx Int" (ruleBodyRead N0 "" (ruleEx (srt "Int")))
  showRd "ruleBodyRead ruleEx2 Foo" (ruleBodyRead N0 "" (ruleEx2 (srt "Foo")))
  showRd "ruleBodyRead ruleEx2 Int" (ruleBodyRead N0 "" (ruleEx2 (srt "Int")))
  showRd "ruleBodyRead ruleExX" (ruleBodyRead N0 "" ruleExX)
  showRd "exRead exEqnT Foo" (exRead N1 (exEqnT (srt "Foo")))
  showRd "ceRead exEqnT Foo" (ceRead N1 (exEqnT (srt "Foo")))

/-- The binders' refusals, and the readings at the right sort. -/
theorem binder_hand :
    reasonOf (ruleBodyRead N0 "" (ruleEx (srt "Foo"))) = some .rhsOperandSort ∧
    reasonOf (ruleBodyRead N0 "" (ruleEx (srt "Int"))) = none ∧
    reasonOf (ruleBodyRead N0 "" (ruleEx2 (srt "Foo"))) = some .rhsOperandSort ∧
    reasonOf (ruleBodyRead N0 "" (ruleEx2 (srt "Int"))) = none ∧
    reasonOf (ruleBodyRead N0 "" ruleExX) = some .rhsOperandSort ∧
    rhsSorted (peelExists (exEqnT (srt "Foo")).rhs).2 = true ∧
    reasonOf (exRead N1 (exEqnT (srt "Foo"))) = some .rhsOperandSort ∧
    reasonOf (ceRead N1 (exEqnT (srt "Foo"))) = some .rhsOperandSort := by
  decide +kernel

/-- At T = Bool the equation is `exOk`, read by `exRead` and `ceRead` (`ex_hand`). -/
example : exEqnT bool = exOk := rfl

/-! ## The other connectives as operands

`\not{s}(φ)`, `\implies{s}(φ, ψ)` and `\forall{s}(x, φ)` are of the sort s and so are their
operands; `\ceil{S1,s}(φ)` and `\floor{S1,s}(φ)` are of the sort s and φ of S1, and so are both
operands of `\in{S1,s}(φ, ψ)` (kore-syntax.md:330). Each operand stands beside `\bottom{SortInt{}}()`
in `\and{SortInt{}}` (`withBot`), so the readers drop it unread and the guard is what refuses it.
- `notIll`, `\not{SortFoo{}}(f(X))`: of sort Foo; `notOk` at Int. `notBodyIll`,
  `\not{SortInt{}}(\and{SortFoo{}}(f(X), f(X)))`: an operand of sort Foo.
- `impIll`, `\implies{SortInt{}}(f(X), \top{SortBool{}}())`; `impOk` with `\top{SortInt{}}()`.
- `forallIll`, `\forall{SortFoo{}}(Y, f(Y))`; `forallOk` at Int.
- `ceilOk`, `\ceil{SortBool{},SortInt{}}(\top{SortBool{}}())`, is read; `ceilSwap`,
  `\ceil{SortInt{},SortBool{}}(\top{SortInt{}}())`, is of sort Bool, and `ceilOpIll`,
  `\ceil{SortBool{},SortInt{}}(\top{SortInt{}}())`, has an operand of sort Int, not Bool: the operand
  sort is the first sort parameter, the result sort the second.
- `floorIll`, `\floor{SortBool{},SortFoo{}}(\top{SortBool{}}())`; `floorOk` at Int.
- `inOk`, `\in{SortBool{},SortInt{}}(B, \top{SortBool{}}())`; `inOpIll` with `\top{SortInt{}}()`.
- `orNotIll`, `\or{SortInt{}}(withBot notIll, f(X), g(X))` (h's equation): refused by `frRead`;
  `orNotOk` with `notOk` is read. -/

def withBot (q : Kore.Pattern) : Kore.Pattern := .and (srt "Int") [q, .bottom (srt "Int")]
def int : Kore.KSort := srt "Int"
def foo : Kore.KSort := srt "Foo"
def notIll : Kore.Pattern := withBot (.not foo fX)
def notOk : Kore.Pattern := withBot (.not int fX)
def notBodyIll : Kore.Pattern := withBot (.not int (.and foo [fX, fX]))
def impIll : Kore.Pattern := withBot (.implies int fX (.top bool))
def impOk : Kore.Pattern := withBot (.implies int fX (.top int))
def forallIll : Kore.Pattern := withBot (.forall foo yv fY)
def forallOk : Kore.Pattern := withBot (.forall int yv fY)
def ceilOk : Kore.Pattern := withBot (.ceil bool int (.top bool))
def ceilSwap : Kore.Pattern := withBot (.ceil int bool (.top int))
def ceilOpIll : Kore.Pattern := withBot (.ceil bool int (.top int))
def floorIll : Kore.Pattern := withBot (.floor bool foo (.top bool))
def floorOk : Kore.Pattern := withBot (.floor bool int (.top bool))
def inOk : Kore.Pattern := withBot (.in bool int B (.top bool))
def inOpIll : Kore.Pattern := withBot (.in bool int B (.top int))
def orNotIll : Kore.Pattern := .or int [notIll, fX, gX]
def orNotOk : Kore.Pattern := .or int [notOk, fX, gX]

/-- The ill-sorted sides, each refused by `clauseBody`. -/
def connIll : List (String × Kore.Pattern) :=
  [("notIll", notIll), ("notBodyIll", notBodyIll), ("impIll", impIll), ("forallIll", forallIll),
   ("ceilSwap", ceilSwap), ("ceilOpIll", ceilOpIll), ("floorIll", floorIll), ("inOpIll", inOpIll)]
/-- Their twins, each read by `clauseBody`. -/
def connOk : List (String × Kore.Pattern) :=
  [("notOk", notOk), ("impOk", impOk), ("forallOk", forallOk), ("ceilOk", ceilOk),
   ("floorOk", floorOk), ("inOk", inOk)]

/--
info: clauseBody notIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \not of sort SortFoo{})
clauseBody notBodyIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\not{SortInt{}}: an operand \and of sort SortFoo{})
clauseBody impIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\implies{SortInt{}}: an operand \top of sort SortBool{})
clauseBody forallIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \forall of sort SortFoo{})
clauseBody ceilSwap: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \ceil of sort SortBool{})
clauseBody ceilOpIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\ceil{SortBool{},SortInt{}}: an operand \top of sort SortInt{})
clauseBody floorIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \floor of sort SortFoo{})
clauseBody inOpIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\in{SortBool{},SortInt{}}: an operand \top of sort SortInt{})
clauseBody notOk: read
clauseBody impOk: read
clauseBody forallOk: read
clauseBody ceilOk: read
clauseBody floorOk: read
clauseBody inOk: read
ruleBodyRead notBodyIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\not{SortInt{}}: an operand \and of sort SortFoo{})
ruleBodyRead ceilOpIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\ceil{SortBool{},SortInt{}}: an operand \top of sort SortInt{})
ruleBodyRead ceilOk: read
frRead orNotIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \not of sort SortFoo{})
frRead orNotOk: read
-/
#guard_msgs in
#eval show IO Unit from do
  for (n, r) in connIll ++ connOk do
    showRd s!"clauseBody {n}" (clauseBody N0 "" (eqn "Lblf" r) none)
  showRd "ruleBodyRead notBodyIll" (ruleBodyRead N0 "" (rule notBodyIll))
  showRd "ruleBodyRead ceilOpIll" (ruleBodyRead N0 "" (rule ceilOpIll))
  showRd "ruleBodyRead ceilOk" (ruleBodyRead N0 "" (rule ceilOk))
  showRd "frRead orNotIll" (frRead N0 (eqn "Lblh" orNotIll))
  showRd "frRead orNotOk" (frRead N0 (eqn "Lblh" orNotOk))

/-- `rhsSorted` on the other connectives' operands, the refusals and the twins' readings. -/
theorem connOp_hand :
    (∀ x ∈ connIll, rhsSorted x.2 = false ∧
      reasonOf (clauseBody N0 "" (eqn "Lblf" x.2) none) = some .rhsOperandSort) ∧
    (∀ x ∈ connOk, rhsSorted x.2 = true ∧ reasonOf (clauseBody N0 "" (eqn "Lblf" x.2) none) = none) ∧
    reasonOf (ruleBodyRead N0 "" (rule notBodyIll)) = some .rhsOperandSort ∧
    reasonOf (ruleBodyRead N0 "" (rule ceilOpIll)) = some .rhsOperandSort ∧
    reasonOf (ruleBodyRead N0 "" (rule ceilOk)) = none ∧
    reasonOf (frRead N0 (eqn "Lblh" orNotIll)) = some .rhsOperandSort ∧
    reasonOf (frRead N0 (eqn "Lblh" orNotOk)) = none := by
  decide +kernel

/-! ## `\iff` and the operands of `\equals`

`\iff{s}(φ, ψ)` is of the sort s and so are φ and ψ; `\equals{S1,s}(φ, ψ)` is of the sort s and φ
and ψ of S1 (kore-syntax.md:330). Each stands beside `\bottom{SortInt{}}()` (`withBot`).
- `iffIll`, `\iff{SortFoo{}}(f(X), f(X))`: of sort Foo. `iffOpIll`,
  `\iff{SortInt{}}(f(X), \top{SortBool{}}())`: an operand of sort Bool; `iffOk` with
  `\top{SortInt{}}()`.
- `eqOpIll`, `\equals{SortBool{},SortInt{}}(B, \top{SortInt{}}())`: an operand of sort Int, not Bool;
  `eqOk` with `\top{SortBool{}}()`.
- `eqTrueIll`, `\equals{SortBool{},SortInt{}}(\top{SortInt{}}(), \dv{SortBool{}}("true"))`, the
  shape `hoist` lifts out of a conjunction: its B is of sort Int, not Bool; `eqTrueOk` with
  `\top{SortBool{}}()`.
- `orEqIll`, `\or{SortInt{}}(eqTrueIll, f(X), g(X))` (h's equation): refused by `frRead`; `orEqOk`
  with `eqTrueOk` is read. -/

def iffIll : Kore.Pattern := withBot (.iff foo fX fX)
def iffOpIll : Kore.Pattern := withBot (.iff int fX (.top bool))
def iffOk : Kore.Pattern := withBot (.iff int fX (.top int))
def eqOpIll : Kore.Pattern := withBot (.equals bool int B (.top int))
def eqOk : Kore.Pattern := withBot (.equals bool int B (.top bool))
def eqTrueIll : Kore.Pattern := withBot (isTrueAt int (.top int))
def eqTrueOk : Kore.Pattern := withBot (isTrueAt int (.top bool))
def orEqIll : Kore.Pattern := .or int [eqTrueIll, fX, gX]
def orEqOk : Kore.Pattern := .or int [eqTrueOk, fX, gX]

/-- The ill-sorted sides, each refused by `clauseBody`. -/
def iffEqIll : List (String × Kore.Pattern) :=
  [("iffIll", iffIll), ("iffOpIll", iffOpIll), ("eqOpIll", eqOpIll), ("eqTrueIll", eqTrueIll)]
/-- Their twins, each read by `clauseBody`. -/
def iffEqOk : List (String × Kore.Pattern) :=
  [("iffOk", iffOk), ("eqOk", eqOk), ("eqTrueOk", eqTrueOk)]

/--
info: clauseBody iffIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\and{SortInt{}}: an operand \iff of sort SortFoo{})
clauseBody iffOpIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\iff{SortInt{}}: an operand \top of sort SortBool{})
clauseBody eqOpIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\equals{SortBool{},SortInt{}}: an operand \top of sort SortInt{})
clauseBody eqTrueIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\equals{SortBool{},SortInt{}}: an operand \top of sort SortInt{})
clauseBody iffOk: read
clauseBody eqOk: read
clauseBody eqTrueOk: read
ruleBodyRead eqTrueIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\equals{SortBool{},SortInt{}}: an operand \top of sort SortInt{})
ruleBodyRead eqOk: read
frRead orEqIll: refused KCore.Parse.RefusalReason.rhsOperandSort (\equals{SortBool{},SortInt{}}: an operand \top of sort SortInt{})
frRead orEqOk: read
-/
#guard_msgs in
#eval show IO Unit from do
  for (n, r) in iffEqIll ++ iffEqOk do
    showRd s!"clauseBody {n}" (clauseBody N0 "" (eqn "Lblf" r) none)
  showRd "ruleBodyRead eqTrueIll" (ruleBodyRead N0 "" (rule eqTrueIll))
  showRd "ruleBodyRead eqOk" (ruleBodyRead N0 "" (rule eqOk))
  showRd "frRead orEqIll" (frRead N0 (eqn "Lblh" orEqIll))
  showRd "frRead orEqOk" (frRead N0 (eqn "Lblh" orEqOk))

/-- `rhsSorted` on `\iff` and on the operands of `\equals`, the refusals and the twins' readings. -/
theorem iffEq_hand :
    (∀ x ∈ iffEqIll, rhsSorted x.2 = false ∧
      reasonOf (clauseBody N0 "" (eqn "Lblf" x.2) none) = some .rhsOperandSort) ∧
    (∀ x ∈ iffEqOk, rhsSorted x.2 = true ∧ reasonOf (clauseBody N0 "" (eqn "Lblf" x.2) none) = none) ∧
    reasonOf (ruleBodyRead N0 "" (rule eqTrueIll)) = some .rhsOperandSort ∧
    reasonOf (ruleBodyRead N0 "" (rule eqOk)) = none ∧
    reasonOf (frRead N0 (eqn "Lblh" orEqIll)) = some .rhsOperandSort ∧
    reasonOf (frRead N0 (eqn "Lblh" orEqOk)) = none := by
  decide +kernel

/-! ## The conjunction of the right side with its `ensures`: `bodyConjFault?`

kompile writes an equation's right side r with its `ensures` ens as `\and{s}(r, ens)` at r's sort s,
the operand of `\equals{s,R}(f(…), _)`, and a rewrite axiom's under its binders as the body of
`\rewrites{s}(…, _)`; each operand of `\and{s}` is of the sort s (kore-syntax.md:195, 330). The
readers' `rhsSortGuard` looks inside r only, so the conjunction and ens are checked on the axiom
(`bodyConjFault?`), and `classifyAxiom` refuses such an equation or rewrite axiom `rhsOperandSort`.
- `ensRule Int (\top{SortFoo})`, `ensRule Int (\equals{SortBool,SortFoo}(X >Int 0, true))`: the
  ensures of another sort than its conjunction's; `ensRule Foo (\top{SortFoo})`: the conjunction of
  another sort than the rewrite's. Refused; the twins at Int are read.
- `ensEqn (\top{SortFoo})`: the same on an equation's conclusion; its twin at Int has no fault. -/

def ensRule (s : Kore.KSort) (en : Kore.Pattern) : Kore.Axiom :=
  ⟨[], .rewrites (srt "Int") (.and (srt "Int") [X, .top (srt "Int")]) (.and s [X, en]), [uid, loc]⟩

def ensEqn (en : Kore.Pattern) : Kore.Axiom :=
  ⟨[], .implies (srt "Int") (.top (srt "Int")) (.equals (srt "Int") (srt "Int") fX (.and (srt "Int") [gX, en])), [uid]⟩

/--
info: some "\\and{SortInt{}}: an operand \\top of sort SortFoo{}, the ensures"
some "\\and{SortInt{}}: an operand \\equals of sort SortFoo{}, the ensures"
some "\\rewrites{SortInt{}}: an operand \\and of sort SortFoo{}, the conjunction of the right side with its ensures"
some "\\and{SortInt{}}: an operand \\top of sort SortFoo{}, the ensures"
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (repr (bodyConjFault? (ensRule (srt "Int") (.top (srt "Foo")))))
  IO.println (repr (bodyConjFault? (ensRule (srt "Int") (isTrueAt (srt "Foo") gt0))))
  IO.println (repr (bodyConjFault? (ensRule (srt "Foo") (.top (srt "Foo")))))
  IO.println (repr (bodyConjFault? (ensEqn (.top (srt "Foo")))))

/-- The ill-sorted conjunctions are faults and the rewrite axioms holding them are refused
`rhsOperandSort` by `classifyAxiom`; their twins are not. -/
theorem ensConj_hand :
    (bodyConjFault? (ensRule (srt "Int") (.top (srt "Foo")))).isSome ∧
    (bodyConjFault? (ensRule (srt "Int") (isTrueAt (srt "Foo") gt0))).isSome ∧
    (bodyConjFault? (ensRule (srt "Foo") (.top (srt "Foo")))).isSome ∧
    (bodyConjFault? (ensEqn (.top (srt "Foo")))).isSome ∧
    bodyConjFault? (ensRule (srt "Int") (.top (srt "Int"))) = none ∧
    bodyConjFault? (ensRule (srt "Int") (isTrueAt (srt "Int") gt0)) = none ∧
    bodyConjFault? (ensEqn (.top (srt "Int"))) = none ∧
    classifyShape (.axiom (ensRule (srt "Int") (.top (srt "Foo")))) = .refused .rhsOperandSort ∧
    classifyShape (.axiom (ensRule (srt "Foo") (.top (srt "Foo")))) = .refused .rhsOperandSort ∧
    classifyShape (.axiom (ensRule (srt "Int") (.top (srt "Int")))) ≠ .refused .rhsOperandSort := by
  decide +kernel

/-! ## The conjunction of the left side or the arguments with the `requires`: `reqConjFault?`

kompile writes a rewrite axiom's left side l with its `requires` req as `\and{s}(l, req)`, the left
operand of `\rewrites{s}`, and an equation's `requires` with its arguments' memberships as
`\and{R}(req, args)`, the premise of `\implies{R}`; each operand of `\and{s}` is of the sort s
(kore-syntax.md:195, 330). The readers take req (`req?`) without its sort, so the conjunction is
checked on the axiom (`reqConjFault?`), and `classifyAxiom` refuses such an equation or rewrite
axiom `rhsOperandSort`.
- `reqRule Int (\top{SortFoo})`, `reqRule Int (\equals{SortBool,SortFoo}(X >Int 0, true))`: the
  requires of another sort than its conjunction's; `reqRule Foo (\top{SortFoo})`: the conjunction
  of another sort than the rewrite's. Refused; the twins at Int have no fault.
- `reqEqn Int (\top{SortFoo})`: an equation's requires of another sort than the premise's
  conjunction; `reqEqn Foo (\top{SortFoo})`: the conjunction of another sort than the `\implies`;
  `reqOwise`: the same requires in an `[owise]` equation's premise. Refused; the twins at Int have
  no fault. -/

def reqRule (s : Kore.KSort) (rq : Kore.Pattern) : Kore.Axiom :=
  ⟨[], .rewrites (srt "Int") (.and s [X, rq]) (.and (srt "Int") [X, .top (srt "Int")]), [uid, loc]⟩

def X0 : Kore.Pattern := ev "X0" (srt "Int")
def argsX : Kore.Pattern := .and (srt "Int") [.in (srt "Int") (srt "Int") X0 X, .top (srt "Int")]
def eqnConcl : Kore.Pattern :=
  .equals (srt "Int") (srt "Int") (ap "Lblf" [X0]) (.and (srt "Int") [gX, .top (srt "Int")])

def reqEqn (s : Kore.KSort) (rq : Kore.Pattern) : Kore.Axiom :=
  ⟨[], .implies (srt "Int") (.and s [rq, argsX]) eqnConcl, [uid]⟩

def reqOwise (rq : Kore.Pattern) : Kore.Axiom :=
  ⟨[], .implies (srt "Int") (.and (srt "Int") [.not (srt "Int") (.bottom (srt "Int")), .and (srt "Int") [rq, argsX]])
    eqnConcl, [uid]⟩

/--
info: some "\\and{SortInt{}}: an operand \\top of sort SortFoo{}, the requires"
some "\\and{SortInt{}}: an operand \\equals of sort SortFoo{}, the requires"
some "\\rewrites{SortInt{}}: an operand \\and of sort SortFoo{}, the conjunction of the left side with its requires"
some "\\and{SortInt{}}: an operand \\top of sort SortFoo{}, the requires"
some "\\implies{SortInt{}}: an operand \\and of sort SortFoo{}, the conjunction of the requires with the arguments"
some "\\and{SortInt{}}: an operand \\top of sort SortFoo{}, the requires"
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (repr (reqConjFault? (reqRule (srt "Int") (.top (srt "Foo")))))
  IO.println (repr (reqConjFault? (reqRule (srt "Int") (isTrueAt (srt "Foo") gt0))))
  IO.println (repr (reqConjFault? (reqRule (srt "Foo") (.top (srt "Foo")))))
  IO.println (repr (reqConjFault? (reqEqn (srt "Int") (.top (srt "Foo")))))
  IO.println (repr (reqConjFault? (reqEqn (srt "Foo") (.top (srt "Foo")))))
  IO.println (repr (reqConjFault? (reqOwise (.top (srt "Foo")))))

/-- The ill-sorted conjunctions are faults and the axioms holding them are refused
`rhsOperandSort` by `classifyAxiom`; their twins are not. -/
theorem reqConj_hand :
    (reqConjFault? (reqRule (srt "Int") (.top (srt "Foo")))).isSome ∧
    (reqConjFault? (reqRule (srt "Int") (isTrueAt (srt "Foo") gt0))).isSome ∧
    (reqConjFault? (reqRule (srt "Foo") (.top (srt "Foo")))).isSome ∧
    (reqConjFault? (reqEqn (srt "Int") (.top (srt "Foo")))).isSome ∧
    (reqConjFault? (reqEqn (srt "Foo") (.top (srt "Foo")))).isSome ∧
    (reqConjFault? (reqOwise (.top (srt "Foo")))).isSome ∧
    reqConjFault? (reqRule (srt "Int") (.top (srt "Int"))) = none ∧
    reqConjFault? (reqRule (srt "Int") (isTrueAt (srt "Int") gt0)) = none ∧
    reqConjFault? (reqEqn (srt "Int") (.top (srt "Int"))) = none ∧
    reqConjFault? (reqEqn (srt "Int") (isTrueAt (srt "Int") gt0)) = none ∧
    reqConjFault? (reqOwise (.top (srt "Int"))) = none ∧
    classifyShape (.axiom (reqRule (srt "Int") (.top (srt "Foo")))) = .refused .rhsOperandSort ∧
    classifyShape (.axiom (reqRule (srt "Foo") (.top (srt "Foo")))) = .refused .rhsOperandSort ∧
    classifyShape (.axiom (reqEqn (srt "Int") (.top (srt "Foo")))) = .refused .rhsOperandSort ∧
    classifyShape (.axiom (reqRule (srt "Int") (.top (srt "Int")))) ≠ .refused .rhsOperandSort ∧
    classifyShape (.axiom (reqEqn (srt "Int") (.top (srt "Int")))) ≠ .refused .rhsOperandSort := by
  decide +kernel

end RhsSortCheck

/-- info: 'RhsSortCheck.refused_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.refused_hand
/-- info: 'RhsSortCheck.read_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.read_hand
/-- info: 'RhsSortCheck.rule_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.rule_hand
/-- info: 'RhsSortCheck.ex_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.ex_hand
/-- info: 'RhsSortCheck.exOp_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.exOp_hand
/-- info: 'RhsSortCheck.topOp_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.topOp_hand
/-- info: 'RhsSortCheck.binder_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.binder_hand
/-- info: 'RhsSortCheck.connOp_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.connOp_hand
/-- info: 'RhsSortCheck.iffEq_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.iffEq_hand
/-- info: 'RhsSortCheck.ensConj_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.ensConj_hand
/-- info: 'KCore.Parse.clauseBody_rhsSorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clauseBody_rhsSorted
/-- info: 'RhsSortCheck.reqConj_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.reqConj_hand
