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

end RhsSortCheck

/-- info: 'RhsSortCheck.refused_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.refused_hand
/-- info: 'RhsSortCheck.read_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.read_hand
/-- info: 'RhsSortCheck.rule_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.rule_hand
/-- info: 'RhsSortCheck.ex_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RhsSortCheck.ex_hand
/-- info: 'KCore.Parse.clauseBody_rhsSorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clauseBody_rhsSorted
