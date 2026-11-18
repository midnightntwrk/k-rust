/-
  The sentences of the counter's getter and of the cell tree's initializers are accounted by their
  content (`Parse.getterEqnOK`, `Parse.initEqnOK`, `Parse.initTotalOK`, `Parse.initFaults`).
  Run from the package root: `lake env lean -j1 test/InitContent.lean`.

  - By the kernel (`decide +kernel`), on a hand-built vocabulary with the configuration
    `<k> K </k> <x> Int </x>`: the sentences kompile writes are accepted, and each condition broken
    alone is not: for the getter one equation (G1), no `requires`, `ensures` or exclusion (G2), the
    top cell's constructor at distinct element variables (G3), the last of them as right side
    (G4); for an initializer one equation (I1), no `requires`, `ensures` or exclusion (I2),
    distinct element variables as patterns (I3), the right side's variables among them (I4), the
    right side over `inj`, the definition's symbols, initializers strictly below and accounted
    projections (I5); for its `functional` axiom a right side of constructors, total interpreted
    symbols and initializers below that have the axiom (I6).
  - By evaluation, on K 7.1.337 kompile's text of fixture e2-cells (`f2-examples/cells.kompile.kore`)
    and six edits of it, each stating something the definition's theory refutes or does not state:
    the unedited text is read with nothing refused or unaccounted; each edit is refused
    (`generatedEquation`): A, B the getter's equation; C the functional axiom of `initOneCell`,
    whose right side `<one>(1 /Int 0)` applies a partial hook; D the added functional axiom of
    `initKCell`, whose right side applies a projection and `Map:lookup`; E both equations of
    `initOneCell` and, with them, its functional axiom; F the equation of `initOneCell`, a right-side
    variable no pattern holds, and its functional axiom. Two more edits leave the reader without a
    sentence its reading of the configuration needs: G the getter's equation removed, refused
    (`missingEquation`); H `<k>` declared over its own sort `KCell` (`<k>(KCell) : KCell`), a cell
    below itself, which is no tree of cells, refused (`configuration`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.InitContent

open KCore KCore.Parse KoreAML

/-! ## The hand-built vocabulary -/

def kCellS : Srt := nRegSorts
def xCellS : Srt := nRegSorts + 2
def kL : Sym := nRegSyms
def xL : Sym := nRegSyms + 1
def fL : Sym := nRegSyms + 2
def uL : Sym := nRegSyms + 3

/-- `f` is a function of the definition; `u` is a parameter with the hook `LIST.unit`'s meaning. -/
def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "XCell", "XCellOpt"]
    symNames := ["Lbl'-LT-'k'-GT-'", "Lbl'-LT-'x'-GT-'", "Lblf", "Lblu"]
    userSorts := [Srt.top, kCellS, xCellS, Srt.counter]
    ctors := [⟨topLabel, [kCellS, xCellS, Srt.counter], Srt.top⟩, ⟨kL, [Srt.k], kCellS⟩, ⟨xL, [Srt.int], xCellS⟩,
      ⟨counterLabel, [Srt.int], Srt.counter⟩]
    fns := [{ label := fL, args := [Srt.int], result := Srt.int, clauses := [] }]
    userSubsorts := []
    pgmSort := Srt.k
    rules := []
    params := [{ sig := ⟨uL, [], Srt.int⟩, impl := some listUnit }] }

def kCell : Cell := .leaf "k" Srt.k { sort := kCellS, label := kL }
def xCell : Cell := .leaf "x" Srt.int { sort := xCellS, label := xL }
def topCell : Cell := Cell.top [kCell, xCell]

def topName : String := c.symName topLabel
def vK : Kore.Pattern := ev "VarK" (srt "KCell")
def vX : Kore.Pattern := ev "VarX" (srt "XCell")
def vC : Kore.Pattern := ev "VarCell" (srt "GeneratedCounterCell")
def vInit : Kore.Pattern := ev "VarInit" (srt "Map")
def tt : Kore.Pattern := dv "Bool" "true"

def eqn (f : String) (pats : List Kore.Pattern) (rhs : Kore.Pattern) : RawEqn :=
  ⟨f, pats, none, none, rhs, [], none, false⟩

/-! ## The getter -/

def getter : RawEqn := eqn getterName [ap topName [vK, vX, vC]] vC

example : topName = "Lbl'-LT-'generatedTop'-GT-'" := by decide +kernel
example : getterEqnOK c [getter] getter = true := by decide +kernel
/-- G1: a second equation. -/
example : getterEqnOK c [getter, getter] getter = false := by decide +kernel
/-- G2: a `requires`, an `ensures`, an exclusion. -/
example : getterEqnOK c [{ getter with req := some tt }] { getter with req := some tt } = false := by decide +kernel
example : getterEqnOK c [{ getter with ens := some tt }] { getter with ens := some tt } = false := by decide +kernel
example : getterEqnOK c [{ getter with competitors := some [] }] { getter with competitors := some [] } = false := by
  decide +kernel
/-- G3: another constructor; a variable twice; an argument that is no variable. -/
example : (let e := eqn getterName [ap "Lbl'-LT-'x'-GT-'" [vK, vX, vC]] vC; getterEqnOK c [e] e) = false := by
  decide +kernel
example : (let e := eqn getterName [ap topName [vK, vC, vC]] vC; getterEqnOK c [e] e) = false := by decide +kernel
example : (let e := eqn getterName [ap topName [vK, ap "Lbl'-LT-'x'-GT-'" [dv "Int" "0"], vC]] vC; getterEqnOK c [e] e) = false := by
  decide +kernel
/-- G4: a right side that is another variable of the pattern, or of none. -/
example : (let e := eqn getterName [ap topName [vK, vX, vC]] (ev "VarOther" (srt "GeneratedCounterCell"));
    getterEqnOK c [e] e) = false := by decide +kernel
example : (let e := eqn getterName [ap topName [vC, vX, vK]] vC; getterEqnOK c [e] e) = false := by decide +kernel

/-! ## The initializers -/

def initK : RawEqn := eqn "LblinitKCell" [vInit]
  (ap "Lbl'-LT-'k'-GT-'" [ap "kseq" [ap "Lblproject'Coln'KItem" [ap "LblMap'Coln'lookup" [vInit, dv "KConfigVar" "$PGM"]],
    ap "dotk" []]])
def initX : RawEqn := eqn "LblinitXCell" [] (ap "Lbl'-LT-'x'-GT-'" [dv "Int" "0"])
def initCounter : RawEqn := eqn "LblinitGeneratedCounterCell" [] (ap "Lbl'-LT-'generatedCounter'-GT-'" [dv "Int" "0"])
def initTop : RawEqn := eqn "LblinitGeneratedTopCell" [vInit]
  (ap topName [ap "LblinitKCell" [vInit], ap "LblinitXCell" [], ap "LblinitGeneratedCounterCell" []])
def eqs : List RawEqn := [getter, initK, initX, initCounter, initTop]
def N : Names := { sorts := c.sortNames, syms := c.symNames }

example : (topCell.all.map (·.initLabel c)) =
    ["LblinitGeneratedTopCell", "LblinitKCell", "LblinitXCell", "LblinitGeneratedCounterCell"] := by decide +kernel
example : initEqnOK N "" eqs c kCell initK = true := by decide +kernel
example : initEqnOK N "" eqs c xCell initX = true := by decide +kernel
example : initEqnOK N "" eqs c Cell.counter initCounter = true := by decide +kernel
example : initEqnOK N "" eqs c topCell initTop = true := by decide +kernel
/-- The standard sentences give no failure, with or without the `functional` axioms kompile writes. -/
example : (initFaults N "" [] eqs [] c topCell).length = 0 := by decide +kernel
example : (initFaults N "" [] eqs ["LblinitXCell", "LblinitGeneratedCounterCell"] c topCell).length = 0 := by
  decide +kernel

/-- The initializer of `<x>` with the right side `r`, among the standard sentences. -/
def xWith (e : RawEqn) : Bool := initEqnOK N "" [getter, initK, e, initCounter, initTop] c xCell e

/-- I1: a second equation. -/
example : initEqnOK N "" (initX :: eqs) c xCell initX = false := by decide +kernel
/-- I2: a `requires`, an `ensures`, an exclusion. -/
example : xWith { initX with req := some tt } = false := by decide +kernel
example : xWith { initX with ens := some tt } = false := by decide +kernel
example : xWith { initX with competitors := some [] } = false := by decide +kernel
/-- I3: a pattern that is no variable; a variable twice. -/
example : xWith { initX with pats := [dv "Int" "0"] } = false := by decide +kernel
example : xWith { initX with pats := [vInit, vInit] } = false := by decide +kernel
/-- I4: a right-side variable no pattern holds. -/
example : xWith { initX with rhs := ap "Lbl'-LT-'x'-GT-'" [ev "VarN" (srt "Int")] } = false := by decide +kernel
example : xWith { initX with pats := [ev "VarN" (srt "Int")], rhs := ap "Lbl'-LT-'x'-GT-'" [ev "VarN" (srt "Int")] } = true := by
  decide +kernel
/-- I5: a symbol of neither the registry nor the definition; the initializer itself; the
initializer of a cell that is not below; a connective. A function of the definition is accepted. -/
example : xWith { initX with rhs := ap "Lbl'-LT-'x'-GT-'" [ap "Lblother" []] } = false := by decide +kernel
example : xWith { initX with rhs := ap "LblinitXCell" [] } = false := by decide +kernel
example : xWith { initX with rhs := ap "LblinitKCell" [] } = false := by decide +kernel
example : xWith { initX with rhs := .and (srt "XCell") [ap "Lbl'-LT-'x'-GT-'" [dv "Int" "0"]] } = false := by decide +kernel
example : xWith { initX with rhs := ap "Lbl'-LT-'x'-GT-'" [ap "Lblf" [dv "Int" "0"]] } = true := by decide +kernel

/-- I6: constructors and literals have one value; a partial hook, a function of the definition, a
projection, and an initializer below without its `functional` axiom do not; a parameter with a
total hook's meaning and an initializer below with the axiom do. -/
example : initTotalOK [] c xCell initX = true := by decide +kernel
example : initTotalOK [] c xCell { initX with rhs := ap "Lbl'-LT-'x'-GT-'" [ap "Lbl'UndsSlsh'Int'Unds'" [dv "Int" "1", dv "Int" "0"]] } = false := by
  decide +kernel
example : initTotalOK [] c xCell { initX with rhs := ap "Lbl'-LT-'x'-GT-'" [ap "Lblf" [dv "Int" "0"]] } = false := by
  decide +kernel
example : initTotalOK [] c xCell { initX with rhs := ap "Lbl'-LT-'x'-GT-'" [ap "Lblu" []] } = true := by decide +kernel
example : initTotalOK [] c kCell initK = false := by decide +kernel
example : initTotalOK ["LblinitKCell", "LblinitXCell"] c topCell initTop = false := by decide +kernel
example : initTotalOK ["LblinitKCell", "LblinitXCell", "LblinitGeneratedCounterCell"] c topCell initTop = true := by
  decide +kernel
/-- A `functional` axiom of `initKCell`, whose equation's right side applies a projection, is a failure. -/
example : ((initFaults N "" [] eqs ["LblinitKCell"] c topCell).map (·.detail)) =
    ["LblinitKCell: functional axiom of a cell's initializer whose equation's right side the definition does not give exactly one value at every argument"] := by
  decide +kernel

/-! ## The text of e2-cells and six edits of it -/

/-- The refusals of `text` (the reader's, then the account's unaccounted sentences), as
`reason head`. -/
def verdict (text : String) : String :=
  match Kore.parseDefinition text with
  | .error e => s!"KORE read error {e}"
  | .ok k => match Parse.parse k with
    | .error _ => toString ((Parse.refusals k).map fun r => s!"{r.reason.name} {r.head}")
    | .ok d => s!"read, unaccounted {((Parse.unconsumed k d).map fun r => s!"{r.reason.name} {r.head}")}"

def getterRhs : String := "       VarCell:SortGeneratedCounterCell{},\n        \\top{SortGeneratedCounterCell{}}())))"
def oneRhs : String := "       Lbl'-LT-'one'-GT-'{}(\\dv{SortInt{}}(\"0\")),\n        \\top{SortOneCell{}}())))"
def oneFunctional : String :=
  "  axiom{R} \\exists{R} (Val:SortOneCell{}, \\equals{SortOneCell{}, R} (Val:SortOneCell{}, LblinitOneCell{}())) [functional{}()] // functional\n"
def oneEqn (rhs uid : String) : String :=
  "  axiom{R} \\implies{R} (\\and{R}(\\top{R}(), \\top{R}()), \\equals{SortOneCell{},R} (LblinitOneCell{}(), \\and{SortOneCell{}} (" ++
    rhs ++ ", \\top{SortOneCell{}}()))) [UNIQUE'Unds'ID{}(\"" ++ uid ++ "\")]\n"

/-- The text without the getter's equation (the sentence after its `// rule` comment, up to the next
one's). -/
def dropGetter (t : String) : String :=
  match t.splitOn "// rule getGeneratedCounterCell" with
  | [a, b] => match b.splitOn "\n// rule " with
    | _ :: rest => a ++ "// rule " ++ "\n// rule ".intercalate rest
    | [] => t
  | _ => t

/-- The edits: A the getter's right side another variable; B the getter `ensures false`; C
`initOneCell() = <one>(1 /Int 0)` with its `functional` axiom; D a `functional` axiom of
`initKCell`; E a second equation `initOneCell() = <one>(1)`; F `initOneCell() = <one>(N:Int)`; G
no equation of the getter; H `<k>(KCell) : KCell`. -/
def edits (t : String) : List (String × String) :=
  [("0", t),
   ("A", t.replace getterRhs "       VarOther:SortGeneratedCounterCell{},\n        \\top{SortGeneratedCounterCell{}}())))"),
   ("B", t.replace getterRhs
      "       VarCell:SortGeneratedCounterCell{},\n        \\equals{SortBool{},SortGeneratedCounterCell{}}(\\dv{SortBool{}}(\"false\"),\\dv{SortBool{}}(\"true\")))))"),
   ("C", t.replace oneRhs
      "       Lbl'-LT-'one'-GT-'{}(Lbl'UndsSlsh'Int'Unds'{}(\\dv{SortInt{}}(\"1\"),\\dv{SortInt{}}(\"0\"))),\n        \\top{SortOneCell{}}())))"),
   ("D", t.replace oneFunctional (oneFunctional ++
      "  axiom{R} \\exists{R} (Val:SortKCell{}, \\equals{SortKCell{}, R} (Val:SortKCell{}, LblinitKCell{}(K0:SortMap{}))) [functional{}()] // functional\n")),
   ("E", t.replace oneFunctional (oneFunctional ++ oneEqn "Lbl'-LT-'one'-GT-'{}(\\dv{SortInt{}}(\"1\"))" "second")),
   ("F", t.replace oneRhs "       Lbl'-LT-'one'-GT-'{}(VarN:SortInt{}),\n        \\top{SortOneCell{}}())))"),
   ("G", dropGetter t),
   ("H", t.replace "symbol Lbl'-LT-'k'-GT-'{}(SortK{})" "symbol Lbl'-LT-'k'-GT-'{}(SortKCell{})")]

/--
info: 0: read, unaccounted []
A: [generatedEquation LblgetGeneratedCounterCell]
B: [generatedEquation LblgetGeneratedCounterCell]
C: [generatedEquation LblinitOneCell]
D: [generatedEquation LblinitKCell]
E: [generatedEquation LblinitOneCell, generatedEquation LblinitOneCell, generatedEquation LblinitOneCell]
F: [generatedEquation LblinitOneCell, generatedEquation LblinitOneCell]
G: [missingEquation E2-CELLS]
H: [configuration Lbl'-LT-'k'-GT-']
-/
#guard_msgs in
#eval show IO Unit from do
  let t ← IO.FS.readFile "f2-examples/cells.kompile.kore"
  for (n, s) in edits t do
    IO.println s!"{n}{if n != "0" && s == t then " (not edited)" else ""}: {verdict s}"

end KCore.InitContent
