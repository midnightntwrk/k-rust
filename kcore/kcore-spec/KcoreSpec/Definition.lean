/-
  KCore. A definition: core, presentation, certificate (KCORE-SPEC.md §7). Reviewed layer.
  The presentation holds what `emit` needs beyond the core to print the KORE back: names of
  variables, locations and sources, unique ids, the order of productions, the imported builtin
  modules (`imports`), the configuration's cell tree (`config`: the cells' names, and the shape
  kompile derives their sorts, constructors and subsorts from, which the core holds as ordinary
  ones), and kompile's choices that carry no meaning:
  - `CtorPres.loc : Option Loc`: `strict`'s generated freezers (`#freezer…`) carry no location and
    no source;
  - a `src` on each sentence's presentation: the file declaring it when it is not the main module's
    (definitions split over files with `requires`);
  - `RulePres.argAttrs`: the production's attributes with an argument (`symbol'Kywd'`, `format`)
    that kompile copies onto its heating and cooling rules;
  - `RulePres.prioAttr`, `ClausePres.prioAttr`: whether the rule's or the equation's priority is
    written `priority{}("n")`; otherwise it is 50 (no attribute) or 200 (`owise{}()`), and `emit`
    writes it accordingly;
  - `ClausePres.overload`: an equation written as a symbol-overload axiom, whose only attribute is
    `symbol-overload{}(f(), g())` (no id, place or priority), and which gives the clause `aside`
    and priority 0.
-/
import KcoreSpec.Core
import KcoreSpec.Kore.Base

set_option autoImplicit false

namespace KCore

abbrev Loc := KoreAML.Loc
abbrev Meta := KoreAML.Meta
abbrev SortUids := KoreAML.SortUids

structure ClausePres where
  names : List String
  info : Meta
  /-- the variables' names in the clause's exclusion from an `[owise]` equation's premise -/
  exclNames : List String
  /-- the equation's `label{}("…")` attribute -/
  label : Option String := none
  /-- the equation's source file, when not the main module's (`requires "expr.k"`) -/
  src : Option String := none
  /-- the priority is written `priority{}("n")` (otherwise 50 is no attribute, 200 is `owise`) -/
  prioAttr : Bool := false
  /-- the second symbol `g` of the equation's `symbol-overload{}(f(), g())` attribute, its only
  attribute: a symbol-overload axiom read as a clause of the function `f`, `aside` and of
  priority 0, which that attribute gives (no `priority{}` is written) -/
  overload : Option String := none
  deriving Repr, Inhabited

structure FnPres where
  kywd : Option String
  loc : Loc
  clauses : List ClausePres
  src : Option String := none
  /-- the `hook{}` attribute of a function declared `hooked-symbol` (a hook no registry hook
  interprets), written with its declaration; `none` for a function declared `symbol` -/
  hook : Option String := none
  deriving Repr, Inhabited

structure CtorPres where
  kywd : Option String
  /-- `none` for a generated constructor (a freezer), written without location and source -/
  loc : Option Loc
  /-- the declaring file, when not the main module's -/
  src : Option String := none
  deriving Repr, Inhabited

structure RulePres where
  names : List String
  info : Meta
  label : Option String
  /-- the rule's attributes without arguments (`concrete`, kompile's `cool-like`); `wf` allows only
  those that do not change which ground steps the rule makes (`inertRuleAttrs`) -/
  attrs : List String
  /-- the priority is written `priority{}("n")` (otherwise 50 is no attribute, 200 is `owise`) -/
  prioAttr : Bool := false
  /-- the attributes with one string argument kompile copies onto the heating and cooling rules
  from their production (`symbol'Kywd'{}("inc")`, `format{}("%1%2")`); `wf` allows only those
  with no meaning (`inertArgAttrs`) -/
  argAttrs : List (String × String) := []
  /-- the rule's source file, when not the main module's -/
  src : Option String := none
  deriving Repr, Inhabited

/-- An equation between two terms that the text states for every element. -/
structure LawEq where
  vars : List Srt
  lhs : Term
  rhs : Term
  deriving Repr

/-- A user parameter symbol's presentation: its `hook{}` attribute, keyword, location and
source. kompile writes a hooked function symbol as `hooked-symbol f(…) : s [function{}(),
hook{}("…"), Location, Source, symbol'Kywd'{}("…")]`, with no axiom about it. -/
structure ParamPres where
  hook : String
  kywd : Option String
  /-- its location, which K does not give the symbols it generates for a collection sort -/
  loc : Option Loc
  src : Option String := none
  /-- declared `total` (or `functional`, K's earlier name of it); the statements of a definition
  with parameters are about the interpretations total on these (`Definition.totalParams`) -/
  total : Bool := false
  deriving Repr, Inhabited

/-! ## The configuration's cells

The presentation holds the configuration's cell tree: the names `emit` writes the cells' symbols
and initializers under, and the shape kompile generates their sorts, constructors and subsorts
from. The semantics holds those sorts, constructors and subsorts as ordinary ones (the first of
`userSorts`, `ctors` and `userSubsorts`, `Presentation.cellsOK`); nothing that evaluates or steps
reads the tree. -/

/-- The numbers of a cell's sorts and symbols: its sort `XCell`, its `XCellOpt` (not for the top
cell), its `XCellFragment` (nodes only); its constructor `<x>`, its `noXCell` (not for the top
cell), its `<x>-fragment` (nodes only). A sort or symbol the cell does not have is `none`. -/
structure CellIds where
  sort : Srt
  opt : Option Srt := none
  frag : Option Srt := none
  label : Sym
  no : Option Sym := none
  fragLabel : Option Sym := none
  deriving Repr, DecidableEq, Inhabited

/-- A configuration cell: a leaf `<name> content </name>` holding a value of sort `content`, or a
node holding its children in order. Cell names are letters, digits and inner dashes
(`Presentation.cellsOK`). -/
inductive Cell where
  | leaf (name : String) (content : Srt) (ids : CellIds)
  | node (name : String) (children : List Cell) (ids : CellIds)
  deriving Repr, Inhabited

namespace Cell

def name : Cell → String
  | .leaf n _ _ => n
  | .node n _ _ => n

def ids : Cell → CellIds
  | .leaf _ _ i => i
  | .node _ _ i => i

def sort (x : Cell) : Srt := x.ids.sort
def optSort (x : Cell) : Option Srt := x.ids.opt
def fragSort (x : Cell) : Option Srt := x.ids.frag
def label (x : Cell) : Sym := x.ids.label

/-- The cell's `noXCell : → XCellOpt`, when it has both. -/
def noCtor (x : Cell) : Option CtorSig :=
  match x.ids.no, x.optSort with
  | some n, some o => some ⟨n, [], o⟩
  | _, _ => none

/-- A node's `<x>-fragment`, when it has the symbol and the sort: one argument for each child with
an `Opt` sort, of that sort (a child without one has no place in the fragment). -/
def fragCtor (cs : List Cell) (i : CellIds) : Option CtorSig :=
  match i.fragLabel, i.frag with
  | some l, some s => some ⟨l, cs.filterMap Cell.optSort, s⟩
  | _, _ => none

/-- The generated counter cell `<generatedCounter> Int </generatedCounter>`. -/
def counter : Cell := .leaf "generatedCounter" Srt.int
  { sort := Srt.counter, opt := some Srt.counterOpt, label := counterLabel, no := some noCounter }

/-- The generated top cell around the user's top-level cells. -/
def top (roots : List Cell) : Cell :=
  .node "generatedTop" (roots ++ [counter])
    { sort := Srt.top, frag := some Srt.topFrag, label := topLabel, fragLabel := some topFragLabel }

mutual
  /-- The constructors of a cell and its descendants, in the order of their symbols (`syms`): the
  cell's `<x>`, its `noXCell` and its `<x>-fragment` (those it has), then its children's. `<x>`
  takes the cell's content (a leaf) or its children's sorts (a node). -/
  def sigs : Cell → List CtorSig
    | .leaf n c i => [⟨i.label, [c], i.sort⟩] ++ (Cell.leaf n c i).noCtor.toList
    | .node n cs i => [⟨i.label, cs.map Cell.sort, i.sort⟩] ++ (Cell.node n cs i).noCtor.toList ++
        (fragCtor cs i).toList ++ sigsList cs
    termination_by structural x => x
  def sigsList : List Cell → List CtorSig
    | [] => []
    | x :: xs => sigs x ++ sigsList xs
    termination_by structural xs => xs
end

mutual
  /-- The sorts of a cell and its descendants: its sort, its `Opt` sort and its fragment sort, those
  it has (the top cell has no `Opt` sort, a leaf no fragment sort). -/
  def sorts : Cell → List Srt
    | .leaf _ _ i => [i.sort] ++ i.opt.toList
    | .node _ cs i => [i.sort] ++ i.opt.toList ++ i.frag.toList ++ sortsList cs
    termination_by structural x => x
  def sortsList : List Cell → List Srt
    | [] => []
    | x :: xs => sorts x ++ sortsList xs
    termination_by structural xs => xs
end

mutual
  /-- The symbols of a cell and its descendants: `<x>`, `noXCell`, and for a node `<x>-fragment`
  (those it has), then its children's. -/
  def syms : Cell → List Sym
    | .leaf _ _ i => [i.label] ++ i.no.toList
    | .node _ cs i => [i.label] ++ i.no.toList ++ i.fragLabel.toList ++ symsList cs
    termination_by structural x => x
  def symsList : List Cell → List Sym
    | [] => []
    | x :: xs => syms x ++ symsList xs
    termination_by structural xs => xs
end

mutual
  /-- `XCell < XCellOpt` for a cell with an `Opt` sort and its descendants. -/
  def optSubs : Cell → List (Srt × Srt)
    | .leaf _ _ i => i.opt.toList.map (i.sort, ·)
    | .node _ cs i => i.opt.toList.map (i.sort, ·) ++ optSubsList cs
    termination_by structural x => x
  def optSubsList : List Cell → List (Srt × Srt)
    | [] => []
    | x :: xs => optSubs x ++ optSubsList xs
    termination_by structural xs => xs
end

/-- Whether the counter cell has an `Opt` sort, a `noGeneratedCounterCell` constructor and a place
in the top cell's fragment: kompile gives it them when the configuration has one top-level cell,
and not when it has several (`<k/> <env/>`). -/
def counterOpt (roots : List Cell) : Bool := roots.length == 1

/-- The cell sorts of a configuration (the top cell's, through `sorts`, less the counter's `Opt`
sort when it has none). -/
def topSorts (roots : List Cell) : List Srt :=
  (sorts (top roots)).filter fun s => counterOpt roots || s != Srt.counterOpt

/-- The cell constructors of a configuration (`sigs`, less the counter's `no` constructor and
fragment place when it has no `Opt` sort). -/
def topSigs (roots : List Cell) : List CtorSig :=
  let base := sigs (top roots)
  if counterOpt roots then base
  else (base.filter (·.result != Srt.counterOpt)).map fun k =>
    if k.result == Srt.topFrag then { k with args := k.args.dropLast } else k

/-- `XCell < XCellOpt` for every cell but the top one (and the counter without `Opt` sort). -/
def topSubs (roots : List Cell) : List (Srt × Srt) :=
  (optSubsList (roots ++ [counter])).filter fun (_, b) => counterOpt roots || b != Srt.counterOpt

end Cell

inductive ProdKind where
  | ctor
  | fn
  | subsort
  deriving Repr, DecidableEq

structure Presentation where
  source : String
  moduleName : String
  moduleLoc : Loc
  /-- the builtin modules the definition imports, by their place in `library` (Builtins.lean),
  in increasing order -/
  imports : List Nat
  /-- kompile writes an argument-less `simplification` attribute as `simplification{}("")`: some
  sentence of the definition gives the attribute an argument (Builtins.lean) -/
  simpArg : Bool
  sortUids : List SortUids
  order : List ProdKind
  ctors : List CtorPres
  fns : List FnPres
  rules : List RulePres
  /-- the configuration: its top-level cells (`<k> $PGM </k>` and `<T>…</T>` are one cell each,
  `<k/> <env/>` two), inside the generated top cell with the counter (`Cell.top`) -/
  config : List Cell
  configLoc : Loc
  /-- the `Source` of the cells' symbols: the user's file, or the builtin module that declares the
  default configuration `<k> $PGM:K </k>` when the definition declares none -/
  configSource : String
  /-- `isX`/`projectX` equation ids of each cell sort, by sort -/
  cellUids : List (Srt × SortUids)
  /-- the initializer equation's id of each cell, by cell name -/
  cellInits : List (String × String)
  /-- the initial value of each leaf cell other than the one holding `$PGM` (`pgmCell`, if any) and the
  counter, by cell name -/
  cellValues : List (String × Term)
  /-- the id of `getGeneratedCounterCell`'s equation -/
  counterUid : String
  /-- the names of the variables standing for the top-level cells in that equation's premise
  (`_DotVar0` for one cell; `_Gen2`, `_Gen1` for two) -/
  counterVars : List String
  /-- how many of the user's KItem constructors kompile places before the fixed `#KConfigValue`
  (it orders constructors by the name of the module declaring them, `K-RUST-CONFIGURATION-VALUES`
  for `#KConfigValue`); it fixes the order inside KItem's distinctness and no-junk axioms -/
  kconfigPos : Nat
  /-- the user's parameter symbols' presentations, in the order of `Semantics.params` after the
  imported modules' (`libParams`) -/
  params : List ParamPres := []
  /-- the user's sorts declared with their location (`sort SortX{} [Location, Source]`, as K
  writes a sort declared alone in a file): sort, location, source -/
  sortLocs : List (Srt × Loc × String) := []
  /-- the sorts, the library's or the definition's own, whose projection `project:X` is read as a
  function, from the text's equation (`emit` writes its declaration and equation as the function's,
  not as the sort's generated ones) -/
  libProjs : List Srt := []
  /-- the functions the text declares and states outside the user module's productions (K's
  `append` in the prelude, the top cell tree's initializers with the cells): `emit` writes no
  production and no equation of them, which the prelude and the cells' sentences hold -/
  generatedFns : List Sym := []
  /-- the leaf cell whose initializer holds `$PGM` projected to `Semantics.pgmSort`, by name: the
  text's initializer equations state which cell it is (`<k>`, or another); `none` where no
  initializer holds `$PGM` (`configuration <k> foo </k>`): every leaf's initial value is then one
  of `cellValues`, and no sentence `emit` writes reads `Semantics.pgmSort` -/
  pgmCell : Option String := some "k"
  /-- the laws the text writes for its functions, each an equation it states for every element;
  `Semantics` holds none of them: the statements about the definition take them at values
  (`FnLaws`). `Parse.presOf` reads them from the text's law axioms on its functions (`Parse.fnLawOf`). -/
  laws : List LawEq := []
  deriving Repr

namespace Presentation
variable (p : Presentation)

/-- The generated top cell around the configuration. -/
def topCell : Cell := Cell.top p.config

/-- The cell sorts, which the semantics' `userSorts` begins with. -/
def cellSorts : List Srt := Cell.topSorts p.config

/-- The cell constructors, which the semantics' `ctors` begins with. -/
def cellCtors : List CtorSig := Cell.topSigs p.config

/-- `XCell < XCellOpt`, which the semantics' `userSubsorts` begins with. -/
def cellSubsorts : List (Srt × Srt) := Cell.topSubs p.config

end Presentation

structure Certificates where
  decreasing : List (Option Nat)
  deriving Repr

structure Definition where
  sem : Semantics
  pres : Presentation
  cert : Certificates
  deriving Repr

/-- The laws the text writes for its functions (`Presentation.laws`). -/
def Definition.laws (d : Definition) : List LawEq := d.pres.laws

def withPres {α β : Type} [Inhabited β] : List α → List β → List (α × β)
  | [], _ => []
  | a :: as, bs => (a, bs.headD default) :: withPres as bs.tail

end KCore
