/-
  The sentences of a K installation's builtin files that no text the reader holds for those files
  states, read as the definition's own when they are about names of their own (`Parse.isOwnBuiltin`).
  Run from the package root: `lake env lean test/OwnBuiltin.lean`.
  - No sentence of the library's text (both forms) or of K-REFLECTION's declares a name, or is an
    axiom headed by a name, outside `Parse.ownBuiltinLibNames`: a library sentence, and one that
    states something else of a library name, are never read as the definition's own.
  - A declaration of a K installation's `domains.md` of a sort no library text declares (`Array`)
    is read as a user's file's sort declaration is, and so is a constructor of that sort; the same
    sort named `Int` (a library sort, its declaration not the library's) is refused
    (`builtinText`); a sort-parametric hooked symbol of a name of its own (MINT's `MInt2Unsigned`)
    is not read (`unread parametricUnused`), as K-REFLECTION's `#unparseKORE`; a user's file's
    sort declaration is not affected.
  - Each kind of axiom, from a K installation's `domains.md` and from a user's file: an own sort's
    subsort axiom, no-junk, no-confusion, injectivity and functional axiom, an own function's
    equation (hand-written forms, each refused `axiomShape` in a user's file), each classified as
    the same sentence of a user's file; a subsort axiom into a library
    sort, a no-junk axiom of a library sort, an equation of a library symbol refused (`builtinText`).
  - Fixtures (test/constructs/fixtures): e6-mod-array, e6-mod-kvar, e3-mint, e2-binder and their
    accounts (`read [own builtin]`), and the parameter symbols of e6-param-ffi,
    e6-param-unification, e6-param-timer and e6-param-rat (params.txt).
  test/FloatLib.lean, test/DefaultConfig.lean and test/StreamIO.lean show that a library sentence,
  the default configuration's cell and a K-REFLECTION sentence or stream rule each altered stay
  refused (`builtinText`).
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- `Source` and `Location` attributes of a sentence of the builtin file `f` of a K installation. -/
def placeAt (f : String) : List Kore.AppPattern :=
  [⟨⟨⟨"org'Stop'kframework'Stop'attributes'Stop'Location"⟩⟩, [], [.string "Location(76,3,76,15)"]⟩,
   ⟨⟨⟨"org'Stop'kframework'Stop'attributes'Stop'Source"⟩⟩, [],
     [.string s!"Source(/k/include/kframework/builtin/{f})"]⟩]

/-- A user file's place. -/
def userPlace : List Kore.AppPattern :=
  [⟨⟨⟨"org'Stop'kframework'Stop'attributes'Stop'Location"⟩⟩, [], [.string "Location(3,3,3,15)"]⟩,
   ⟨⟨⟨"org'Stop'kframework'Stop'attributes'Stop'Source"⟩⟩, [], [.string "Source(/src/u/a.k)"]⟩]

def sortDecl (n : String) (as : List Kore.AppPattern) : Kore.Sentence :=
  .sort ⟨⟨⟨n⟩⟩, [], as⟩

def srt (n : String) : Kore.KSort := .ctor ⟨⟨n⟩⟩ []

/-- `arr` of ARRAY-IN-K: a constructor of `Array`. -/
def arrDecl : Kore.Sentence :=
  .symbol ⟨⟨⟨⟨⟨"Lblarr'LParUndsCommUndsCommUndsRParUnds'ARRAY-IN-K'Unds'Array'Unds'List'Unds'Int'Unds'KItem"⟩⟩, []⟩⟩,
    [srt "SortList", srt "SortInt", srt "SortKItem"], srt "SortArray",
    [⟨⟨⟨"constructor"⟩⟩, [], []⟩, ⟨⟨⟨"functional"⟩⟩, [], []⟩, ⟨⟨⟨"injective"⟩⟩, [], []⟩] ++ placeAt "domains.md"⟩

/-- MINT's `MInt2Unsigned{W}`: sort-parametric, hooked. -/
def mintDecl : Kore.Sentence :=
  .hookedSymbol ⟨⟨⟨⟨⟨"LblMInt2Unsigned'LParUndsRParUnds'MINT'Unds'Int'Unds'MInt"⟩⟩, [⟨⟨⟨"SortWidth"⟩⟩⟩]⟩⟩,
    [.ctor ⟨⟨"SortMInt"⟩⟩ [.var ⟨⟨⟨"SortWidth"⟩⟩⟩]], srt "SortInt",
    [⟨⟨⟨"function"⟩⟩, [], []⟩, ⟨⟨⟨"hook"⟩⟩, [], [.string "MINT.uvalue"]⟩] ++ placeAt "domains.md"⟩

/--
info: library sentences with a name or head outside ownBuiltinLibNames: 0
-/
#guard_msgs in
#eval show IO Unit from do
  let all := (Parse.libraryBare.map (·.2)) ++ Parse.reflectionModuleText
  let bad := all.filter fun s => match s with
    | .axiom a => (Parse.ownBuiltinAxiomHead? a).any (!Parse.ownBuiltinLibNames.contains ·)
    | _ => (Parse.ownBuiltinDeclName? s).any (!Parse.ownBuiltinLibNames.contains ·)
  IO.println s!"library sentences with a name or head outside ownBuiltinLibNames: {bad.length}"

/--
info: [(read, true), (read, true), (refused builtinText, false), (unread parametricUnused, true), (read, false)]
-/
#guard_msgs in
#eval show IO Unit from do
  let ss := [sortDecl "SortArray" (placeAt "domains.md"), arrDecl, sortDecl "SortInt" (placeAt "domains.md"),
    mintDecl, sortDecl "SortArray" userPlace]
  IO.println (ss.map fun s => ((Parse.classify s).name, Parse.isOwnBuiltin s))

/-- Axioms of each kind, with the `Source` `src`, in a module of a KORE text. -/
def axiomsText (src : String) : String :=
  let P := s!"org'Stop'kframework'Stop'attributes'Stop'Source\{}(\"Source({src})\")"
  "[]\nmodule M\n" ++
  -- subsort Foo < Array; subsort Array < KItem (a library sort)
  s!"  axiom\{R} \\exists\{R}(Val:SortArray\{}, \\equals\{SortArray\{}, R}(Val:SortArray\{}, inj\{SortFoo\{}, SortArray\{}}(From:SortFoo\{}))) [subsort\{SortFoo\{}, SortArray\{}}(), {P}]\n" ++
  s!"  axiom\{R} \\exists\{R}(Val:SortKItem\{}, \\equals\{SortKItem\{}, R}(Val:SortKItem\{}, inj\{SortArray\{}, SortKItem\{}}(From:SortArray\{}))) [subsort\{SortArray\{}, SortKItem\{}}(), {P}]\n" ++
  -- no-junk of Array; of Int (a library sort)
  s!"  axiom\{} \\or\{SortArray\{}}(\\exists\{SortArray\{}}(X0:SortInt\{}, Lblarr\{}(X0:SortInt\{})), \\bottom\{SortArray\{}}()) [constructor\{}(), {P}]\n" ++
  s!"  axiom\{} \\or\{SortInt\{}}(\\exists\{SortInt\{}}(X0:SortInt\{}, Lblarr\{}(X0:SortInt\{})), \\bottom\{SortInt\{}}()) [constructor\{}(), {P}]\n" ++
  -- no-confusion, injectivity, functional of own constructors
  s!"  axiom\{} \\not\{SortArray\{}}(\\and\{SortArray\{}}(Lblarr\{}(X0:SortInt\{}), Lblnil\{}())) [constructor\{}(), {P}]\n" ++
  s!"  axiom\{} \\implies\{SortArray\{}}(\\and\{SortArray\{}}(Lblarr\{}(X0:SortInt\{}), Lblarr\{}(Y0:SortInt\{})), Lblarr\{}(\\and\{SortInt\{}}(X0:SortInt\{}, Y0:SortInt\{}))) [constructor\{}(), {P}]\n" ++
  s!"  axiom\{R} \\exists\{R}(Val:SortArray\{}, \\equals\{SortArray\{}, R}(Val:SortArray\{}, Lblarr\{}(K0:SortInt\{}))) [functional\{}(), {P}]\n" ++
  -- an equation of an own function; of a library symbol
  s!"  axiom\{R} \\implies\{R}(\\top\{R}(), \\equals\{SortInt\{}, R}(Lblsz\{}(X0:SortArray\{}), \\and\{SortInt\{}}(\\dv\{SortInt\{}}(\"0\"), \\top\{SortInt\{}}()))) [{P}]\n" ++
  s!"  axiom\{R} \\implies\{R}(\\top\{R}(), \\equals\{SortInt\{}, R}(LblsizeList\{}(X0:SortList\{}), \\and\{SortInt\{}}(\\dv\{SortInt\{}}(\"0\"), \\top\{SortInt\{}}()))) [{P}]\n" ++
  "endmodule\n[]\n"

def axiomsOf (src : String) : List Kore.Sentence :=
  match Kore.parseDefinition (axiomsText src) with
  | .ok k => ((k.modules.getLast?.map (·.sentences)).getD [])
  | .error _ => []

/--
info: 9 sentences
(refused axiomShape, (refused axiomShape, true))
(refused builtinText, (refused axiomShape, false))
(refused axiomShape, (refused axiomShape, true))
(refused builtinText, (refused axiomShape, false))
(refused axiomShape, (refused axiomShape, true))
(refused axiomShape, (refused axiomShape, true))
(refused axiomShape, (refused axiomShape, true))
(refused axiomShape, (refused axiomShape, true))
(refused builtinText, (refused axiomShape, false))
-/
#guard_msgs in
#eval show IO Unit from do
  let b := axiomsOf "/k/include/kframework/builtin/domains.md"
  let u := axiomsOf "/src/u/a.k"
  IO.println s!"{b.length} sentences"
  for (x, y) in b.zip u do
    IO.println ((Parse.classify x).name, (Parse.classify y).name, Parse.isOwnBuiltin x)
