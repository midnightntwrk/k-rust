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
   ⟨⟨⟨"org'Stop'kframework'Stop'attributes'Stop'Source"⟩⟩, [], [.string "Source(/home/u/a.k)"]⟩]

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
