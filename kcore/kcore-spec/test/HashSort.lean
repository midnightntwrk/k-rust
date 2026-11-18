/-
  A sort without a projection, read from K 7.1.337 kompile's KORE. Run from the package root:
  `lake env lean test/HashSort.lean`.
  - `f2-examples/hashsort.kompile.kore` (`hashsort.k`): a token sort `#Tok`, as wasm's
    `syntax #Layout [token]`. kompile declares `is#Tok` with its equations and no projection
    `project:#Tok`, neither its declaration nor its equation (it writes none for a sort whose name
    begins with `#`). No sentence can apply a projection the text does not declare: the sort is read
    without one (its presentation's projection id is empty), nothing unaccounted, `coreOK` (decided by
    the compiled `coreOK`, not in the kernel).
  - KItem's no-junk sentence (sentence 278) lists no `inj{#Tok, KItem}` and no subsort sentence puts
    `#Tok` below KItem: the reading adds `#Tok < KItem` (`ReadingNote.tokKItem`, listed by
    `Parse.tokKItemOmitted` with the subsort not stated; its guards: test/TokKItem.lean).
  - with `project:#Tok` declared (`symbol Lblproject'Coln''Hash'Tok{}(SortK{}) : Sort'Hash'Tok{}
    [function{}()]`, as kompile declares a projection) and no equation: a function of which the text
    states its declaration only, a parameter symbol (`Parse.isGenFn`); the sort still has no
    projection equation (its id empty), nothing unaccounted.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The projection of `#Tok`, as kompile would declare it. -/
def projDecl : Kore.Sentence :=
  .symbol { symbol := { ident := ⟨⟨"Lblproject'Coln''Hash'Tok"⟩⟩, sortVars := [] },
            sorts := [.ctor ⟨⟨"SortK"⟩⟩ []], sort := .ctor ⟨⟨"Sort'Hash'Tok"⟩⟩ [],
            attributes := [⟨⟨⟨"function"⟩⟩, [], []⟩] }

/-- The text with `projDecl` after the user module's first sentence. -/
def withProj (k : Kore.Definition) : Kore.Definition :=
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.take 1 ++ [projDecl] ++ m.sentences.drop 1 }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`): `#Tok`'s projection id, what is
unaccounted, `coreOK`, KItem's no-junk sentences that leave out a sort below KItem (`tokKItem`); or
the refusal. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let k := edit k
    return match Parse.parse k with
      | .ok d =>
        let proj := (d.sem.userSorts.filter (d.sem.sortName · == "'Hash'Tok")).map fun X => (uidsOf d.sem d.pres X).proj
        s!"read; #Tok's projection id {repr proj}; unaccounted {(Parse.unconsumed k d).map (·.detail)}; coreOK {d.sem.coreOK}; tokKItem {Parse.tokKItemOmitted k d}"
      | .error r => s!"{r.reason.name}{if r.detail.isEmpty then "" else " " ++ r.detail}"

/--
info: read; #Tok's projection id [""]; unaccounted []; coreOK true; tokKItem [(278, [('Hash'Tok, false)])]
read; #Tok's projection id [""]; unaccounted []; coreOK true; tokKItem [(279, [('Hash'Tok, false)])]
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/hashsort.kompile.kore")
  IO.println (← verdict "f2-examples/hashsort.kompile.kore" withProj)
