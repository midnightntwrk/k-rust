/-
  Sorts and declarations read from K 7.1.337 kompile's own KORE: a text read with nothing refused is
  well formed, or names its construct. Run from the package root: `lake env lean test/SortsDecls.lean`.
  - `f2-examples/sortlabel.kompile.kore` (`sortlabel.k`, the construct triage's fixture
    e2-sort-label): `syntax Foo [label(fooSort)]`, a sort declared with `label`, a name: a sort of the
    definition, read, `wf` true.
  - `f2-examples/myint.kompile.kore` (`myint.k`): `syntax MyInt [hook(INT.Int)]`, a sort of the
    user's hooked to the library carrier Int: read, `wf` true (its literals are Int's).
  - `f2-examples/kresfn.kompile.kore` (`kresfn.k`): `syntax K ::= f(Int) [function]`, a function
    whose result sort is K: read, `wf` true (`resultSortOK` admits K).
  - `f2-examples/iot.kompile.kore`: K-REFLECTION's `#noParse`, a constructor of K-IO's `IOError`
    read as the definition's own (`ReadingNote.reflectionAsOwn`): `wf` true (`ctorResultOK` admits a
    library sort of constructor terms).
  - `sortlabel` with an attribute `nat{}("8")` added to the sort's declaration: refused by name
    (`sortAttribute`).
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The sort declaration of `SortX` with the attribute `a` added. -/
def addSortAttr (X : String) (a : Kore.AppPattern) (k : Kore.Definition) : Kore.Definition :=
  let edit := fun (s : Kore.Sentence) => match s with
    | .sort x => if x.sort.ident.name == X then .sort { x with attributes := x.attributes ++ [a] } else s
    | _ => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map edit }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`): "read" with `wf`, or its refusal. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse (edit k) with
    | .ok d => s!"read, wf {wf d}"
    | .error r => s!"{r.reason.name} {r.detail}"

/--
info: read, wf true
read, wf true
read, wf true
read, wf true
sortAttribute SortFoo: nat
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/sortlabel.kompile.kore")
  IO.println (← verdict "f2-examples/myint.kompile.kore")
  IO.println (← verdict "f2-examples/kresfn.kompile.kore")
  IO.println (← verdict "f2-examples/iot.kompile.kore")
  IO.println (← verdict "f2-examples/sortlabel.kompile.kore"
    (addSortAttr "SortFoo" ⟨⟨⟨"nat"⟩⟩, [], [.string "8"]⟩))
