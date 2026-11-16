/-
  An `[owise]` equation beside a `non-executable` one, read from K 7.1.337 kompile's KORE. Run from
  the package root: `lake env lean test/OwiseNonExecutable.lean`.
  - `f2-examples/owisene.kompile.kore` (`owisene.k`): `choose(a, Y) = Y`, `choose(b, Y) = Y`
    [non-executable], `choose(X, _) = X` [owise]. kompile's `[owise]` premise negates the first
    equation only. The `non-executable` equation is an axiom of the text, read as an `aside`
    clause: one no clause's priority premise negates. Read.
  - with the `non-executable` attribute dropped: the premise is not kompile's form for the
    equations it stands beside (`exclusionShape`).
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The text without any axiom's `non-executable` attribute. -/
def dropNonExec (k : Kore.Definition) : Kore.Definition :=
  let sent := fun (s : Kore.Sentence) => match s with
    | .axiom a => .axiom { a with attributes := a.attributes.filter (·.head.ident.name != "non-executable") }
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`). -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse (edit k) with
    | .ok _ => "read"
    | .error r => s!"{r.head}: {r.reason.name}"

/--
info: read
Lblchoose: exclusionShape
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/owisene.kompile.kore")
  IO.println (← verdict "f2-examples/owisene.kompile.kore" dropNonExec)
