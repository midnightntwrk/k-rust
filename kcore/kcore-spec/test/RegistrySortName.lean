/-
  A user sort named like a library sort whose module the text does not import, read from K
  7.1.337 kompile's KORE. Run from the package root: `lake env lean test/RegistrySortName.lean`.
  - `f2-examples/rsn.kompile.kore` (`rsn.k`): `syntax Bytes ::= ".Bytes"` with INT imported and
    BYTES not; kompile writes the plain sort `sort SortBytes{} []`. Names are numbered registry
    first, so it would read as the library's Bytes, which no imported module declares: refused with
    a reason of its own (`registrySortName`).
  - the same text with every name holding `Bytes` renamed to `Bytez` (the sort, its constructor,
    predicate and projection): read.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The reader's verdict on the text at `path`, its text edited by `edit` first. -/
def verdict (path : String) (edit : String → String := id) : IO String := do
  match Kore.parseDefinition (edit (← IO.FS.readFile path)) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse k with
    | .ok _ => "read"
    | .error r => s!"{r.head}: {r.reason.name} {r.detail}"

/--
info: SortBytes: registrySortName Bytes
read
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/rsn.kompile.kore")
  IO.println (← verdict "f2-examples/rsn.kompile.kore" fun t => t.replace "Bytes" "Bytez")
