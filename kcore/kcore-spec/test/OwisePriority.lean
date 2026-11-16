/-
  An `[owise]` equation beside another equation of priority 200 or more is refused by the reader
  (`owisePriority`), without the tie. The text's `[owise]` premise excludes every other equation,
  so it orders the `[owise]` equation after that one; the reading gives the `[owise]` equation
  priority 200, after the smaller priorities only, and puts two equations of one priority side by
  side. Run from the package root: `lake env lean test/OwisePriority.lean`.
  - `f2-examples/fprio-refused.kore` (krust's) and `fprio-refused.kompile.kore` (K 7.1.337's):
    `hi-top`, of priority 250, beside `hi-ow` `[owise]`;
  - the same text with `hi-top`'s priority made 200: refused for the same reason;
  - `f2-examples/fprio.kore`, whose `[owise]` equations are beside priorities 30 and 50 only: read.
-/
import KcoreSpec.Account

open KCore

/-- `priority{}("from")` made `priority{}("to")` on the user module's axioms. -/
def setPriority (from_ to : String) (k : Kore.Definition) : Kore.Definition :=
  let attr := fun (ap : Kore.AppPattern) => match ap.head.ident.name, ap.args with
    | "priority", [.string v] => if v == from_ then { ap with args := [.string to] } else ap
    | _, _ => ap
  let sent := fun (s : Kore.Sentence) => match s with
    | .axiom a => .axiom { a with attributes := a.attributes.map attr }
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`): "read", or its refusal. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse (edit k) with
    | .ok _ => "read"
    | .error r => r.reason.name

/--
info: owisePriority
owisePriority
owisePriority
owisePriority
read
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/fprio-refused.kore")
  IO.println (← verdict "f2-examples/fprio-refused.kompile.kore")
  IO.println (← verdict "f2-examples/fprio-refused.kore" (setPriority "250" "200"))
  IO.println (← verdict "f2-examples/fprio-refused.kompile.kore" (setPriority "250" "200"))
  IO.println (← verdict "f2-examples/fprio.kore")
