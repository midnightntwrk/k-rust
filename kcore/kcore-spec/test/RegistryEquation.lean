/-
  A user's equation of a symbol the registry interprets, read from K 7.1.337 kompile's KORE. Run
  from the package root: `lake env lean test/RegistryEquation.lean`.
  - `f2-examples/regeq.kompile.kore` (`regeq.k`, as K's regression test macro-rewrite):
    `rule (5 => 6) : _`, with `:` a macro for `ListItem(I) L`, is kompile's equation
    `_List_(ListItem(5), L) = _List_(ListItem(6), L)` of LIST's concatenation. The registry fixes
    `_List_`'s meaning (list concatenation, under which the two sides are distinct lists), and no
    function of the definition has the equation as a clause: the equation is a premise about an
    interpreted symbol at every element of its sorts, which `Γ` does not state; refused
    (`hookEquation`), the symbol named.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The reader's verdict on the text at `path`: the refusal, or the sentences unaccounted. -/
def verdict (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse k with
    | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).map fun r => s!"{r.head}: {r.detail}"}"
    | .error r => s!"{r.reason.name} {r.detail}"

/--
info: hookEquation Lbl'Unds'List'Unds': a symbol of the registry
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/regeq.kompile.kore")
