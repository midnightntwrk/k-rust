/-
  A user's equation of a symbol the registry interprets, read from K 7.1.337 kompile's KORE. Run
  from the package root: `lake env lean test/RegistryEquation.lean`.
  - `f2-examples/regeq.kompile.kore` (`regeq.k`, as K's regression test macro-rewrite):
    `rule (5 => 6) : _`, with `:` a macro for `ListItem(I) L`, is kompile's equation
    `_List_(ListItem(5), L) = _List_(ListItem(6), L)` of LIST's concatenation. The registry fixes
    `_List_`'s meaning (list concatenation), and no function of the definition has the equation as a
    clause: it is a user's sentence about a symbol whose value the registry gives
    (`Parse.regLemmaEqn`), which the reader does not put in `Γ` and neither claims true nor refuses
    for being false. The text is read with `_List_` as it is, and the equation is accounted for (no
    sentence unaccounted); it is owed at values (the account's class `user lemma at values`). Here
    it is false at every value of `L` (the two sides are lists whose first items differ), so `Γ` with
    it has no model and the text is not tied: a test of the reader's check, not a row's evidence.
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
info: read; unaccounted []
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/regeq.kompile.kore")
