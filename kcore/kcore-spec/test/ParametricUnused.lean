/-
  A sort-parametric symbol of the user's, read from K 7.1.337 kompile's KORE. Run from the package
  root: `lake env lean test/ParametricUnused.lean`.
  - `f2-examples/parsym.kompile.kore` (`parsym.k`): `syntax {S} S ::= pair(S, S) [function]`, KORE's
    `symbol pair{S}(S, S) : S`, applied only in a lemma. The declaration is part of the reading only
    through the instances a read sentence applies, so it is not read (`unread parametricUnused`), the
    lemma is inert, and the text is read with nothing unaccounted.
  - `f2-examples/parsym-app.kompile.kore` (`parsym-app.k`): a rule applies `pair{C}`, an instance at
    which the text states no equation: read, a parameter (test/ParametricInstance.lean).
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The reader's verdict on the text at `path`: the class of `pair`'s declaration, and the refusal
or the sentences unaccounted. -/
def verdict (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let decl := ((k.modules.getLast?.map (·.sentences)).getD []).filterMap fun s => match s with
      | .symbol x => if x.symbol.ident.ident.name == "Lblpair" then some (Parse.classifyShape s).name else none
      | _ => none
    return s!"{decl}; " ++ match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).map (·.detail)}"
      | .error r => s!"{r.reason.name} {r.detail}"

/--
info: [unread parametricUnused]; read; unaccounted []
[unread parametricUnused]; read; unaccounted []
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/parsym.kompile.kore")
  IO.println (← verdict "f2-examples/parsym-app.kompile.kore")
