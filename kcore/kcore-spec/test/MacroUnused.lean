/-
  Macro and alias symbols a text declares and does not apply, read from K 7.1.337 kompile's KORE.
  Run from the package root: `lake env lean test/MacroUnused.lean`.
  - `f2-examples/mlmacro.kompile.kore` (`mlmacro.k`, the construct fixture e2-macro): `m1(Int) [macro]`,
    `m2(Int) [macro-rec]`, `a1(Int) [alias]`, `a2(Int) [alias-rec]` with one rule each, and
    `rule f(X) => m1(X) +Int m2(X) +Int a1(X) +Int a2(X)`. kompile has expanded the four in `f`'s
    equation and writes no axiom for their rules: the text holds their four declarations and no
    application of them. A declaration is part of the reading only through an application, so each
    is not read (`unread macroUnused`), no other sentence is classified so, and the text is read
    with nothing unaccounted: `f`'s equation is the one clause of `f`, applying none of the four.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The reader's verdict on the text at `path`: the class of the declaration of each symbol of
`names`, the number of sentences classified `unread macroUnused`, and the refusal, or the sentences
unaccounted and whether a clause of a function applies a symbol of `names`. -/
def verdict (path : String) (names : List String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let decl := ((k.modules.getLast?.map (·.sentences)).getD []).filterMap fun s => match s with
      | .symbol x => if names.contains x.symbol.ident.ident.name then
          some (x.symbol.ident.ident.name, (Parse.classifyShape s).name) else none
      | _ => none
    let n := ((Parse.classCounts k).filter fun (c, _) => c == "unread macroUnused").map (·.2)
    return s!"{decl}; {n}; " ++ match Parse.parse k with
      | .ok d =>
        let applied := d.sem.fns.any fun fn => fn.clauses.any fun cl =>
          (Term.heads cl.rhs).any fun g => names.contains (d.sem.symName g)
        s!"read; unaccounted {(Parse.unconsumed k d).map (·.detail)}; functions {d.sem.fns.length}; applied {applied}"
      | .error r => s!"{r.reason.name} {r.detail}"

/--
info: [(Lbla1, unread macroUnused), (Lbla2, unread macroUnused), (Lblm1, unread macroUnused), (Lblm2, unread macroUnused)]; [4]; read; unaccounted []; functions 1; applied false
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/mlmacro.kompile.kore" ["Lblm1", "Lblm2", "Lbla1", "Lbla2"])
