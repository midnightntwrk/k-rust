/-
  The instances of a user's sort-parametric function, read from K 7.1.337 kompile's KORE. Run from
  the package root: `lake env lean test/ParametricInstance.lean`.
  In KORE the instances of a sort-parametric symbol are distinct symbols, related by no sentence
  the text does not state. Each instance a read sentence applies is a symbol of the definition's own:
  a function whose clauses are the equations the text states at that instance, or, where it states
  none, a parameter (total when the declaration is).
  - `f2-examples/parsel.kompile.kore` (`parsel.k`): `syntax {S} S ::= sel(Bool, S, S) [function]`,
    its two equations written by kompile at `sel{K}`, a rule applying `sel{Int}`: `sel{K}` a function
    with two clauses, `sel{Int}` a parameter. Nothing unaccounted, `coreOK` (decided by the compiled
    `coreOK`, not in the kernel).
  - `f2-examples/parsel-int.kompile.kore` (`parsel-int.k`): the equations' variables at Int, which
    kompile writes at `sel{Int}`: `sel{Int}` a function with the two clauses, no parameter.
  - `f2-examples/parsel-tot.kompile.kore` (`parsel-tot.k`): `idp` declared `total` (one `functional`
    axiom quantified over the sort variable), its equation at `idp{K}`, applied at `idp{Int}`:
    `idp{K}` a total function, `idp{Int}` a total parameter.
  - `parsel` with the rule's application at a sort the text does not declare: refused at the rule
    (`parametricSymbol`).
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The reader's verdict on the text at `path` (its text edited by `edit`): the user functions
with their clause counts and totality, the user parameters with their totality, what is
unaccounted, `coreOK`; or the refusal. -/
def verdict (path : String) (edit : String → String := id) : IO String := do
  match Kore.parseDefinition (edit (← IO.FS.readFile path)) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    return match Parse.parse k with
      | .ok d =>
        let fns := d.sem.fns.map fun f => (d.sem.symName f.label, f.clauses.length, f.total)
        let ps := (withPres d.sem.params d.pres.params).map fun (p, pp) => (d.sem.symName p.sig.name, pp.total)
        s!"read; fns {fns}; params {ps}; unaccounted {(Parse.unconsumed k d).map (·.detail)}; coreOK {d.sem.coreOK}"
      | .error r => s!"{r.reason.name} {r.detail}"

/--
info: read; fns [(Lblsel{K}, (2, false))]; params [(Lblsel{Int}, false)]; unaccounted []; coreOK true
read; fns [(Lblsel{Int}, (2, false))]; params []; unaccounted []; coreOK true
read; fns [(Lblidp{K}, (1, true))]; params [(Lblidp{Int}, true)]; unaccounted []; coreOK true
parametricSymbol Lblsel
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/parsel.kompile.kore")
  IO.println (← verdict "f2-examples/parsel-int.kompile.kore")
  IO.println (← verdict "f2-examples/parsel-tot.kompile.kore")
  IO.println (← verdict "f2-examples/parsel.kompile.kore" fun s =>
    s.replace "Lblsel{SortInt{}}" "Lblsel{SortNope{}}")
