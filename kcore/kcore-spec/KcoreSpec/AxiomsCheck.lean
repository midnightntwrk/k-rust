/-
  The axioms check (checked layer; a meta program, not part of the specification): every
  declaration of a scope depends on no axiom but `propext`, `Classical.choice` and `Quot.sound`
  (`collectAxioms`), so none uses `sorryAx` (a `sorry`), an `axiom` of its own, or
  `Lean.ofReduceBool` (`native_decide`). An error names the declarations and their other axioms
  (the first 20); otherwise one line gives the count.

      #axioms_modules P₁ P₂ …   the declarations of the imported modules whose name has one of the
                                prefixes P₁, P₂, … (test/Axioms.lean: the library; a row package)
      #axioms_here              the declarations of the current file (a test file, the command
                                appended after its text)

  What no declaration holds is not checked: an `example` leaves no constant in the environment,
  so the axioms its proof uses are not seen here (the textual tripwire of test/release.sh covers
  that). `#axioms_modules` fails when the scope holds no declaration; `#axioms_here` reports a
  count of 0 as such.
-/
import Lean

namespace KCore.AxiomsCheck
open Lean Elab Command

/-- Lean's three axioms, the only ones admitted. -/
def stdAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The declarations among `cs` that depend on an axiom outside `stdAxioms`, with those axioms. -/
def outside (cs : List Name) : CommandElabM (Array (Name × Array Name)) := do
  let mut bad := #[]
  for c in cs do
    let other := (← collectAxioms c).filter (!stdAxioms.contains ·)
    unless other.isEmpty do bad := bad.push (c, other)
  return bad

/-- The error naming the failing declarations, or the line with the count. -/
def report (what : String) (n : Nat) (bad : Array (Name × Array Name)) : CommandElabM Unit := do
  unless bad.isEmpty do
    let shown := bad.toList.take 20 |>.map fun (c, a) => m!"{c}: {a.toList}"
    throwError m!"{bad.size} of {n} declarations of {what} depend on other axioms:{indentD (MessageData.joinSep shown Format.line)}"
  logInfo m!"axioms: {n} declarations of {what}, each within propext, Classical.choice, Quot.sound"

syntax (name := axiomsModules) "#axioms_modules" (ppSpace ident)+ : command
syntax (name := axiomsHere) "#axioms_here" : command

elab_rules : command
  | `(#axioms_modules $ps*) => do
    let prefixes := ps.map (·.getId)
    let env ← getEnv
    let cs := env.constants.map₁.toList.filterMap fun (c, _) => do
      let idx ← env.getModuleIdxFor? c
      let m := env.header.moduleNames[idx.toNat]!
      if prefixes.any (·.isPrefixOf m) then some c else none
    let what := s!"the {", ".intercalate (prefixes.toList.map toString)} modules"
    if cs.isEmpty then throwError "no declaration of {what} found"
    report what cs.length (← outside cs)
  | `(#axioms_here) => do
    let cs := (← getEnv).constants.map₂.toList.map (·.1)
    report "this file" cs.length (← outside cs)

end KCore.AxiomsCheck
