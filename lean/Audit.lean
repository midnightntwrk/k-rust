/-
`lake exe krust-audit`: the axiom audit behind `scripts/lean-check.sh`.

It imports the built `KRust` library, enumerates every declaration whose module is `KRust` or
lies under `KRust.`, and fails when
  * any such declaration depends on `sorryAx` (written `sorry` or `admit`, or an elaboration
    error that Lean replaced by `sorry`),
  * any such declaration is an `axiom` (assumptions are named hypotheses of theorems), or
  * any such theorem depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`
    (for example an `axiom` added by a module).
The declarations are read from the environment, not from a hand-kept list.
Exit codes: 0 ok, 1 check failed.
-/
import Lean

open Lean

/-- The axioms a `KRust` theorem may depend on: the three axioms of Lean's standard foundations. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether a module belongs to the `KRust` library. -/
def isKRustModule (module : Name) : Bool :=
  module == `KRust || (`KRust).isPrefixOf module

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `KRust }] {} (trustLevel := 0)
  let mut failures : Array String := #[]
  let mut theorems := 0
  let mut declarations := 0
  for (name, info) in env.constants.map₁.toList do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let some module := env.header.moduleNames[moduleIdx.toNat]? | continue
    unless isKRustModule module do continue
    declarations := declarations + 1
    let (axioms, _) ← (collectAxioms name : CoreM (Array Name)).toIO
      { fileName := "<krust-audit>", fileMap := default } { env }
    if axioms.contains ``sorryAx then
      failures := failures.push s!"{name} ({module}) uses sorry"
    if let .axiomInfo _ := info then
      failures := failures.push s!"{name} ({module}) is an axiom; state it as a named hypothesis"
    if let .thmInfo _ := info then
      theorems := theorems + 1
      let extra := axioms.filter (fun ax => ax != ``sorryAx && !allowedAxioms.contains ax)
      unless extra.isEmpty do
        failures := failures.push s!"{name} ({module}) depends on axioms {extra.toList}"
  if declarations == 0 then
    IO.eprintln "krust-audit: no declarations found in the KRust modules"
    return 1
  for failure in failures do
    IO.eprintln s!"krust-audit: {failure}"
  if failures.isEmpty then
    IO.println s!"krust-audit: ok, {declarations} declarations, {theorems} theorems, axioms within {allowedAxioms}"
    return 0
  return 1
