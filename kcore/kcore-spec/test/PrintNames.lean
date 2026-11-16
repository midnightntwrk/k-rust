/-
  Prints the numbers F2's parse gives named sorts and symbols of a KORE text, as Lean constants
  (compiled; what the generator of ARCHITECTURE.md §3.8 writes as a definition's readable names):

      lean --run test/PrintNames.lean KORE NAMESPACE sym:CONST=NAME sort:CONST=NAME ...
-/
import KcoreSpec.Parse
open KCore

def main (argv : List String) : IO UInt32 := do
  let path :: ns :: specs := argv | IO.eprintln "usage: PrintNames KORE NAMESPACE (sym|sort):CONST=NAME..."; return 2
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | IO.eprintln s!"{path}: KORE does not parse"; return 1
  let .ok d := Parse.parse k | IO.eprintln s!"{path}: KCore's parse refuses it"; return 1
  IO.println s!"namespace {ns}"
  for spec in specs do
    let [kind, rest] := spec.splitOn ":" | IO.eprintln s!"bad {spec}"; return 2
    let c :: nameParts := rest.splitOn "=" | IO.eprintln s!"bad {spec}"; return 2
    let name := "=".intercalate nameParts
    let n? := if kind == "sym" then
        (List.range (nRegSyms + d.sem.symNames.length)).find? (d.sem.symName · == name)
      else (List.range (nRegSorts + d.sem.sortNames.length)).find? (d.sem.sortName · == name)
    let some n := n? | IO.eprintln s!"{path}: no {kind} {name}"; return 1
    IO.println s!"/-- `{name}` -/\n@[match_pattern, reducible] def {c} : {if kind == "sym" then "Sym" else "Srt"} := {n}"
  IO.println s!"end {ns}"
  return 0
