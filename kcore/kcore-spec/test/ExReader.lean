/-
  The reader on rules whose right side is under `\exists` (`\rewrites(\and(lhs, req), \exists(x̄,
  \and(rhs, ens)))`), read from K 7.1.337 kompile's KORE (test/constructs/fixtures, the kompiled
  texts copied to f2-examples). Run from the package root: `lake env lean -j1 test/ExReader.lean`.

  The rule's existential variables are its `exs`, in the text's order of nesting. A rule
  `rulePlainEx` admits is read (`Parse.openRefusal` gives none); an existential variable the right
  side holds under no constructor, of an unconfined sort, is refused `openRight`.
  - `exrhs` (e3-vars): `c(_, _Y) => d(?Z:Int)`: read, `exs` the one variable `?Z`, under the
    constructor d (arm A).
  - `exvarstwo` (e3-vars-two): `c() => d(?Y:Int, ?Z:Int)`, written `\exists(?Y, \exists(?Z, …))`:
    read, `exs` `?Y` then `?Z`; with the binders swapped in the text (`swapped`), `?Z` then `?Y`.
  - `exvarsbool` (e3-vars-bool): `c() => d(?Z:Bool)`: read (arm A, and Bool is confined).
  - `exvarslist` (e3-vars-list): `L => ListItem(?V:Int) L`: `openRight`, `?V` under the list's
    symbols, which are no constructors, and Int unconfined.
  `rulesPlain` asks `rulePlainEx` of each rule (`Semantics.rulesPlain_iff_ex`), so the three read
  texts are well formed and have `coreOK` (`Vars.rule2` for e3-vars, by the kernel).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace ExReader

/-- The reader on a text: its first refusal, or each rule with existential variables (their names
in the order of `exs`, `rulePlainEx`, whether `openRefusal` gives none) and the definition's
failing `wf` conjuncts, `rulesPlain` and `coreOK`. -/
def show1 (n : String) : IO Unit := do
  match Kore.parseDefinition (← IO.FS.readFile s!"f2-examples/{n}.kompile.kore") with
  | .error e => IO.println s!"{n}: KORE read error {e}"
  | .ok k =>
    match (Parse.refusals k).find? (·.reason != .aliasDeclaration) with
    | some r => IO.println s!"{n}: {repr r.reason} {r.detail}"
    | none => match Parse.parse k with
      | .error r => IO.println s!"{n}: refused {repr r.reason} {r.detail}"
      | .ok d =>
        for ((r, p), i) in (d.sem.rules.zip d.pres.rules).zipIdx do
          if !r.exs.isEmpty then
            IO.println s!"{n} rule {i}: exs {r.exs} {r.exs.map fun j => p.names.getD j ""}; rulePlainEx {d.sem.rulePlainEx r}; openRefusal none {(Parse.openRefusal d.sem r p.names).isNone}"
        IO.println s!"{n}: wf failing {(d.report.filter (!·.2)).map (·.1)}; rulesPlain {d.sem.rulesPlain}; coreOK {d.sem.coreOK}"

/--
info: exrhs rule 2: exs [5] ['Ques'Z]; rulePlainEx true; openRefusal none true
exrhs: wf failing []; rulesPlain true; coreOK true
exvarstwo rule 0: exs [2, 3] ['Ques'Y, 'Ques'Z]; rulePlainEx true; openRefusal none true
exvarstwo: wf failing []; rulesPlain true; coreOK true
exvarsbool rule 0: exs [1] ['Ques'Z]; rulePlainEx true; openRefusal none true
exvarsbool: wf failing []; rulesPlain true; coreOK true
exvarslist: KCore.Parse.RefusalReason.openRight Var'Ques'V:Int: bound by \exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
-/
#guard_msgs in
#eval show IO Unit from do
  for n in ["exrhs", "exvarstwo", "exvarsbool", "exvarslist"] do show1 n

/-- The binders of exvarstwo's rule swapped, `\exists(?Z, \exists(?Y, …))`, the body unchanged:
`exs` follows the nesting (`?Z` then `?Y`), not the order in which the body first holds them. -/
def swapped : IO Unit := do
  let t ← IO.FS.readFile "f2-examples/exvarstwo.kompile.kore"
  let a := "(Var'Ques'Y:SortInt{},  \\exists{SortGeneratedTopCell{}} (Var'Ques'Z:SortInt{},"
  let b := "(Var'Ques'Z:SortInt{},  \\exists{SortGeneratedTopCell{}} (Var'Ques'Y:SortInt{},"
  match Kore.parseDefinition (t.replace a b) with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k => match Parse.parse k with
    | .error r => IO.println s!"refused {repr r.reason} {r.detail}"
    | .ok d =>
      let p := d.pres.rules.getD 0 default
      match d.sem.rules with
      | r :: _ => IO.println s!"swapped: changed {decide (t.replace a b ≠ t)}; exs {r.exs} {r.exs.map fun j => p.names.getD j ""}"
      | [] => IO.println "swapped: no rule"

/-- info: swapped: changed true; exs [3, 2] ['Ques'Z, 'Ques'Y] -/
#guard_msgs in
#eval swapped

/-! ## Kernel-checked: the read rules and their existential variables -/

namespace Vars

definition_of defn from "f2-examples/exrhs.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- **`c(_, _Y) => d(?Z:Int)`**: the rule 2 has the one existential variable 5, `?Z`, which the
left side and the `requires` do not hold; it is well sorted, `rulePlainEx` admits it (arm A: under
the constructor d) and `openRefusal` gives none; `rulesPlain` and `coreOK` hold of the text. -/
theorem rule2 :
    (c.rules[2]'(by decide +kernel)).exs = [5] ∧
    (defn.pres.rules.getD 2 default).names.getD 5 "" = "'Ques'Z" ∧
    c.ruleSorted (c.rules[2]'(by decide +kernel)) = true ∧
    c.rulePlainEx (c.rules[2]'(by decide +kernel)) = true ∧
    (Parse.openRefusal c (c.rules[2]'(by decide +kernel)) []).isNone = true ∧
    c.rulesPlain = true ∧ c.coreOK = true := by
  decide +kernel

end Vars

namespace Two

definition_of defn from "f2-examples/exvarstwo.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- **`\exists(?Y, \exists(?Z, …))`**: `exs` is `?Y` then `?Z`, the text's order of nesting. -/
theorem rule0 :
    (c.rules[0]'(by decide +kernel)).exs = [2, 3] ∧
    ((defn.pres.rules.getD 0 default).names.getD 2 "", (defn.pres.rules.getD 0 default).names.getD 3 "") =
      ("'Ques'Y", "'Ques'Z") ∧
    c.ruleSorted (c.rules[0]'(by decide +kernel)) = true ∧
    c.rulePlainEx (c.rules[0]'(by decide +kernel)) = true := by
  decide +kernel

end Two

/-- info: 'ExReader.Vars.rule2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vars.rule2
/-- info: 'ExReader.Two.rule0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Two.rule0

end ExReader
