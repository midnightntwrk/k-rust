/-
  Projections applied by the generated initializers of cells outside the top cell tree, read from
  K 7.1.337 kompile's own KORE. Run from the package root: `lake env lean test/InitProjection.lean`.
  - `f2-examples/starinit.kompile.kore` (`starinit.k`): below the cell `<t>` of multiplicity `*`, the
    cells `<v> $V:Int </v>` and `<p> $P:Cmd </p>`. Their initializers `initVCell`, `initPCell` are
    functions with the generated equations `initVCell(Init) = <v>(project:Int(Init[$V]))` and
    `initPCell(Init) = <p>(project:Cmd(Init[$P]))`. The reader numbers the projections these
    equations apply as it numbers those a user's axiom applies: `project:Int`, a library sort's, is a
    function with the text's equation, and so is `project:Cmd`, a user sort's (no parameter symbol
    of either name). `coreOK` holds.
  - the same text without `project:Cmd`'s declaration: the initializer applies a symbol the text
    does not declare, refused (`unknownSymbol`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The text without the declaration of the symbol `n`. -/
def dropDecl (n : String) (k : Kore.Definition) : Kore.Definition :=
  let keep := fun (s : Kore.Sentence) => match s with
    | .symbol x => x.symbol.ident.ident.name != n
    | _ => true
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.filter keep }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`): "read", or its refusal. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse (edit k) with
    | .ok _ => "read"
    | .error r => s!"{r.reason.name} {r.detail}"

/--
info: read
unknownSymbol Lblproject'Coln'Cmd
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/starinit.kompile.kore")
  IO.println (← verdict "f2-examples/starinit.kompile.kore" (dropDecl "Lblproject'Coln'Cmd"))

namespace StarInit

definition_of defn from "f2-examples/starinit.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- `project:Int` is a function of the definition, its one clause the text's equation
`project:Int(kseq(inj{Int,KItem}(V), dotk)) = V`; so is `project:Cmd`, with its equation
`project:Cmd(kseq(inj{Cmd,KItem}(V), dotk)) = V`; neither is a parameter symbol. -/
theorem projections :
    (c.fns.filter fun f => c.symName f.label == "Lblproject'Coln'Int").map (·.clauses.length) = [1] ∧
    (c.fns.filter fun f => c.symName f.label == "Lblproject'Coln'Cmd").map (·.clauses.length) = [1] ∧
    (c.params.any fun k => c.symName k.sig.name == "Lblproject'Coln'Cmd" ||
      c.symName k.sig.name == "Lblproject'Coln'Int") = false := by
  decide +kernel

/-- The initializers of `<v>` and `<p>` are functions with one clause each. -/
theorem inits :
    (c.fns.filter fun f => c.symName f.label == "LblinitVCell" || c.symName f.label == "LblinitPCell").map
      (·.clauses.length) = [1, 1] := by
  decide +kernel

tables_of T from "f2-examples/starinit.kompile.kore"

theorem T_eq : T = tables c := by decide +kernel

-- `faithCoreOK` by `decide_cheap`: each conjunct apart, the names on their codes
set_option maxHeartbeats 1000000 in
open Faithful Faithful.Model in
/-- `coreOK`, conjunct by conjunct, the sort checks from the tables. -/
theorem coreOK : c.coreOK = true :=
  Semantics.coreOK_of_T T_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide_cheap)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end StarInit

#print axioms StarInit.coreOK
#print axioms StarInit.projections
