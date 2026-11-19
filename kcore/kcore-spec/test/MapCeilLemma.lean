/-
  MAP's module whole in a text without the definedness lemma of a map concatenation, read from K
  7.1.337 kompile's KORE. Run from the package root: `lake env lean test/MapCeilLemma.lean`.
  - `f2-examples/mapl.kompile.kore` (`mapl.k`, `--backend llvm`): the text holds MAP's sentences
    (the installation's `domains.md` as `Source`) and not the lemma
    `#Ceil(K0 |-> K1 Rest) = (K0 in_keys(Rest) = false) ∧ #Ceil(K1)` [simplification], which MAP's
    text in the library holds without a place. The lemma is no sentence of MAP's file and states
    nothing the reading reads (`inert simplification`), so the account does not require it
    (`Parse.missingBuiltin`): read, nothing unaccounted, MAP whole.
  - with a sentence of MAP's file dropped (the declaration of `Map:update`): MAP is not whole
    (`builtinIncomplete`, MAP).
  - in the kernel, `coreOK` holds.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The text without the hooked symbol `n`'s declaration. -/
def dropHooked (n : String) (k : Kore.Definition) : Kore.Definition :=
  let keep := fun (s : Kore.Sentence) => match s with
    | .hookedSymbol x => x.symbol.ident.ident.name != n
    | _ => true
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.filter keep }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`): the refusal, or the sentences
unaccounted and the module of each library sentence the text lacks. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let k := edit k
    return match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).map (·.detail)}; missing {(Parse.missingBuiltin k d).map (·.head)}"
      | .error r => s!"{r.reason.name} {r.detail}"

/--
info: read; unaccounted []; missing []
read; unaccounted []; missing [MAP]
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/mapl.kompile.kore")
  IO.println (← verdict "f2-examples/mapl.kompile.kore" (dropHooked "LblMap'Coln'update"))

namespace MapL

definition_of defn from "f2-examples/mapl.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

tables_of T from "f2-examples/mapl.kompile.kore"

theorem T_eq : T = tables c := by decide +kernel

-- `faithCoreOK` by `decide_cheap`: each conjunct apart, the names on their codes
set_option maxHeartbeats 1000000 in
open Faithful Faithful.Model in
/-- `coreOK`, conjunct by conjunct, the sort checks from the tables. -/
theorem coreOK : c.coreOK = true :=
  Semantics.coreOK_of_T T_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide_cheap)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MapL

#print axioms MapL.coreOK
