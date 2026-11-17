/-
  A cell sort below a sort of the definition, read from K 7.1.337 kompile's own KORE. Run from the
  package root: `lake env lean test/CellSubsort.lean`.
  - `f2-examples/cellsub.kompile.kore` (`cellsub.k`, after K's checks/checkCellSortDeclOK.k):
    `syntax Pgm ::= KCell`. The subsort `KCell < Pgm` is between two sorts of the definition, the
    configuration's cell sort and a user sort; the reader reads it (`eventOf`). Read with nothing
    unaccounted and no inert axiom not induced; in the kernel the pair is a declared subsort and a
    k cell injected into `Pgm` is a value of `Pgm`.
  - the same text without the subsort axiom: `Pgm`'s no-junk axiom lists `inj{KCell, Pgm}`, which the
    definition then does not induce (`inertMismatch`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The text without its `subsort{SortKCell{}, SortPgm{}}` axiom. -/
def dropCellSubsort (k : Kore.Definition) : Kore.Definition :=
  let keep := fun (s : Kore.Sentence) => match s with
    | .axiom a => !(a.attributes.any fun ap => ap.head.ident.name == "subsort" &&
        decide (ap.sorts = [KoreAML.srt "KCell", KoreAML.srt "Pgm"]))
    | _ => true
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.filter keep }]).getD [] }

/-- The reader's verdict and the account's refusals on the text at `path` (edited by `edit`). -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let k := edit k
    return match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).length}; {(Parse.uninduced k d).map (·.reason.name)}"
      | .error r => r.reason.name

/--
info: read; unaccounted 0; []
read; unaccounted 0; [inertMismatch]
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/cellsub.kompile.kore")
  IO.println (← verdict "f2-examples/cellsub.kompile.kore" dropCellSubsort)

namespace CellSub

definition_of defn from "f2-examples/cellsub.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def kCell : Sym := 389
def go : Sym := 392
def kCellS : Srt := 33
def pgmS : Srt := 35

theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName go = "Lblgo" ∧
    c.sortName kCellS = "KCell" ∧ c.sortName pgmS = "Pgm" := by decide +kernel

theorem kcell_pgm : c.userSubsorts.contains (kCellS, pgmS) = true := by decide +kernel

/-- `<k>(go(1))` injected into `Pgm` is a value of `Pgm`. -/
theorem injected_value :
    c.sortOf (.inj kCellS pgmS (.ctor kCell [.ctor kseq [.inj pgmS Srt.kitem (.ctor go [.dv Srt.int (.int 1)]),
      .ctor dotk []]])) = some pgmS := by decide +kernel

end CellSub

#print axioms CellSub.injected_value
