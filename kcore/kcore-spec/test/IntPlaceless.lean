/-
  A library sort declared again by the user, read from K 7.1.337 kompile's own KORE. Run from the
  package root: `lake env lean test/IntPlaceless.lean`.
  - `f2-examples/intre.kompile.kore` (`intre.k`): the user module declares `syntax Int` again (as
    wasm's wasm-data/int-type.k does), and kompile writes `hooked-sort SortInt{} [hasDomainValues{}(),
    hook{}("INT.Int")]` without `Source` or `Location`. That is, up to the place, the declaration of
    the library's `UNSIGNED-INT-SYNTAX`, so the reader imports that module (`placelessModule?`): Int
    is a library sort, `Int < Num` is read, nothing is unaccounted, and in the kernel an Int injected
    into `Num` is a value of `Num`.
  - the same text with the declaration's `hasDomainValues` attribute dropped: no library sentence,
    so the declaration is a hooked sort of the user's whose hook is no collection's, refused by name
    (`userHookedSort`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The declaration of `SortInt` without its `hasDomainValues` attribute. -/
def dropDomainValues (k : Kore.Definition) : Kore.Definition :=
  let sent := fun (s : Kore.Sentence) => match s with
    | .hookedSort x => if x.sort.ident.name == "SortInt" then
        .hookedSort { x with attributes := x.attributes.filter (·.head.ident.name != "hasDomainValues") }
      else .hookedSort x
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`), and the sentences unaccounted. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let k := edit k
    return match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).map (·.detail)}"
      | .error r => r.reason.name

/--
info: read; unaccounted []
userHookedSort
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/intre.kompile.kore")
  IO.println (← verdict "f2-examples/intre.kompile.kore" dropDomainValues)

namespace IntRe

definition_of defn from "f2-examples/intre.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def numS : Srt := 33

theorem names_ok : c.sortName numS = "Num" := by decide +kernel

/-- UNSIGNED-INT-SYNTAX is imported: Int is a library sort below KItem. -/
theorem int_library : c.lib.sortsBelowKItem.contains Srt.int = true := by decide +kernel

theorem int_num : c.userSubsorts.contains (Srt.int, numS) = true := by decide +kernel

/-- `5` injected into `Num` is a value of `Num`. -/
theorem injected_value : c.sortOf (.inj Srt.int numS (.dv Srt.int (.int 5))) = some numS := by
  decide +kernel

end IntRe

#print axioms IntRe.injected_value
