/-
  The symbol declarations of `f2-examples/e2-cells-stream.kompile.kore` with a K builtin file's
  `Source`, without a `hook` attribute and without sort parameters, that name no symbol of Γ and
  are K-IO's: `#open/1`, `#stdin`, `#stdout` and `#stderr` (INT-COMMON's `_dividesInt_` is the
  fifth such declaration of the text; test/GenEqsNodirE2CellsStream.lean, `lackedDeclared_split`).
  Each is stated by the kernel's decision of `hasSym`,
  the definition of the tie's files (test/TieE2CellsStreamDecls.lean) on the same literals. A test file
  imports no test file, so this one repeats the literals and `hasSym`. Run from the package root:
  `lake env lean -j1 test/TieE2CellsStreamLacked.lean`.

  Measured alone (LEAN_NUM_THREADS=1, `lake env lean -j1`, a 12G memory scope): 45 s, peak 2.8 GiB.

  Their declarations' items are not among Γ's, and the sentences applying them (axioms 2811 to 2814)
  are of the tie's no-direction class (`account_absent`, test/TieE2CellsStreamAbsent.lean).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE2CellsStream

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-cells-stream.kompile.kore"
definition_of defn from "f2-examples/e2-cells-stream.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- Γ has a symbol under the name `n`. -/
noncomputable def hasSym (n : String) : Bool := (kernelSyms c).any fun k => c.symName k.name == n

/-- Γ has no symbol `#open/1` (`#open(_)`, of sort IOInt). -/
theorem lacked_open1 : hasSym "Lbl'Hash'open'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'String" = false := by
  decide +kernel

/-- Γ has no symbol `#stdin`. -/
theorem lacked_stdin : hasSym "Lbl'Hash'stdin'Unds'K-IO'Unds'Int" = false := by decide +kernel

/-- Γ has no symbol `#stdout`. -/
theorem lacked_stdout : hasSym "Lbl'Hash'stdout'Unds'K-IO'Unds'Int" = false := by decide +kernel

/-- Γ has no symbol `#stderr`. -/
theorem lacked_stderr : hasSym "Lbl'Hash'stderr'Unds'K-IO'Unds'Int" = false := by decide +kernel

end KCore.TieE2CellsStream

#check @KCore.TieE2CellsStream.lacked_open1
#check @KCore.TieE2CellsStream.lacked_stdin
#check @KCore.TieE2CellsStream.lacked_stdout
#check @KCore.TieE2CellsStream.lacked_stderr
#print axioms KCore.TieE2CellsStream.lacked_open1
#print axioms KCore.TieE2CellsStream.lacked_stdin
#print axioms KCore.TieE2CellsStream.lacked_stdout
#print axioms KCore.TieE2CellsStream.lacked_stderr
