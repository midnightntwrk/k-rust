/-
  Part Attrs of the tie (C14) on `f2-examples/e2-cells-stream.kompile.kore`, test/TieE2CellsStream.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py e2-cells-stream --split`; run from the package root:
  `lake env lean -j1 test/TieE2CellsStreamAttrs.lean`.

  Measured alone (LEAN_NUM_THREADS=1, `lake env lean -j1`, a 12G memory scope): 148 s, peak
  3.7 GiB.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE2CellsStream

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-cells-stream.kompile.kore"
definition_of defn from "f2-examples/e2-cells-stream.kompile.kore"
user_axioms U from "f2-examples/e2-cells-stream.kompile.kore" module "E2-CELLS-STREAM"
user_axioms PreludeKseq from "f2-examples/e2-cells-stream.kompile.kore" module "KSEQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-! ## The attributes -/

/-- The conjuncts of `attrsAgree`, each its own decision; `ctors`, `fns` and
`hooks` over the symbol declarations (`symDeclsAt`) by blocks of 50, `prios` conjunct by
conjunct, each list by blocks of 50 (`decide_cheap`). Each block is a decision with a
heartbeat budget of its own, and their number is not known here: the theorems set no bound of
their own (the run's time limit bounds them). -/
theorem attrs_colls : AttrsAgree.colls kore defn.sem = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem attrs_ctors : AttrsAgree.ctors kore defn.sem = true := by
  unfold AttrsAgree.ctors; decide_cheap 50
set_option maxHeartbeats 0 in
theorem attrs_fns : AttrsAgree.fns kore defn.sem = true := by
  unfold AttrsAgree.fns; decide_cheap 50
set_option maxHeartbeats 0 in
theorem attrs_hooks : AttrsAgree.hooks kore defn.sem = true := by
  unfold AttrsAgree.hooks; decide_cheap 50
set_option maxHeartbeats 0 in
theorem attrs_prios : AttrsAgree.prios kore defn = true := by
  unfold AttrsAgree.prios; dsimp only; decide_cheap 50

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. -/
theorem attrs_agree : attrsAgree kore defn = true := by
  unfold attrsAgree
  rw [attrs_ctors, attrs_fns, attrs_hooks, attrs_colls, attrs_prios]
  rfl

end KCore.TieE2CellsStream

#check @KCore.TieE2CellsStream.attrs_agree
#print axioms KCore.TieE2CellsStream.attrs_agree
