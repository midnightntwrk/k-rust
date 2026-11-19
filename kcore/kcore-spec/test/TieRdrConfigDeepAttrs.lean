/-
  Part Attrs of the tie (C14) on `f2-examples/rdr-config-deep.kompile.kore`, test/TieRdrConfigDeep.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `TIEGEN_PROBE_TIMEOUT=3000 python3 -I test/constructs/tiegen.py rdr-config-deep --split --cons-head
  --wf-parts --sig-chunk-first 13 --account-sorted --heads-literal --heads-codes --chunk 50
  --attrs-blocks 50 --decl-parts --fn-blocks 27 --absent-file --decl-syms-literal --nojunk-eq
  --nojunk-blocks 25 --sig-positions --fnfun-chunk 34`;
  run from the package root: `lake env lean -j1 test/TieRdrConfigDeepAttrs.lean`
  (717 s, peak 7.6 GiB under a 12 GiB scope with one Lean thread).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRdrConfigDeep

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rdr-config-deep.kompile.kore"
definition_of defn from "f2-examples/rdr-config-deep.kompile.kore"
user_axioms U from "f2-examples/rdr-config-deep.kompile.kore" module "RDR-CONFIG-DEEP"

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

end KCore.TieRdrConfigDeep

#check @KCore.TieRdrConfigDeep.attrs_agree
#print axioms KCore.TieRdrConfigDeep.attrs_agree
