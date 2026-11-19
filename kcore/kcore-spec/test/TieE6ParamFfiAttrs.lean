/-
  Part Attrs of the tie (C14) on `f2-examples/e6-param-ffi.kompile.kore`, test/TieE6ParamFfi.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py e6-param-ffi --split`; run from the package root:
  `lake env lean -j1 test/TieE6ParamFfiAttrs.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE6ParamFfi

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6-param-ffi.kompile.kore"
definition_of defn from "f2-examples/e6-param-ffi.kompile.kore"
user_axioms U from "f2-examples/e6-param-ffi.kompile.kore" module "E6-PARAM-FFI"
user_axioms PreludeKseq from "f2-examples/e6-param-ffi.kompile.kore" module "KSEQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-! ## The attributes -/

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. -/
theorem attrs_agree : attrsAgree kore defn = true := by decide +kernel

end KCore.TieE6ParamFfi

#check @KCore.TieE6ParamFfi.attrs_agree
#print axioms KCore.TieE6ParamFfi.attrs_agree
