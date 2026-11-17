/-
  Attribute agreement (C14, layer 1) on kore.k's text as kompile wrote it
  (`examples/ref-kk/RefKk/definition.kore`), on the literals `kore` and `defn`. Nothing here reads
  `Parse.parse` or `emit`. Run from the package root: `lake env lean test/TieKkAttrs.lean`.

  - `attrs_agree`: `attrsAgree kore defn = true`, joined from its five conjuncts (constructors,
    functions, hooks, collection symbols, priorities), each its own kernel decision.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKk

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
definition_of defn from "examples/ref-kk/RefKk/definition.kore"

theorem attrs_ctors : AttrsAgree.ctors kore defn.sem = true := by decide +kernel
theorem attrs_fns : AttrsAgree.fns kore defn.sem = true := by decide +kernel
theorem attrs_hooks : AttrsAgree.hooks kore defn.sem = true := by decide +kernel
theorem attrs_colls : AttrsAgree.colls kore defn.sem = true := by decide +kernel
theorem attrs_prios : AttrsAgree.prios kore defn = true := by decide +kernel

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. -/
theorem attrs_agree : attrsAgree kore defn = true := by
  unfold attrsAgree
  rw [attrs_ctors, attrs_fns, attrs_hooks, attrs_colls, attrs_prios]
  rfl

end KCore.TieKk

#check @KCore.TieKk.attrs_agree
#print axioms KCore.TieKk.attrs_agree
