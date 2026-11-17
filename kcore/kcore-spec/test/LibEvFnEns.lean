/-
  Library equations in the function form entailed at values (`EntailsAtValues`, direction Ev) on
  `f2-examples/ens.kompile.kore`, for every interpretation H, each from the library's one statement
  of the equation (`KcoreSpec/LibEvFnLib.lean`, through `LibEv.FnEqn.entailed_reg`): the text's
  axiom is compared with the equation's pattern over the registry's names, and its translation with
  the text's declarations with the translation `FnEqn.entailed` is about.
  Run from the package root: `lake env lean test/LibEvFnEns.lean`.

  - 174 (`I1 =/=Int I2 => notBool (I1 ==Int I2)`, domains.md 1453): `fn174`.
  - 180 (`false #as _Gen1 andBool _Gen0 => _Gen1`, 1143): `fn180`.
  - 246 (`minInt(I1, I2) => I1 requires I1 <Int I2`, 1450): `fn246`.
  - 247 (`minInt(I1, I2) => I2 requires I1 >=Int I2`, 1451): `fn247`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvFnEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"
user_axioms U from "f2-examples/ens.kompile.kore" module "ENS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide +kernel
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

theorem fn174 (H : HookParams) : EntailsAtValues (cH H) U.ax174 (trS U.ax174).pat := by
  rw [(by decide +kernel : (trS U.ax174).pat = (trAxiom [] [] U.ax174).pat)]
  exact LibEv.fnNeInt_ev (coreOKH H) (shapesOKH H) U.ax174 (by decide +kernel) (by decide +kernel)

theorem fn180 (H : HookParams) : EntailsAtValues (cH H) U.ax180 (trS U.ax180).pat := by
  rw [(by decide +kernel : (trS U.ax180).pat = (trAxiom [] [] U.ax180).pat)]
  exact LibEv.fnAndFalse_ev (coreOKH H) (shapesOKH H) U.ax180 (by decide +kernel) (by decide +kernel)

theorem fn246 (H : HookParams) : EntailsAtValues (cH H) U.ax246 (trS U.ax246).pat := by
  rw [(by decide +kernel : (trS U.ax246).pat = (trAxiom [] [] U.ax246).pat)]
  exact LibEv.fnMinLt_ev (coreOKH H) (shapesOKH H) U.ax246 (by decide +kernel) (by decide +kernel)

theorem fn247 (H : HookParams) : EntailsAtValues (cH H) U.ax247 (trS U.ax247).pat := by
  rw [(by decide +kernel : (trS U.ax247).pat = (trAxiom [] [] U.ax247).pat)]
  exact LibEv.fnMinGe_ev (coreOKH H) (shapesOKH H) U.ax247 (by decide +kernel) (by decide +kernel)

end KCore.LibEvFnEns

#check @KCore.LibEv.FnEqn.entailed
#check @KCore.LibEv.FnEqn.entailed_reg
/-- info: 'KCore.LibEvFnEns.fn174' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnEns.fn174
/-- info: 'KCore.LibEvFnEns.fn180' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnEns.fn180
/-- info: 'KCore.LibEvFnEns.fn246' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnEns.fn246
/-- info: 'KCore.LibEvFnEns.fn247' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnEns.fn247
