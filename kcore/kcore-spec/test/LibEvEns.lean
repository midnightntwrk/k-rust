/-
  Library equations entailed at values (`EntailsAtValues`, direction Ev) on
  `f2-examples/ens.kompile.kore`, for every interpretation H, each from the library's one statement
  of the equation (`KcoreSpec/LibEvInt.lean`): the text's axiom is compared with the equation's
  pattern over the registry's names, and its translation with the text's declarations with the
  translation `Eqn.entailed` is about.
  Run from the package root: `lake env lean test/LibEvEns.lean`.

  - 156 (`X %Int N => X requires 0 <=Int X andBool X <Int N`, domains.md 1377): `ev156`.
  - 158 (`I +Int B => B +Int I`, 1415): `ev158`.
  - 159 (`I +Int 0 => I`, 1373): `ev159`.
  - 165 (`A -Int I => A +Int (0 -Int I)`, 1416): `ev165`.
  - 166 (`I -Int 0 => I`, 1374): `ev166`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"
user_axioms U from "f2-examples/ens.kompile.kore" module "ENS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

theorem ev156 (H : HookParams) : EntailsAtValues (cH H) U.ax156 (trS U.ax156).pat := by
  rw [(by decide +kernel : (trS U.ax156).pat = (trAxiom [] [] U.ax156).pat)]
  exact LibEv.tmodSmall_ev (coreOKH H) (shapesOKH H) U.ax156 (by decide +kernel) (by decide +kernel)

theorem ev158 (H : HookParams) : EntailsAtValues (cH H) U.ax158 (trS U.ax158).pat := by
  rw [(by decide +kernel : (trS U.ax158).pat = (trAxiom [] [] U.ax158).pat)]
  exact LibEv.addComm_ev (coreOKH H) (shapesOKH H) U.ax158 (by decide +kernel) (by decide +kernel)

theorem ev159 (H : HookParams) : EntailsAtValues (cH H) U.ax159 (trS U.ax159).pat := by
  rw [(by decide +kernel : (trS U.ax159).pat = (trAxiom [] [] U.ax159).pat)]
  exact LibEv.addZero_ev (coreOKH H) (shapesOKH H) U.ax159 (by decide +kernel) (by decide +kernel)

theorem ev165 (H : HookParams) : EntailsAtValues (cH H) U.ax165 (trS U.ax165).pat := by
  rw [(by decide +kernel : (trS U.ax165).pat = (trAxiom [] [] U.ax165).pat)]
  exact LibEv.subAsAdd_ev (coreOKH H) (shapesOKH H) U.ax165 (by decide +kernel) (by decide +kernel)

theorem ev166 (H : HookParams) : EntailsAtValues (cH H) U.ax166 (trS U.ax166).pat := by
  rw [(by decide +kernel : (trS U.ax166).pat = (trAxiom [] [] U.ax166).pat)]
  exact LibEv.subZero_ev (coreOKH H) (shapesOKH H) U.ax166 (by decide +kernel) (by decide +kernel)

end KCore.LibEvEns

#check @KCore.LibEv.den_val
#check @KCore.LibEv.Eqn.entailed
#check @KCore.LibEv.Eqn.entailed_reg
/-- info: 'KCore.LibEvEns.ev156' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvEns.ev156
/-- info: 'KCore.LibEvEns.ev158' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvEns.ev158
/-- info: 'KCore.LibEvEns.ev159' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvEns.ev159
/-- info: 'KCore.LibEvEns.ev165' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvEns.ev165
/-- info: 'KCore.LibEvEns.ev166' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvEns.ev166
