/-
  The BOOL simplifications on `f2-examples/ens.kompile.kore`, entailed at values
  (`EntailsAtValues`, direction Ev) for every interpretation H, each from the library's one
  statement of the equation (`KcoreSpec/LibEvBool.lean`). These are the text's `simplification`
  sentences with a Bool result that are term equations and hold no injection.
  Run from the package root: `lake env lean test/LibEvBoolEns.lean`.

  - 181 (`B andBool true => B`, domains.md 1142): `ev181`.
  - 182 (`_ andBool false => false`, domains.md 1144): `ev182`.
  - 185 (`K andThenBool true => K`, domains.md 1147): `ev185`.
  - 186 (`_ andThenBool false => false`, domains.md 1149): `ev186`.
  - 190 (`B impliesBool false => notBool B`, domains.md 1168): `ev190`.
  - 191 (`_ impliesBool true => true`, domains.md 1167): `ev191`.
  - 196 (`B orBool false => B`, domains.md 1158): `ev196`.
  - 197 (`_ orBool true => true`, domains.md 1156): `ev197`.
  - 200 (`K orElseBool false => K`, domains.md 1163): `ev200`.
  - 201 (`_ orElseBool true => true`, domains.md 1161): `ev201`.
  - 205 (`B xorBool false => B`, domains.md 1152): `ev205`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvBoolEns

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

theorem ev181 (H : HookParams) : EntailsAtValues (cH H) U.ax181 (trS U.ax181).pat := by
  rw [(by decide +kernel : (trS U.ax181).pat = (trAxiom [] [] U.ax181).pat)]
  exact LibEv.bAndTrue_ev (coreOKH H) (shapesOKH H) U.ax181 (by decide +kernel) (by decide +kernel)

theorem ev182 (H : HookParams) : EntailsAtValues (cH H) U.ax182 (trS U.ax182).pat := by
  rw [(by decide +kernel : (trS U.ax182).pat = (trAxiom [] [] U.ax182).pat)]
  exact LibEv.bAndFalse_ev (coreOKH H) (shapesOKH H) U.ax182 (by decide +kernel) (by decide +kernel)

theorem ev185 (H : HookParams) : EntailsAtValues (cH H) U.ax185 (trS U.ax185).pat := by
  rw [(by decide +kernel : (trS U.ax185).pat = (trAxiom [] [] U.ax185).pat)]
  exact LibEv.bAndThenTrue_ev (coreOKH H) (shapesOKH H) U.ax185 (by decide +kernel) (by decide +kernel)

theorem ev186 (H : HookParams) : EntailsAtValues (cH H) U.ax186 (trS U.ax186).pat := by
  rw [(by decide +kernel : (trS U.ax186).pat = (trAxiom [] [] U.ax186).pat)]
  exact LibEv.bAndThenFalse_ev (coreOKH H) (shapesOKH H) U.ax186 (by decide +kernel) (by decide +kernel)

theorem ev190 (H : HookParams) : EntailsAtValues (cH H) U.ax190 (trS U.ax190).pat := by
  rw [(by decide +kernel : (trS U.ax190).pat = (trAxiom [] [] U.ax190).pat)]
  exact LibEv.bImpliesFalse_ev (coreOKH H) (shapesOKH H) U.ax190 (by decide +kernel) (by decide +kernel)

theorem ev191 (H : HookParams) : EntailsAtValues (cH H) U.ax191 (trS U.ax191).pat := by
  rw [(by decide +kernel : (trS U.ax191).pat = (trAxiom [] [] U.ax191).pat)]
  exact LibEv.bImpliesTrue_ev (coreOKH H) (shapesOKH H) U.ax191 (by decide +kernel) (by decide +kernel)

theorem ev196 (H : HookParams) : EntailsAtValues (cH H) U.ax196 (trS U.ax196).pat := by
  rw [(by decide +kernel : (trS U.ax196).pat = (trAxiom [] [] U.ax196).pat)]
  exact LibEv.bOrFalse_ev (coreOKH H) (shapesOKH H) U.ax196 (by decide +kernel) (by decide +kernel)

theorem ev197 (H : HookParams) : EntailsAtValues (cH H) U.ax197 (trS U.ax197).pat := by
  rw [(by decide +kernel : (trS U.ax197).pat = (trAxiom [] [] U.ax197).pat)]
  exact LibEv.bOrTrue_ev (coreOKH H) (shapesOKH H) U.ax197 (by decide +kernel) (by decide +kernel)

theorem ev200 (H : HookParams) : EntailsAtValues (cH H) U.ax200 (trS U.ax200).pat := by
  rw [(by decide +kernel : (trS U.ax200).pat = (trAxiom [] [] U.ax200).pat)]
  exact LibEv.bOrElseFalse_ev (coreOKH H) (shapesOKH H) U.ax200 (by decide +kernel) (by decide +kernel)

theorem ev201 (H : HookParams) : EntailsAtValues (cH H) U.ax201 (trS U.ax201).pat := by
  rw [(by decide +kernel : (trS U.ax201).pat = (trAxiom [] [] U.ax201).pat)]
  exact LibEv.bOrElseTrue_ev (coreOKH H) (shapesOKH H) U.ax201 (by decide +kernel) (by decide +kernel)

theorem ev205 (H : HookParams) : EntailsAtValues (cH H) U.ax205 (trS U.ax205).pat := by
  rw [(by decide +kernel : (trS U.ax205).pat = (trAxiom [] [] U.ax205).pat)]
  exact LibEv.bXorFalse_ev (coreOKH H) (shapesOKH H) U.ax205 (by decide +kernel) (by decide +kernel)

end KCore.LibEvBoolEns

/-- info: 'KCore.LibEvBoolEns.ev181' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolEns.ev181
/-- info: 'KCore.LibEvBoolEns.ev182' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolEns.ev182
/-- info: 'KCore.LibEvBoolEns.ev185' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolEns.ev185
/-- info: 'KCore.LibEvBoolEns.ev186' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolEns.ev186
/-- info: 'KCore.LibEvBoolEns.ev190' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolEns.ev190
/-- info: 'KCore.LibEvBoolEns.ev191' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolEns.ev191
/-- info: 'KCore.LibEvBoolEns.ev196' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolEns.ev196
/-- info: 'KCore.LibEvBoolEns.ev197' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolEns.ev197
/-- info: 'KCore.LibEvBoolEns.ev200' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolEns.ev200
/-- info: 'KCore.LibEvBoolEns.ev201' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolEns.ev201
/-- info: 'KCore.LibEvBoolEns.ev205' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolEns.ev205
