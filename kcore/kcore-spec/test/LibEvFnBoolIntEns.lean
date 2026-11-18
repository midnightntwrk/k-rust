/-
  The equations of BOOL and INT in the function form entailed at values (`EntailsAtValues`,
  direction Ev) on `f2-examples/ens.kompile.kore`, for every interpretation H, each from the
  library's one statement of the equation (`KcoreSpec/LibEvFnBoolInt.lean`). With
  `test/LibEvFnEns.lean`'s 174, 180, 246, 247 these are the twenty sentences of ens from
  domains.md 1138 to 1170 and 1438 to 1457 that are read, are no `simplification` and apply only
  symbols Γ has. Of the other three of those lines that ens holds, 189 (1454, `dividesInt`)
  applies a symbol Γ does not have; 208 and 265 (1438, 1440, the bit ranges) are
  `test/LibEvFnBitRangeEns.lean`'s.
  Run from the package root: `lake env lean test/LibEvFnBoolIntEns.lean`.

  - 173 (`B1 =/=Bool B2 => notBool (B1 ==Bool B2)`, domains.md 1170): `fn173`.
  - 183 (`true andBool B => B`, 1141): `fn183`.
  - 184 (`false #as _Gen1 andThenBool _Gen0 => _Gen1`, 1148): `fn184`.
  - 187 (`true andThenBool K => K`, 1146): `fn187`.
  - 188 (`I1 divInt I2 => (I1 -Int (I1 modInt I2)) /Int I2 requires I2 =/=Int 0`, 1442): `fn188`.
  - 192 (`false impliesBool _ => true`, 1166): `fn192`.
  - 193 (`true impliesBool B => B`, 1165): `fn193`.
  - 198 (`false orBool B => B`, 1157): `fn198`.
  - 199 (`true orBool _ => true`, 1155): `fn199`.
  - 202 (`false orElseBool K => K`, 1162): `fn202`.
  - 203 (`true orElseBool _ => true`, 1160): `fn203`.
  - 204 (`B xorBool B => false`, 1153): `fn204`.
  - 206 (`false xorBool B => B`, 1151): `fn206`.
  - 209 (`freshInt(I) => I`, 1457): `fn209`.
  - 248 (`notBool false => true`, 1139): `fn248`.
  - 249 (`notBool true => false`, 1138): `fn249`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvFnBoolIntEns

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

theorem fn173 (H : HookParams) : EntailsAtValues (cH H) U.ax173 (trS U.ax173).pat := by
  rw [(by decide +kernel : (trS U.ax173).pat = (trAxiom [] [] U.ax173).pat)]
  exact LibEv.fnNeBool_ev (coreOKH H) (shapesOKH H) U.ax173 (by decide +kernel) (by decide +kernel)

theorem fn183 (H : HookParams) : EntailsAtValues (cH H) U.ax183 (trS U.ax183).pat := by
  rw [(by decide +kernel : (trS U.ax183).pat = (trAxiom [] [] U.ax183).pat)]
  exact LibEv.fnAndTrue_ev (coreOKH H) (shapesOKH H) U.ax183 (by decide +kernel) (by decide +kernel)

theorem fn184 (H : HookParams) : EntailsAtValues (cH H) U.ax184 (trS U.ax184).pat := by
  rw [(by decide +kernel : (trS U.ax184).pat = (trAxiom [] [] U.ax184).pat)]
  exact LibEv.fnAndThenFalse_ev (coreOKH H) (shapesOKH H) U.ax184 (by decide +kernel) (by decide +kernel)

theorem fn187 (H : HookParams) : EntailsAtValues (cH H) U.ax187 (trS U.ax187).pat := by
  rw [(by decide +kernel : (trS U.ax187).pat = (trAxiom [] [] U.ax187).pat)]
  exact LibEv.fnAndThenTrue_ev (coreOKH H) (shapesOKH H) U.ax187 (by decide +kernel) (by decide +kernel)

theorem fn188 (H : HookParams) : EntailsAtValues (cH H) U.ax188 (trS U.ax188).pat := by
  rw [(by decide +kernel : (trS U.ax188).pat = (trAxiom [] [] U.ax188).pat)]
  exact LibEv.fnDivInt_ev (coreOKH H) (shapesOKH H) U.ax188 (by decide +kernel) (by decide +kernel)

theorem fn192 (H : HookParams) : EntailsAtValues (cH H) U.ax192 (trS U.ax192).pat := by
  rw [(by decide +kernel : (trS U.ax192).pat = (trAxiom [] [] U.ax192).pat)]
  exact LibEv.fnImpliesFalse_ev (coreOKH H) (shapesOKH H) U.ax192 (by decide +kernel) (by decide +kernel)

theorem fn193 (H : HookParams) : EntailsAtValues (cH H) U.ax193 (trS U.ax193).pat := by
  rw [(by decide +kernel : (trS U.ax193).pat = (trAxiom [] [] U.ax193).pat)]
  exact LibEv.fnImpliesTrue_ev (coreOKH H) (shapesOKH H) U.ax193 (by decide +kernel) (by decide +kernel)

theorem fn198 (H : HookParams) : EntailsAtValues (cH H) U.ax198 (trS U.ax198).pat := by
  rw [(by decide +kernel : (trS U.ax198).pat = (trAxiom [] [] U.ax198).pat)]
  exact LibEv.fnOrFalse_ev (coreOKH H) (shapesOKH H) U.ax198 (by decide +kernel) (by decide +kernel)

theorem fn199 (H : HookParams) : EntailsAtValues (cH H) U.ax199 (trS U.ax199).pat := by
  rw [(by decide +kernel : (trS U.ax199).pat = (trAxiom [] [] U.ax199).pat)]
  exact LibEv.fnOrTrue_ev (coreOKH H) (shapesOKH H) U.ax199 (by decide +kernel) (by decide +kernel)

theorem fn202 (H : HookParams) : EntailsAtValues (cH H) U.ax202 (trS U.ax202).pat := by
  rw [(by decide +kernel : (trS U.ax202).pat = (trAxiom [] [] U.ax202).pat)]
  exact LibEv.fnOrElseFalse_ev (coreOKH H) (shapesOKH H) U.ax202 (by decide +kernel) (by decide +kernel)

theorem fn203 (H : HookParams) : EntailsAtValues (cH H) U.ax203 (trS U.ax203).pat := by
  rw [(by decide +kernel : (trS U.ax203).pat = (trAxiom [] [] U.ax203).pat)]
  exact LibEv.fnOrElseTrue_ev (coreOKH H) (shapesOKH H) U.ax203 (by decide +kernel) (by decide +kernel)

theorem fn204 (H : HookParams) : EntailsAtValues (cH H) U.ax204 (trS U.ax204).pat := by
  rw [(by decide +kernel : (trS U.ax204).pat = (trAxiom [] [] U.ax204).pat)]
  exact LibEv.fnXorSame_ev (coreOKH H) (shapesOKH H) U.ax204 (by decide +kernel) (by decide +kernel)

theorem fn206 (H : HookParams) : EntailsAtValues (cH H) U.ax206 (trS U.ax206).pat := by
  rw [(by decide +kernel : (trS U.ax206).pat = (trAxiom [] [] U.ax206).pat)]
  exact LibEv.fnXorFalse_ev (coreOKH H) (shapesOKH H) U.ax206 (by decide +kernel) (by decide +kernel)

theorem fn209 (H : HookParams) : EntailsAtValues (cH H) U.ax209 (trS U.ax209).pat := by
  rw [(by decide +kernel : (trS U.ax209).pat = (trAxiom [] [] U.ax209).pat)]
  exact LibEv.fnFreshInt_ev (coreOKH H) (shapesOKH H) U.ax209 (by decide +kernel) (by decide +kernel)

theorem fn248 (H : HookParams) : EntailsAtValues (cH H) U.ax248 (trS U.ax248).pat := by
  rw [(by decide +kernel : (trS U.ax248).pat = (trAxiom [] [] U.ax248).pat)]
  exact LibEv.fnNotFalse_ev (coreOKH H) U.ax248 (by decide +kernel) (by decide +kernel)

theorem fn249 (H : HookParams) : EntailsAtValues (cH H) U.ax249 (trS U.ax249).pat := by
  rw [(by decide +kernel : (trS U.ax249).pat = (trAxiom [] [] U.ax249).pat)]
  exact LibEv.fnNotTrue_ev (coreOKH H) U.ax249 (by decide +kernel) (by decide +kernel)

end KCore.LibEvFnBoolIntEns

/-- info: 'KCore.LibEvFnBoolIntEns.fn173' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn173
/-- info: 'KCore.LibEvFnBoolIntEns.fn183' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn183
/-- info: 'KCore.LibEvFnBoolIntEns.fn184' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn184
/-- info: 'KCore.LibEvFnBoolIntEns.fn187' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn187
/-- info: 'KCore.LibEvFnBoolIntEns.fn188' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn188
/-- info: 'KCore.LibEvFnBoolIntEns.fn192' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn192
/-- info: 'KCore.LibEvFnBoolIntEns.fn193' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn193
/-- info: 'KCore.LibEvFnBoolIntEns.fn198' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn198
/-- info: 'KCore.LibEvFnBoolIntEns.fn199' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn199
/-- info: 'KCore.LibEvFnBoolIntEns.fn202' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn202
/-- info: 'KCore.LibEvFnBoolIntEns.fn203' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn203
/-- info: 'KCore.LibEvFnBoolIntEns.fn204' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn204
/-- info: 'KCore.LibEvFnBoolIntEns.fn206' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn206
/-- info: 'KCore.LibEvFnBoolIntEns.fn209' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn209
/-- info: 'KCore.LibEvFnBoolIntEns.fn248' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn248
/-- info: 'KCore.LibEvFnBoolIntEns.fn249' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBoolIntEns.fn249
