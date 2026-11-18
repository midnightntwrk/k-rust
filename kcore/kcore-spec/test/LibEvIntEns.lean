/-
  The INT simplifications of three terms and of `modInt` on `f2-examples/ens.kompile.kore`, entailed
  at values (`EntailsAtValues`, direction Ev) for every interpretation H, each from the library's one
  statement of the equation (`KcoreSpec/LibEvInt.lean`), as test/LibEvEns.lean does for 156, 158,
  159, 165, 166. With those five, these are the text's `simplification` sentences with an Int
  result that are term equations over symbols Γ has and hold no injection.
  Run from the package root: `lake env lean test/LibEvIntEns.lean`.

  - 160 (`I1 +Int (B +Int I3) => B +Int (I1 +Int I3)`, domains.md 1419): `ev160`.
  - 161 (`I1 +Int (I2 +Int C) => (I1 +Int I2) +Int C`, domains.md 1421): `ev161`.
  - 162 (`I1 +Int (I2 -Int C) => (I1 +Int I2) -Int C`, domains.md 1422): `ev162`.
  - 163 (`(A +Int I2) +Int I3 => A +Int (I2 +Int I3)`, domains.md 1418): `ev163`.
  - 164 (`(I1 -Int B) +Int I3 => (I1 +Int I3) -Int B`, domains.md 1423): `ev164`.
  - 167 (`I1 -Int (B +Int I3) => (I1 -Int I3) -Int B`, domains.md 1420): `ev167`.
  - 168 (`I1 -Int (I2 +Int C) => (I1 -Int I2) -Int C`, domains.md 1424): `ev168`.
  - 169 (`I1 -Int (I2 -Int C) => (I1 -Int I2) +Int C`, domains.md 1425): `ev169`.
  - 170 (`(C -Int I2) -Int I3 => C -Int (I2 +Int I3)`, domains.md 1426): `ev170`.
  - 194 (`I1 modInt I2 => ((I1 %Int absInt(I2)) +Int absInt(I2)) %Int absInt(I2) requires I2 =/=Int 0`, domains.md 1445): `ev194`.
  - 195 (`X modInt N => X requires 0 <=Int X andBool X <Int N`, domains.md 1376): `ev195`.
  - 171 (`X <<Int 0 => X`, domains.md 1380): `ev171`.
  - 172 (`0 <<Int Y => 0 requires 0 <=Int Y`, domains.md 1381): `ev172`.
  - 178 (`X >>Int 0 => X`, domains.md 1382): `ev178`.
  - 179 (`0 >>Int Y => 0 requires 0 <=Int Y`, domains.md 1383): `ev179`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvIntEns

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

theorem ev160 (H : HookParams) : EntailsAtValues (cH H) U.ax160 (trS U.ax160).pat := by
  rw [(by decide +kernel : (trS U.ax160).pat = (trAxiom [] [] U.ax160).pat)]
  exact LibEv.addLeftComm_ev (coreOKH H) (shapesOKH H) U.ax160 (by decide +kernel) (by decide +kernel)

theorem ev161 (H : HookParams) : EntailsAtValues (cH H) U.ax161 (trS U.ax161).pat := by
  rw [(by decide +kernel : (trS U.ax161).pat = (trAxiom [] [] U.ax161).pat)]
  exact LibEv.addAssocRev_ev (coreOKH H) (shapesOKH H) U.ax161 (by decide +kernel) (by decide +kernel)

theorem ev162 (H : HookParams) : EntailsAtValues (cH H) U.ax162 (trS U.ax162).pat := by
  rw [(by decide +kernel : (trS U.ax162).pat = (trAxiom [] [] U.ax162).pat)]
  exact LibEv.addSubAssoc_ev (coreOKH H) (shapesOKH H) U.ax162 (by decide +kernel) (by decide +kernel)

theorem ev163 (H : HookParams) : EntailsAtValues (cH H) U.ax163 (trS U.ax163).pat := by
  rw [(by decide +kernel : (trS U.ax163).pat = (trAxiom [] [] U.ax163).pat)]
  exact LibEv.addAssoc_ev (coreOKH H) (shapesOKH H) U.ax163 (by decide +kernel) (by decide +kernel)

theorem ev164 (H : HookParams) : EntailsAtValues (cH H) U.ax164 (trS U.ax164).pat := by
  rw [(by decide +kernel : (trS U.ax164).pat = (trAxiom [] [] U.ax164).pat)]
  exact LibEv.subAddComm_ev (coreOKH H) (shapesOKH H) U.ax164 (by decide +kernel) (by decide +kernel)

theorem ev167 (H : HookParams) : EntailsAtValues (cH H) U.ax167 (trS U.ax167).pat := by
  rw [(by decide +kernel : (trS U.ax167).pat = (trAxiom [] [] U.ax167).pat)]
  exact LibEv.subAddSwap_ev (coreOKH H) (shapesOKH H) U.ax167 (by decide +kernel) (by decide +kernel)

theorem ev168 (H : HookParams) : EntailsAtValues (cH H) U.ax168 (trS U.ax168).pat := by
  rw [(by decide +kernel : (trS U.ax168).pat = (trAxiom [] [] U.ax168).pat)]
  exact LibEv.subAddAssoc_ev (coreOKH H) (shapesOKH H) U.ax168 (by decide +kernel) (by decide +kernel)

theorem ev169 (H : HookParams) : EntailsAtValues (cH H) U.ax169 (trS U.ax169).pat := by
  rw [(by decide +kernel : (trS U.ax169).pat = (trAxiom [] [] U.ax169).pat)]
  exact LibEv.subSubAssoc_ev (coreOKH H) (shapesOKH H) U.ax169 (by decide +kernel) (by decide +kernel)

theorem ev170 (H : HookParams) : EntailsAtValues (cH H) U.ax170 (trS U.ax170).pat := by
  rw [(by decide +kernel : (trS U.ax170).pat = (trAxiom [] [] U.ax170).pat)]
  exact LibEv.subSubAdd_ev (coreOKH H) (shapesOKH H) U.ax170 (by decide +kernel) (by decide +kernel)

theorem ev194 (H : HookParams) : EntailsAtValues (cH H) U.ax194 (trS U.ax194).pat := by
  rw [(by decide +kernel : (trS U.ax194).pat = (trAxiom [] [] U.ax194).pat)]
  exact LibEv.emodAsTmod_ev (coreOKH H) (shapesOKH H) U.ax194 (by decide +kernel) (by decide +kernel)

theorem ev195 (H : HookParams) : EntailsAtValues (cH H) U.ax195 (trS U.ax195).pat := by
  rw [(by decide +kernel : (trS U.ax195).pat = (trAxiom [] [] U.ax195).pat)]
  exact LibEv.emodSmall_ev (coreOKH H) (shapesOKH H) U.ax195 (by decide +kernel) (by decide +kernel)

theorem ev171 (H : HookParams) : EntailsAtValues (cH H) U.ax171 (trS U.ax171).pat := by
  rw [(by decide +kernel : (trS U.ax171).pat = (trAxiom [] [] U.ax171).pat)]
  exact LibEv.shlZero_ev (coreOKH H) (shapesOKH H) U.ax171 (by decide +kernel) (by decide +kernel)

theorem ev172 (H : HookParams) : EntailsAtValues (cH H) U.ax172 (trS U.ax172).pat := by
  rw [(by decide +kernel : (trS U.ax172).pat = (trAxiom [] [] U.ax172).pat)]
  exact LibEv.zeroShl_ev (coreOKH H) (shapesOKH H) U.ax172 (by decide +kernel) (by decide +kernel)

theorem ev178 (H : HookParams) : EntailsAtValues (cH H) U.ax178 (trS U.ax178).pat := by
  rw [(by decide +kernel : (trS U.ax178).pat = (trAxiom [] [] U.ax178).pat)]
  exact LibEv.shrZero_ev (coreOKH H) (shapesOKH H) U.ax178 (by decide +kernel) (by decide +kernel)

theorem ev179 (H : HookParams) : EntailsAtValues (cH H) U.ax179 (trS U.ax179).pat := by
  rw [(by decide +kernel : (trS U.ax179).pat = (trAxiom [] [] U.ax179).pat)]
  exact LibEv.zeroShr_ev (coreOKH H) (shapesOKH H) U.ax179 (by decide +kernel) (by decide +kernel)

end KCore.LibEvIntEns

/-- info: 'KCore.LibEvIntEns.ev160' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev160
/-- info: 'KCore.LibEvIntEns.ev161' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev161
/-- info: 'KCore.LibEvIntEns.ev162' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev162
/-- info: 'KCore.LibEvIntEns.ev163' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev163
/-- info: 'KCore.LibEvIntEns.ev164' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev164
/-- info: 'KCore.LibEvIntEns.ev167' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev167
/-- info: 'KCore.LibEvIntEns.ev168' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev168
/-- info: 'KCore.LibEvIntEns.ev169' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev169
/-- info: 'KCore.LibEvIntEns.ev170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev170
/-- info: 'KCore.LibEvIntEns.ev194' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev194
/-- info: 'KCore.LibEvIntEns.ev195' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev195
/-- info: 'KCore.LibEvIntEns.ev171' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev171
/-- info: 'KCore.LibEvIntEns.ev172' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev172
/-- info: 'KCore.LibEvIntEns.ev178' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev178
/-- info: 'KCore.LibEvIntEns.ev179' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIntEns.ev179
