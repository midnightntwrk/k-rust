/-
  The two `==K` simplifications at K sequences of one injected item on
  `f2-examples/ens.kompile.kore`, entailed at values (`EntailsAtValues`, direction Ev) for every
  interpretation H, from the library's statements (`KcoreSpec/LibEvBoolK.lean`).
  Run from the package root: `lake env lean test/LibEvBoolKEns.lean`.

  - 176 (`inj{Bool, KItem}(K1) ==K inj{Bool, KItem}(K2) => K1 ==Bool K2`, domains.md 2338): `ev176`.
  - 177 (`inj{Int, KItem}(I1) ==K inj{Int, KItem}(I2) => I1 ==Int I2`, domains.md 1404): `ev177`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvBoolKEns

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
theorem boolBelowH (H : HookParams) : Srt.bool ∈ (cH H).sortsBelowKItem :=
  List.contains_iff_mem.mp (by decide +kernel : c.sortsBelowKItem.contains Srt.bool = true)
theorem intBelowH (H : HookParams) : Srt.int ∈ (cH H).sortsBelowKItem :=
  List.contains_iff_mem.mp (by decide +kernel : c.sortsBelowKItem.contains Srt.int = true)

theorem ev176 (H : HookParams) : EntailsAtValues (cH H) U.ax176 (trS U.ax176).pat := by
  rw [(by decide +kernel : (trS U.ax176).pat = (trAxiom [] [] U.ax176).pat)]
  exact LibEv.boolKEq_ev (coreOKH H) (shapesOKH H) (boolBelowH H) U.ax176 (by decide +kernel)
    (by decide +kernel)

theorem ev177 (H : HookParams) : EntailsAtValues (cH H) U.ax177 (trS U.ax177).pat := by
  rw [(by decide +kernel : (trS U.ax177).pat = (trAxiom [] [] U.ax177).pat)]
  exact LibEv.intKEq_ev (coreOKH H) (shapesOKH H) (intBelowH H) U.ax177 (by decide +kernel)
    (by decide +kernel)

end KCore.LibEvBoolKEns

/-- info: 'KCore.LibEvBoolKEns.ev176' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolKEns.ev176
/-- info: 'KCore.LibEvBoolKEns.ev177' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolKEns.ev177
