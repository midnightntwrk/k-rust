/-
  The collection laws entailed at values (`EntailsAtValues`, direction Ev) on
  `f2-examples/ens.kompile.kore`, for every interpretation H, each from the library's one statement
  of the law (`KcoreSpec/LibEvLaw.lean`, through `LibEv.Law.entailed_reg`): the nine sentences of
  the class "collection law" of `test/TieEns.lean`.
  Run from the package root: `lake env lean test/LibEvLawEns.lean`.

  - 53, 54, 55: associativity, the right unit and the left unit of `_List_`.
  - 57, 58, 59: of `_Map_`.
  - 60, 62, 63: of `_Set_` (61 is set idempotence, which Γ refutes).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvLawEns

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

theorem law53 (H : HookParams) : EntailsAtValues (cH H) U.ax53 (trS U.ax53).pat := by
  rw [(by decide +kernel : (trS U.ax53).pat = (trAxiom [] [] U.ax53).pat)]
  exact LibEv.listAssoc_ev (coreOKH H) (shapesOKH H) U.ax53 (by decide +kernel) (by decide +kernel)

theorem law54 (H : HookParams) : EntailsAtValues (cH H) U.ax54 (trS U.ax54).pat := by
  rw [(by decide +kernel : (trS U.ax54).pat = (trAxiom [] [] U.ax54).pat)]
  exact LibEv.listUnitR_ev (coreOKH H) (shapesOKH H) U.ax54 (by decide +kernel) (by decide +kernel)

theorem law55 (H : HookParams) : EntailsAtValues (cH H) U.ax55 (trS U.ax55).pat := by
  rw [(by decide +kernel : (trS U.ax55).pat = (trAxiom [] [] U.ax55).pat)]
  exact LibEv.listUnitL_ev (coreOKH H) (shapesOKH H) U.ax55 (by decide +kernel) (by decide +kernel)

theorem law57 (H : HookParams) : EntailsAtValues (cH H) U.ax57 (trS U.ax57).pat := by
  rw [(by decide +kernel : (trS U.ax57).pat = (trAxiom [] [] U.ax57).pat)]
  exact LibEv.mapAssoc_ev (coreOKH H) (shapesOKH H) U.ax57 (by decide +kernel) (by decide +kernel)

theorem law58 (H : HookParams) : EntailsAtValues (cH H) U.ax58 (trS U.ax58).pat := by
  rw [(by decide +kernel : (trS U.ax58).pat = (trAxiom [] [] U.ax58).pat)]
  exact LibEv.mapUnitR_ev (coreOKH H) (shapesOKH H) U.ax58 (by decide +kernel) (by decide +kernel)

theorem law59 (H : HookParams) : EntailsAtValues (cH H) U.ax59 (trS U.ax59).pat := by
  rw [(by decide +kernel : (trS U.ax59).pat = (trAxiom [] [] U.ax59).pat)]
  exact LibEv.mapUnitL_ev (coreOKH H) (shapesOKH H) U.ax59 (by decide +kernel) (by decide +kernel)

theorem law60 (H : HookParams) : EntailsAtValues (cH H) U.ax60 (trS U.ax60).pat := by
  rw [(by decide +kernel : (trS U.ax60).pat = (trAxiom [] [] U.ax60).pat)]
  exact LibEv.setAssoc_ev (coreOKH H) (shapesOKH H) U.ax60 (by decide +kernel) (by decide +kernel)

theorem law62 (H : HookParams) : EntailsAtValues (cH H) U.ax62 (trS U.ax62).pat := by
  rw [(by decide +kernel : (trS U.ax62).pat = (trAxiom [] [] U.ax62).pat)]
  exact LibEv.setUnitR_ev (coreOKH H) (shapesOKH H) U.ax62 (by decide +kernel) (by decide +kernel)

theorem law63 (H : HookParams) : EntailsAtValues (cH H) U.ax63 (trS U.ax63).pat := by
  rw [(by decide +kernel : (trS U.ax63).pat = (trAxiom [] [] U.ax63).pat)]
  exact LibEv.setUnitL_ev (coreOKH H) (shapesOKH H) U.ax63 (by decide +kernel) (by decide +kernel)

end KCore.LibEvLawEns

#check @KCore.LibEv.Law.entailed
#check @KCore.LibEv.Law.entailed_reg
/-- info: 'KCore.LibEvLawEns.law53' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvLawEns.law53
/-- info: 'KCore.LibEvLawEns.law54' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvLawEns.law54
/-- info: 'KCore.LibEvLawEns.law55' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvLawEns.law55
/-- info: 'KCore.LibEvLawEns.law57' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvLawEns.law57
/-- info: 'KCore.LibEvLawEns.law58' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvLawEns.law58
/-- info: 'KCore.LibEvLawEns.law59' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvLawEns.law59
/-- info: 'KCore.LibEvLawEns.law60' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvLawEns.law60
/-- info: 'KCore.LibEvLawEns.law62' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvLawEns.law62
/-- info: 'KCore.LibEvLawEns.law63' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvLawEns.law63
