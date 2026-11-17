/-
  The equations of SET and LIST in the function form entailed at values (`EntailsAtValues`,
  direction Ev) on `f2-examples/ens.kompile.kore`, for every interpretation H, each from the
  library's one statement of the equation (`KcoreSpec/LibEvFnColl.lean`). They are the two
  sentences of ens from the MAP, SET and LIST sections of domains.md that are read and are no
  `simplification`; the text holds no `simplification` of those sections over element variables.
  Run from the package root: `lake env lean test/LibEvFnCollEns.lean`.

  - 207 (`S1 |Set S2 => S1 (S2 -Set S1)`, domains.md 749): `fn207`.
  - 264 (`pushList(K, L1) => ListItem(K) L1`, 955): `fn264`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvFnCollEns

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

theorem fn207 (H : HookParams) : EntailsAtValues (cH H) U.ax207 (trS U.ax207).pat := by
  rw [(by decide +kernel : (trS U.ax207).pat = (trAxiom [] [] U.ax207).pat)]
  exact LibEv.fnSetUnion_ev (coreOKH H) (shapesOKH H) U.ax207 (by decide +kernel) (by decide +kernel)

theorem fn264 (H : HookParams) : EntailsAtValues (cH H) U.ax264 (trS U.ax264).pat := by
  rw [(by decide +kernel : (trS U.ax264).pat = (trAxiom [] [] U.ax264).pat)]
  exact LibEv.fnPushList_ev (coreOKH H) (shapesOKH H) U.ax264 (by decide +kernel) (by decide +kernel)

end KCore.LibEvFnCollEns

/-- info: 'KCore.LibEvFnCollEns.fn207' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnCollEns.fn207
/-- info: 'KCore.LibEvFnCollEns.fn264' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnCollEns.fn264
