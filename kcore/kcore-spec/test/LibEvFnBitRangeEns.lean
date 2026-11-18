/-
  The equations of `bitRangeInt` and `signExtendBitRangeInt` (INT, domains.md 1438 and 1440) on
  `f2-examples/ens.kompile.kore` entailed at values (`EntailsAtValues`) for every interpretation H,
  each from the library's one statement of the equation (`KcoreSpec/LibEvFnBitRange.lean`, through
  `LibEv.FnEqn.entailed_reg`): the text's axiom is the statement's pattern over the registry's
  names, and its translation with the text's declarations is the translation the statement is
  about. Both apply only symbols Γ has (`>>Int`, `<<Int`, `modInt`, `+Int`, `-Int` and the two bit
  ranges are interpreted by the registry). Run from the package root:
  `lake env lean test/LibEvFnBitRangeEns.lean`.

  - 208 (`bitRangeInt(I, IDX, LEN) => (I >>Int IDX) modInt (1 <<Int LEN)`, 1438): `ev208`.
  - 265 (`signExtendBitRangeInt(I, IDX, LEN) => (bitRangeInt(I, IDX, LEN) +Int (1 <<Int (LEN -Int 1)))
    modInt (1 <<Int LEN) -Int (1 <<Int (LEN -Int 1))`, 1440): `ev265`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvFnBitRangeEns

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

theorem ev208 (H : HookParams) : EntailsAtValues (cH H) U.ax208 (trS U.ax208).pat := by
  rw [(by decide +kernel : (trS U.ax208).pat = (trAxiom [] [] U.ax208).pat)]
  exact LibEv.fnBitRange_ev (coreOKH H) (shapesOKH H) U.ax208 (by decide +kernel) (by decide +kernel)

theorem ev265 (H : HookParams) : EntailsAtValues (cH H) U.ax265 (trS U.ax265).pat := by
  rw [(by decide +kernel : (trS U.ax265).pat = (trAxiom [] [] U.ax265).pat)]
  exact LibEv.fnSignExt_ev (coreOKH H) (shapesOKH H) U.ax265 (by decide +kernel) (by decide +kernel)

end KCore.LibEvFnBitRangeEns

/-- info: 'KCore.LibEvFnBitRangeEns.ev208' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBitRangeEns.ev208
/-- info: 'KCore.LibEvFnBitRangeEns.ev265' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnBitRangeEns.ev265
