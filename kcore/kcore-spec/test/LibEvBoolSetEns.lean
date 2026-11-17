/-
  The eight Bool predicate sentences over set variables on `f2-examples/ens.kompile.kore`, entailed
  at set values (`EntailsAtSetValues`: each free set variable at a set of values of its sort) for
  every interpretation H, from the library's statements (KcoreSpec/LibEvBoolSet.lean).
  Run from the package root: `lake env lean test/LibEvBoolSetEns.lean`.

  - 154, 142, 148, 141 (domains.md 1176 to 1179): `notBool @B` at a literal against `@B` at its
    negation (`LibEv.boolNotSet_ev`).
  - 153, 139 (1181, 1182): `@B1 andBool @B2` at `true` (`LibEv.boolAndSet_ev`).
  - 147, 140 (1183, 1184): `@B1 orBool @B2` at `false` (`LibEv.boolOrSet_ev`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvBoolSetEns

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

theorem ev154 (H : HookParams) : EntailsAtSetValues (cH H) U.ax154 (trS U.ax154).pat := by
  rw [(by decide +kernel : (trS U.ax154).pat = (trAxiom [] [] U.ax154).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) true true U.ax154 (by decide +kernel) (by decide +kernel)
theorem ev142 (H : HookParams) : EntailsAtSetValues (cH H) U.ax142 (trS U.ax142).pat := by
  rw [(by decide +kernel : (trS U.ax142).pat = (trAxiom [] [] U.ax142).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) true false U.ax142 (by decide +kernel) (by decide +kernel)
theorem ev148 (H : HookParams) : EntailsAtSetValues (cH H) U.ax148 (trS U.ax148).pat := by
  rw [(by decide +kernel : (trS U.ax148).pat = (trAxiom [] [] U.ax148).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) false true U.ax148 (by decide +kernel) (by decide +kernel)
theorem ev141 (H : HookParams) : EntailsAtSetValues (cH H) U.ax141 (trS U.ax141).pat := by
  rw [(by decide +kernel : (trS U.ax141).pat = (trAxiom [] [] U.ax141).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) false false U.ax141 (by decide +kernel) (by decide +kernel)
theorem ev153 (H : HookParams) : EntailsAtSetValues (cH H) U.ax153 (trS U.ax153).pat := by
  rw [(by decide +kernel : (trS U.ax153).pat = (trAxiom [] [] U.ax153).pat)]
  exact LibEv.boolAndSet_ev (coreOKH H) (shapesOKH H) true U.ax153 (by decide +kernel) (by decide +kernel)
theorem ev139 (H : HookParams) : EntailsAtSetValues (cH H) U.ax139 (trS U.ax139).pat := by
  rw [(by decide +kernel : (trS U.ax139).pat = (trAxiom [] [] U.ax139).pat)]
  exact LibEv.boolAndSet_ev (coreOKH H) (shapesOKH H) false U.ax139 (by decide +kernel) (by decide +kernel)
theorem ev147 (H : HookParams) : EntailsAtSetValues (cH H) U.ax147 (trS U.ax147).pat := by
  rw [(by decide +kernel : (trS U.ax147).pat = (trAxiom [] [] U.ax147).pat)]
  exact LibEv.boolOrSet_ev (coreOKH H) (shapesOKH H) true U.ax147 (by decide +kernel) (by decide +kernel)
theorem ev140 (H : HookParams) : EntailsAtSetValues (cH H) U.ax140 (trS U.ax140).pat := by
  rw [(by decide +kernel : (trS U.ax140).pat = (trAxiom [] [] U.ax140).pat)]
  exact LibEv.boolOrSet_ev (coreOKH H) (shapesOKH H) false U.ax140 (by decide +kernel) (by decide +kernel)

end KCore.LibEvBoolSetEns

#check @KCore.LibEv.SvEqn.entailed
/-- info: 'KCore.LibEvBoolSetEns.ev154' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolSetEns.ev154
/-- info: 'KCore.LibEvBoolSetEns.ev142' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolSetEns.ev142
/-- info: 'KCore.LibEvBoolSetEns.ev148' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolSetEns.ev148
/-- info: 'KCore.LibEvBoolSetEns.ev141' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolSetEns.ev141
/-- info: 'KCore.LibEvBoolSetEns.ev153' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolSetEns.ev153
/-- info: 'KCore.LibEvBoolSetEns.ev139' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolSetEns.ev139
/-- info: 'KCore.LibEvBoolSetEns.ev147' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolSetEns.ev147
/-- info: 'KCore.LibEvBoolSetEns.ev140' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvBoolSetEns.ev140
