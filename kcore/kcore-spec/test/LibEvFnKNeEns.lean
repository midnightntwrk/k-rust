/-
  domains.md 2355 (`K1 =/=K K2 => notBool (K1 ==K K2)`, K 7.1.337), axiom 175 of
  `f2-examples/ens.kompile.kore`, entailed at values (`EntailsAtValues`, direction Ev) for every
  interpretation H, from the library's one statement of the equation (`LibEv.fnNeK_ev`,
  `KcoreSpec/LibEvFnKNe.lean`): the text's axiom is compared with the equation's pattern over the
  registry's names, and its translation with the text's declarations with the translation
  `FnEqn.entailed` is about.
  Run from the package root: `lake env lean test/LibEvFnKNeEns.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvFnKNeEns

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

theorem fn175 (H : HookParams) : EntailsAtValues (cH H) U.ax175 (trS U.ax175).pat := by
  rw [(by decide +kernel : (trS U.ax175).pat = (trAxiom [] [] U.ax175).pat)]
  exact LibEv.fnNeK_ev (coreOKH H) U.ax175 (by decide +kernel) (by decide +kernel)

end KCore.LibEvFnKNeEns

#check @KCore.LibEv.fnNeK_ev
/-- info: 'KCore.LibEvFnKNeEns.fn175' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnKNeEns.fn175
