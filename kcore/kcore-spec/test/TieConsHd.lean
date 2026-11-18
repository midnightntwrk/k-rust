/-
  `tchConsB` (KcoreSpec/TieConsHd.lean) on a text's user module, against `tieConsB`: on every
  sentence the two agree (`agree_ctor_comm`; 28 constructor sentences, `some_cons`), so on this
  text deciding the constructor sentences at the sentence's sort and heads, with Γ's items shown
  by their membership lemmas, leaves none out that the search over every sort, generator and item
  accepts.
  `cons_hd_sound`: what `tchConsB` accepts `tieConsB` accepts, on any text (`tchConsB_sound`).
  Run from the package root: `lake env lean -j1 test/TieConsHd.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieConsHdTest

open KCore ML Faithful KoreAML

namespace CtorComm
definition_of defn from "f2-examples/c3-ctor-comm.kompile.kore"
user_axioms U from "f2-examples/c3-ctor-comm.kompile.kore" module "C3-CTOR-COMM"
noncomputable abbrev c : Semantics := defn.sem
theorem agree_ctor_comm : U.all.all (fun ad => tchConsB c ad.ax == tieConsB c ad.ax) = true := by decide +kernel
theorem some_cons : (U.all.filter (fun ad => tchConsB c ad.ax)).length = 28 := by decide +kernel
end CtorComm

theorem cons_hd_sound (c : Semantics) (a : Kore.Axiom) (h : tchConsB c a = true) : tieConsB c a = true :=
  tchConsB_sound h

end KCore.TieConsHdTest

#print axioms KCore.TieConsHdTest.CtorComm.agree_ctor_comm
#print axioms KCore.Faithful.tchConsB_sound
