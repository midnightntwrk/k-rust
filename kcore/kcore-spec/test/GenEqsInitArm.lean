/-
  The axioms of the account's arm for the cell tree's initializers (`KcoreSpec/GenEqsInitArm.lean`:
  `Parse.initEqnOK`, `Parse.initFunctionalOK` against the model of `KcoreSpec/GenEqsInit.lean`).
  Run from the package root: `lake env lean -j1 test/GenEqsInitArm.lean`.

  `GenEqs.init_arm_eqn` (an initializer's equation at values), `GenEqs.init_arm_functional` (the
  instance of a `functional` axiom of an initializer at all values of a sort) and
  `GenEqs.model_with_inits_arm` (the model with the initializers' equations) depend on the standard
  axioms only.

  The arm is instanced on kompiled texts, read as the account reads each (the user module's scan
  and names), in `test/GenEqsInitAcctSortLabel.lean` (`f2-examples/sortlabel.kompile.kore`),
  `test/GenEqsInitAcctVars.lean` (`f2-examples/e3-vars.kompile.kore`),
  `test/GenEqsInitAcctFresh.lean` (`f2-examples/freshcfg.kompile.kore`) and
  `test/GenEqsInitNested.lean` (`f2-examples/cellsplain.kompile.kore`).
-/
import KcoreSpec

set_option autoImplicit false

open KCore KCore.GenEqs

namespace GenEqsInitArm

/-- info: 'KCore.GenEqs.init_arm_eqn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms init_arm_eqn
/-- info: 'KCore.GenEqs.init_arm_functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms init_arm_functional
/-- info: 'KCore.GenEqs.model_with_inits_arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_with_inits_arm

end GenEqsInitArm
