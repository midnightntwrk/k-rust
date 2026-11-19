/-
  Checks of KCore, and the axioms of its generic theorems.
  1. The tie, end to end (`Tied k`: parse, `wf`, and `emit` equal to the text up to sentence order)
     for peano and the probe `f2-examples/prio.kore`, by compiled evaluation (`#guard`, a test:
     nothing proved rests on it). The kernel proofs of the same are the generated packages' ties
     (examples/*/…/Tie.lean).
  2. The data the statements read, on the probe (compiled, a test): `ΓCons` has one refined
     distinctness item (Cons-Dist′, for `inj{B,KItem}` and `inj{C,KItem}`, whose sorts share the
     lower bound D), and `ΓRules`' two rules of a larger priority carry the negated-competitor
     premise beside the left-hand side, the `requires` and the right-hand side's definedness.
  3. `Exec.step_iff`, subject reduction, determinism (`Det.deterministic_of`), the functionality
     of evaluation (`Eval.functional`) and what decides its premise (`clauseFixed_sound`,
     `matchIndependentAll_of`, `Det.coherentAll_of`), the meaning of exclusive clauses (`Det.clausesExclusive_sound`),
     of patterns apart (`Det.overlap_sound`) and of `fnExclusiveOK` (`Det.fnExclusiveOK_sound`)
     and their parts, the lazy decider's soundness (`definedArg_sound`) and what a lazy obligation
     gives at its occurrence (`LazyOcc.iteParam_true`, `LazyOcc.andBool_false`), what `wf` and
     `Obligations` give of the theory (`hypModel_of`), soundness (`sound`) and completeness
     (`complete`), and their forms over a semantics (`hypModel_of_core`, `sound_hyp`,
     `complete_hyp`, `sound_core`, `complete_core`) rest on Lean's three axioms only, and so do the
     derivation of `collsNotCtors` (`collsNotCtors_of`) and the failures of soundness without
     `kindsApart` or `sortsNumbered` (`KindsWitness.not_sound`, `SortsWitness.not_sound`) and
     with an overloading symbol listed twice (`OvlTwiceWitness.not_sound`).
-/
import KcoreSpec.Statements
import KcoreSpec.Sound
import KcoreSpec.StepIffWf
import KcoreSpec.HooksApart
import KcoreSpec.DetSound
import KcoreSpec.LazySound
import KcoreSpec.FnExclusive
import KcoreSpec.Kore.Subject
import KcoreSpec.Kore.Import
import KcoreSpec.ModelKindsWitness
import KcoreSpec.ModelItesWitness
import KcoreSpec.ModelOvlTwiceWitness
import KcoreSpec.ModelSortsWitness

set_option autoImplicit false

namespace KCore.Checks

open KCore

set_option maxRecDepth 200000 in
kore_definition prioKore from "f2-examples/prio.kore"

/-! ## 1. The tie (compiled) -/

#guard decide (Tied KoreAML.Peano.kore)
#guard decide (Tied prioKore)
#guard (Parse.parse KoreAML.Peano.kore).toOption.isSome
#guard (Parse.parse prioKore).toOption.map (fun d => d.sem.rules.map (·.prio)) == some [40, 50, 200]

/-! ## 2. The refined Cons-Dist and the priority premise, on the probe (compiled) -/

/-- A sort of a definition by name. -/
def sortNamed (d : Definition) (n : String) : Srt := nRegSorts + d.sem.sortNames.idxOf n

#guard (Parse.parse prioKore).toOption.any fun d =>
  ((Faithful.consItemsK d.sem).filter (·.rule == "Cons-Dist′")).map (·.label) ==
    ["cons-dist′ inj SortB SortKItem / inj SortC SortKItem"]
#guard (Parse.parse prioKore).toOption.any fun d =>
  (d.sem.lowerBounds (sortNamed d "B") (sortNamed d "C")).map d.sem.sortName == ["D"]
#guard (Parse.parse prioKore).toOption.any fun d =>
  d.sem.rules.map (fun r => match Faithful.prioRuleK d.sem r with
    | .rewrites _ (.and _ cs) _ => cs.length
    | _ => 0) == [3, 4, 4]

/-! ## 3. Axioms -/

/-- info: 'KCore.Exec.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exec.step_iff

/-- info: 'KCore.Exec.step_iff_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exec.step_iff_of

/-- info: 'KCore.Exec.step_iff_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exec.step_iff_of_ok

/-- info: 'KCore.Det.deterministic_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Det.deterministic_of

/-- info: 'KCore.Det.deterministic_except' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Det.deterministic_except

/-- info: 'KCore.Eval.functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Eval.functional

/-- info: 'KCore.EvalTerm.functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EvalTerm.functional

/-- info: 'KCore.clauseFixed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clauseFixed_sound

/-- info: 'KCore.matchIndependentAll_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms matchIndependentAll_of

/-- info: 'KCore.Det.coherentAll_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Det.coherentAll_of

/-- info: 'KCore.Det.clausesExclusive_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Det.clausesExclusive_sound

/-- info: 'KCore.Det.overlap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Det.overlap_sound

/-- info: 'KCore.Det.fnExclusiveOK_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Det.fnExclusiveOK_sound

/-- info: 'KCore.Det.witnessed_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Det.witnessed_of

/-- info: 'KCore.Exec.successorsN_sound_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exec.successorsN_sound_wf

/-- info: 'KCore.rhs_sorted_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rhs_sorted_wf

/-- info: 'KCore.step_of_apply_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_of_apply_wf

/-- info: 'KCore.Eval.sorted_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Eval.sorted_wf

/-- info: 'KCore.hook_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hook_sorted

/-- info: 'KCore.NamesApart.srReady_of_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NamesApart.srReady_of_wf

/-- info: 'KCore.NamesApart.matchReady_of_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NamesApart.matchReady_of_wf

/-- info: 'KCore.NamesApart.declaredClosure_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NamesApart.declaredClosure_trans

/-- info: 'KCore.isHook_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isHook_iff

/-- info: 'KCore.Definition.hooksApart_of_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Definition.hooksApart_of_wf

/-- info: 'KCore.Semantics.definedArg_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Semantics.definedArg_sound

/-- info: 'KCore.hook_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hook_total

/-- info: 'KCore.lazyOccs_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lazyOccs_hold

/-- info: 'KCore.iteParam_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iteParam_true

/-- info: 'KCore.iteParam_true_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iteParam_true_eq

/-- info: 'KCore.andBool_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms andBool_false

/-- info: 'KCore.andBool_false_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms andBool_false_eq

/-- info: 'KCore.LazyOcc.iteParam_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LazyOcc.iteParam_true

/-- info: 'KCore.LazyOcc.andBool_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LazyOcc.andBool_false

/-- info: 'KCore.hypModel_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hypModel_of

/-- info: 'KCore.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sound

/-- info: 'KCore.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms complete

/-- info: 'KCore.hypModel_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hypModel_of_core

/-- info: 'KCore.sound_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sound_hyp

/-- info: 'KCore.complete_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms complete_hyp

/-- info: 'KCore.sound_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sound_core

/-- info: 'KCore.complete_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms complete_core

/-- info: 'KCore.Faithful.collsNotCtors_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Faithful.collsNotCtors_of

/-- info: 'KCore.Faithful.KindsWitness.not_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Faithful.KindsWitness.not_sound

/-- info: 'KCore.Faithful.OvlTwiceWitness.not_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Faithful.OvlTwiceWitness.not_sound

/-- info: 'KCore.Faithful.SortsWitness.not_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Faithful.SortsWitness.not_sound

end KCore.Checks
