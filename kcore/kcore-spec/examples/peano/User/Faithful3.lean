/-
  Peano in the third stage of faithfulness: `Stage2` gives `Stage3` (`stage3_of_stage2`), so the
  third stage's theorem applies to peano with the `Hyp` and `Stage2` of User/Faithful.lean. Peano's
  one function, `pred`, is total, so this instantiates the theorem without exercising a partial
  function.
-/
import User.Faithful
import KcoreSpec.FaithfulStage3

set_option autoImplicit false

namespace Peano.FaithfulWitness3

open KCore KCore.Faithful Peano

/-- **Peano is in the third stage.** -/
theorem stage3 : Stage3 c := stage3_of_stage2 FaithfulWitness.stage2

/-- **Every step of peano is a theorem of `Γ`**, by the third stage's theorem. -/
theorem step_sound : ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) :=
  step_sound_stage3 c FaithfulWitness.hyp FaithfulWitness.rules_bind FaithfulWitness.clauses_bind stage3

#print axioms step_sound

end Peano.FaithfulWitness3
