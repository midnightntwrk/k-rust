/-
  A run certificate on peano (KcoreSpec/Cert.lean): `run(s(s(z)))` reaches `done(z)` in three
  steps (rules 0, 0, 1), and `done(z)` is stuck. Each check is one kernel decision; soundness is the
  generic `Cert.checkRun_sound` from the package's three conditions.
-/
import User.Statements
import KcoreSpec.Cert

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Peano.CertTest

open KCore KCore.Cert Peano

def runs : List (Nat × GroundTerm) :=
  [(0, cfg (run (s z)) ctr0), (0, cfg (run z) ctr0), (1, cfg (done (natVal z)) ctr0)]

theorem peano_run : checkRun c 100 (cfg (run (s (s z))) ctr0) runs (cfg (done (natVal z)) ctr0) = true := by
  decide +kernel
theorem peano_stuck : stuckCheck c 100 (cfg (done (natVal z)) ctr0) = true := by decide +kernel

/-- `run(s(s(z)))` reaches `done(z)`, and `done(z)` has no successor. -/
theorem peano_reaches :
    ∃ (hs : c.sortOf (cfg (run (s (s z))) ctr0) = some topCellSort)
      (hf : c.sortOf (cfg (done (natVal z)) ctr0) = some topCellSort),
      Reach (Step c) ⟨_, hs⟩ ⟨_, hf⟩ ∧ ∀ y, ¬ Step c ⟨_, hf⟩ y :=
  let ⟨hs, hf, hr⟩ := checkRun_sound ok srReady matchReady peano_run c.hooks
  ⟨hs, hf, hr, stuckCheck_sound ok srReady matchReady c.hooks (coherent_withHooks c.hooks) (x := ⟨_, hf⟩) peano_stuck⟩

/-- info: 'Peano.CertTest.peano_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms peano_reaches

end Peano.CertTest
