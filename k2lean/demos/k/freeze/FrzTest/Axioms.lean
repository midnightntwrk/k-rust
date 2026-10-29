import Frz.Proofs
import KPrelude.Tactic

/-! The axiom guard of the freeze fixture: its names are the frozen theorems, and a refutation. -/

#k2l_assert_axioms Frz.f_double Frz.g_id
#k2l_refuted Frz.three
