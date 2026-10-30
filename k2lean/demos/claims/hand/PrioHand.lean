import KPrioClaims.PrioSpec

/-! Hand-written: the claim of `demos/claims/prio-open.txt`.

* `swapped_false`: the decoder's family claim with source and destination swapped is false. At
  opcode 22 the decoder gives `mv(rb, rc)`, which is not `mv(rc, rb)` and has no successor; the
  refutation instantiates the claim there and follows the closed run (`kc_refute`). -/

set_option maxHeartbeats 0

open KPrio KPrelude KClaims

namespace KPrioClaims.Hand

theorem swapped_false : ¬ PrioSpec.Claim.swapped := by
  intro h
  have h0 := h 0 22 _ _ rfl rfl rfl
  kc_refute h0

end KPrioClaims.Hand
