import KImpClaims.ImpSimpleSpec
import KImpClaims.ImpSumSpec
import KImpClaims.ImpTwoSumAuxSpec
import KImpClaims.ImpDiv0Spec

/-! Hand-written: the claims of `demos/claims/kimp-open.txt`.

* `two_sum_spec`: the generic tactic, given the two per-loop claims of
  `demos/claims/specs/imp-two-sum-aux-spec.k` (proved generically in `ImpTwoSumAuxSpec`) as lemmas.
  `two_sum_spec'` is the same statement, proved in the auxiliary module itself.
* `bmc_loop_concrete_false`, `bmc_loop_symbolic_false`: the two `bmc-*` claims are false; each
  refutation instantiates the claim (empty continuation, and `S = 0`) and follows the closed run
  with the executable `step` (`kc_refute`), showing that the target never holds and that the run
  ends in a configuration without a successor.
* `div0_seven_false`, `div0_any_int_false`: `5 / 0` rewrites to `5 /Int 0`, which is `⊥`, so the
  configuration has no successor (`step` returns `undefined`) and is not the target. -/

set_option maxHeartbeats 0

open KImp KPrelude KClaims

namespace KImpClaims.Hand

theorem two_sum_spec_inst : ∀ c Q, ImpSumSpec.Inst.«two-sum-spec» c Q → AF Step Q c := by
  apply AF.circularity_inst
  intro n ih c Q hi
  kc_intro hi
  kc_auto circ [ih] using [ImpTwoSumAuxSpec.Inst.«loop-n».holds, ImpTwoSumAuxSpec.Inst.«loop-m».holds]

theorem two_sum_spec : ImpSumSpec.Claim.«two-sum-spec» :=
  ImpSumSpec.Claim.«two-sum-spec».of_inst two_sum_spec_inst

theorem two_sum_spec' : ImpSumSpec.Claim.«two-sum-spec» := ImpTwoSumAuxSpec.Claim.«two-sum-spec».holds

theorem bmc_loop_concrete_false : ¬ ImpSimpleSpec.Claim.«bmc-loop-concrete» := by
  intro h
  have h0 := h .dotk 0
  kc_refute h0

theorem bmc_loop_symbolic_false : ¬ ImpSimpleSpec.Claim.«bmc-loop-symbolic» := by
  intro h
  have h0 := h .dotk 0 0 _ rfl rfl
  kc_refute h0

theorem div0_seven_false : ¬ ImpDiv0Spec.Claim.«div0-seven» := by
  intro h
  have h0 := h (.«<env>» .nil) .dotk 0
  kc_refute h0

theorem div0_any_int_false : ¬ ImpDiv0Spec.Claim.«div0-any-int» := by
  intro h
  have h0 := h (.«<env>» .nil) .dotk 0
  kc_refute h0

#k2l_assert_axioms two_sum_spec two_sum_spec' bmc_loop_concrete_false bmc_loop_symbolic_false
  div0_seven_false div0_any_int_false

end KImpClaims.Hand
