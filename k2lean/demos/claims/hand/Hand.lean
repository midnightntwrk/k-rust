import KImpClaims.ImpSimpleSpec
import KImpClaims.ImpSumSpec
import KImpClaims.ImpTwoSumAuxSpec
import KImpClaims.ImpDiv0Spec
import KImpClaims.ImpInvSpec
import KImpClaims.ExprDiv

/-! Hand-written: the claims of `demos/claims/kimp-open.txt`.

* `two_sum_spec`: the generic tactic, given the two per-loop claims of
  `demos/claims/specs/imp-two-sum-aux-spec.k` (proved generically in `ImpTwoSumAuxSpec`) as lemmas.
  `two_sum_spec'` is the same statement, proved in the auxiliary module itself.
* `bmc_loop_concrete_false`, `bmc_loop_symbolic_false`: the two `bmc-*` claims are false; each
  refutation instantiates the claim (empty continuation, and `S = 0`) and follows the closed run
  with the executable `step` (`kc_refute`), showing that the target never holds and that the run
  ends in a configuration without a successor.
* `div0_seven_false`, `div0_any_int_false`: `5 / 0` rewrites to `5 /Int 0`, which is `⊥`, so the
  configuration has no successor (`step` returns `undefined`) and is not the target.
* `copy_false`, `copy_loop_false`: the claims of `imp-inv-spec.k` over every configuration. With
  `$x` bound to the expression `1 + 2`, the lookup puts `1 + 2` on `<k>`, which evaluates to `3`, so
  `$y` ends up bound to `3`, not to `1 + 2`. Under the invariant that store values are `Value`s
  they hold (`generated/kimpinv-claims`, `k2lean claims --assume-invariant`).
* `expr_div_false`: the obligation of `_/_` in `kimp-expr-div.toml` is false, at `1 / 0`, which has
  no successor; as a reachability claim it is turned into an all-path one (`Step` is
  deterministic) and refuted like `div0_seven_false`. -/

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

/-- The expression `1 + 2`, as a store value. -/
def onePlusTwo : SortKItem :=
  inj_Expr_KItem (SortExpr.inj_Expr (SortExpr.Own.«_+_» (SortExpr.inj_Int 1) (SortExpr.inj_Int 2)))

theorem copy_false : ¬ ImpInvSpec.Claim.copy := by
  intro h
  have h0 := h .dotk (.inj_Int 0) 0 onePlusTwo _ rfl
  kc_refute h0

theorem copy_loop_false : ¬ ImpInvSpec.Claim.«copy-loop» := by
  intro h
  have h0 := h .dotk 0 1 onePlusTwo _ _ rfl rfl rfl
  kc_refute h0

theorem expr_div_false : ¬ ExprDiv.Obl.«AExp._/_» := by
  intro h
  have lit : ∀ i : Int, ∀ c Q, ExprDiv.Inst .AExp (SortExpr.inj_Int i) c Q → Reach Step Q c :=
    fun i => ExprDiv.Inst.of_forall fun _ _ _ => Reach.here ⟨i, rfl⟩
  have h0 := h _ _ (.«AExp.val» 1) (.«AExp.val» 0) (lit 1) (lit 0) .dotk (.«<env>» .nil)
    (.«<generatedCounter>» 0)
  have h1 := (AF_iff_EF_of_det (R := Step) (fun _ _ _ h₁ h₂ => Step.deterministic h₁ h₂)).2 h0.toEF
  kc_refute h1

#k2l_assert_axioms two_sum_spec two_sum_spec' bmc_loop_concrete_false bmc_loop_symbolic_false
  div0_seven_false div0_any_int_false copy_false copy_loop_false expr_div_false

end KImpClaims.Hand
