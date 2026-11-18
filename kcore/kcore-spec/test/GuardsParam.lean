/-
  An instance of the `param_undetermined` shape (findings/REVIEW-RN-reading-notes.md section 3, G6;
  DONE-0 C2, row `parameter`; C7 form (c)) at a parameter symbol no hook implements (`impl = none`).
  The schema and its two named interpretations are KcoreSpec/ParamSchema.lean's
  (`param_undetermined`, `param_undetermined_const`, `param_undetermined_point`, `fnHyp_of_fns_nil`):
  over all interpretations H, in every semantics `coreOK` accepts whose parameters are no open
  generator, Γ entails neither that the application has no value nor that it is a given value `v` of
  the result sort. Each hypothesis is a decidable fact about the data (`coreOK`, the parameters'
  `raw`, the lookup, `impl`, the sorts), closed on a text's literal by `decide +kernel` (or
  `decide_cheap` for `coreOK`). Run from the package root: `lake env lean -j1 test/GuardsParam.lean`.

  The instance below (`OneParam`, a semantics with one parameter `P : Int → Int` and no function)
  closes every hypothesis so: `P(0)` is not determined, with `pointH`, which differs from
  `HookParams.none` at the one point.
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.Guards

open KCore ML Faithful ParamSchema

/-! ## An instance: one parameter `P : Int → Int`, no function -/

namespace OneParam

/-- A semantics with the configuration `<k> K </k>`, the generated counter and one parameter symbol
`P : Int → Int` that no hook implements. -/
def P : Sym := nRegSyms + 4
def kP : ParamSig := ⟨⟨P, [Srt.int], Srt.int⟩, none, false, false, false⟩
def nc : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "LblP"]
    userSorts := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
    ctors := [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
      ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
      ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
    fns := []
    params := [kP]
    userSubsorts := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
    pgmSort := Srt.k
    rules := [] }

theorem nc_coreOK : nc.coreOK = true := by decide_cheap
theorem nc_noRaw : ∀ k ∈ nc.params, k.raw = false := by decide +kernel
theorem nc_fns : nc.fns = [] := rfl
theorem nc_readsConfined : nc.readsConfined = false := by decide +kernel

/-- **`P(0)` is not determined**: over all interpretations Γ entails neither `P(0) = ⊥` nor
`P(0) = 0`. -/
theorem P0_undetermined :
    ¬ (∀ H : HookParams, Γ (nc.withHooks H) ⊧ (paramApp (nc.withHooks H) kP.sig.name [int 0] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (nc.withHooks H) ⊧
      (paramApp (nc.withHooks H) kP.sig.name [int 0] ≡ den (nc.withHooks H) (int 0))) :=
  param_undetermined_point nc nc_coreOK nc_noRaw (k := kP) (by decide +kernel) rfl (by decide +kernel)
    (by decide +kernel) (fnHyp_of_fns_nil nc nc_noRaw nc_fns nc_readsConfined _)
    (fnHyp_of_fns_nil nc nc_noRaw nc_fns nc_readsConfined _)

end OneParam

end KCore.Guards

/-- info: 'KCore.ParamSchema.param_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamSchema.param_undetermined
/-- info: 'KCore.ParamSchema.param_undetermined_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamSchema.param_undetermined_const
/-- info: 'KCore.ParamSchema.param_undetermined_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamSchema.param_undetermined_point
/-- info: 'KCore.Guards.OneParam.P0_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Guards.OneParam.P0_undetermined
