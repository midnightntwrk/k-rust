/-
  A rule's `ensures` as a field of `Rule` (`Rule.ens`), read by `Step` as a premise of the right
  side (`Step.rule`'s `hens`) and never by `NotApplies`. Run from the package root:
  `lake env lean test/EnsField.lean`.

  The configuration is `<k> K </k>` with the generated counter. Two rules, on every configuration:
  - `r50`: `<k> X </k> <generatedCounter> N </generatedCounter> => <k> X </k> <generatedCounter> 1 </generatedCounter>
    ensures false`, of priority 50;
  - `r200`: the same left side `=> <k> X </k> <generatedCounter> 2 </generatedCounter>`, of priority 200.
  At `<k> . </k> <generatedCounter> 0 </generatedCounter>`, `r50` matches and has no `requires`, so it
  applies (`¬ NotApplies`) and blocks `r200`; its `ensures` is false, so it gives no successor. The
  configuration has no `Step` successor. With `ensures true` in place of `ensures false` (one rule,
  `c1`), the configuration steps to the counter 1.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace EnsField

open Faithful.UndefRhsWitness (kIds cellSorts cellCtors cellSubsorts)

/-- The left side of both rules: any configuration. -/
def lhs : Term := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.var 1]]

/-- The right side with the counter `n`. -/
def rhsAt (n : Int) : Term := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.dv Srt.int (.int n)]]

def r50 : Rule :=
  { vars := [Srt.k, Srt.int], lhs := lhs, req := none, rhs := rhsAt 1,
    ens := some (.dv Srt.bool (.bool false)), prio := 50 }

def r200 : Rule :=
  { vars := [Srt.k, Srt.int], lhs := lhs, req := none, rhs := rhsAt 2, ens := none, prio := 200 }

/-- `r50` with `ensures true`. -/
def r50t : Rule := { r50 with ens := some (.dv Srt.bool (.bool true)) }

def base : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

def c : Semantics := { base with rules := [r50, r200] }
def c1 : Semantics := { base with rules := [r50t] }

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOK1 : c1.coreOK = true := by decide_cheap

/-- An `ensures` that is not `\top` is a Bool, as `ruleSorted` asks. -/
theorem sorted_ens : c.rules.all c.ruleSorted = true := by decide +kernel

/-- `<k> . </k> <generatedCounter> n </generatedCounter>`. -/
def cfg (n : Int) : GroundTerm := .ctor topLabel [.ctor kIds.label [.ctor dotk []], .ctor counterLabel [int n]]

theorem cfg_sort : c.sortOf (cfg 0) = some topCellSort := by decide +kernel
theorem cfg_sort1_0 : c1.sortOf (cfg 0) = some topCellSort := by decide +kernel
theorem cfg_sort1_1 : c1.sortOf (cfg 1) = some topCellSort := by decide +kernel

def A : Config c := ⟨cfg 0, cfg_sort⟩

def σ : Subst := [(0, .ctor dotk []), (1, int 0)]

theorem hσ (d : Semantics) (hk : d.sortOf (.ctor dotk []) = some Srt.k) (hi : d.sortOf (int 0) = some Srt.int) :
    d.WellSorted [Srt.k, Srt.int] σ := by
  intro i s h
  match i, h with
  | 0, h => cases h; exact ⟨_, rfl, hk⟩
  | 1, h => cases h; exact ⟨_, rfl, hi⟩

theorem hmatch (d : Semantics) (hc1 : d.isCtor topLabel = true) (hc2 : d.isCtor kIds.label = true)
    (hc3 : d.isCtor counterLabel = true) : PatVal d σ lhs (cfg 0) :=
  .ctor hc1 (.cons (.ctor hc2 (.cons (.var rfl) .nil)) (.cons (.ctor hc3 (.cons (.var rfl) .nil)) .nil))

/-- **`r50` applies at A**: it matches and has no `requires`. -/
theorem r50_applies : ¬ NotApplies c r50 A.val := by
  intro h
  cases h σ ((hσ c (by decide +kernel) (by decide +kernel)).at _)
    (hmatch c (by decide +kernel) (by decide +kernel) (by decide +kernel)) with
  | intro ht _ _ => cases ht
  | pre h => cases h

/-- **A has no successor**: `r50` has none (its `ensures` is false), and `r200` is blocked by
`r50`, which applies. -/
theorem A_stuck : ∀ y, ¬ Step c A y := by
  intro y h
  cases h with
  | rule r mem σ' _ _ _ _ _ hens _ hprio =>
    simp only [c, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · cases hens _ rfl
    · exact r50_applies (hprio r50 (by simp [c]) (by decide))

/-- With `ensures true`: A steps to the counter 1. -/
theorem A_steps1 : Step c1 ⟨cfg 0, cfg_sort1_0⟩ ⟨cfg 1, cfg_sort1_1⟩ :=
  .rule r50t (by simp [c1]) σ (hσ c1 (by decide +kernel) (by decide +kernel))
    (hmatch c1 (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (fun t h => by cases h) .top
    (.ctor (by decide +kernel)
      (.cons (.ctor (by decide +kernel) (.cons (.var (i := 0)) .nil))
        (.cons (.ctor (by decide +kernel) (.cons .dv .nil)) .nil)))
    (fun t h => by cases h; exact .dv) .top
    (fun r' h hlt => by
      simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact absurd hlt (by decide))

end EnsField

end KCore

/-- info: 'KCore.EnsField.A_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KCore.EnsField.A_stuck

/-- info: 'KCore.EnsField.A_steps1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KCore.EnsField.A_steps1

/-- info: 'KCore.EnsField.r50_applies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KCore.EnsField.r50_applies

/-- info: 'KCore.EnsField.coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KCore.EnsField.coreOK
