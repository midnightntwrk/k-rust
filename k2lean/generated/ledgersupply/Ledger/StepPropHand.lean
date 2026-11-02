import Ledger.StepPropDefs

/-! The step property `supplyUp` of the gate's library `ledgersupply` (the fixture ledger, with
`gen --step-property supplyUp@supply`) is false: its one open case, rule `burn`, has a step that
lowers the supply. Burning 1 from account 0's balance of 1, at a supply of 0, leads to a supply of
`-1`. So `StepProp.lean` does not build, which is the expected outcome (`B-INV-21-design.md` §2). -/

namespace Ledger

open KPrelude

/-- Some step of rule `burn` does not satisfy `supplyUp`: the supply goes from `0` to `-1`. -/
theorem StepProp.burn_lowers :
    ∃ c c', Step c c' ∧ ¬ StepProp.holds c c' := by
  refine ⟨_, _, Step.burn 0 1 SortK.dotk _ 0 (SortFeesCell.«<fees>» 0) (SortGeneratedCounterCell.«<generatedCounter>» 0)
    MapHook.unit 1 _ rfl rfl rfl, ?_⟩
  simp only [StepProp.holds, StepProp.rel, StepProp.value, StepProp.content_supply,
    StepProp.cell_supply, StepProp.cell_books, StepProp.cell_T]
  decide

#k2l_assert_axioms StepProp.burn_lowers

end Ledger
