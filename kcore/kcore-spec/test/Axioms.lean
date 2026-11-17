/-
  The axioms of the whole library: every declaration of a `KcoreSpec.*` module (theorems,
  definitions, instances) depends on no axiom but `propext`, `Classical.choice` and `Quot.sound`
  (`#axioms_modules`, KcoreSpec/AxiomsCheck.lean). So no declaration uses `sorryAx` (a `sorry`), an
  `axiom` of its own, or `Lean.ofReduceBool` (`native_decide`). Fails, naming the declarations and
  the axioms, otherwise. Run from the package root: `lake env lean test/Axioms.lean`. The same
  check runs over each test file (test/integration.sh, row axioms-tests) and the row packages (row
  axioms-packages).
-/
import KcoreSpec

#axioms_modules KcoreSpec
