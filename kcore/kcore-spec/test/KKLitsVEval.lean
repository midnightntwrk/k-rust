/-
  What an evaluation of `d₀ d` produces has a `kore.k` form (`KcoreSpec/KKLitsVEval.lean`): under
  `execReady d` and `encodable d`, a function's result at arguments of its argument sorts, and the
  value of a clause's or a rule's `requires`, right side or `ensures` under a well-sorted
  substitution, are `litsV`. The reason is the value's sort, never `Float`. Run from the package
  root: `lake env lean test/KKLitsVEval.lean`.
-/
import KcoreSpec.KKLitsVEval

set_option autoImplicit false

namespace KCore.KK.TestLitsVEval

open KCore KCore.KK

#check @eval_litsV
#check @evalTerm_litsV_clause
#check @evalTerm_litsV_rule
#check @evalTerm_litsV_sorted_kkv

/-- The sorts the statements rest on are not `Float`. -/
example : Srt.bool ≠ Srt.float ∧ topCellSort ≠ Srt.float := by decide

/-- A Float value is sorted and not `litsV`: the statements need the sort, not only sortedness. -/
example : litsV (.dv Srt.float (.float 53 11 0)) = false := rfl

#print axioms eval_litsV
#print axioms evalTerm_litsV_clause
#print axioms evalTerm_litsV_rule

end KCore.KK.TestLitsVEval
