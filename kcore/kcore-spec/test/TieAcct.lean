/-
  `tacAccount_of_msort` (KcoreSpec/TieAcct.lean) on twelve sentence indices in three class lists:
  the class lists, sorted, are the range 1..12, so they are a permutation of the indices and the
  indices are distinct. The direct decision agrees, and class lists with a repeated index do not
  sort to the range.
  Run from the package root: `lake env lean -j1 test/TieAcct.lean`.
-/
import KcoreSpec.TieAcct

set_option autoImplicit false

namespace KCore.TieAcctTest

/-- Three classes of the twelve sentences. -/
def tacClasses : List (String × List Nat) :=
  [("a", [3, 1, 7, 10]), ("b", [2, 12, 5, 4]), ("c", [6, 9, 8, 11])]

/-- The sentences' indices, in text order. -/
def tacIdx : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

theorem tac_sorted :
    KoreAML.Distinct.msort (KoreAML.Distinct.passesFor 12) (tacClasses.flatMap (·.2)) = List.range' 1 12 := by
  decide +kernel

theorem tac_idx : tacIdx = List.range' 1 12 := by decide +kernel

/-- The account, from the sort. -/
theorem tac_account : (tacClasses.flatMap (·.2)).isPerm tacIdx = true ∧ tacIdx.Nodup :=
  tacAccount_of_msort tac_sorted tac_idx

/-- The same permutation, decided directly. -/
example : (tacClasses.flatMap (·.2)).isPerm tacIdx = true := by decide +kernel

/-- With 4 in place of 11 the classes repeat an index and miss one: they do not sort to the range. -/
example : KoreAML.Distinct.msort (KoreAML.Distinct.passesFor 12)
    [3, 1, 7, 10, 2, 12, 5, 4, 6, 9, 8, 4] ≠ List.range' 1 12 := by decide +kernel

#check @tacAccount_of_msort
#print axioms tac_account

end KCore.TieAcctTest
