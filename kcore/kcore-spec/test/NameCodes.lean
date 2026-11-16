/-
  The conjuncts of `faithCoreOK` that read names, decided on the names' codes (NameCodes.lean).
  Run from the package root: `lake env lean test/NameCodes.lean`.
  - A code `iteCoded` accepts is that of a name beginning `Lblite{`, whatever follows.
  - The semantics of ModelItesWitness.lean (two parameters named `Lblite{Int}` and `Lblite{Int]`):
    both are the symbols `iteIdx` lists, and the decision on codes refuses `itesApart` as the
    conjunct does, while it gives `namesNumbered` and `namesApartK`.
  - kompile's text of `f2-examples/libsub.k`: the three conjuncts from their decisions on codes, and
    `faithCoreOK` from them (`faithCoreOK_of_partsK`).
  The codes are given by `rfl` here (`(allSymNames c).map strCode` itself); a generated package
  states them as a table checked by blocks of rows (`codeRows`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Faithful KCore.Faithful.Model KoreAML.Distinct

namespace NameCodesTest

theorem coded : iteCoded (strCode "Lblite{Int}") = true ∧ iteCoded (strCode "Lblite{") = true ∧
    iteCoded (strCode "Lblite") = false ∧ iteCoded (strCode "Lblit{e") = false ∧
    iteCoded (strCode "XLblite{Int}") = false ∧ iteCoded (strCode "") = false := by decide

namespace Ites

abbrev c : Semantics := ItesWitness.c

theorem ite_idx : iteIdx ((allSymNames c).map strCode) = [nRegSyms + 4, nRegSyms + 5] := by decide +kernel

theorem namesNumbered : Faithful.namesNumbered c = true :=
  namesNumbered_of_codes rfl ite_idx (by decide +kernel)

theorem namesApartK : Model.namesApartK c = true :=
  namesApartK_of_codes rfl rfl (by decide +kernel)

/-- The decision on codes refuses the semantics `itesApart` refuses (`ItesWitness.not_itesApart`). -/
theorem itesApartC_false : itesApartC c [nRegSyms + 4, nRegSyms + 5] ((allSortNames c).map strCode) = false := by
  decide +kernel

end Ites

namespace LibSub

definition_of defn from "f2-examples/libsub.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem ite_idx : iteIdx ((allSymNames c).map strCode) = [] := by decide +kernel

theorem faithCoreOK : c.faithCoreOK = true :=
  Semantics.faithCoreOK_of_partsK (namesNumbered_of_codes rfl ite_idx (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (namesApartK_of_codes rfl rfl (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (itesApart_of_codes rfl rfl ite_idx (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end LibSub

end NameCodesTest

#print axioms NameCodesTest.Ites.namesNumbered
#print axioms NameCodesTest.LibSub.faithCoreOK
#print axioms KCore.Faithful.Model.namesNumbered_of_codes
#print axioms KCore.Faithful.Model.itesApart_of_codes
#print axioms KCore.Faithful.Model.namesApartK_of_codes
#print axioms KCore.Semantics.faithCoreOK_of_partsK
