/-
  `tnjItem_pat_of_disj` and `tnjItem_any_of_eq` (KcoreSpec/TieNoJunkBlk.lean) on base's no-junk
  sentence of KCellOpt, a sort of two generators (`noKCell` and the injection from KCell): its
  disjuncts are those of Γ's no-junk item of KCellOpt and it applies no alias, so its translation
  is that item's pattern, which is an item of `consItemsK c`, shown without scanning that list.
  Run from the package root: `lake env lean -j1 test/TieNoJunkBlk.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieNoJunkBlkTest

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/base.kompile.kore"
definition_of defn from "f2-examples/base.kompile.kore"
user_axioms U from "f2-examples/base.kompile.kore" module "BASE"

noncomputable abbrev c : Semantics := defn.sem

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The sort KCellOpt. -/
noncomputable def kco : Srt := ((consSorts c).find? (c.sortName · == "KCellOpt")).getD 0

theorem kco_mem : kco ∈ consSorts c := by decide +kernel
theorem kco_gens : (c.gens kco).isEmpty = false := by decide +kernel
theorem kco_two : (c.gens kco).length = 2 := by decide +kernel

theorem ax86_sortVars : U.ax86.ax.sortVars = [] := by decide +kernel
theorem ax86_pattern : U.ax86.ax.pattern =
    .or (srt (c.sortName kco)) (noJunkDisjuncts (c.sortName kco) [] ((c.gens kco).map (Gen.toK c))) := by
  decide +kernel
theorem ax86_aliasFree : TieFRRead.aliasFreeFR kore.aliasNames U.ax86.ax.pattern = true := by
  decide +kernel

/-- The translation of KCellOpt's no-junk sentence is Γ's no-junk item of KCellOpt. -/
theorem ax86_item : (trS U.ax86).pat =
    (Cons.noJunkItem (c.sortName kco) ((c.gens kco).map (Gen.toK c))).pat :=
  tnjItem_pat_of_disj ax86_sortVars ax86_pattern rfl ax86_aliasFree

/-- The statement a tie's `nojunk_items` asks of the sentence. -/
theorem ax86_any : (consItemsK c).any (·.pat == (trS U.ax86).pat) = true :=
  tnjItem_any_of_eq kco_mem kco_gens ax86_item

#check @tnjItem_pat_of_disj
#check @tnjItem_any_of_eq
#print axioms ax86_item
#print axioms ax86_any

end KCore.TieNoJunkBlkTest
