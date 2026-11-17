/-
  An optional cell's distinctness axiom, on `f2-examples/optcell.kompile.kore`
  (`<one multiplicity="?"> 0 </one>`; the text of fixture c3-cells-opt under the module name
  OPTCELL). The sort OneCell has two constructors, the cell `<one>` and the constant `.OneCell`
  kompile declares for the absent cell, and the text states them distinct:
  `\not{SortOneCell{}}(\and{SortOneCell{}}(Lbl'Stop'OneCell{}(), Lbl'-LT-'one'-GT-'{}(Y0:SortInt{})))`,
  `[constructor]`. The reader classes the axiom inert (`distinctCtors`) and reads both symbols as
  constructors of the sort.

  - `dist_one`: the text holds one such axiom.
  - `dist_checked` (kernel): it is the no-confusion sentence of two generators of a constructor sort
    of the read definition, and `consItemsK` holds their Cons-Fun items and their Cons-Dist item
    (`tieConsB`).
  - `dist_entailed`: `Γ (d.sem.withHooks H) ⊧ tr s` for that sentence, for every H.
  The account finds the axiom among those the definition's constructors induce
  (`Parse.uninduced`): `kcore account` of the text prints `inert constructor axioms not induced by
  the constructors: 0` and `refused by the account: 0`, as the accounts of fixtures c3-cells-opt
  and e2-cells do.
  Run from the package root: `lake env lean test/OptCellDistinct.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.OptCellDistinct

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/optcell.kompile.kore"
definition_of defn from "f2-examples/optcell.kompile.kore"
user_axioms U from "f2-examples/optcell.kompile.kore" module "OPTCELL"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The text's distinctness axioms of `.OneCell`. -/
noncomputable def dist : List AxiomDecl := U.all.filter fun ad => match ad.ax.pattern with
  | .not _ (.and _ [.app f _ _, .app g _ _]) =>
    f.ident.name == "Lbl'Stop'OneCell" && g.ident.name == "Lbl'-LT-'one'-GT-'"
  | _ => false

theorem dist_one : dist.length = 1 := by decide +kernel

theorem coreOK : c.coreOK = true := by decide +kernel
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- Both symbols are constructors of the read definition, of one sort. -/
theorem both_ctors : ((c.ctors.filter fun k =>
    c.symName k.name == "Lbl'Stop'OneCell" || c.symName k.name == "Lbl'-LT-'one'-GT-'").map
      fun k => c.sortName k.result) = ["OneCell", "OneCell"] := by decide +kernel

theorem dist_checked : dist.all (fun ad => tieConsB c ad.ax) = true := by decide +kernel

/-- The axiom reads no declaration and no alias: its translation with the text's declarations is
its translation with none. -/
theorem dist_trS : dist.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **Γ entails the optional cell's distinctness axiom, for every H.** -/
theorem dist_entailed (H : HookParams) : ∀ ad ∈ dist, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp dist_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp dist_checked ad had)) ad.index ad.module hI

end KCore.OptCellDistinct

#print axioms KCore.OptCellDistinct.dist_entailed
