/-
  `Faithful.setColl_idem_refuted_text` on `f2-examples/starinit.kompile.kore`, whose configuration
  has the cell `<t multiplicity="*" type="Set">`: the text's idempotence sentence of its own set
  collection `_TCellSet_` (99, hooked to SET.concat) and of the library's `_Set_` (95) are both
  decided to be set idempotence sentences of a set collection whose key sort has a value
  (`setIdemTextOK`), so Γ with either has no model, for every H with `OvlOK` (a tie has it from
  `coreOK`). Run from the package root: `lake env lean -j1 test/SetIdemColl.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.SetIdemCollTest

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/starinit.kompile.kore"
definition_of defn from "f2-examples/starinit.kompile.kore"
user_axioms U from "f2-examples/starinit.kompile.kore" module "STARINIT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem own_idem_ok_99 : setIdemTextOK c "Lbl'Unds'TCellSet'Unds'" "K" U.ax99 = true := by decide +kernel
theorem own_idem_trS_99 : (trS U.ax99).pat = (trAxiom [] [] U.ax99).pat := by decide +kernel
theorem lib_idem_ok_95 : setIdemTextOK c "Lbl'Unds'Set'Unds'" "K" U.ax95 = true := by decide +kernel

/-- The own collection is not the library's: its sort is the cell set's. -/
theorem own_coll_99 : ((setCollOfConcat? c "Lbl'Unds'TCellSet'Unds'").map (c.sortName ·.sort)) = some "TCellSet" ∧
    ((setCollOfConcat? c "Lbl'Unds'TCellSet'Unds'").map (·.sort)) ≠ some Srt.set := by decide +kernel

/-- **Sentence 99, the own `_TCellSet_`'s idempotence, is refuted** for every H with `OvlOK`. -/
theorem own_idem_refuted_99 (H : HookParams) [OvlOK (cH H)] :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax99).pat) := by
  intro M hM I hI hax
  rw [own_idem_trS_99] at hax
  exact setColl_idem_refuted_text c H own_idem_ok_99 M hM I hI hax

end KCore.SetIdemCollTest

#check @KCore.SetIdemCollTest.own_idem_refuted_99
#check @KCore.SetIdemCollTest.lib_idem_ok_95
#print axioms KCore.SetIdemCollTest.own_idem_refuted_99
#print axioms KCore.SetIdemCollTest.lib_idem_ok_95
#print axioms KCore.SetIdemCollTest.own_coll_99
