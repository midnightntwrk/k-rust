import KTerm.Functions
import KPrelude.Tactic

/-! `align`, `size` and `sizeTy` of term.k are least fixed points of their equations
(term-termination.toml): on the table `ty(0) |-> arr(ty(0), 2)` the type `ty(0)` contains itself,
K's rewriting does not terminate, and the functions have no value there. The gate elaborates this
file against the generated library kterm-ar. -/

namespace KTerm
open KPrelude

/-- The table whose entry for `ty(0)` is an array of `ty(0)`. -/
def cyclic : SortMap := MapHook.element (SortKItem.inj_Ty (SortTy.«ty(_)» 0))
  (SortKItem.inj_Info (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2))

theorem info_cyclic : K.info cyclic (SortTy.«ty(_)» 0) = some (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2) := by
  decide

/-- One function that matches its argument: `align(M, arr(ty(0), 2)) => align(M, arr(ty(0), 2))`. -/
theorem align_diverges : K.align cyclic (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2) = none := by
  refine K.align.fixpoint_induct cyclic (fun f => f (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2) = none)
    (Lean.Order.admissible_apply (fun _ v => v = none) _ (Lean.Order.admissible_flatOrder _ rfl))
    (fun f h => ?_)
  simp [info_cyclic, h]

/-- A group: `sizeTy(M, ty(0)) => size(M, arr(ty(0), 2)) => 2 *Int sizeTy(M, ty(0))`. -/
theorem sizeTy_diverges : K.sizeTy cyclic (SortTy.«ty(_)» 0) = none := by
  refine K.sizeTy.fixpoint_induct cyclic (fun f => f (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2) = none)
    (fun g => g (SortTy.«ty(_)» 0) = none)
    (Lean.Order.admissible_apply (fun _ v => v = none) _ (Lean.Order.admissible_flatOrder _ rfl))
    (Lean.Order.admissible_apply (fun _ v => v = none) _ (Lean.Order.admissible_flatOrder _ rfl))
    (fun g hg => ?_) (fun f hf => ?_)
  · simp [hg]
  · simp [info_cyclic, hf]

#k2l_assert_axioms KTerm.align_diverges
#k2l_assert_axioms KTerm.sizeTy_diverges

end KTerm
