import KTerm.Diverges
import KPrelude.Tactic

/-! The proofs that K's rewriting of the least fixed points does not terminate (TERM-1).
Written once by k2lean and never overwritten: edit it. Each is `theorem F.diverges :
F.diverges.statement`, an infinite chain of pending calls (`KPrelude.Pending.chain_of_fixed`,
`chain_of_cycle`); `KTermTest/Diverges.lean` checks it. A group with no proof here is open.

`align`, `size` and `sizeTy` of term.k recurse on a type read from a table, an arbitrary map
(`term-termination.toml`): on the table `ty(0) |-> arr(ty(0), 2)` the type `ty(0)` contains
itself, and K's rewriting cycles: `align(M, arr(ty(0), 2))` waits for itself, and
`sizeTy(M, ty(0))` for `size(M, arr(ty(0), 2))`, which waits for `sizeTy(M, ty(0))`. -/

namespace KTerm

open KPrelude

/-- The table whose entry for `ty(0)` is an array of `ty(0)`. -/
def cyclic : SortMap := MapHook.element (SortKItem.inj_Ty (SortTy.«ty(_)» 0))
  (SortKItem.inj_Info (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2))

theorem info_cyclic : K.info cyclic (SortTy.«ty(_)» 0) = some (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2) := by
  decide

/-- The call has no value: the evaluation's cycle, read by the least fixed point's induction. -/
theorem align_none : K.align cyclic (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2) = none := by
  refine K.align.fixpoint_induct cyclic (fun f => f (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2) = none)
    (Lean.Order.admissible_apply (fun _ v => v = none) _ (Lean.Order.admissible_flatOrder _ rfl))
    (fun f h => ?_)
  simp [info_cyclic, h]

theorem sizeTy_none : K.sizeTy cyclic (SortTy.«ty(_)» 0) = none ∧
    K.size cyclic (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2) = none := by
  constructor
  · refine K.sizeTy.fixpoint_induct cyclic (fun f => f (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2) = none)
      (fun g => g (SortTy.«ty(_)» 0) = none)
      (Lean.Order.admissible_apply (fun _ v => v = none) _ (Lean.Order.admissible_flatOrder _ rfl))
      (Lean.Order.admissible_apply (fun _ v => v = none) _ (Lean.Order.admissible_flatOrder _ rfl))
      (fun g hg => ?_) (fun f hf => ?_)
    · simp [hg]
    · simp [info_cyclic, hf]
  · refine K.size.fixpoint_induct cyclic (fun f => f (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2) = none)
      (fun g => g (SortTy.«ty(_)» 0) = none)
      (Lean.Order.admissible_apply (fun _ v => v = none) _ (Lean.Order.admissible_flatOrder _ rfl))
      (Lean.Order.admissible_apply (fun _ v => v = none) _ (Lean.Order.admissible_flatOrder _ rfl))
      (fun g hg => ?_) (fun f hf => ?_)
    · simp [hg]
    · simp [info_cyclic, hf]

/-- `align(M, arr(ty(0), 2))` waits for itself. -/
theorem K.align.diverges : K.align.diverges.statement :=
  ⟨_, Pending.chain_of_fixed _ (.align cyclic (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2))
    (by simp [K.align.pending, info_cyclic, align_none])⟩

/-- `sizeTy(M, ty(0))` waits for `size(M, arr(ty(0), 2))`, which waits for `sizeTy(M, ty(0))`. -/
theorem K.size.diverges : K.size.diverges.statement :=
  ⟨_, Pending.chain_of_cycle _ [.sizeTy cyclic (SortTy.«ty(_)» 0),
      .size cyclic (SortInfo.«arr(_,_)» (SortTy.«ty(_)» 0) 2)] (by decide) (by
    intro i hi
    match i, hi with
    | 0, _ => simp [K.size.pending, info_cyclic, sizeTy_none.2]
    | 1, _ => simp [K.size.pending, sizeTy_none.1])⟩

end KTerm
