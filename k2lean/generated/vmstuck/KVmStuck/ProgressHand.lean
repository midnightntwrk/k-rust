import KVmStuck.ProgressDefs
import KVmStuck.Adequacy

/-! Hand-written proofs of the cases of `progress` listed in `open-progress-cases.txt`.

`k2lean gen` wrote this file once, because it did not exist, and never changes it. Prove each case below as the
theorem it names, or refute it (`theorem Progress.case.h.refuted : ¬ Progress.case.h.statement`, marked
`| refuted hand` in the list; a witness configuration, with `step_stuck` for its last part). The generated proofs use `k2l_progress [rules] => prog_close`, then
`exfalso; simp_all [Bool.false_eq_true, Ending, Ending.content, Eqn.«_=/=Int__1», Eqn.«halted(_)_VMSTUCK_Bool_K_1», Eqn.«halted(_)_VMSTUCK_Bool_K_2», Eqn.«halted(_)_VMSTUCK_Bool_K_3», Eqn.«itemOk(_)_VMSTUCK_Bool_KItem_1», Eqn.«itemOk(_)_VMSTUCK_Bool_KItem_2», Eqn.«itemOk(_)_VMSTUCK_Bool_KItem_3», Eqn.«itemOk(_)_VMSTUCK_Bool_KItem_4», Eqn.«kOk(_)_VMSTUCK_Bool_K_1», Eqn.«kOk(_)_VMSTUCK_Bool_K_2», Invariant, Invariant.cell_T, Invariant.cell_k, Invariant.content_k, Invariant.kOk, KPrelude.BoolHook.and, KPrelude.BoolHook.eq, KPrelude.BoolHook.implies, KPrelude.BoolHook.ne, KPrelude.BoolHook.not, KPrelude.BoolHook.or, KPrelude.BoolHook.xor, KPrelude.IntHook.add, KPrelude.IntHook.eq, KPrelude.IntHook.ge, KPrelude.IntHook.gt, KPrelude.IntHook.le, KPrelude.IntHook.lt, KPrelude.IntHook.mul, KPrelude.IntHook.ne, KPrelude.IntHook.sub, KPrelude.KEqHook.eq, KPrelude.KEqHook.ite, KPrelude.KEqHook.ne, KPrelude.bind_bool_eq_some_true, Option.bind_fun_some, Option.some.injEq, and_false, false_and, false_or, inj_Bool_KItem, inj_GeneratedCounterCellOpt_KItem, inj_GeneratedCounterCell_GeneratedCounterCellOpt, inj_GeneratedCounterCell_KItem, inj_GeneratedTopCellFragment_KItem, inj_GeneratedTopCell_KItem, inj_Instr_KItem, inj_Int_KItem, inj_KCellOpt_KItem, inj_KCell_KCellOpt, inj_KCell_KItem, inj_KConfigVar_KItem, inj_List_KItem, inj_Map_KItem, inj_Pgm_KItem, inj_Set_KItem, inj_StackCellOpt_KItem, inj_StackCell_KItem, inj_StackCell_StackCellOpt, inj_Stack_KItem, inj_Status_KItem, inj_TCellFragment_KItem, inj_TCellOpt_KItem, inj_TCell_KItem, inj_TCell_TCellOpt, or_false, proj_GeneratedCounterCellOpt_GeneratedCounterCell, proj_KCellOpt_KCell, proj_KItem_Bool, proj_KItem_GeneratedCounterCell, proj_KItem_GeneratedCounterCellOpt, proj_KItem_GeneratedTopCell, proj_KItem_GeneratedTopCellFragment, proj_KItem_Instr, proj_KItem_Int, proj_KItem_KCell, proj_KItem_KCellOpt, proj_KItem_KConfigVar, proj_KItem_List, proj_KItem_Map, proj_KItem_Pgm, proj_KItem_Set, proj_KItem_Stack, proj_KItem_StackCell, proj_KItem_StackCellOpt, proj_KItem_Status, proj_KItem_TCell, proj_KItem_TCellFragment, proj_KItem_TCellOpt, proj_StackCellOpt_StackCell, proj_TCellOpt_TCell]`. -/

namespace KVmStuck

open KPrelude

/-- `pop` on an empty stack: the configuration satisfies `kOk`, has not halted, and no rule applies
(the rule that halts `pop` on an empty stack is missing from `vmstuck.k`). -/
theorem Progress.case.«Instr.pop».refuted : ¬ Progress.case.«Instr.pop».statement := by
  intro h
  have := h SortK.dotk (SortGeneratedCounterCell.«<generatedCounter>» 0) (SortStackCell.«<stack>» SortStack.«.Stack»)
    (by simp [Invariant, Invariant.kOk, Invariant.cell_T, Invariant.cell_k, Invariant.content_k,
              Eqn.«kOk(_)_VMSTUCK_Bool_K_1», Eqn.«kOk(_)_VMSTUCK_Bool_K_2», Eqn.«itemOk(_)_VMSTUCK_Bool_KItem_1»,
              KPrelude.BoolHook.and])
    (by simp [Ending, Ending.content]; decide)
  exact step_stuck (by rfl) this

end KVmStuck
