import CoroJoin.ProgressDefs
import CoroJoin.Adequacy

/-! Hand-written proofs of the cases of `progress` listed in `open-progress-cases.txt`.

`k2lean gen` wrote this file once, because it did not exist, and never changes it. Prove each case below as the
theorem it names, or refute it (`theorem Progress.case.h.refuted : ¬ Progress.case.h.statement`, marked
`| refuted hand` in the list; a witness configuration, with `step_stuck` for its last part). The generated proofs use `k2l_progress [rules] => prog_close`, then
`exfalso; simp_all [Bool.false_eq_true, Ending.content, Ending.elem, Eqn.notBool__1, Eqn.notBool__2, Eqn.«ended(_)_COROJOIN_Bool_K_1», Eqn.«ended(_)_COROJOIN_Bool_K_2», Eqn.«ended(_)_COROJOIN_Bool_K_3», Eqn.«ended(_)_COROJOIN_Bool_K_4», Eqn.«itemOk(_)_COROJOIN_Bool_KItem_1», Eqn.«itemOk(_)_COROJOIN_Bool_KItem_2», Eqn.«itemOk(_)_COROJOIN_Bool_KItem_3», Eqn.«itemOk(_)_COROJOIN_Bool_KItem_4», Eqn.«itemOk(_)_COROJOIN_Bool_KItem_5», Eqn.«kOk(_)_COROJOIN_Bool_K_1», Eqn.«kOk(_)_COROJOIN_Bool_K_2», Invariant, Invariant.cell_T, Invariant.cell_k, Invariant.cell_procs, Invariant.content_k, Invariant.content_procs, Invariant.kOk, Invariant.kOk_elem, KPrelude.BoolHook.and, KPrelude.BoolHook.eq, KPrelude.BoolHook.implies, KPrelude.BoolHook.ne, KPrelude.BoolHook.not, KPrelude.BoolHook.or, KPrelude.BoolHook.xor, KPrelude.IntHook.add, KPrelude.IntHook.eq, KPrelude.IntHook.ge, KPrelude.IntHook.gt, KPrelude.IntHook.le, KPrelude.IntHook.lt, KPrelude.IntHook.mul, KPrelude.IntHook.ne, KPrelude.IntHook.sub, KPrelude.KEqHook.eq, KPrelude.KEqHook.ite, KPrelude.KEqHook.ne, KPrelude.bind_bool_eq_some_true, Option.bind_fun_some, Option.some.injEq, and_false, false_and, false_or, inj_Bool_KItem, inj_GeneratedCounterCellOpt_KItem, inj_GeneratedCounterCell_GeneratedCounterCellOpt, inj_GeneratedCounterCell_KItem, inj_GeneratedTopCellFragment_KItem, inj_GeneratedTopCell_KItem, inj_Instr_KItem, inj_Int_KItem, inj_KCellOpt_KItem, inj_KCell_KCellOpt, inj_KCell_KItem, inj_KConfigVar_KItem, inj_List_KItem, inj_Map_KItem, inj_NonceCellOpt_KItem, inj_NonceCell_KItem, inj_NonceCell_NonceCellOpt, inj_Pgm_KItem, inj_PidCellOpt_KItem, inj_PidCell_KItem, inj_PidCell_PidCellOpt, inj_Pid_KItem, inj_ProcCellFragment_KItem, inj_ProcCellMap_KItem, inj_ProcCell_KItem, inj_ProcsCellFragment_KItem, inj_ProcsCellOpt_KItem, inj_ProcsCell_KItem, inj_ProcsCell_ProcsCellOpt, inj_Set_KItem, inj_TCellFragment_KItem, inj_TCellOpt_KItem, inj_TCell_KItem, inj_TCell_TCellOpt, or_false, proj_GeneratedCounterCellOpt_GeneratedCounterCell, proj_KCellOpt_KCell, proj_KItem_Bool, proj_KItem_GeneratedCounterCell, proj_KItem_GeneratedCounterCellOpt, proj_KItem_GeneratedTopCell, proj_KItem_GeneratedTopCellFragment, proj_KItem_Instr, proj_KItem_Int, proj_KItem_KCell, proj_KItem_KCellOpt, proj_KItem_KConfigVar, proj_KItem_List, proj_KItem_Map, proj_KItem_NonceCell, proj_KItem_NonceCellOpt, proj_KItem_Pgm, proj_KItem_Pid, proj_KItem_PidCell, proj_KItem_PidCellOpt, proj_KItem_ProcCell, proj_KItem_ProcCellFragment, proj_KItem_ProcCellMap, proj_KItem_ProcsCell, proj_KItem_ProcsCellFragment, proj_KItem_ProcsCellOpt, proj_KItem_Set, proj_KItem_TCell, proj_KItem_TCellFragment, proj_KItem_TCellOpt, proj_NonceCellOpt_NonceCell, proj_PidCellOpt_PidCell, proj_ProcsCellOpt_ProcsCell, proj_TCellOpt_TCell]`. -/

namespace CoroJoin

open KPrelude

/-- Two processes that join each other: `root` at `join(child(root, 0))` and its child at
`join(root)`. Both satisfy `kOk`, neither has ended, and no rule applies: a deadlock. The case's
element is the child, whose key is the larger, so no element ranks above it. -/
theorem Progress.case.«Instr.join(_)».refuted : ¬ Progress.case.«Instr.join(_)».statement := by
  intro h
  let child := SortPid.«child(_,_)» SortPid.root 0
  let ec := SortProcCell.«<proc>» (SortPidCell.«<pid>» child) (SortNonceCell.«<nonce>» 0)
    (SortKCell.«<k>» (SortK.kseq (SortKItem.inj_Instr (SortInstr.«join(_)» SortPid.root)) SortK.dotk))
  let er := SortProcCell.«<proc>» (SortPidCell.«<pid>» SortPid.root) (SortNonceCell.«<nonce>» 1)
    (SortKCell.«<k>» (SortK.kseq (SortKItem.inj_Instr (SortInstr.«join(_)» child)) SortK.dotk))
  have hm : MapHook.concat (MapHook.element (SortPidCell.«<pid>» child) ec)
      (MapHook.element (SortPidCell.«<pid>» SortPid.root) er : SortProcCellMap) =
      some (MapHook.update (MapHook.element (SortPidCell.«<pid>» SortPid.root) er) (SortPidCell.«<pid>» child) ec) :=
    MapHook.concat_element_iff.2 ⟨MapHook.wf_element, by rfl, rfl⟩
  have hok : ∀ (k : SortPidCell) (e : SortProcCell) (r : SortProcCellMap), MapHook.concat (MapHook.element k e) r =
      some (MapHook.update (MapHook.element (SortPidCell.«<pid>» SortPid.root) er) (SortPidCell.«<pid>» child) ec) →
      (k = SortPidCell.«<pid>» child ∧ e = ec) ∨ (k = SortPidCell.«<pid>» SortPid.root ∧ e = er) := by
    intro k e r hk
    have hmem := MapHook.mem_toList_of_concat_element hk
    rw [MapHook.update_def] at hmem
    simp [ListIso.toList_ofList, MapHook.element] at hmem
    rcases SAL.mem_insert hmem with h1 | h1
    · left; simp_all
    · right; simp_all
  have hA : Progress.Above (MapHook.update (MapHook.element (SortPidCell.«<pid>» SortPid.root) er) (SortPidCell.«<pid>» child) ec) (SortPidCell.«<pid>» child) ec := by
    intro k' e' r' h' hlt
    rcases hok k' e' r' h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hlt (Nat.lt_irrefl _)
    · exfalso
      simp only [Progress.rank, child] at hlt
      simp [SortPidCell.«<pid>», SortPid.«child(_,_)», SortPid.root] at hlt
      omega
  have hok1 : ∀ e, e = ec ∨ e = er → Invariant.kOk_elem (SortPidCell.«<pid>» SortPid.root, e) := by
    rintro e (rfl | rfl) <;>
      simp [Invariant.kOk_elem, Invariant.cell_k, Invariant.content_k, ec, er, Eqn.«kOk(_)_COROJOIN_Bool_K_1»,
        Eqn.«kOk(_)_COROJOIN_Bool_K_2», Eqn.«itemOk(_)_COROJOIN_Bool_KItem_1», KPrelude.BoolHook.and]
  have hI : Invariant (SortGeneratedTopCell.«<generatedTop>» (SortTCell.«<T>» (SortProcsCell.«<procs>»
      (MapHook.update (MapHook.element (SortPidCell.«<pid>» SortPid.root) er) (SortPidCell.«<pid>» child) ec)))
      (SortGeneratedCounterCell.«<generatedCounter>» 0)) := by
    simp only [Invariant, Invariant.kOk, Invariant.cell_T, Invariant.cell_procs, Invariant.content_procs]
    exact MapHook.entriesOn_concat hm (MapHook.entriesOn_element (hok1 ec (Or.inl rfl)))
      (MapHook.entriesOn_element (hok1 er (Or.inr rfl)))
  have hK : Progress.Keys (SortGeneratedTopCell.«<generatedTop>» (SortTCell.«<T>» (SortProcsCell.«<procs>»
      (MapHook.update (MapHook.element (SortPidCell.«<pid>» SortPid.root) er) (SortPidCell.«<pid>» child) ec)))
      (SortGeneratedCounterCell.«<generatedCounter>» 0)) :=
    MapHook.entriesOn_concat hm (MapHook.entriesOn_element rfl) (MapHook.entriesOn_element rfl)
  have hE : ¬ Ending.elem ec := by
    simp [Ending.elem, Ending.content, ec]
    decide
  have := h SortPid.root SortK.dotk (SortNonceCell.«<nonce>» 0) (SortPidCell.«<pid>» child) _ _
    (SortGeneratedCounterCell.«<generatedCounter>» 0) hm hI hE hK hA
  exact step_stuck (by rfl) 0 this

end CoroJoin
