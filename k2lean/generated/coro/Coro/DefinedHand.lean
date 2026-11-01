import Coro.DefinedDefs
import Coro.Adequacy

/-! Hand-written proofs of the rules listed in `open-defined-rules.txt`.

`k2lean gen` wrote this file once, because it did not exist, and never changes it. Prove each rule's definedness
below as the theorem it names, or refute it (`theorem Defined.r.refuted : ¬ Defined.r.statement`, marked
`| refuted hand` in the list: an instance where the rule applies and no step exists). -/

namespace Coro

open KPrelude

/-- `spawn` is not defined under `kOk` alone: it inserts its child at `child(P, N)`, and `kOk` says
nothing of which keys exist. Here `root` is at `spawn` with nonce `0` while `child(root, 0)` is
already a key and has ended, so the rule applies (`kOk` holds) and nothing steps. The fact that
excludes this, a process's nonce above every child it has spawned, relates the bindings of the map
to each other, which no generated invariant closer reads yet (INV-14). -/
theorem Defined.spawn.refuted : ¬ Defined.spawn.statement := by
  intro h
  let kc : SortPidCell := SortPidCell.«<pid>» (SortPid.«child(_,_)» SortPid.root 0)
  let D : SortProcCellMap := MapHook.element kc
    (SortProcCell.«<proc>» kc (SortNonceCell.«<nonce>» 0) (SortKCell.«<k>» SortK.dotk))
  let kr : SortPidCell := SortPidCell.«<pid>» SortPid.root
  let vr : SortProcCell := SortProcCell.«<proc>» kr (SortNonceCell.«<nonce>» 0)
    (SortKCell.«<k>» (SortK.kseq (SortKItem.inj_Instr
      (SortInstr.«spawn(_)» SortPgm.«.List{"_;__CORO-SYNTAX_Pgm_Instr_Pgm"}_Pgm»)) SortK.dotk))
  have hm : MapHook.concat (MapHook.element kr vr) D = some (MapHook.update D kr vr) :=
    MapHook.concat_element_iff.2 ⟨MapHook.wf_element, by decide, rfl⟩
  obtain ⟨c', hs⟩ := h _ (SortGeneratedCounterCell.«<generatedCounter>» 0) D SortPid.root 0 _ SortK.dotk hm
    (MapHook.entriesOn_concat hm
      (MapHook.entriesOn_element (by
        simp [vr, Invariant.kOk_elem, Invariant.content_k, Invariant.cell_k,
          Eqn.«kOk(_)_CORO_Bool_K_1», Eqn.«kOk(_)_CORO_Bool_K_2», Eqn.«itemOk(_)_CORO_Bool_KItem_1»,
          BoolHook.and]))
      (MapHook.entriesOn_element (by
        simp [Invariant.kOk_elem, Invariant.content_k, Invariant.cell_k, Eqn.«kOk(_)_CORO_Bool_K_1»])))
    (by simp only [Progress.Keys, MapHook.EntriesOn]; decide +kernel)
    (fun _ h => absurd h (Nat.not_lt_zero _))
  have hnil : successors (SortGeneratedTopCell.«<generatedTop>» (SortTCell.«<T>»
      (SortProcsCell.«<procs>» (MapHook.update D kr vr))) (SortGeneratedCounterCell.«<generatedCounter>» 0)) = [] := by
    decide +kernel
  have := successors_iff.2 hs
  rw [hnil] at this
  simp at this

end Coro
