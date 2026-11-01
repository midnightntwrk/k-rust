import TwoOutConf.Views
import TwoLayer.Equations

/-! The witness `two-spends` satisfies `wfOut`, by hand: the root task's claims, computed by their
equations, repeat nothing (two resumes spend `o(3, 0)`, which `wfOut` does not claim). The kernel
does not evaluate the claims' functions, which recurse well-founded, so the proof takes the map
apart and rewrites by the equations before `decide`, as `TwoLayerTx`'s `wf_script` does. -/

set_option maxHeartbeats 0

namespace TwoOutConf

open KPrelude TwoLayer

/-- A map literal of one binding is that binding. -/
theorem ofEntries_one {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V] (k : K) (v : V) :
    (MapHook.ofEntries [(k, v)] : M) = MapHook.element k v := by
  simp [MapHook.ofEntries, MapHook.update_def, MapHook.element, MapHook.unit, ListIso.toList_ofList,
    SAL.insert]

theorem hand.witness.«two-spends».legal : TwoLayer.Invariant witness.«two-spends» := by
  show Invariant.wfOut _
  unfold Invariant.wfOut; rw [Invariant.wfOut_cells]
  simp only [witness.«two-spends», Invariant.cell_T, Invariant.cell_tasks, Option.bind_fun_some,
    ofEntries_one]
  rw [Invariant.mclaimsOut_noDup]
  refine ⟨MapHook.wf_element, MapHook.entriesOn_element ⟨rfl, ?_⟩, rfl, ?_⟩ <;>
    (try rw [MapHook.claimsOf_element]) <;>
    simp only [Invariant.mclaimsOut_g, Invariant.cell_k, Invariant.content_k,
      Eqn.«kclaimsOut(_)_TWOLAYER_List_K_2», Eqn.«pclaimsOut(_)_TWOLAYER_List_Pgm_1»,
      Eqn.«pclaimsOut(_)_TWOLAYER_List_Pgm_2», Eqn.«iclaimsOut(_)_TWOLAYER_List_Instr_1»,
      Eqn.«iclaimsOut(_)_TWOLAYER_List_Instr_2»,
      Option.bind_some, Option.bind_fun_some, Option.map_some, Option.getD_some] <;>
    decide

end TwoOutConf
