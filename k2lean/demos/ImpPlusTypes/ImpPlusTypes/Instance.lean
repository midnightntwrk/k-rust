import ImpPlusTypes.Progress

/-!
# IMP++'s type soundness as an instance of no stuck states (SND-17)

HAND-WRITTEN. `soundness`'s theorem (`ImpPlusTypes.soundness`, `Soundness.lean`), derived instead
from `gen --progress` under `Typed` (`KImpPlus.no_stuck`): a program the checker accepts starts
typed (`wt_init`) with its one thread at its key cell (`keys_init`), and an ending (every thread
`kDone`) is `Final`, since the typing makes the thread map well formed, so that each of its bindings
is a match `K |-> V REST`.
-/

namespace ImpPlusTypes

open KPrelude

/-- An ending is `Final`: both say every thread is `kDone`, one of each match of the thread map,
the other of each binding, which are the same bindings in a well-formed map. -/
theorem final_of_ending {c : KImpPlus.SortGeneratedTopCell} (hw : MapHook.WF (threadsOf c))
    (h : KImpPlus.Ending c) : Final c := by
  have hm : KImpPlus.Progress.map c = threadsOf c := by
    k2l_cases c with ⟨⟨⟨m⟩, _, _, _⟩, _⟩
    rfl
  refine Classical.byContradiction fun hn => ?_
  obtain ⟨k, e, r, he, hq⟩ := MapHook.exists_not_of_not_entriesOn hw hn
  have hd := h k e r (by rw [hm]; exact he)
  -- `Ending.elem` and `kDone ∘ kOf` read the same cell, the same way, once `e` is a thread
  apply hq
  k2l_cases e with ⟨_, ⟨_⟩, _⟩
  all_goals exact hd

/-- The initial configuration's one thread is at its key cell. -/
theorem keys_init (P : KImpPlus.SortStmts) (i : KImpPlus.SortIdCell) (g : KImpPlus.SortEnvCell)
    (g_2 : KImpPlus.SortStoreCell) (g_3 : KImpPlus.SortInputCell) (g_4 : KImpPlus.SortOutputCell)
    (g_5 : KImpPlus.SortGeneratedCounterCell) : KImpPlus.Progress.Keys (init P i g g_2 g_3 g_4 g_5) :=
  MapHook.entriesOn_element rfl

theorem star_of_stepsN {n : Nat} {c c' : KImpPlus.SortGeneratedTopCell}
    (h : StepsN KImpPlus.Step n c c') : Star KImpPlus.Step c c' := by
  induction h with
  | refl _ => exact Star.refl _
  | step hs _ ih => exact Star.step hs ih

/-- **Type soundness, from no stuck states.** The statement of `ImpPlusTypes.soundness`. -/
theorem soundness_of_progress {G : TEnv} {P : KImpPlus.SortStmts} {i : KImpPlus.SortIdCell}
    {g : KImpPlus.SortEnvCell} {g_2 : KImpPlus.SortStoreCell} {g_3 : KImpPlus.SortInputCell}
    {g_4 : KImpPlus.SortOutputCell} {g_5 : KImpPlus.SortGeneratedCounterCell}
    (hP : KImpPlusTypes.K.«wts(_,_)_IMPPLUS-TYPING_Bool_Stmts_Map» (tr_SortStmts P) G = some true)
    {n : Nat} {c : KImpPlus.SortGeneratedTopCell} (h : StepsN KImpPlus.Step n (init P i g g_2 g_3 g_4 g_5) c) :
    Final c ∨ Applies c :=
  (KImpPlus.no_stuck ⟨G, wt_init hP⟩ (keys_init P i g g_2 g_3 g_4 g_5) (star_of_stepsN h)).imp
    (final_of_ending (wt_stepsN h (wt_init hP)).1) id

#k2l_assert_axioms final_of_ending keys_init star_of_stepsN soundness_of_progress

end ImpPlusTypes
