import ImpTypes.Progress
import KPrelude.Soundness

/-!
# Type soundness as an instance of no stuck states (SND-16)

HAND-WRITTEN. `soundness`'s theorem (`ImpTypes.soundness`, `Soundness.lean`), derived instead from
`gen --progress` under `Typed` (`KImp.no_stuck`): a program the checker accepts starts typed
(`wt_init`), and an ending (`<k>` empty) is `Final`.
-/

namespace ImpTypes

open KPrelude

theorem final_of_ending {c : KImp.SortGeneratedTopCell} (h : KImp.Ending c) : Final c := by
  k2l_cases c with ⟨k, e, g⟩
  all_goals k2l_norm_idx
  k2l_cases k with ⟨k⟩
  all_goals k2l_norm_idx
  simp only [KImp.Ending, KImp.Ending.content] at h
  subst h
  trivial

theorem star_of_stepsN {n : Nat} {c c' : KImp.SortGeneratedTopCell} (h : StepsN KImp.Step n c c') :
    Star KImp.Step c c' := by
  induction h with
  | refl _ => exact Star.refl _
  | step hs _ ih => exact Star.step hs ih

/-- **Type soundness, from no stuck states.** The statement of `ImpTypes.soundness`. -/
theorem soundness_of_progress {G : TEnv} {P : KImp.SortStmt} {E : KImp.SortMap}
    {g : KImp.SortGeneratedCounterCell}
    (hP : KImpTypes.K.«wt(_,_)_IMP-TYPING_Bool_Stmt_Map» (tr_SortStmt P) G = some true) (hE : envTy G E)
    {n : Nat} {c : KImp.SortGeneratedTopCell} (h : StepsN KImp.Step n (init P E g) c) :
    Final c ∨ KImp.App c :=
  (KImp.no_stuck ⟨G, wt_init hP hE⟩ (star_of_stepsN h)).imp_left final_of_ending

#k2l_assert_axioms final_of_ending star_of_stepsN soundness_of_progress

end ImpTypes
