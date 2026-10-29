import HandoffConf.ProgressDefs
import Handoff.Adequacy

/-! Hand-written proofs of the cases of `progress` listed in `open-progress-cases.txt`.

`k2lean gen` wrote this file once, because it did not exist, and never changes it. The one case
here is `resume`, which waits on the shared cells `<procs>` and `<vals>`, not on a partner element:
what it waits for is done because a task that still claims it would rank higher (`Live`'s
acyclic order, `HandoffConf.taskRank`), so would be an ending, and an ending runs nothing. -/

set_option linter.unusedVariables false

namespace Handoff

variable [Hooks]

open KPrelude HandoffConf

/-- What a task with one pending instruction waits for is done: a task claiming it would rank
higher (`Closed.acyc`), so would be an ending (`Above`), and an ending has nothing to run. -/
theorem Progress.deps_sat {m rest : SortTaskCellMap} {kc : SortTidCell} {e : SortTaskCell}
    {i : SortInstr} {x : Claim} {p : SortMap}
    (hm : MapHook.concat (MapHook.element kc e) rest = some m) (hie : instrs e = [i])
    (hx : iclaims i = [x]) (hc : Closed m p) (hA : Progress.Above m kc e) :
    ∀ d ∈ deps i, sat p d := by
  have hp : PendI m i := ⟨kc, e, MapHook.lookup_of_concat_element hm, by rw [hie]; simp⟩
  intro d hd
  rcases hc.ready i hp d hd with s | ⟨i', ⟨k', t', hl, hi'⟩, hd'⟩
  · exact s
  exfalso
  have lt := acyc_H hc.acyc i hp x (by rw [hx]; simp) d hd ⟨i', ⟨k', t', hl, hi'⟩, hd'⟩
  have re : taskRank m kc e = H m x := by simp [taskRank, hie, hx]
  have le := le_taskRank (m := m) (k := k') hi' hd'
  have en := hA k' t' _ (MapHook.concat_element_remove (MapHook.wf_of_concat_element hm) hl)
    (by simp only [Progress.rank]; omega)
  k2l_cases t' with ⟨a, b, ⟨K⟩⟩
  all_goals k2l_norm_idx
  simp only [Ending.elem, Ending.content] at en
  subst en
  simp [instrs] at hi'

/-- `resume(Q, N, I)`: `Q` is at turn `N` (its previous turn is done, its own is not), and the input
is bound to an `Int` (the turn that writes it is done, `Live.ledger`); `resume-lit` or `resume-oid`
applies, its matches rebuilt from the lookups. -/
theorem Progress.hand.«Instr.resume(_,_,_)» : Progress.case.«Instr.resume(_,_,_)».statement := by
  intro Q N I R e0_1 kc rest m x0_1 x1_1 x1_2 hm hI hE hK hA
  have := hI.taskOk hm
  simp [TaskOk] at this
  subst this
  k2l_cases x1_1 with ⟨p⟩
  all_goals k2l_norm_idx
  k2l_cases x1_2 with ⟨v⟩
  all_goals k2l_norm_idx
  have po : ∀ k w, MapHook.lookup p k = some w → ∃ M S, w = st M S ∧ 0 ≤ M := hI.procs_ok
  have pw : MapHook.WF p := hI.procs_wf
  have vw : MapHook.WF v := hI.vals_wf
  have led : ∀ Q N, doneP p Q N →
      ∃ V, MapHook.lookup v (.inj_Oid (.«o(_,_)» Q N)) = some (.inj_Int V) := hI.ledger
  have ds : ∀ d ∈ deps (.«resume(_,_,_)» Q N I), sat p d :=
    Progress.deps_sat hm rfl rfl hI.closed hA
  have hp : PendI m (.«resume(_,_,_)» Q N I) :=
    ⟨kc, _, MapHook.lookup_of_concat_element hm, by simp [instrs]⟩
  have fr : ¬ doneP p Q N := hI.closed.fresh _ hp (.inl (Q, N)) (by simp [iclaims])
  -- `Q` is at turn `N`
  have turn : ∃ S, MapHook.lookup p (.inj_Int Q) = some (st N S) := by
    have d1 := ds (if N = 0 then .inr Q else .inl (Q, N - 1)) (by simp [deps])
    by_cases h0 : N = 0
    · subst h0
      simp only [ite_true] at d1
      obtain ⟨w, hl⟩ := d1
      obtain ⟨M, S, rfl, hM⟩ := po _ _ hl
      have : ¬ (0 < M) := fun h => fr ⟨M, S, hl, Int.le_refl 0, h⟩
      exact ⟨S, by rw [hl, show M = 0 by omega]⟩
    · simp only [h0, ite_false] at d1
      obtain ⟨M, S, hl, h1, h2⟩ := d1
      have hNM : ¬ ((N : Int) < M) := fun h => fr ⟨M, S, hl, by omega, h⟩
      have hMN : M = N := by
        have h3 := Int.not_lt.mp hNM
        omega
      exact ⟨S, by rw [hl, hMN]⟩
  obtain ⟨S, hl⟩ := turn
  have hm5 := MapHook.concat_element_remove pw hl
  k2l_cases I with ⟨V⟩
  all_goals k2l_norm_idx
  · k2l_cases V with ⟨P, M⟩
    all_goals k2l_norm_idx
    have d2 := ds (.inl (P, M)) (by simp [deps])
    obtain ⟨W, hW⟩ := led P M d2
    exact App.«resume-oid» m p v x0_1 kc rest e0_1 Q N _ _ S _ W hm hm5
      (MapHook.concat_element_remove vw hW)
  · exact App.«resume-lit» m p v x0_1 kc rest e0_1 Q N V _ S hm hm5

end Handoff
