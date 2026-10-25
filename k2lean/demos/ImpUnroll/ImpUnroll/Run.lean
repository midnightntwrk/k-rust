import ImpUnroll.Refine

/-! What the stuttering bisimulation says of whole runs: a run of kimp to a terminal state (final,
stuck or undefined) and the variant's run from the translation of its start end in states that
are translations of each other. `X` never relates a terminal state of kimp, which can always
complete its one-armed `if`. -/

namespace ImpUnroll

open KPrelude

theorem not_terminal_of_X {c : KImp.SortGeneratedTopCell} {d : KUnroll.SortGeneratedTopCell}
    (h : X c d) : ¬ Terminal KImp.Step c := by
  cases h
  exact fun ht => ht _ (KImp.Step.«IMP.if-else» _ _ _ _ _)

theorem run_terminal {c c' : KImp.SortGeneratedTopCell} (h : Star KImp.Step c c')
    (ht : Terminal KImp.Step c') :
    ∃ d', Star KUnroll.Step (tr_SortGeneratedTopCell c) d' ∧ Terminal KUnroll.Step d' ∧
      d' = tr_SortGeneratedTopCell c' := by
  obtain ⟨d', hd, htd, hr | hx⟩ := run_fwd h ht
  · exact ⟨d', hd, htd, hr⟩
  · exact absurd ht (not_terminal_of_X hx)

theorem run_terminal_back {c : KImp.SortGeneratedTopCell} {d' : KUnroll.SortGeneratedTopCell}
    (h : Star KUnroll.Step (tr_SortGeneratedTopCell c) d') (ht : Terminal KUnroll.Step d') :
    ∃ c', Star KImp.Step c c' ∧ Terminal KImp.Step c' ∧ d' = tr_SortGeneratedTopCell c' := by
  obtain ⟨c', hc, htc, hr | hx⟩ := run_bwd h ht
  · exact ⟨c', hc, htc, hr⟩
  · exact absurd htc (not_terminal_of_X hx)

#k2l_assert_axioms not_terminal_of_X run_terminal run_terminal_back

end ImpUnroll
