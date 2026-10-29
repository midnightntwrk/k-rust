import HandoffSeqRel.Sim
import HandoffConf.Slots
import KPrelude.Forward
import Handoff.Init
import HandoffSeq.Init

/-! The script's result is the one every ready order gives: `handoffseq`'s steps are matched by
`handoff`'s (`sim`, a `Forward.Sim`), at the script's end `handoff` has no task left (`sim_end`),
and every run of `handoff` to a terminal configuration ends there (`HandoffConf.terminal_unique`,
under the script's well-formedness: `wf` in K, the generated `Handoff.Invariant`). The composition
is the prelude's `Forward.result_unique_of`.

The well-formedness is not assumed: a script that runs to its end in order names no claim twice
(`claims_of_run`), so its initial configuration satisfies `wf` (`HandoffConf.invariant_init`). A
creation needs its process to be absent, and a resume needs its process at the turn it names and
moves it to the next, so no process is created twice and no turn is resumed twice. -/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HandoffSeqRel

open KPrelude MapHook MapRep HandoffConf

variable [Handoff.Hooks]

/-- `handoffseq` has run its script to the end. -/
def Done (s : HandoffSeq.SortGeneratedTopCell) : Prop := ∃ sp sv c, s = scfg .dotk sp sv c

theorem not_done {s : HandoffSeq.SortGeneratedTopCell} {P : HandoffSeq.SortPgm} {f : Procs} {g : Vals}
    (h : SAt s P f g) (hd : Done s) : False := by
  obtain ⟨sp, sv, c, rfl, -, -⟩ := h
  obtain ⟨sp', sv', c', e⟩ := hd
  simp at e

theorem terminal_done {sp sv : HandoffSeq.SortMap} {c : HandoffSeq.SortGeneratedCounterCell} :
    Terminal HandoffSeq.Step (scfg .dotk sp sv c) := by
  intro c' h; cases h

/-- Both at the same point of the script, or both done. -/
def Rel (s : HandoffSeq.SortGeneratedTopCell) (r : Handoff.SortGeneratedTopCell) : Prop :=
  Sim s r ∨ Fin s r

/-- `handoffseq`'s steps are matched by `handoff`'s. -/
theorem sim : Forward.Sim HandoffSeq.Step Handoff.Step Rel := by
  intro s s' r h st
  rcases h with h | ⟨f, g, ⟨sp, sv, c, rfl, -, -⟩, -⟩
  · exact step_sim h st
  · exact (terminal_done _ st).elim

/-- At the script's end, `handoff` is terminal, with the same bindings. -/
theorem sim_end {s : HandoffSeq.SortGeneratedTopCell} {r : Handoff.SortGeneratedTopCell} (h : Rel s r)
    (hd : Done s) : ∃ r', Star Handoff.Step r r' ∧ Terminal Handoff.Step r' ∧ Fin s r' := by
  rcases h with ⟨P, f, g, hs, -⟩ | ⟨f, g, hsd, ⟨rp, rv, c, rfl, hp, hv⟩⟩
  · exact (not_done hs hd).elim
  · exact ⟨_, .refl _, terminal_rdone, f, g, hsd, rp, rv, c, rfl, hp, hv⟩

/-! ## The script's well-formedness, from a run to its end -/

/-- A claim that the bindings `f` still allow: a process not yet created, a turn not yet passed. -/
def Fresh (f : Procs) : Claim → Prop
  | .inr Q => f Q = none
  | .inl (Q, N) => ∀ M S, f Q = some (M, S) → M ≤ N

theorem fresh_new {f : Procs} {Q S : Int} {l : List Claim} (l₀ : f Q = none)
    (h : l.Nodup ∧ ∀ x ∈ l, Fresh (upd f Q (0, S)) x) :
    (.inr Q :: l).Nodup ∧ ∀ x ∈ (.inr Q :: l : List Claim), Fresh f x := by
  refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, h.1⟩, fun x hx => ?_⟩
  · have := h.2 _ hm; simp [Fresh, upd] at this
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact l₀
    have hf := h.2 x hx
    rcases x with ⟨Q', M⟩ | Q'
    · intro M' S' e
      by_cases hq : Q' = Q
      · subst hq; rw [l₀] at e; cases e
      · exact hf M' S' (by simp [upd, hq, e])
    · by_cases hq : Q' = Q
      · subst hq; simp [Fresh, upd] at hf
      · simpa [Fresh, upd, hq] using hf

theorem fresh_resume {f : Procs} {Q N S S' : Int} {l : List Claim} (l₀ : f Q = some (N, S))
    (h : l.Nodup ∧ ∀ x ∈ l, Fresh (upd f Q (IntHook.add N 1, S')) x) :
    (.inl (Q, N) :: l).Nodup ∧ ∀ x ∈ (.inl (Q, N) :: l : List Claim), Fresh f x := by
  refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, h.1⟩, fun x hx => ?_⟩
  · have := h.2 _ hm (IntHook.add N 1) S' (by simp [upd])
    simp [IntHook.add] at this; omega
  · rcases List.mem_cons.1 hx with rfl | hx
    · intro M S'' e
      rw [l₀] at e; cases e; exact Int.le_refl _
    have hf := h.2 x hx
    rcases x with ⟨Q', M⟩ | Q'
    · intro M' S'' e
      by_cases hq : Q' = Q
      · subst hq
        rw [l₀] at e; cases e
        have := hf (IntHook.add N 1) S' (by simp [upd])
        simp [IntHook.add] at this; omega
      · exact hf M' S'' (by simp [upd, hq, e])
    · by_cases hq : Q' = Q
      · subst hq; simp [Fresh, upd] at hf
      · simpa [Fresh, upd, hq] using hf

/-- A script that `handoffseq` runs to its end names no creation and no turn twice, and only
creations and turns that the bindings it starts from allow. -/
theorem claims_of_run {s t : HandoffSeq.SortGeneratedTopCell} (h : Star HandoffSeq.Step s t) (ht : Done t) :
    ∀ {P f g}, SAt s P f g →
      (pclaims (trPgm P)).Nodup ∧ ∀ x ∈ pclaims (trPgm P), Fresh f x := by
  induction h with
  | refl s => intro P f g hs; exact (not_done hs ht).elim
  | step st rest ih =>
    intro P f g hs
    obtain ⟨sp, sv, c, rfl, hp, hv⟩ := hs
    cases st with
    | new Q S P₁ _ _ _ sp' hr =>
      simp only [trPgm_cons, trInstr, pclaims, iclaims, List.singleton_append]
      exact fresh_new (rep_none pkS_inj hp (concat_element_iff.1 hr).2.1)
        (ih ht ⟨sp', sv, c, rfl, rep_insert pkS_inj hp hr, hv⟩)
    | «resume-lit» Q N V P₁ _ D3 _ D2 S r9 sp' r4 sv' hm hr hr_3 hr_5 hr_7 =>
      simp only [trPgm_cons, trInstr, pclaims, iclaims, List.singleton_append]
      exact fresh_resume (rep_some pkS_inj pvS_inj hp (lookup_of_concat_element hm))
        (ih ht ⟨sp', sv', c, rfl, rep_rebind pkS_inj hp hm hr_3, rep_insert (a := (Q, N)) vkS_inj hv hr_7⟩)
    | «resume-oid» Q N I P₁ _ _ _ D2 S D3 V r9 sp' r10 x sv' hm hm_6 hr hr_9 hr_11 hr_13 hr_15 =>
      simp only [trPgm_cons, trInstr, pclaims, iclaims, List.singleton_append]
      exact fresh_resume (rep_some pkS_inj pvS_inj hp (lookup_of_concat_element hm))
        (ih ht ⟨sp', sv', c, rfl, rep_rebind pkS_inj hp hm hr_9, rep_insert2 (a := (Q, N)) vkS_inj hv hm_6 hr_13 hr_15⟩)
    | nil => simp [trPgm_nil, pclaims]

/-- Both definitions start from the script `P` with no process and no value. -/
theorem sim_init (P : HandoffSeq.SortPgm) : Rel (HandoffSeq.init P) (Handoff.init (trPgm P)) :=
  .inl ⟨P, fun _ => none, fun _ => none, ⟨unit, unit, _, rfl, rep_unit, rep_unit⟩,
    ⟨0, unit, unit, _, Int.le_refl 0, by rw [← element_eq_update]; rfl, rep_unit, rep_unit⟩⟩

/-! ## The script's result -/

/-- The run of the script in its order is a run of `handoff`: it ends with no task left, at the
same bindings. -/
theorem run_exists {P : HandoffSeq.SortPgm} {s : HandoffSeq.SortGeneratedTopCell}
    (hs : Star HandoffSeq.Step (HandoffSeq.init P) s) (hd : Done s) :
    ∃ r, Star Handoff.Step (Handoff.init (trPgm P)) r ∧ Terminal Handoff.Step r ∧ Fin s r :=
  Forward.result_of sim (fun _ _ => sim_end) (sim_init P) hs hd

/-- **The script's result is the one every ready order gives.** If `handoffseq` runs the script `P`
to its end, then every run of `handoff` from `P` to a terminal configuration leaves no task and
ends with the same processes and values: the same bindings of `<procs>` and `<vals>`. -/
theorem result_unique {P : HandoffSeq.SortPgm} {s : HandoffSeq.SortGeneratedTopCell}
    {r : Handoff.SortGeneratedTopCell} (hs : Star HandoffSeq.Step (HandoffSeq.init P) s) (hd : Done s)
    (hr : Star Handoff.Step (Handoff.init (trPgm P)) r) (ht : Terminal Handoff.Step r) : Fin s r :=
  have hw : Handoff.Invariant (Handoff.init (trPgm P)) :=
    HandoffConf.invariant_init (claims_of_run hs hd ⟨unit, unit, _, rfl, rep_unit, rep_unit⟩).1
  Forward.result_unique_of sim (fun _ _ => sim_end) (fun _ _ => terminal_unique hw) (sim_init P) hs hd hr ht

#k2l_assert_axioms result_unique run_exists

end HandoffSeqRel
