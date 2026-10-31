import HandoffSeqRel.Run
import HandoffConf.Ends

/-! The transaction theorem of a script (`product.md` §4): for a script that runs to its end in its
own order, every order its readiness allows ends, all in one configuration, which is the result of
the script's own order. It composes three results by name, restating none:
- every run of `handoff` ends (`HandoffConf.terminates`, the work left drops at every step);
- every terminal configuration reached is the same one (`HandoffConf.terminal_unique`, under the
  well-formedness that the script's run gives, `invariant_of_run`);
- the script's own order reaches it, with no task left and the same bindings of `<procs>` and
  `<vals>` (`run_exists`, `Fin`).

No task left is an acceptable ending: every task's `<k>` is empty, vacuously. A script whose
own order does not run to its end is outside this statement; for it, an acceptable ending under
the script's closure alone needs that a rule which applies takes a step (`HandoffConf/Live.lean`). -/

set_option linter.unusedVariables false

namespace HandoffSeqRel

open KPrelude

variable [Handoff.Hooks]

/-- **Every order of a script ends in its own order's result.** If `handoffseq` runs the script `P`
to its end, some run of `handoff` from `P` reaches a terminal configuration `r` with no task left
and the bindings of that run, and every run of `handoff` from `P` ends, in `r`. -/
theorem transaction {P : HandoffSeq.SortPgm} {s : HandoffSeq.SortGeneratedTopCell}
    (hs : Star HandoffSeq.Step (HandoffSeq.init P) s) (hd : Done s) :
    ∃ r, Star Handoff.Step (Handoff.init (tr_SortPgm P)) r ∧ Terminal Handoff.Step r ∧ Fin s r ∧
      Ends.Every Handoff.Step (Handoff.init (tr_SortPgm P)) (· = r) := by
  obtain ⟨r, hr, ht, hf⟩ := run_exists hs hd
  exact ⟨r, hr, ht, hf, Ends.every_of (HandoffConf.terminates _) fun b hb hbt =>
    HandoffConf.terminal_unique (invariant_of_run hs hd) hb hbt hr ht⟩

#k2l_assert_axioms transaction

end HandoffSeqRel
