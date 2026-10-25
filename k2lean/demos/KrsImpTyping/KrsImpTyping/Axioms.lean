import KrsImpTyping.Typing
import KrsImpTyping.Preserve
import KPrelude.Tactic

/-! Axiom guard of the typing invariant (hand-written; `Typing.lean` proves `Step.wt` by hand,
`Preserve.lean` re-proves it with `k2l_preserve`). -/

#k2l_assert_axioms KrsImp.Typing.Step.wt KrsImp.Typing.Reach.wt KrsImp.Typing.TStep_iff
#k2l_assert_axioms KrsImpTypingPres.wt_preserved KrsImpTypingPres.Step.wt KrsImpTypingPres.TStep_iff
