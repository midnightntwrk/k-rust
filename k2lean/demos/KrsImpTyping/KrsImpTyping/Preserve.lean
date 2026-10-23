import KrsImpTyping.Typing
import KPrelude.InvTactic
import KPrelude.InvColl
import KPrelude.Tactic

/-! Hand-written. `Step.wt` of `Typing.lean` (KRS's declared cell type `env: Map<Id, Value>` is
preserved by all 82 rules of the generated KRS IMP), re-proved with the invariant core
(`KPrelude.Invariant`) and `k2l_preserve` only, over `Typing.lean`'s own `WT`. -/

namespace KrsImpTypingPres

open KPrelude KrsImp KrsImp.Typing

theorem wt_preserved : Preserved Step WT := by
  k2l_preserve [EnvOk, EntryOk]

/-- The statement of `KrsImp.Typing.Step.wt`. -/
theorem Step.wt {c c' : SortGeneratedTopCell} (h : Step c c') (hw : WT c) : WT c' :=
  wt_preserved c c' hw h

/-- The typed view from the core, at `WT`. -/
theorem TStep_iff (t : TConfig WT) (c' : SortGeneratedTopCell) :
    Step t.1 c' ↔ ∃ t' : TConfig WT, t'.1 = c' ∧ KPrelude.TStep Step WT t t' :=
  KPrelude.TStep_iff wt_preserved t c'

#k2l_assert_axioms wt_preserved Step.wt TStep_iff

end KrsImpTypingPres
