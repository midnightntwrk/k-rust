import ImpPlusTypes.Soundness

/-!
# IMP++'s runtime typing as the legality of `gen --progress` (SND-17)

HAND-WRITTEN. Type soundness is the no stuck states theorem under the checker's typing: `Typed` is
the runtime typing that `k2lean soundness` generates (`WTc G`: every thread's `<k>` a well-typed
continuation), under some typing environment. It is the kind 2 invariant of IMP++'s
`gen --progress` (`--assume-invariant ImpPlusTypes.Typed`), with `<k>` in the cell map `<threads>`;
`Typed.thread` is what it says of each element (`--element-fact`), and the ending is `kDone`
(`--ending-lean`): a thread is finished, or waits at `join(T);`, which the language lets it do
forever (`join(0);` waits on itself). The cases are in `Progress.lean` (namespace `KImpPlus`);
`Instance.lean` derives `soundness`'s theorem from them.
-/

namespace ImpPlusTypes

open KPrelude

/-- A configuration typed under some typing environment. -/
def Typed (c : KImpPlus.SortGeneratedTopCell) : Prop := ∃ G, WTc G c

/-- Every rule keeps `Typed`: it keeps `WTc G` for each `G` (`preserved`). -/
theorem Typed.preserved : Preserved KImpPlus.Step Typed :=
  fun c c' ⟨G, h⟩ hs => ⟨G, ImpPlusTypes.preserved G c c' h hs⟩

/-- A thread whose `<k>` is a well-typed continuation that leaves nothing. -/
def ThreadTyped (e : KImpPlus.SortThreadCell) : Prop := ∃ G, kty G none (kOf e) = true

/-- What `Typed` says of a thread of the configuration: its `<k>` is well typed. -/
theorem Typed.thread {c : KImpPlus.SortGeneratedTopCell} {k : KImpPlus.SortIdCell}
    {e : KImpPlus.SortThreadCell} {r : KImpPlus.SortThreadCellMap}
    (h : Typed c) (hm : MapHook.concat (MapHook.element k e) r = some (threadsOf c)) : ThreadTyped e :=
  let ⟨G, _, hall⟩ := h
  ⟨G, (MapHook.entry_of_concat_element hm hall).2⟩

#k2l_assert_axioms Typed.preserved Typed.thread

end ImpPlusTypes
