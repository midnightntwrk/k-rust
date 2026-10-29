import ImpTypes.Soundness

/-!
# kimp's runtime typing as the legality of `gen --progress` (SND-16)

HAND-WRITTEN. Type soundness is the no stuck states theorem under the checker's typing: `Typed`
is the runtime typing that `k2lean soundness` generates (`WTc envTy G`: `<k>` a well-typed
continuation, the store typed by `envTy`), under some typing environment. It is the kind 2
invariant of kimp's `gen --progress` (`--assume-invariant ImpTypes.Typed`), whose cases are in
`Progress.lean` (namespace `KImp`) and whose one hand case is in `ProgressHand.lean`; `Instance.lean`
derives `soundness`'s theorem from them.
-/

namespace ImpTypes

open KPrelude

/-- A configuration typed under some typing environment. -/
def Typed (c : KImp.SortGeneratedTopCell) : Prop := ∃ G, WTc envTy G c

/-- Every rule keeps `Typed`: it keeps `WTc envTy G` for each `G` (`preserved`). -/
theorem Typed.preserved : Preserved KImp.Step Typed :=
  fun c c' ⟨G, h⟩ hs => ⟨G, ImpTypes.preserved G c c' h hs⟩

#k2l_assert_axioms Typed.preserved

end ImpTypes
