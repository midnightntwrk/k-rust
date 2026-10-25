import KrsImpTyping.Typing
import KrsImp.Invariants
import KPrelude.Tactic

/-! Hand-written. The invariant that `k2lean gen --sidecar demos/k/krs-imp/k2lean-sidecar.json`
generates from KRS's declared cell type `env: Map<Id, Value>` (`KrsImp.Invariant`, in the generated
`KrsImp/InvariantDefs.lean`) is the predicate `WT` of `Typing.lean` (written by hand), and
the generated `Invariant.preserved` gives `Typing.lean`'s `Step.wt`.

The two predicates differ only in how they say that a key is an `Id`: the generated one by the
projection (`∃ y, proj_KItem_Id k = some y`, the form it uses for every declared sort, since a
sort with subsorts such as `Value` has no single injection constructor), `Typing.lean` by the
constructor (`∃ y, k = SortKItem.inj_Id y`). `proj_eq_some_KItem_Id` makes them equal.

The configuration is split by `k2l_cases`, which in the arity-indexed universe also refutes the
constructors of the term family that no configuration has, and is `rcases` in the other. -/

namespace KrsImpTypingSidecar

open KPrelude KrsImp

theorem entry_iff (p : SortKItem × SortKItem) : Invariant.entry_env p ↔ Typing.EntryOk p := by
  unfold Invariant.entry_env Typing.EntryOk
  constructor
  · rintro ⟨⟨k, hk⟩, hv⟩
    exact ⟨⟨k, proj_eq_some_KItem_Id.1 hk⟩, hv⟩
  · rintro ⟨⟨k, hk⟩, hv⟩
    exact ⟨⟨k, proj_eq_some_KItem_Id.2 hk⟩, hv⟩

/-- The generated invariant is `Typing.lean`'s `WT`. -/
theorem inv_iff_wt (c : SortGeneratedTopCell) : Invariant c ↔ Typing.WT c := by
  k2l_cases c with ⟨_, ⟨m⟩, _⟩
  simp only [Invariant, Invariant.declared_env, Invariant.cell_env, Invariant.content_env, Typing.WT, Typing.EnvOk,
    MapHook.EntriesOn, entry_iff]

/-- `Typing.lean`'s `Step.wt`, from the generated `Invariant.preserved`. -/
theorem Step.wt {c c' : SortGeneratedTopCell} (h : Step c c') (hw : Typing.WT c) : Typing.WT c' :=
  (inv_iff_wt c').1 (Invariant.preserved c c' ((inv_iff_wt c).2 hw) h)

#k2l_assert_axioms entry_iff inv_iff_wt Step.wt

end KrsImpTypingSidecar
