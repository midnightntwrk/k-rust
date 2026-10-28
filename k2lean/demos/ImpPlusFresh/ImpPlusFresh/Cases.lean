import ImpPlusFresh.Invariant
import KImpPlus.Preserves
import KPrelude.InvTactic
import KPrelude.InvColl

/-!
# Every rule of `KImpPlus` keeps `Invariant` (kind 2 layout: `Cases.lean`)

HAND-WRITTEN. `preserved` applies the generated `KImpPlus.Step.preserves_of` (62 rules) through
`k2l_preserve … hand ImpPlusFresh.hand`: the case of rule `r` is the theorem `ImpPlusFresh.hand.r` below when it
exists, and the tactic's closers prove it otherwise. A build logs
`k2l_preserve: N of M rules closed; hand: [...]; open: [...]`; each rule in `open` is an
`unsolved goals` error tagged by the rule, showing its goal `P lhs → P rhs` with the rule's
variables and side conditions in context. Give the closers more lemmas
(`k2l_preserve [l₁, …] split [f, …] hand …`), or prove the case by hand below:
`k2lean new-invariant --lib … --out … --from-log BUILD.log` adds a stub per open rule.

A hand case is stated as the generated `KImpPlus.Step.Case.r Invariant`, by reference, so an edit of
rule `r` changes what its hand case must prove and nothing else here; `k2lean diff OLD NEW --hand
THIS_PROJECT` lists the hand cases to revisit after a regeneration.
-/

namespace ImpPlusFresh

open KPrelude

/-- A location below the counter is below its successor. -/
theorem locBelow_succ {n : Int} : ∀ k, LocBelow n k → LocBelow (n + 1) k :=
  fun _ ⟨i, hk, hi⟩ => ⟨i, hk, by omega⟩

/-- An id at most the counter is at most its successor. -/
theorem idAtMost_succ {n : Int} : ∀ k, IdAtMost n k → IdAtMost (n + 1) k :=
  fun _ h => by unfold IdAtMost at *; omega

namespace hand

/-! ## HAND CASE `int X, Xs;` (imp.k:85:3)

`k2l_preserve` does not close this rule's case. Its statement is `KImpPlus.Step.Case.«int X, Xs;»` in
`KImpPlus/Preserves.lean`; after the introductions the goal is `P lhs → P rhs`, with the rule's
variables and side conditions in context. -/

theorem «int X, Xs;» : KImpPlus.Step.Case.«int X, Xs;» (Invariant) := by
  intro m DotVar2 Gen6 Gen7 Fresh k DotVar3 X Xs DotVar5 Rho r r_2 hm hr hr_3 hpri
  intro h
  simp only [Invariant, tCell, counterCell, counterVal, threadsCell, storeCell, threadMap, storeMap,
    KImpPlus.K.«freshInt(_)_INT_Int_Int», IntHook.add, Int.add_zero] at h hr hr_3 ⊢
  obtain ⟨hs, ht⟩ := h
  refine ⟨?_, ?_⟩
  · -- the new location is the counter's value, below its successor
    exact MapHook.entriesOn_concat hr_3 (MapHook.entriesOn_element ⟨Fresh, rfl, by omega⟩)
      (MapHook.entriesOn_mono hs fun p => locBelow_succ p.1)
  · -- the thread keeps its id
    have hk : IdAtMost Fresh k := MapHook.entry_of_concat_element hm ht
    exact MapHook.entriesOn_concat hr (MapHook.entriesOn_element (idAtMost_succ k hk))
      (MapHook.entriesOn_mono (MapHook.entriesOn_of_concat_right hm ht) fun p => idAtMost_succ p.1)

/-! ## HAND CASE `spawn S` (imp.k:101:3)

`k2l_preserve` does not close this rule's case. Its statement is `KImpPlus.Step.Case.«spawn S»` in
`KImpPlus/Preserves.lean`; after the introductions the goal is `P lhs → P rhs`, with the rule's
variables and side conditions in context. -/

theorem «spawn S» : KImpPlus.Step.Case.«spawn S» (Invariant) := by
  intro m Gen7 Gen5 Gen6 Fresh k DotVar2 S DotVar4 Rho r r_2 hm hr hr_3 hpri
  intro h
  simp only [Invariant, tCell, counterCell, counterVal, threadsCell, storeCell, threadMap,
    KImpPlus.K.«freshInt(_)_INT_Int_Int», IntHook.add, Int.add_zero] at h hr ⊢
  obtain ⟨hs, ht⟩ := h
  refine ⟨MapHook.entriesOn_mono hs fun p => locBelow_succ p.1, ?_⟩
  -- the new thread's id is the counter's successor, and the spawning thread keeps its id
  have hk : IdAtMost Fresh k := MapHook.entry_of_concat_element hm ht
  have hnew : MapHook.KeysOn (IdAtMost (Fresh + 1)) r :=
    MapHook.entriesOn_concat hr (MapHook.entriesOn_element (show idVal _ ≤ _ by simp [idVal]))
      (MapHook.entriesOn_element (idAtMost_succ k hk))
  exact MapHook.entriesOn_concat hr_3 hnew
    (MapHook.entriesOn_mono (MapHook.entriesOn_of_concat_right hm ht) fun p => idAtMost_succ p.1)

-- k2lean new-invariant --from-log: new hand cases go above this line
end hand

/-- Every rule of `KImpPlus` keeps `Invariant`. -/
theorem preserved : Preserved KImpPlus.Step Invariant := by
  k2l_preserve [tCell, counterCell, counterVal, threadsCell, storeCell, threadMap, storeMap, LocBelow, IdAtMost, idVal,
    KImpPlus.K.«freshInt(_)_INT_Int_Int»] hand ImpPlusFresh.hand

end ImpPlusFresh
