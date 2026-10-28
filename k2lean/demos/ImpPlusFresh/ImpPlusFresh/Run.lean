import ImpPlusFresh.Cases
import KImpPlus.Init
import KPrelude.InvSteps
import KPrelude.Tactic

/-!
# Every run keeps `Invariant` (kind 2 layout: `Run.lean`)

HAND-WRITTEN, stable under edits of the K rules (it depends on the configuration declaration
only, through the generated `KImpPlus.init`). `init_holds` is `Invariant` at the initial configuration
for the configuration variables `pgm`, `stdin`, `io`, with no hypothesis on them: the store starts
empty, the one thread has id `0`, and the counter starts at `0`. `star` and `stepsN` extend it to
every configuration reachable from there; `store_fresh` and `thread_fresh` are what it is for.
-/

namespace ImpPlusFresh

open KPrelude

/-- The initial configuration satisfies `Invariant`: its store is empty, its one thread has id `0`,
and the counter starts at `0`. -/
theorem init_holds (pgm : KImpPlus.SortStmts) (stdin : KImpPlus.SortString) (io : KImpPlus.SortString) : Invariant (KImpPlus.init pgm stdin io) := by
  simp only [Invariant, KImpPlus.init, tCell, counterCell, counterVal, threadsCell, storeCell,
    threadMap, storeMap]
  exact ⟨MapHook.entriesOn_unit, MapHook.entriesOn_element (show idVal _ ≤ _ by simp [idVal])⟩

/-- Every configuration reachable from the initial configuration satisfies `Invariant`. -/
theorem star {pgm : KImpPlus.SortStmts} {stdin : KImpPlus.SortString} {io : KImpPlus.SortString} {c : KImpPlus.SortGeneratedTopCell} (h : Star KImpPlus.Step (KImpPlus.init pgm stdin io) c) : Invariant c :=
  preserved.star h (init_holds pgm stdin io)

/-- Every configuration reached in `n` steps from the initial configuration satisfies `Invariant`. -/
theorem stepsN {pgm : KImpPlus.SortStmts} {stdin : KImpPlus.SortString} {io : KImpPlus.SortString} {n : Nat} {c : KImpPlus.SortGeneratedTopCell} (h : StepsN KImpPlus.Step n (KImpPlus.init pgm stdin io) c) : Invariant c :=
  preserved.stepsN h (init_holds pgm stdin io)

/-- What the invariant is for: at a configuration that satisfies it, the location the next `int`
allocates (the counter's value) is not a key of `<store>`, so the rule's `concat` is defined. -/
theorem store_fresh {c : KImpPlus.SortGeneratedTopCell} (h : Invariant c) (v : KImpPlus.SortKItem) :
    (KImpPlus.SortKItem.inj_Int (counterVal (counterCell c)), v) ∉
      ListIso.toList (storeMap (storeCell (tCell c))) := by
  intro hm
  obtain ⟨i, hk, hi⟩ := h.1 _ hm
  cases hk
  omega

/-- The id the next `spawn` gives (the counter's successor) is not the key of a thread, so the
rule's `concat` is defined. -/
theorem thread_fresh {c : KImpPlus.SortGeneratedTopCell} (h : Invariant c) (t : KImpPlus.SortThreadCell) :
    (KImpPlus.SortIdCell.«<id>» (counterVal (counterCell c) + 1), t) ∉
      ListIso.toList (threadMap (threadsCell (tCell c))) := by
  intro hm
  have := h.2 _ hm
  simp only [IdAtMost, idVal] at this
  omega

#k2l_assert_axioms store_fresh thread_fresh preserved hand.«int X, Xs;» hand.«spawn S» init_holds star stepsN

end ImpPlusFresh
