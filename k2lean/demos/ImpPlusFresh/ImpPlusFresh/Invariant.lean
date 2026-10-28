import KImpPlus.Rules
import KPrelude.InvColl

/-! IMP++'s fresh values stay fresh: every location of `<store>` is below K's generated counter,
and every thread's `<id>` is at most the counter. A rule that allocates (`int X, Xs;`, `spawn S`)
takes the counter's value as the new location (`!N`) or the counter plus one as the new thread's
id (`!T +Int 1`), and increments it; so the new key is not already a key. K cannot state this:
the counter is K's own cell, which the definition's syntax does not name. -/

namespace ImpPlusFresh

open KPrelude KImpPlus

/-- The `<T>` cell of a configuration. -/
def tCell : SortGeneratedTopCell → SortTCell
  | .«<generatedTop>» t _ => t

/-- The `<generatedCounter>` cell of a configuration. -/
def counterCell : SortGeneratedTopCell → SortGeneratedCounterCell
  | .«<generatedTop>» _ g => g

/-- The value of K's generated counter. -/
def counterVal : SortGeneratedCounterCell → Int
  | .«<generatedCounter>» n => n

/-- The `<threads>` cell of a `<T>` cell. -/
def threadsCell : SortTCell → SortThreadsCell
  | .«<T>» th _ _ _ => th

/-- The `<store>` cell of a `<T>` cell. -/
def storeCell : SortTCell → SortStoreCell
  | .«<T>» _ s _ _ => s

/-- The thread map of a `<threads>` cell. -/
def threadMap : SortThreadsCell → SortThreadCellMap
  | .«<threads>» m => m

/-- The map of a `<store>` cell. -/
def storeMap : SortStoreCell → SortMap
  | .«<store>» m => m

/-- A store location: an integer below `n`. -/
def LocBelow (n : Int) (k : SortKItem) : Prop := ∃ i : Int, k = SortKItem.inj_Int i ∧ i < n

/-- The integer of an `<id>` cell. -/
def idVal : SortIdCell → Int
  | .«<id>» i => i

/-- A thread id at most `n`. -/
def IdAtMost (n : Int) (k : SortIdCell) : Prop := idVal k ≤ n

/-- Every store location is below the counter, and every thread id is at most it. -/
def Invariant (c : SortGeneratedTopCell) : Prop :=
  MapHook.KeysOn (LocBelow (counterVal (counterCell c))) (storeMap (storeCell (tCell c))) ∧
    MapHook.KeysOn (IdAtMost (counterVal (counterCell c))) (threadMap (threadsCell (tCell c)))

end ImpPlusFresh
