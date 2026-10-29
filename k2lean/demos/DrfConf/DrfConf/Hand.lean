import DrfConf.Views
import Drf.Adequacy

/-! The slot of `DrfConf.Slots` that is false, refuted by hand: two workers with counts 1 and 2
each write `<acc>`, and the two writes do not join. After one write the only step is the other
worker's (`successors`, which lists every step: `successors_iff`), so the configurations reached
from the two first writes in at most one step are `<acc>` 1 then 2, and `<acc>` 2 then 1, and
none is reached from both. -/

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace DrfConf

open KPrelude Drf

/-- Worker `i` with count `n`, at its key. -/
def wk (i : Int) : SortWidCell := .«<wid>» i
def wr (i n : Int) : SortWorkerCell := .«<worker>» (wk i) (.«<todo>» n)

/-- The workers 0 and 1 with counts `n₀` and `n₁`. -/
def ws (n₀ n₁ : Int) : SortWorkerCellMap :=
  MapHook.update (MapHook.update MapHook.unit (wk 0) (wr 0 n₀)) (wk 1) (wr 1 n₁)

/-- The configuration of the workers `m` and the accumulator `a`, the program done. -/
def conf (m : SortWorkerCellMap) (a : Int) : SortGeneratedTopCell :=
  .«<generatedTop>» (.«<T>» (.«<k>» .dotk) (.«<workers>» m) (.«<acc>» a) (.«<next>» 2))
    (.«<generatedCounter>» 0)

/-- Worker 0 writes 1. -/
theorem put₀ : StepBy .put (conf (ws 1 2) 0) (conf (ws 0 2) 1) := fun _ h =>
  h _ _ _ _ _ (MapHook.element (wk 1) (wr 1 2)) 0 1 _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- Worker 1 writes 2. -/
theorem put₁ : StepBy .put (conf (ws 1 2) 0) (conf (ws 1 0) 2) := fun _ h =>
  h _ _ _ _ _ (MapHook.element (wk 0) (wr 0 1)) 1 2 _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- What each first write reaches in at most one step. -/
theorem reach {c d : SortGeneratedTopCell} (h : Opt Drf.Step c d) : d ∈ c :: successors c := by
  rcases h with rfl | h
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (successors_iff.mpr h)

theorem apart : ∀ d ∈ conf (ws 0 2) 1 :: successors (conf (ws 0 2) 1),
    d ∉ conf (ws 1 0) 2 :: successors (conf (ws 1 0) 2) := by
  decide +kernel

theorem hand.join.open.put.put.refuted : ¬ join.open.put.put.statement := fun h => by
  obtain ⟨a, b, ha, hb, e⟩ := h put₀ put₁
  subst e
  exact apart _ (reach ha) (reach hb)

#k2l_assert_axioms hand.join.open.put.put.refuted

end DrfConf
