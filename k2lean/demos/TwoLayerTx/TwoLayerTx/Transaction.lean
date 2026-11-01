import TwoConf.Legal.Slots
import TwoLayer.Measure
import TwoLayer.Adequacy

/-!
# The transaction statement of the combined form (`docs/direction.md` §8 step 4)

For a well-formed script (`wf`, the claims of its instructions and running segments distinct) that
has one run to no task left, every order its readiness allows ends, all in that run's configuration.
Unlike `TwoParamTx`, a segment is not one step: its small steps (`add`, `dbl`, `loop`, `yield`) are
rules of their own, interleaved with the other tasks'. It composes three results by name:
- every run from the script's start ends: the work left, `measure` in the fixture (a weight per task
  summed over the `<tasks>` cell map, plus the steps of each suspended process's code left summed
  over `<procs>`), is lowered by every rule (`TwoLayer.Measure.lower`, every case by
  `k2l_measure`) and is defined at the start (`defined`), so `TwoLayer.Measure.terminates`;
- every terminal configuration reached under `wf` is the same one (`TwoConf.Legal.terminal_unique`);
- the given run reaches a configuration with no task left, which has no step (`terminal_of_noTasks`).

`no_stuck` is what this says of every configuration such a script reaches: one that does not step
has no task left, in any order. For a concrete script, both hypotheses are computed: `wf` is a
static fact about the script, and the run is the library's executable `run` (`run_sound`), so
`transaction_run` takes only its result (`TwoLayerTx/Example.lean`). By `no_stuck`, if the script
can finish at all, the order `run` takes finishes too.
-/

namespace TwoLayerTx

open KPrelude

/-- No task left: the `<tasks>` cell map is empty. -/
def NoTasks (c : TwoLayer.SortGeneratedTopCell) : Prop :=
  ∃ p v n, c = .«<generatedTop>» (.«<T>» (.«<tasks>» MapHook.unit) p v) n

/-- A map a rule matches as `K |-> V REST` is not empty. -/
theorem concat_element_ne_unit {k : TwoLayer.SortTidCell} {v : TwoLayer.SortTaskCell}
    {r : TwoLayer.SortTaskCellMap} (h : MapHook.concat (MapHook.element k v) r = some MapHook.unit) :
    False := by
  have := (MapHook.perm_toList_concat h).length_eq
  simp [MapHook.unit, MapHook.element, ListIso.toList_ofList] at this

/-- With no task left, no rule applies: each matches a task. -/
theorem terminal_of_noTasks {c : TwoLayer.SortGeneratedTopCell} (h : NoTasks c) :
    Terminal TwoLayer.Step c := by
  obtain ⟨p, v, n, rfl⟩ := h
  intro c' hs
  cases hs <;> exact concat_element_ne_unit ‹_›

/-- The measure is defined at a script's start: the work of the one task holding the script, `pw`
of it, which has a value by the fixture's lemma `pw(P) >=Int 0` (`TwoLayer.Simp.s_d904b378633d`),
and no process yet (`pwork` of the empty map is `0`). -/
theorem defined (P : TwoLayer.SortPgm) : (TwoLayer.Measure.value (TwoLayer.init P)).isSome := by
  have h := TwoLayer.Simp.s_d904b378633d P
  cases hp : TwoLayer.K.«pw(_)_TWOLAYER_Int_Pgm» P with
  | none => simp [hp] at h
  | some w =>
    simp only [TwoLayer.Measure.value, TwoLayer.Measure.cell_T, TwoLayer.init,
      TwoLayer.Eqn.«measure(_)_TWOLAYER_Int_TCell_1», TwoLayer.Measure.pwork_unit, Option.bind_some]
    rw [Option.isSome_iff_exists]
    exact ⟨_, Option.bind_eq_some_iff.2 ⟨_, (TwoLayer.Measure.work_eq _ _).2 ⟨MapHook.wf_element,
      (MapHook.claimsDef_element (T := TwoLayer.Measure.work_test) (g := TwoLayer.Measure.work_g)).2
        ⟨rfl, by simp [TwoLayer.Measure.work_g, TwoLayer.Measure.cell_k, TwoLayer.Measure.content_k,
          TwoLayer.Eqn.«kw(_)_TWOLAYER_Int_K_2», hp]⟩, rfl⟩, rfl⟩⟩

/-- **Every order of a script ends in its run's result.** If the script `P` is well formed and some
run from its start reaches a configuration `r` with no task left, then `r` is terminal and every run
from the start ends, in `r`. -/
theorem transaction {P : TwoLayer.SortPgm} {r : TwoLayer.SortGeneratedTopCell}
    (hwf : TwoLayer.Invariant (TwoLayer.init P)) (hr : Star TwoLayer.Step (TwoLayer.init P) r)
    (hn : NoTasks r) :
    Terminal TwoLayer.Step r ∧ Ends.Every TwoLayer.Step (TwoLayer.init P) (· = r) :=
  ⟨terminal_of_noTasks hn, Ends.every_of (TwoLayer.Measure.terminates _ (defined P)) fun _ hb hbt =>
    TwoConf.Legal.terminal_unique hwf hb hbt hr (terminal_of_noTasks hn)⟩

/-- **No stuck state.** For a script as in `transaction`, every configuration reached from its start
that does not step has no task left. -/
theorem no_stuck {P : TwoLayer.SortPgm} {r : TwoLayer.SortGeneratedTopCell}
    (hwf : TwoLayer.Invariant (TwoLayer.init P)) (hr : Star TwoLayer.Step (TwoLayer.init P) r)
    (hn : NoTasks r) {e : TwoLayer.SortGeneratedTopCell} (he : Star TwoLayer.Step (TwoLayer.init P) e)
    (ht : Terminal TwoLayer.Step e) : NoTasks e :=
  TwoConf.Legal.terminal_unique hwf he ht hr (terminal_of_noTasks hn) ▸ hn

/-- `transaction` with the run computed: the library's `run` from the script's start, which takes
only `Step`s (`TwoLayer.run_sound`). -/
theorem transaction_run {P : TwoLayer.SortPgm} (fuel : Nat)
    (hwf : TwoLayer.Invariant (TwoLayer.init P)) (hn : NoTasks (TwoLayer.run fuel (TwoLayer.init P)).config) :
    Terminal TwoLayer.Step (TwoLayer.run fuel (TwoLayer.init P)).config ∧
      Ends.Every TwoLayer.Step (TwoLayer.init P) (· = (TwoLayer.run fuel (TwoLayer.init P)).config) :=
  transaction hwf (Star.of_stepsN (TwoLayer.run_sound fuel _)) hn

#k2l_assert_axioms terminal_of_noTasks defined transaction no_stuck transaction_run

end TwoLayerTx
