import TwoParamConf.Slots
import TwoParam.Measure

/-!
# The transaction statement of the parameterized form (`docs/direction.md` §8 step 4)

For a well-formed script (`wf`, the claims of its instructions distinct) that has one run to no task
left, every order its readiness allows ends, all in that run's configuration, whatever the lower
layer computes (`TwoParam.Hooks`, a parameter). It composes four results by name, restating none:
- the invariant, `wf` and the outputs' `valsOk`, holds at the start of a well-formed script: no
  output exists yet (`TwoParam.Invariant.init_holds`, `invariant_init`);
- every run from the script's start ends: the work left, `measure` in the fixture (a weight per
  task summed over the `<tasks>` cell map), is lowered by every rule (`TwoParam.Measure.lower`, every
  case by `k2l_measure`) and is defined at the start (`defined`), so `TwoParam.Measure.terminates`;
- every terminal configuration reached under the invariant is the same one
  (`TwoParamConf.terminal_unique`);
- the given run reaches a configuration with no task left, which has no step (`terminal_of_noTasks`).

`no_stuck` is what this says of every configuration such a script reaches: one that does not step
has no task left, in any order. `wf` is a hypothesis, a static fact about a concrete script (no
claim named twice); the run is one too, which a concrete script has only for a concrete lower layer
(`TwoLayerTx.transaction_run` computes it in the combined form).
-/

namespace TwoParamTx

open KPrelude

variable [TwoParam.Hooks]

/-- No task left: the `<tasks>` cell map is empty. -/
def NoTasks (c : TwoParam.SortGeneratedTopCell) : Prop :=
  ∃ p v n, c = .«<generatedTop>» (.«<T>» (.«<tasks>» MapHook.unit) p v) n

/-- A map a rule matches as `K |-> V REST` is not empty. -/
theorem concat_element_ne_unit {k : TwoParam.SortTidCell} {v : TwoParam.SortTaskCell}
    {r : TwoParam.SortTaskCellMap} (h : MapHook.concat (MapHook.element k v) r = some MapHook.unit) :
    False := by
  have := (MapHook.perm_toList_concat h).length_eq
  simp [MapHook.unit, MapHook.element, ListIso.toList_ofList] at this

/-- With no task left, no rule applies: each matches a task. -/
theorem terminal_of_noTasks {c : TwoParam.SortGeneratedTopCell} (h : NoTasks c) :
    Terminal TwoParam.Step c := by
  obtain ⟨p, v, n, rfl⟩ := h
  intro c' hs
  cases hs <;> exact concat_element_ne_unit ‹_›

/-- The measure is defined at a script's start: the work of the one task holding the script, `pw`
of it, which has a value by the fixture's lemma `pw(P) >=Int 0` (`TwoParam.Simp.s_7fb4767b11d6`,
which states the value nonnegative and so defined). -/
theorem defined (P : TwoParam.SortPgm) : (TwoParam.Measure.value (TwoParam.init P)).isSome := by
  have h := TwoParam.Simp.s_7fb4767b11d6 P
  cases hp : TwoParam.K.«pw(_)_TWOPARAM_Int_Pgm» P with
  | none => simp [hp] at h
  | some w =>
    simp only [TwoParam.Measure.value, TwoParam.Measure.cell_T, TwoParam.init,
      TwoParam.Eqn.«measure(_)_TWOPARAM_Int_TCell_1», Option.bind_fun_some]
    exact Option.isSome_iff_exists.2 ⟨_, (TwoParam.Measure.work_eq _ _).2 ⟨MapHook.wf_element,
      (MapHook.claimsDef_element (T := TwoParam.Measure.work_test) (g := TwoParam.Measure.work_g)).2
        ⟨rfl, by simp [TwoParam.Measure.work_g, TwoParam.Measure.cell_k, TwoParam.Measure.content_k,
          TwoParam.Eqn.«kw(_)_TWOPARAM_Int_K_2», hp]⟩, rfl⟩⟩

/-- The invariant at a well-formed script's start: `wf` is the hypothesis, and `valsOk` holds of
the empty `<vals>`. -/
theorem invariant_init {P : TwoParam.SortPgm} (hwf : TwoParam.Invariant.wf (TwoParam.init P)) :
    TwoParam.Invariant (TwoParam.init P) :=
  TwoParam.Invariant.init_holds P (by
    rw [TwoParam.Invariant.wf, TwoParam.Invariant.wf_cells] at hwf; exact hwf)

/-- **Every order of a script ends in its run's result.** If the script `P` is well formed and some
run from its start reaches a configuration `r` with no task left, then `r` is terminal and every run
from the start ends, in `r`. -/
theorem transaction {P : TwoParam.SortPgm} {r : TwoParam.SortGeneratedTopCell}
    (hwf : TwoParam.Invariant.wf (TwoParam.init P)) (hr : Star TwoParam.Step (TwoParam.init P) r)
    (hn : NoTasks r) :
    Terminal TwoParam.Step r ∧ Ends.Every TwoParam.Step (TwoParam.init P) (· = r) :=
  ⟨terminal_of_noTasks hn, Ends.every_of (TwoParam.Measure.terminates _ (defined P)) fun _ hb hbt =>
    TwoParamConf.terminal_unique (invariant_init hwf) hb hbt hr (terminal_of_noTasks hn)⟩

/-- **No stuck state.** For a script as in `transaction`, every configuration reached from its start
that does not step has no task left, whatever the lower layer computes. -/
theorem no_stuck {P : TwoParam.SortPgm} {r : TwoParam.SortGeneratedTopCell}
    (hwf : TwoParam.Invariant.wf (TwoParam.init P)) (hr : Star TwoParam.Step (TwoParam.init P) r)
    (hn : NoTasks r) {e : TwoParam.SortGeneratedTopCell} (he : Star TwoParam.Step (TwoParam.init P) e)
    (ht : Terminal TwoParam.Step e) : NoTasks e :=
  TwoParamConf.terminal_unique (invariant_init hwf) he ht hr (terminal_of_noTasks hn) ▸ hn

#k2l_assert_axioms terminal_of_noTasks defined invariant_init transaction no_stuck

end TwoParamTx
