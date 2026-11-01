import TwoLayerTx.Transaction

/-!
# One transaction, every order (`docs/direction.md` §8 step 4)

A concrete script of the combined form, with nothing assumed. Two processes pass outputs to each
other: process 1 yields `7` from `5`, process 2 adds `2` to it and yields `9`, and process 1, resumed
with that, doubles `16` and yields `32`. Every order its readiness allows ends with no task left and
the one output `o(1, 1) |-> 32` (both others are spent). `transaction_run` gives that from two
computed facts:
- `wf`: the script names no claim twice, from the claims' equations and `decide` (`wf_script`);
- the run: `TwoLayer.run` from the script's start ends with no task left (`run_ends`), and its
  configuration holds that output (`run_vals`), both by the kernel's evaluation (`rfl`).

The kernel evaluates `run` here because the code has no `loop`: `loop`'s step calls `app`, which is
defined by well-founded recursion and does not reduce in the kernel. The library's fuel twins
(`NS/Fuel.lean`), which would evaluate it, are not generated for twolayer, since functions that are
not recursive (`kclaims`, the measure's `iw`) call well-founded ones.
-/

namespace TwoLayerTx.Example

open KPrelude TwoLayer

/-- The empty code and the empty script. -/
abbrev nilS : SortStmts := .«.List{"_;__TWOLAYER-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»
abbrev nilP : SortPgm := .«.List{"_&__TWOLAYER-SYNTAX_Pgm_Instr_Pgm"}_Pgm»

/-- `new(1, {add(2) ; yield ; dbl ; yield}) & new(2, {add(1) ; add(1) ; yield})
& resume(1, 0, 5) & resume(2, 0, o(1, 0)) & resume(1, 1, o(2, 0))`. -/
def script : SortPgm :=
  .«_&_» (.«new(_,_)» 1 (.«{_}» (.«_;_» (.«add(_)» 2) (.«_;_» .yield (.«_;_» .dbl (.«_;_» .yield nilS))))))
  (.«_&_» (.«new(_,_)» 2 (.«{_}» (.«_;_» (.«add(_)» 1) (.«_;_» (.«add(_)» 1) (.«_;_» .yield nilS)))))
  (.«_&_» (.«resume(_,_,_)» 1 0 (.inj_Int 5))
  (.«_&_» (.«resume(_,_,_)» 2 0 (.inj_Oid (.«o(_,_)» 1 0)))
  (.«_&_» (.«resume(_,_,_)» 1 1 (.inj_Oid (.«o(_,_)» 2 0))) nilP))))

/-- The outputs of a configuration. -/
def valsOf : SortGeneratedTopCell → SortMap
  | .«<generatedTop>» (.«<T>» _ _ (.«<vals>» v)) _ => v

/-- The script is well formed: its one task's claims, computed by their equations, repeat nothing. -/
theorem wf_script : TwoLayer.Invariant (init script) := by
  show Invariant.wf _
  unfold Invariant.wf; rw [Invariant.wf_cells]
  simp only [init, Invariant.cell_T, Invariant.cell_tasks, Option.bind_fun_some]
  rw [Invariant.mclaims_noDup]
  refine ⟨MapHook.wf_element, MapHook.entriesOn_element ⟨rfl, ?_⟩, rfl, ?_⟩ <;>
    (try rw [MapHook.claimsOf_element]) <;>
    simp only [Invariant.mclaims_g, Invariant.cell_k, Invariant.content_k, script,
      Eqn.«kclaims(_)_TWOLAYER_List_K_2», Eqn.«pclaims(_)_TWOLAYER_List_Pgm_1»,
      Eqn.«pclaims(_)_TWOLAYER_List_Pgm_2», Eqn.«iclaims(_)_TWOLAYER_List_Instr_1»,
      Eqn.«iclaims(_)_TWOLAYER_List_Instr_2», Eqn.«iclaims(_)_TWOLAYER_List_Instr_3»,
      Option.bind_some, Option.bind_fun_some, Option.map_some, Option.getD_some] <;>
    decide

/-- The library's run from the script's start ends with no task left. -/
theorem run_ends : NoTasks (run 100 (init script)).config := ⟨_, _, _, rfl⟩

/-- and with the one output `o(1, 1) |-> 32`. -/
theorem run_vals : valsOf (run 100 (init script)).config =
    MapHook.element (.inj_Oid (.«o(_,_)» 1 1)) (.inj_Int 32) := rfl

/-- **Every order of the script ends with no task left and the output `o(1, 1) |-> 32`.** -/
theorem every_order : Ends.Every Step (init script) fun c =>
    NoTasks c ∧ valsOf c = MapHook.element (.inj_Oid (.«o(_,_)» 1 1)) (.inj_Int 32) := by
  intro s h0 hs
  obtain ⟨n, ht, he⟩ := (transaction_run 100 wf_script run_ends).2 s h0 hs
  exact ⟨n, ht, he ▸ ⟨run_ends, run_vals⟩⟩

#k2l_assert_axioms wf_script run_ends run_vals every_order

end TwoLayerTx.Example
