import KRange.Invariants
import KPrelude.Tactic

/-! The heartbeat budget of one rule in `k2l_preserve` (`k2l.preserve.maxHeartbeats`).

The `Preserved` form of `tests/fixtures/range`'s invariant, with a budget of 2,000 per rule and no
bound on the proof itself (`maxHeartbeats 0`, since the elaboration after the tactic counts every
rule's heartbeats): `seq` and `set` close within it (measured: `set` at 500), `alloc`, whose
closers apply the `Int`-range lemma, does not (it needs between 5,000 and 10,000, Lean v4.34.0).
The heartbeat limit is a runtime exception, which `try … catch` rethrows; `k2l_preserve` catches it
around each rule's closers, so `alloc` is left open, restored, and the tactic goes on. `#guard_msgs`
checks the two log lines, and `alloc` is then proved by the generated case of the kind 1
invariant.

`preserved_cases` is the same proof in the per-case mode (`apply Step.preserves_of`, then
`all_goals k2l_preserve`): each rule has the same budget there, not what the rules before it left
of the theorem's count, so with `maxHeartbeats 0` `alloc` reaches it all the same. -/

namespace InvBudget

open KPrelude KRange

/--
info: k2l_preserve: rule alloc reached the heartbeat limit in its closers; it is left open
---
info: k2l_preserve: 2 of 3 rules closed; open: [alloc]
-/
#guard_msgs in
set_option maxHeartbeats 0 in
set_option k2l.preserve.maxHeartbeats 2000 in
theorem preserved : Preserved Step Invariant := by
  k2l_preserve [Invariant.storeNat, Invariant.cell_store, Invariant.content_store, Eqn.«isNat(_)_RANGE_Bool_KItem_1», Eqn.«isNat(_)_RANGE_Bool_KItem_2», Eqn.«storeNat(_)_RANGE_Bool_Map_1», Invariant.natVals_iff, Option.bind_fun_some]
  case alloc => apply Invariant.case.alloc <;> assumption

/--
info: k2l_preserve: rule alloc reached the heartbeat limit in its closers; it is left open
---
info: k2l_preserve: rule alloc not closed; the goal is its case, with the rule's variables and side conditions introduced
-/
#guard_msgs in
set_option maxHeartbeats 0 in
set_option k2l.preserve.maxHeartbeats 2000 in
theorem preserved_cases : Preserved Step Invariant := by
  apply Step.preserves_of
  all_goals k2l_preserve [Invariant.storeNat, Invariant.cell_store, Invariant.content_store, Eqn.«isNat(_)_RANGE_Bool_KItem_1», Eqn.«isNat(_)_RANGE_Bool_KItem_2», Eqn.«storeNat(_)_RANGE_Bool_Map_1», Invariant.natVals_iff, Option.bind_fun_some]
  case alloc => apply Invariant.case.alloc <;> assumption

#k2l_assert_axioms preserved preserved_cases

end InvBudget
