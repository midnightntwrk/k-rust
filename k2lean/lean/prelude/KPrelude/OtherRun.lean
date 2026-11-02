import Lean
import KPrelude.Scaffold

/-!
# The other run's priority premise (`k2lean noninterference` with priority ranks)

A step by a rule of rank `i > 0` carries `hpri : ∀ j, j < i → ¬ App j c`: no rule of an earlier
rank applies at `c`. In noninterference's `SameQ`, the other run, at the same low stack, takes the
same rule, and that step owes the premise at the other configuration `c₂`. It holds when every
rule of an earlier rank that applies at `c₂` applies at `c` too: its left-hand side clashes with
the common stack, or it reads only what the two configurations share, so its `App` is rebuilt at
`c` from the same hypotheses, against `c`'s `hpri`. A rule of an earlier rank that reads a cell the
two configurations do not share (the store, a private input) is not rebuilt: that rule's `SameQ`
case is the hand module's (`docs/design.md` §3.7).

- `k2l_ctor_assumption`: closes a goal that is an application of an inductive predicate by one of
  its constructors whose premises are all hypotheses, each constructor tried in turn.
- `k2l_pri_other`: closes `∀ j, j < i → ¬ App j c₂` from a hypothesis `∀ j, j < i → ¬ App j c₁` in
  the context, by cases on the `App j c₂` assumed (a rank `≥ i` by `omega`, a clash by `cases`)
  and `k2l_ctor_assumption` at `c₁`.

The same premise after another step (`k2lean confluence`, two steps from one configuration
commuted): a step at `c` by a rule of rank `i > 0` is taken again after the other step, at `c₁`,
and owes `hpri` there. A rule of an earlier rank that applies at `c₁` applies at `c` when the other
step did not enable it: it reads only cells the step left alone, or it matches the map the step
updated at a binding the step did not write.

- `k2l_pri_map hm hr`: closes `App j c` from a match `concat (element K V) R' = some r` in the
  context, a binding of `c₁`'s map `r`, where the step updated `c`'s map `m` at `k`
  (`hm : concat (element k v) R = some m`, `hr : concat (element k w) R = some r`): at `K = k` the
  match's value is `w` (refuted by `cases` when the pattern's differs), at another key it is a
  binding of `m` too (`MapHook.concat_element_same_or_comm`), rebuilt by `k2l_ctor_assumption`.
- `k2l_pri_back hp` and `k2l_pri_back hp hm hr`: close `∀ j, j < i → ¬ App j c₁` from `hp`, the
  premise at `c`, by cases on the `App j c₁` assumed and, at `c`, `k2l_ctor_assumption` or
  `k2l_pri_map hm hr`.
-/

namespace KPrelude.OtherRun

open Lean Meta Elab Tactic in
/-- Close the goal, an inductive predicate applied to its indices, by a constructor whose premises
are all hypotheses: each constructor is applied in turn, its propositions closed by `assumption`
(which also fixes the arguments they mention), then its other arguments. -/
elab "k2l_ctor_assumption" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  let .const n _ := t.getAppFn | throwError "k2l_ctor_assumption: the goal is not an inductive predicate"
  let some (.inductInfo i) := (← getEnv).find? n
    | throwError "k2l_ctor_assumption: {n} is not an inductive type"
  for c in i.ctors do
    let s ← saveState
    try
      let gs ← g.apply (← mkConstWithFreshMVarLevels c)
      let props ← gs.filterM fun g' => do isProp (← g'.getType)
      let rest ← gs.filterM fun g' => do return !(← isProp (← g'.getType))
      for g' in props ++ rest do
        unless ← g'.isAssigned do g'.assumption
      return
    catch _ => s.restore
  throwError "k2l_ctor_assumption: no constructor of {n} applies by hypotheses"

open Lean Meta Elab Tactic in
/-- Close `∀ j, j < i → ¬ App j c₂` (the other run's priority premise) from a hypothesis
`∀ j, j < i → ¬ App j c₁`: assume `App j c₂`, case on it, and rebuild each case at `c₁`. -/
elab "k2l_pri_other" : tactic => withMainContext do
  let g ← getMainGoal
  let (fs, g) ← g.introN 3
  let [j, hj, ha] := fs.toList | throwError "k2l_pri_other: the goal is not `∀ j, j < i → ¬ _`"
  replaceMainGoal [g]
  withMainContext do
    for d in ← getLCtx do
      if d.isImplementationDetail || d.fvarId == ha || d.fvarId == hj || d.fvarId == j then continue
      unless (← whnfR (← instantiateMVars d.type)).isForall do continue
      let s ← saveState
      try
        let h ← Term.exprToSyntax (mkFVar d.fvarId)
        let jt ← Term.exprToSyntax (mkFVar j)
        let hjt ← Term.exprToSyntax (mkFVar hj)
        let hat ← Term.exprToSyntax (mkFVar ha)
        evalTactic (← `(tactic| (
          refine $h $jt $hjt ?_
          cases $hat:term <;> first | omega | k2l_ctor_assumption)))
        if (← getUnsolvedGoals).isEmpty then return
        throwError "k2l_pri_other: goals remain"
      catch _ => s.restore
    throwError "k2l_pri_other: no hypothesis `∀ j, j < i → ¬ App j c` gives the premise"

open Lean Meta Elab Tactic in
/-- Close `App j c` from a binding of the updated map `r` in the context (`k2l_pri_map hm hr`): each
hypothesis `concat (element K V) R' = some r` is tried in turn. -/
elab "k2l_pri_map " hm:term:max hr:term:max : tactic => withMainContext do
  let he ← Term.elabTerm hr none
  let me ← Term.elabTerm hm none
  let r ← (do
    let t ← instantiateMVars (← inferType he)
    let some (_, _, rhs) := t.eq? | throwError "k2l_pri_map: {hr} is not an equation"
    unless rhs.isAppOfArity ``Option.some 2 do throwError "k2l_pri_map: {hr} is not `_ = some r`"
    pure rhs.appArg!)
  for d in ← getLCtx do
    if d.isImplementationDetail || mkFVar d.fvarId == he || mkFVar d.fvarId == me then continue
    let t ← instantiateMVars d.type
    let some (_, lhs, rhs) := t.eq? | continue
    unless lhs.getAppFn.constName? == some ``KPrelude.MapHook.concat do continue
    unless rhs.isAppOfArity ``Option.some 2 do continue
    unless ← isDefEq rhs.appArg! r do continue
    let s ← saveState
    try
      let h ← Term.exprToSyntax (mkFVar d.fvarId)
      evalTactic (← `(tactic| (
        rcases KPrelude.MapHook.concat_element_same_or_comm $hr $h $hm $h with ⟨-, hv, -⟩ | ⟨_, _, _, a, -, -, -⟩
        all_goals first | (cases hv; done) | k2l_ctor_assumption)))
      if (← getUnsolvedGoals).isEmpty then return
      throwError "k2l_pri_map: goals remain"
    catch _ => s.restore
  throwError "k2l_pri_map: no binding of the updated map rebuilds the rule at the configuration before"

/-- `∀ j, j < i → ¬ App j c₁` from `hp`, the premise at `c`, where `c₁` is `c` after a step that
leaves alone what the rules of earlier ranks read. -/
macro "k2l_pri_back " hp:term:max : tactic => `(tactic| (
  intro j hj ha
  refine $hp j hj ?_
  cases ha <;> first | omega | k2l_ctor_assumption))

/-- `∀ j, j < i → ¬ App j c₁` from `hp`, the premise at `c`, where `c₁` is `c` after a step that
updated `c`'s map at one binding (`hm`, `hr`). -/
macro "k2l_pri_back " hp:term:max hm:term:max hr:term:max : tactic => `(tactic| (
  intro j hj ha
  refine $hp j hj ?_
  cases ha <;> first | omega | k2l_ctor_assumption | k2l_pri_map $hm $hr))

end KPrelude.OtherRun
