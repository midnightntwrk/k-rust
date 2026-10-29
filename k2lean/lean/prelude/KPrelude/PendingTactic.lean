import KPrelude.Tactic
import KPrelude.Pending

/-!
# The derived soundness of a pending-call function (TERM-1c)

Tactics for `F.pending_sound` (`NS/DivergesSound.lean`): a group's `pending` and its functions are
the same cascade with other leaves, so a pending call `c'` of `c` comes from the applying
equation's right-hand side, at a bind of a call of the group whose value is `none`, and the
function's cascade reaches the same equation and the same bind. -/

namespace KPrelude

open Lean Meta Elab Tactic

/-- Case-split every hypothesis that is an `∃`, an `∧` or an `∨`, in every goal, until none is
left (at most 64 rounds). -/
partial def k2lDestructLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let mut progress := false
  let mut out := #[]
  for g in ← getGoals do
    if ← g.isAssigned then continue
    let sub ← g.withContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← whnfR (← instantiateMVars d.type)
        if t.isAppOfArity ``Exists 2 || t.isAppOfArity ``And 2 || t.isAppOfArity ``Or 2 then
          return some ((← g.cases d.fvarId).map (·.mvarId))
      return none
    match sub with
    | some gs => out := out ++ gs; progress := true
    | none => out := out.push g
  setGoals out.toList
  if progress then k2lDestructLoop (fuel - 1)

elab "k2l_destruct" : tactic => k2lDestructLoop 64

/-- One arm of a least fixed point group's `pending_sound` (TERM-1c), `h : pending call = some c'`
with `pending` unfolded at `h`: split the arm's cascade down to the leaf that returned `c'` (the
applying equation's right-hand side, where `pendCall` met a call of the group whose value is
`none`), read the values of the binds before it off `h`, and show both calls undefined (`u`, the
group's `Call.undef`): the waited-for call by its `none`, the call itself by unfolding its
function (`e`, its `eq_def`), whose cascade reaches the same equation and the same bind. -/
syntax "k2l_pending_arm " ident ident ident : tactic
macro_rules
  | `(tactic| k2l_pending_arm $h $u $e) => `(tactic|
      ((repeat' (first
          | (simp only [↓reduceIte, Bool.false_eq_true, ite_true, ite_false] at $h:ident)
          | split at $h:ident)) <;>
        (try (simp at $h:ident; done)) <;> (try contradiction) <;>
        (try simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
          KPrelude.pendCall_eq_some] at $h:ident) <;>
        k2l_destruct <;> (try (simp at *; done)) <;> subst_vars <;>
        (constructor <;> (try simp only [$u:ident]) <;>
          first
            | assumption
            | (rw [$e:ident]; simp [*]; done)
            | (rw [$e:ident]
               (repeat' (first
                 | (simp only [↓reduceIte, Bool.false_eq_true, ite_true, ite_false])
                 | split)) <;> simp_all))))

end KPrelude
