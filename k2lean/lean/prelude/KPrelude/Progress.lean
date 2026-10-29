import Lean
import KPrelude.Soundness
import KPrelude.Hooks

/-!
# Progress: some rule applies (`gen --progress`, SND-13)

The tactic of a generated progress case (`k2lean/docs/design.md`, §3.9): at a configuration whose
head of `<k>` is fixed, prove `App c` from the rules whose left-hand side has that head, given in
order.

`k2l_progress [r₁, …] => close` loops over the goals:
1. *search*: `apply` each rule's `App` constructor in turn and run `close` on what is left (its
   `requires`, its collection facts); the first rule for which everything closes proves the goal.
   When none does, it cases on the first `Bool`-valued application in a rule's remaining goals that
   no hypothesis decides (a side condition such as `isKResult(HOLE)` or `B =/=Int 0`), and searches
   again in both branches;
2. *split*: on a goal no rule closes (and, with `else stuck`, that `stuck` does not close), it cases
   on a variable of the configuration at a position
   where some rule's left-hand side has a constructor (an operand that a rule needs to be an `Int`, a
   stack that a rule needs to be non-empty), and loops on each case.
A goal where neither step makes progress is left as it is: there, no rule of the head applies, so
the generated proof closes it from the invariant or the ending, or the case is open.
Every step is `apply`, `by_cases` or `cases`, so the tactic cannot prove a false goal.
-/

namespace KPrelude.Progress

open Lean Meta Elab Tactic

/-- The Boolean connectives a side condition is built from; any other `Bool`-valued application is
an atom of the condition. -/
def connectives : List Name :=
  [``KPrelude.BoolHook.not, ``KPrelude.BoolHook.and, ``KPrelude.BoolHook.or, ``KPrelude.BoolHook.xor,
   ``KPrelude.BoolHook.implies, ``KPrelude.BoolHook.eq, ``KPrelude.BoolHook.ne, ``and, ``or, ``not,
   ``Eq, ``Not, ``And, ``Or]

/-- The atoms of `e`, outermost first: its `Bool`-valued applications that are not built by a
connective and have no loose bound variable or metavariable. -/
partial def atoms (e : Expr) : MetaM (Array Expr) := do
  let e ← instantiateMVars e
  if !e.isApp then return #[]
  if let .const n _ := e.getAppFn then
    if !connectives.contains n && !e.hasLooseBVars && !e.hasMVar then
      if (← whnfR (← inferType e)).isConstOf ``Bool then return #[e]
  let mut out := #[]
  for a in e.getAppArgs do
    out := out ++ (← atoms a)
  return out

/-- Whether a hypothesis already decides `a`: `a = b` or `¬ a = b`. -/
def decided (a : Expr) : MetaM Bool := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let t := if t.isAppOfArity ``Not 1 then t.appArg! else t
    if t.isAppOfArity ``Eq 3 then
      if ← withNewMCtxDepth (isDefEq (t.getArg! 1) a) then return true
  return false

/-- The first atom of `e` that no hypothesis decides. -/
def undecided (e : Expr) : MetaM (Option Expr) := do
  for a in ← atoms e do
    if !(← decided a) then return some a
  return none

/-- Search among the constructors `cs` (see the module documentation), at most `fuel` atoms deep;
returns the goals where no rule applies. -/
partial def search (cs : Array Name) (close : TSyntax ``Lean.Parser.Tactic.tacticSeq) (fuel : Nat) :
    TacticM (List MVarId) := do
  let mut atom : Option Expr := none
  for c in cs do
    let s ← saveState
    try
      evalTactic (← `(tactic| apply $(mkIdent c):ident))
      evalTactic (← `(tactic| all_goals (try ($close))))
      let gs ← getGoals
      if gs.isEmpty then return []
      if atom.isNone then
        for g in gs do
          if atom.isNone then
            atom ← g.withContext do undecided (← g.getType)
      s.restore
    catch _ => s.restore
  match atom, fuel with
  | some a, fuel + 1 =>
    let g ← getMainGoal
    let (gt, gf) ← g.withContext do
      let hyp ← mkEq a (mkConst ``Bool.true)
      let (gt, gf) ← g.byCases hyp (← mkFreshUserName `hb)
      pure (gt.mvarId, gf.mvarId)
    let mut out := []
    for g' in [gt, gf] do
      setGoals [g']
      out := out ++ (← search cs close fuel)
    return out
  | _, _ => return [← getMainGoal]

/-- A variable of `e` at a position where the pattern `p` has a constructor: what to case on for `p`
to match. Both sides are unfolded reducibly (a K constructor is a reducible definition over the
family); a variable of `p` matches anything, and a clash of constructors means `p` cannot match. -/
partial def mismatch (p e : Expr) : MetaM (Option Expr) := do
  let p ← whnfR (← instantiateMVars p)
  if p.isMVar then return none
  let e ← whnfR e
  if e.isFVar then
    return if p.isApp || p.isConst then some e else none
  match p.getAppFn, e.getAppFn with
  | .const n _, .const n' _ =>
    if n != n' || p.getAppNumArgs != e.getAppNumArgs then return none
    for (a, b) in p.getAppArgs.zip e.getAppArgs do
      if let some x ← mismatch a b then return some x
    return none
  | _, _ => return none

/-- A variable of the main goal's configuration that one of the constructors `cs` needs to be a
constructor. -/
def splitVar (cs : Array Name) (g : MVarId) : MetaM (Option Expr) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless t.isApp do return none
  for c in cs do
    let k ← mkConstWithFreshMVarLevels c
    let (_, _, concl) ← forallMetaTelescope (← inferType k)
    unless concl.isApp do continue
    if let some x ← mismatch concl.appArg! t.appArg! then
      if x.isFVar then return some x
  return none

/-- Whether `stuck` closes the goal `g` (a configuration the invariant or the ending excludes). -/
def closes (stuck : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) (g : MVarId) : TacticM Bool := do
  let some t := stuck | return false
  let s ← saveState
  try
    setGoals [g]
    evalTactic t
    if (← getGoals).isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

/-- See the module documentation; `fuel` bounds the splits along one branch. A goal that `stuck`
closes is not split further. -/
partial def loop (cs : Array Name) (close : TSyntax ``Lean.Parser.Tactic.tacticSeq)
    (stuck : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) (fuel : Nat) : TacticM Unit := do
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    for r in ← search cs close 4 do
      if ← closes stuck r then continue
      let x? ← splitVar cs r
      match x?, fuel with
      | some x, fuel + 1 =>
        setGoals [r]
        Soundness.casesVar x
        evalTactic (← `(tactic| all_goals k2l_norm_idx))
        loop cs close stuck fuel
        out := out ++ (← getGoals)
      | _, _ => out := out.push r
  setGoals out.toList

elab "k2l_progress " "[" cs:ident,* "]" " => " close:tacticSeq : tactic => do
  let cs ← cs.getElems.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  loop cs close none 6

/-- `k2l_progress [r₁, …] => close else stuck`: the same, and a goal no rule closes is first given
to `stuck`, which closes it when the invariant or the ending excludes the configuration, before it
is split further. -/
elab "k2l_progress " "[" cs:ident,* "]" " => " close:tacticSeq " else " stuck:tacticSeq : tactic => do
  let cs ← cs.getElems.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  loop cs close (some stuck) 6

end KPrelude.Progress
