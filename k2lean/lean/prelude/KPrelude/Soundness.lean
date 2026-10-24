import Lean

/-!
# Case splits for type soundness (`k2lean soundness`)

The generic tactics of a generated type-soundness proof (`k2lean/docs/design.md`, §3.3). Each is
a loop that cases on one kind of subterm of the goal and recurses on every new goal, at most
`fuel` cases deep; the constants it looks for are its arguments, so the same loop serves every
generated library. A loop that finds nothing to case on leaves the goal as it is.

- `k2l_cases_apps [f, …] fuel n`: case on the value of an application of one of the functions
  `f` (an `Option`, or a `Bool`), with an equation, and on the enumeration-typed value inside
  `some`; used by the inversion lemmas of a type checker's functions, whose two sides compute
  once the recursive calls have values.
- `k2l_cases_args [C, …] [T, …] fuel n`: case on the variables of the types `T` that are
  arguments of the argument of an application of one of the constructors `C` (the operands of
  the head item of `<k>`: whether an operand is a value decides between heating and the
  operator's own rule).
- `k2l_cases_bools fuel n`: case on the Boolean variables of the goal (a literal decides between
  `if-true` and `if-false`).
- `k2l_cases_frz [C] [T] fuel n => tac`: run `tac`, then case on a variable of type `T` that is an
  argument of an application of `C`, or the last argument of such an argument (the `SortK`
  arguments of freezers, until they have the shape `kseq y .dotk` the cooling rules match).
- `k2l_cases_typing [f, …] fuel n => tac`: run `tac`, then case on the first application of one
  of the functions `f` (a sort projection of a variable, or a typing function), with an equation,
  and on the enumeration-typed value inside `some`.
-/

namespace KPrelude.Soundness

open Lean Meta Elab Tactic

/-- Is `t` an inductive type whose constructors all take no argument (other than `Bool`)? -/
def isEnum (t : Expr) : MetaM Bool := do
  let t ← whnfR t
  let .const n _ := t.getAppFn | return false
  if n == ``Bool then return false
  let some (.inductInfo info) := (← getEnv).find? n | return false
  if info.numIndices != 0 || info.numParams != 0 then return false
  for c in info.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? c | return false
    if ci.numFields != 0 then return false
  return true

/-- Run `k` on each current goal and collect the goals it leaves. -/
def eachGoal (k : TacticM Unit) : TacticM Unit := do
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    k
    out := out ++ (← getGoals)
  setGoals out.toList

/-- Case on the value of the term `e` of the main goal with an equation `_h`; when it is an
`Option` of an enumeration, also on the value inside `some`. -/
def caseValue (e : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let ty ← g.withContext do whnfR (← inferType e)
  let x ← g.withContext (Term.exprToSyntax e)
  let inner ← if ty.isAppOfArity ``Option 1 then g.withContext (isEnum ty.appArg!) else pure false
  if inner then
    evalTactic (← `(tactic| ((rcases _h : $x:term with _ | v) <;> (try cases v))))
  else
    evalTactic (← `(tactic| rcases _h : $x:term with _ | _))

/-- An application of one of `fs` in `t`, with no loose bound variable. -/
def findApp (fs : Array Name) (t : Expr) (pred : Expr → Bool := fun _ => true) : Option Expr :=
  t.find? fun e => !e.hasLooseBVars && pred e && match e.getAppFn with
    | .const n _ => fs.contains n && e.getAppNumArgs > 0
    | _ => false

partial def appsLoop (fs : Array Name) (fuel : Nat) : TacticM Unit := do
  if (← getGoals).isEmpty || fuel = 0 then return
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e := findApp fs t | return
  caseValue e
  eachGoal (appsLoop fs (fuel - 1))

partial def argsLoop (cs ts : Array Name) (fuel : Nat) : TacticM Unit := do
  if (← getGoals).isEmpty || fuel = 0 then return
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let x? ← g.withContext do
    if let some it := findApp cs t (fun e => e.getAppNumArgs == 1) then
      for x in it.appArg!.getAppArgs do
        if x.isFVar then
          if let .const n _ := (← whnfR (← inferType x)).getAppFn then
            if ts.contains n then return some x
    return none
  let some x := x? | return
  let hx ← g.withContext (Term.exprToSyntax x)
  evalTactic (← `(tactic| cases $hx:term))
  eachGoal (argsLoop cs ts (fuel - 1))

partial def boolsLoop (fuel : Nat) : TacticM Unit := do
  if (← getGoals).isEmpty || fuel = 0 then return
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let x? ← g.withContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      if (← whnfR ldecl.type).isConstOf ``Bool && (t.find? (· == ldecl.toExpr)).isSome then
        return some ldecl.toExpr
    return none
  let some x := x? | return
  let hx ← g.withContext (Term.exprToSyntax x)
  evalTactic (← `(tactic| cases $hx:term))
  eachGoal (boolsLoop (fuel - 1))

partial def frzLoop (cs ts : Array Name) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) (fuel : Nat) :
    TacticM Unit := do
  if (← getGoals).isEmpty || fuel = 0 then return
  evalTactic (← `(tactic| try ($tac)))
  if (← getGoals).isEmpty then return
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let cand ← g.withContext do
    if let some f := findApp cs t (fun e => e.getAppNumArgs == 1) then
      for x in f.appArg!.getAppArgs do
        let x' := if x.isApp then x.appArg! else x
        if x'.isFVar then
          if let .const n _ := (← whnfR (← inferType x')).getAppFn then
            if ts.contains n then return some x'
    return none
  let some x := cand | return
  let hx ← g.withContext (Term.exprToSyntax x)
  evalTactic (← `(tactic| cases $hx:term))
  eachGoal (frzLoop cs ts tac (fuel - 1))

/-- Is `e` an application of one of `fs` whose last argument is a variable, or of a function
of `gs`? -/
def typingHead (fs gs : Array Name) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => (fs.contains n && e.getAppNumArgs > 0 && e.appArg!.isFVar) ||
      (gs.contains n && e.getAppNumArgs > 0)
  | _ => false

partial def typingLoop (fs gs : Array Name) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) (fuel : Nat) :
    TacticM Unit := do
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| try ($tac)))
  if (← getGoals).isEmpty || fuel = 0 then return
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e := t.find? (fun e => !e.hasLooseBVars && typingHead fs gs e) | return
  caseValue e
  eachGoal (typingLoop fs gs tac (fuel - 1))

def names (xs : Array Ident) : TacticM (Array Name) :=
  xs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i

syntax fuelOpt := &" fuel " num

/-- See the module documentation. -/
elab "k2l_cases_apps " "[" fs:ident,* "]" f:(fuelOpt)? : tactic => do
  let fuel := match f with | some s => s.raw[1].isNatLit?.getD 6 | none => 6
  appsLoop (← names fs.getElems) fuel

/-- See the module documentation. -/
elab "k2l_cases_args " "[" cs:ident,* "]" " [" ts:ident,* "]" f:(fuelOpt)? : tactic => do
  let fuel := match f with | some s => s.raw[1].isNatLit?.getD 2 | none => 2
  argsLoop (← names cs.getElems) (← names ts.getElems) fuel

/-- See the module documentation. -/
elab "k2l_cases_bools" f:(fuelOpt)? : tactic => do
  let fuel := match f with | some s => s.raw[1].isNatLit?.getD 3 | none => 3
  boolsLoop fuel

/-- See the module documentation. -/
elab "k2l_cases_frz " "[" cs:ident,* "]" " [" ts:ident,* "]" f:(fuelOpt)? " => " tac:tacticSeq : tactic => do
  let fuel := match f with | some s => s.raw[1].isNatLit?.getD 6 | none => 6
  frzLoop (← names cs.getElems) (← names ts.getElems) tac fuel

/-- See the module documentation: `fs` are the sort projections (cased on when applied to a
variable), `gs` the typing functions (cased on at any argument). -/
elab "k2l_cases_typing " "[" fs:ident,* "]" " [" gs:ident,* "]" f:(fuelOpt)? " => " tac:tacticSeq : tactic => do
  let fuel := match f with | some s => s.raw[1].isNatLit?.getD 4 | none => 4
  typingLoop (← names fs.getElems) (← names gs.getElems) tac fuel

end KPrelude.Soundness
