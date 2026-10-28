import Lean
import KPrelude.FamilyCases

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
- `k2l_cases_args [C, …] [T, …] within [U, …] fuel n`: case on the variables of the types `T`
  that are arguments of the argument of an application of one of the constructors `C` (the
  operands of the head item of `<k>`: whether an operand is a value decides between heating and
  the operator's own rule); with `within`, also on the variables of the types `T` or `U` inside an
  argument of a type `U` (a hole inside a list argument, IMP++'s `print(E, AEs)`), nearest first.
- `k2l_cases_bools fuel n`: case on the Boolean variables of the goal (a literal decides between
  `if-true` and `if-false`).
- `k2l_cases_frz [C] [T] fuel n => tac`: run `tac`, then case on a variable of type `T` that is an
  argument of an application of `C`, or the last argument of such an argument (the `SortK`
  arguments of freezers, until they have the shape `kseq y .dotk` the cooling rules match).
- `k2l_cases_typing [f, …] fuel n => tac`: run `tac`, then case on the first application of one
  of the functions `f` (a sort projection of a variable, or a typing function), with an equation,
  and on the enumeration-typed value inside `some`.
- `k2l_has_ctor [C, …]`: fails unless the goal has an application of one of the constructors
  `C`; it guards a case of a proof that chooses among cases by `first`.
- `k2l_norm_idx`: compute the sort indices of the goal and its hypotheses.

On the arity-indexed term family (design.md §2.1) the loops split a family term by
`familyCases`, with its sort index computed first; they recognize an enumeration sort by its value
forms, which have no arguments; and they find a constructor application up to unfolding the K
constructor's reducible definition. On an inductive type without indices they are `cases` and a
syntactic search.
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

/-- Whether `t` is a sort of the arity-indexed term family (`NS.Term s`, design.md §2.1), whose
values are not the family's constructors: `familyCases` enumerates them. -/
def isFamily (t : Expr) : MetaM Bool := do
  return (← whnfR t).getAppFn.constName?.any (KPrelude.isFamilyName (← getEnv))

/-- The constant naming the type `t`, as written or once reducible definitions are unfolded:
on the arity-indexed family a sort `NS.SortX` is a reducible name of `NS.Term .SortX`. -/
def typeNames (t : Expr) : MetaM (Array Name) := do
  let mut out := #[]
  if let .const n _ := t.getAppFn then out := out.push n
  if let .const n _ := (← whnfR t).getAppFn then out := out.push n
  return out

/-- Is `t` one of the types named `ts`? On the arity-indexed family a variable's type may be the
family at an index still to compute (`Term (A2_0 s c)` after a case split), so there it is
compared with each named sort up to definitional unfolding. -/
def isOneOf (t : Expr) (ts : Array Name) : MetaM Bool := do
  if (← typeNames t).any ts.contains then return true
  unless ← isFamily t do return false
  ts.anyM fun n => withNewMCtxDepth do isDefEq t (mkConst n)

/-- `cases` on the variable `x` of the main goal; on the arity-indexed family, the cases of its
sort's values only (`familyCases`). -/
def casesVar (x : Expr) : TacticM Unit := do
  let g ← getMainGoal
  if ← g.withContext do isFamily (← inferType x) then
    -- the sort index computed first (`A1_0 s c` of an argument of a case before): the cases'
    -- injections are then at the sort itself, as the lemmas and the rules state them
    let g ← g.withContext do
      let ty ← whnfR (← inferType x)
      let idx' ← whnfD ty.appArg!
      if idx' == ty.appArg! then pure g
      else g.replaceLocalDeclDefEq x.fvarId! (mkApp ty.appFn! idx')
    let gs ← KPrelude.familyCases g x.fvarId!
    replaceMainGoal (gs.map (·.1)).toList
  else
    let hx ← g.withContext (Term.exprToSyntax x)
    evalTactic (← `(tactic| cases $hx:term))

/-- On the arity-indexed family: case on `x` when its sort is an enumeration, every value form
without arguments (as `isEnum` says of an inductive type); otherwise leave the goal. -/
def casesEnumFamily (x : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let s ← saveState
  try
    let gs ← KPrelude.familyCases g x.fvarId!
    if gs.all (·.2.isEmpty) then replaceMainGoal (gs.map (·.1)).toList else s.restore
  catch _ => s.restore

/-- Is the definition `n` applied to `k` arguments a family's tag (`NS.Tag`)? Read off its
declared type, `∀ x₁ … xₖ, NS.Tag`, without inferring the application's type: the application's
type is that codomain with the arguments substituted, and a constant has no argument to
substitute. -/
def returnsTag (env : Environment) (n : Name) (k : Nat) : Bool := Id.run do
  let some (.defnInfo d) := env.find? n | return false
  let mut t := d.type
  for _ in [0:k] do
    let .forallE _ _ b _ := t | return false
    t := b
  return match t with
    | .const (.str p "Tag") _ => isFamilyName env (.str p "Term")
    | _ => false

/-- `e` with every sort index computed: a subterm of a family's tag type (`NS.Tag`) that is an
application of a definition (`A2_0 s c`, the sort of an argument, after `familyCases`) is replaced
by its `whnfD`, a tag. The result is definitionally equal to `e`. -/
def normIdx (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.transform e (post := fun x => do
    let .const n _ := x.getAppFn | return .continue
    unless x.getAppNumArgs > 0 && returnsTag env n x.getAppNumArgs do return .continue
    let w ← whnfD x
    return .done (if w.getAppFn.isConst && (← isConstructorApp w) then w else x))

/-- `k2l_norm_idx`: compute the sort indices of the goal and of its hypotheses (`normIdx`), so
that terms the family's case splits produced have their sorts as lemmas and rules state them. -/
elab "k2l_norm_idx" : tactic => liftMetaTactic fun g => g.withContext do
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty' ← normIdx ty
    if ty' != ty then g ← g.replaceLocalDeclDefEq d.fvarId ty'
  let t ← instantiateMVars (← g.getType)
  let t' ← normIdx t
  if t' != t then g ← g.replaceTargetDefEq t'
  return [g]

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
  let innerFam ← if ty.isAppOfArity ``Option 1 then g.withContext (isFamily ty.appArg!) else pure false
  if inner then
    evalTactic (← `(tactic| ((rcases _h : $x:term with _ | v) <;> (try cases v))))
  else if innerFam then
    -- `some v` with `v` a term of the family: cased when its sort is an enumeration
    evalTactic (← `(tactic| rcases _h : $x:term with _ | $(mkIdent `kcV):ident))
    eachGoal do
      let g ← getMainGoal
      let some d := (← g.getDecl).lctx.findFromUserName? `kcV | return
      casesEnumFamily d.toExpr
  else
    evalTactic (← `(tactic| rcases _h : $x:term with _ | _))

/-- An application of one of `fs` in `t`, with no loose bound variable. -/
def findApp (fs : Array Name) (t : Expr) (pred : Expr → Bool := fun _ => true) : Option Expr :=
  t.find? fun e => !e.hasLooseBVars && pred e && match e.getAppFn with
    | .const n _ => fs.contains n && e.getAppNumArgs > 0
    | _ => false

/-- The closed subterms of `t` built by a constructor of an arity-indexed family, outermost first. -/
partial def familyCtorApps (env : Environment) (t : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := match t.getAppFn with
    | .const (.str p c) _ =>
      if !t.hasLooseBVars && isFamilyName env p && (c == "inj" || c.startsWith "c") then acc.push t
      else acc
    | _ => acc
  match t with
  | .app f a => familyCtorApps env a (familyCtorApps env f acc)
  | .lam _ d b _ | .forallE _ d b _ => familyCtorApps env b (familyCtorApps env d acc)
  | .letE _ ty v b _ => familyCtorApps env b (familyCtorApps env v (familyCtorApps env ty acc))
  | .mdata _ b => familyCtorApps env b acc
  | _ => acc

/-- The argument of an application in `t` of one of the one-argument constructors `cs`. On the
arity-indexed family a K constructor is a reducible definition (`SortKItem.inj_Expr x` is
`Term.inj … x`), which the goal holds unfolded: there an application is a subterm built by a
family constructor that unifies, with reducible transparency, with one of `cs` applied to a fresh
argument. -/
def findCtorArg (cs : Array Name) (t : Expr) : MetaM (Option Expr) := do
  if let some e := findApp cs t (fun e => e.getAppNumArgs == 1) then return some e.appArg!
  for e in familyCtorApps (← getEnv) t do
    for n in cs do
      let c ← mkConstWithFreshMVarLevels n
      let (args, _, _) ← forallMetaTelescope (← inferType c)
      unless args.size == 1 do continue
      if ← withReducible (isDefEq e (mkApp c args[0]!)) then
        return some (← instantiateMVars args[0]!)
  return none

partial def appsLoop (fs : Array Name) (fuel : Nat) : TacticM Unit := do
  if (← getGoals).isEmpty || fuel = 0 then return
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e := findApp fs t | return
  caseValue e
  eachGoal (appsLoop fs (fuel - 1))

partial def argsLoop (cs ts : Array Name) (fuel : Nat) (us : Array Name := #[]) : TacticM Unit := do
  if (← getGoals).isEmpty || fuel = 0 then return
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let x? ← g.withContext do
    if let some arg ← findCtorArg cs t then
      -- the operands, nearest first: a direct argument, then one inside an argument of a sort
      -- of `us` (IMP++'s `print(E, AEs)` evaluates `E`, the head of its list argument)
      let mut level := arg.getAppArgs
      for _ in [0:3] do
        let mut next := #[]
        for x in level do
          let tx ← inferType x
          if x.isFVar then
            if ← isOneOf tx ts <||> isOneOf tx us then return some x
          else if x.isApp && (← isOneOf tx us) then
            next := next ++ x.getAppArgs
        level := next
    return none
  let some x := x? | return
  casesVar x
  eachGoal (argsLoop cs ts (fuel - 1) us)

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
    if let some arg ← findCtorArg cs t then
      for x in arg.getAppArgs do
        let x' := if x.isApp then x.appArg! else x
        if x'.isFVar then
          if ← isOneOf (← inferType x') ts then return some x'
    return none
  let some x := cand | return
  casesVar x
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
syntax withinOpt := &" within " "[" ident,* "]"

/-- See the module documentation. -/
elab "k2l_cases_apps " "[" fs:ident,* "]" f:(fuelOpt)? : tactic => do
  let fuel := match f with | some s => s.raw[1].isNatLit?.getD 6 | none => 6
  appsLoop (← names fs.getElems) fuel

/-- See the module documentation. -/
elab "k2l_cases_args " "[" cs:ident,* "]" " [" ts:ident,* "]" w:(withinOpt)? f:(fuelOpt)? : tactic => do
  let fuel := match f with | some s => s.raw[1].isNatLit?.getD 2 | none => 2
  let us ← match w with
    | some s => names (s.raw[2].getSepArgs.map (⟨·⟩))
    | none => pure #[]
  argsLoop (← names cs.getElems) (← names ts.getElems) fuel us

/-- See the module documentation. -/
elab "k2l_cases_bools" f:(fuelOpt)? : tactic => do
  let fuel := match f with | some s => s.raw[1].isNatLit?.getD 3 | none => 3
  boolsLoop fuel

/-- See the module documentation. -/
elab "k2l_cases_frz " "[" cs:ident,* "]" " [" ts:ident,* "]" f:(fuelOpt)? " => " tac:tacticSeq : tactic => do
  let fuel := match f with | some s => s.raw[1].isNatLit?.getD 6 | none => 6
  frzLoop (← names cs.getElems) (← names ts.getElems) tac fuel

/-- See the module documentation. -/
elab "k2l_has_ctor " "[" cs:ident,* "]" : tactic => do
  let g ← getMainGoal
  let cs ← names cs.getElems
  let found ← g.withContext do findCtorArg cs (← instantiateMVars (← g.getType))
  if found.isNone then throwError "k2l_has_ctor: no application of {cs} in the goal"

/-- See the module documentation: `fs` are the sort projections (cased on when applied to a
variable), `gs` the typing functions (cased on at any argument). -/
elab "k2l_cases_typing " "[" fs:ident,* "]" " [" gs:ident,* "]" f:(fuelOpt)? " => " tac:tacticSeq : tactic => do
  let fuel := match f with | some s => s.raw[1].isNatLit?.getD 4 | none => 4
  typingLoop (← names fs.getElems) (← names gs.getElems) tac fuel

end KPrelude.Soundness
