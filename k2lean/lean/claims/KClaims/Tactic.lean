import Lean
import KClaims.RuleStep
import KClaims.Exec
import KClaims.Succ
import KClaims.StepInv
import KClaims.SimpAttr
import KClaims.MapLoc
import KPrelude.Hooks
import KPrelude.Coll
import KPrelude.InvColl
import KPrelude.FamilyCases
import KPrelude.Tactic

/-!
# Symbolic execution tactics for generated claims

`kc_intro h` opens a claim instance `h : Inst c Q` (substitutes the configuration and the
post-condition, evaluates the map patterns of the left-hand side, turns the requires clause
into propositions) and splits single-constructor cell variables.

`kc_auto` then explores the goal `AFn Step Q n c` (or `AF Step Q c`) as K's prover does, one
configuration at a time:

1. **target**: `Q c` holds — witnesses for the right-hand side's existentials (`?X`, the values
   of partial functions, the map) are found by unification up to arithmetic, and the remaining
   arithmetic, map and `ensures` goals are closed by the closing tactic;
2. **claim**: an instance of a circularity (after at least one step: the index has decreased)
   or of an already proved claim — continue from its post-condition (`AFn.trans`);
3. **rule**: some rule matcher returns a successor — continue there (`AFn.of_rule`); for a
   relation that is not a function, every successor (`ExecSucc`), and where those do not reduce
   (a symbolic part read before the position that decides), the cases of the relation itself
   (`tryRel`);
4. **split**: no rule fires because a Boolean in the configuration is not a literal — case
   split on it (the branch's path condition becomes a hypothesis; a branch whose condition
   simplifies to `False` closes).

A configuration where none of these applies stays as an open goal. Nothing in this file is
trusted: every step builds an ordinary proof term, checked by the kernel.
-/

namespace KClaims.Tactic

open Lean Meta Elab Tactic

attribute [kc_simp] KPrelude.IntHook.add KPrelude.IntHook.sub KPrelude.IntHook.mul
  KPrelude.IntHook.tdiv KPrelude.IntHook.tmod KPrelude.IntHook.ediv KPrelude.IntHook.emod
  KPrelude.IntHook.neg KPrelude.IntHook.abs KPrelude.IntHook.min KPrelude.IntHook.max
  KPrelude.IntHook.lt KPrelude.IntHook.le KPrelude.IntHook.gt KPrelude.IntHook.ge
  KPrelude.IntHook.eq KPrelude.IntHook.ne
  KPrelude.BoolHook.not KPrelude.BoolHook.and KPrelude.BoolHook.or KPrelude.BoolHook.xor
  KPrelude.BoolHook.implies KPrelude.BoolHook.eq KPrelude.BoolHook.ne
  KPrelude.KEqHook.eq KPrelude.KEqHook.ne KPrelude.KEqHook.ite

/-- Leaves: values the tactics keep as terms (arithmetic, Booleans, strings, functions, proofs). -/
def isLeafType (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  if ty.isSort || ty.isForall then return true
  match ty.getAppFn with
  | .const n _ => return n == ``Int || n == ``Bool || n == ``Nat || n == ``String || n == ``Char
  | _ => return true

/-- Constructor normal form, except at leaves: a non-leaf subterm whose weak head normal form
is a constructor application is replaced by it. Maps written with hooks (`update`, `concat`,
…) on concrete keys become their canonical sorted form. -/
partial def norm (e : Expr) : MetaM Expr := do
  if e.hasLooseBVars then return e
  let ty ← inferType e
  if ← isLeafType ty then return e
  if ← isProp ty then return e
  let w ← whnfD e
  -- a projection out of a known pair (a map lookup's value) is the variable it projects
  if w.isFVar then return w
  let isC ← if w.getAppFn.isConst then isConstructorApp w else pure false
  let e' := if isC then w else e
  match e'.getAppFn with
  | .const n _ =>
    match (← getEnv).find? n with
    | some (.ctorInfo ci) =>
      let args := e'.getAppArgs
      let mut out := #[]
      for i in [:args.size] do
        if i < ci.numParams then out := out.push args[i]!
        else out := out.push (← norm args[i]!)
      return mkAppN e'.getAppFn out
    | _ => return e
  | _ => return e

/-- The configuration argument of an `AF`/`AFn`/`EF` goal, and a function rebuilding the goal. -/
def configOf (t : Expr) : Option (Expr × (Expr → Expr)) :=
  match t.getAppFnArgs with
  | (``KClaims.AF, #[α, R, P, c]) => some (c, fun c' => mkAppN t.getAppFn #[α, R, P, c'])
  | (``KClaims.AFn, #[α, R, P, n, c]) => some (c, fun c' => mkAppN t.getAppFn #[α, R, P, n, c'])
  | (``KClaims.Reach, #[α, R, P, c]) => some (c, fun c' => mkAppN t.getAppFn #[α, R, P, c'])
  | _ => none

def normGoal (g : MVarId) : MetaM MVarId := g.withContext do
  let t ← instantiateMVars (← g.getType)
  -- a case split's motive can leave the target as a beta-redex or annotated
  let t' := t.cleanupAnnotations.headBeta
  let t := t'
  match configOf t with
  | some (c, mk) => g.replaceTargetDefEq (mk (← norm c))
  | none =>
    match t.eq? with
    | some (_, a, b) => g.replaceTargetDefEq (← mkEq (← norm a) (← norm b))
    | none => pure g

/-- `kc_norm`: constructor normal form of the goal's configuration, or of both sides of an
equation. -/
elab "kc_norm" : tactic => liftMetaTactic fun g => do return [← normGoal g]

/-- The rule matchers of relation `R`, from its `RuleSet` instance. -/
def getRules (R : Expr) : MetaM (Array Expr) := do
  let rty ← whnfR (← inferType R)
  let .forallE _ α _ _ := rty | throwError "kc: relation expected, got {R}"
  let A ← mkFreshExprMVar (← mkArrow α (mkSort Level.zero))
  let inst ← synthInstance (mkAppN (mkConst ``KClaims.RuleSet) #[α, A, R])
  let A ← instantiateMVars A
  let mut l ← whnfD (mkAppN (mkConst ``KClaims.RuleSet.rules) #[α, A, R, inst])
  let mut out := #[]
  repeat
    match l.getAppFnArgs with
    | (``List.cons, #[_, h, t]) => out := out.push h; l ← whnfD t
    | _ => break
  return out

/-- An `AFn` goal with an index of the form `m + 1`; `cases` on a variable index (the `0` case is
closed by `AFn.zero`). `none` if the goal is not `AFn`. -/
def succIndex (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let (``KClaims.AFn, #[_, _, _, n, _]) := t.getAppFnArgs | return some g
  let n ← instantiateMVars n
  if n.isAppOfArity ``Nat.succ 1 then return some g
  if n.isAppOfArity ``HAdd.hAdd 6 && (n.getArg! 5).nat? == some 1 then return some g
  unless n.isFVar do return none
  let subs ← g.cases n.fvarId!
  let mut res := none
  for s in subs do
    if s.ctorName == ``Nat.zero then
      let tz ← instantiateMVars (← s.mvarId.getType)
      let zs := tz.getAppArgs
      s.mvarId.assign (mkAppN (mkConst ``KClaims.AFn.zero) #[zs[0]!, zs[1]!, zs[2]!, zs[4]!])
    else res := some s.mvarId
  return res

/-- Step: the first rule matcher that returns a successor. -/
def predIndex (n : Expr) : Option Expr :=
  if n.isAppOfArity ``Nat.succ 1 then some n.appArg!
  else if n.isAppOfArity ``HAdd.hAdd 6 then some (n.getArg! 4)
  else none

/-- The local hypothesis named `hinv`: the assumed invariant at the goal's configuration (the
`inv` mode of `kc_auto`). -/
def invHyp? : MetaM (Option LocalDecl) := do
  return (← getLCtx).findFromUserName? `hinv

/-- Step by the first rule matcher that returns a successor. With `inv = some hP` (`hP : Preserved
R P`) and a hypothesis `hinv : P c`, the step is `AFn.of_rule_inv`, and the new goal has
`hinv : P c'` in place of the old one. -/
def tryRules (rules : Array Expr) (g : MVarId) (inv : Option Expr := none) : MetaM (Option MVarId) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (c, mk) := configOf t | return none
  let mk := match t.getAppFnArgs with
    | (``KClaims.AFn, #[α, R, P, n, _]) =>
      fun c' => mkAppN t.getAppFn #[α, R, P, (predIndex n).getD n, c']
    | _ => mk
  let α ← inferType c
  for r in rules do
    let s ← saveState
    let c' ← mkFreshExprMVar α
    let lhs ← mkAppM ``KPrelude.RuleResult.next? #[← mkAppM ``KPrelude.Rule.run #[r, c]]
    let rhs ← mkAppM ``Option.some #[c']
    if ← isDefEq lhs rhs then
      let c'' ← norm (← instantiateMVars c')
      let rhs'' ← mkAppM ``Option.some #[c'']
      let h ← mkExpectedTypeHint (← mkEqRefl rhs'') (← mkEq lhs rhs'')
      if t.isAppOf ``KClaims.Reach then
        let k ← mkFreshExprSyntheticOpaqueMVar (mk c'')
        g.assign (← mkAppM ``KClaims.Reach.of_rule #[r, h, k])
        return some k.mvarId!
      match inv, ← invHyp? with
      | some hP, some hd =>
        let Pc ← match (← instantiateMVars (← inferType hP)).getAppFnArgs with
          | (``KPrelude.Preserved, #[_, _, P]) => pure (P.beta #[c'']).headBeta
          | _ => throwError "kc: inv expects a proof of `Preserved R P`"
        let k ← mkFreshExprSyntheticOpaqueMVar (← mkArrow Pc (mk c''))
        let lem := if t.isAppOf ``KClaims.AFn then ``KClaims.AFn.of_rule_inv else ``KClaims.AF.of_rule_inv
        g.assign (← mkAppM lem #[hP, hd.toExpr, r, h, k])
        let (_, g') ← k.mvarId!.intro `hinv
        let g' ← (try g'.clear hd.fvarId catch _ => pure g')
        return some g'
      | _, _ =>
        let k ← mkFreshExprSyntheticOpaqueMVar (mk c'')
        let lem := if t.isAppOf ``KClaims.AFn then ``KClaims.AFn.of_rule else ``KClaims.AF.of_rule
        let pf ← mkAppM lem #[r, h, k]
        g.assign pf
        return some k.mvarId!
    s.restore
  return none

/-- The `ExecSucc` instance of relation `R`, if it has one. -/
def getSucc? (R : Expr) : MetaM (Option Expr) := do
  let rty ← whnfR (← inferType R)
  let .forallE _ α _ _ := rty | return none
  try
    return some (← synthInstance (mkAppN (mkConst ``KClaims.ExecSucc) #[α, R]))
  catch _ => return none

/-- Step by every successor (`ExecSucc`, for a relation that is not a function): `succ c` reduced
to an explicit list, then one goal per successor (`AF.of_succ`, `AFn.of_succ`). `none` when the
list does not reduce (a symbolic part decides which rule applies: a split comes first) or is
empty (no rule applies). -/
def trySucc (g : MVarId) : MetaM (Option (List MVarId)) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (c, _) := configOf t | return none
  let (lem, mk) ← match t.getAppFnArgs with
    | (``KClaims.AFn, #[α, R, P, n, _]) =>
      pure (``KClaims.AFn.of_succ, fun c' => mkAppN t.getAppFn #[α, R, P, (predIndex n).getD n, c'])
    | (``KClaims.AF, #[α, R, P, _]) => pure (``KClaims.AF.of_succ, fun c' => mkAppN t.getAppFn #[α, R, P, c'])
    | _ => return none
  let R := t.getAppArgs[1]!
  let α ← inferType c
  let some inst ← getSucc? R | return none
  let sc := mkAppN (mkConst ``KClaims.ExecSucc.succ) #[α, R, inst, c]
  let mut l ← whnfD sc
  let mut elems : Array Expr := #[]
  repeat
    match l.getAppFnArgs with
    | (``List.cons, #[_, h, tl]) => elems := elems.push (← norm h); l ← whnfD tl
    | (``List.nil, _) => break
    | _ => return none
  if elems.isEmpty then return none
  let lst ← mkListLit α elems.toList
  unless ← isDefEq sc lst do return none
  let hl ← mkExpectedTypeHint (← mkEqRefl lst) (← mkEq sc lst)
  let p ← withLocalDeclD `d α fun d => do mkLambdaFVars #[d] (mk d)
  let ks ← elems.mapM fun e => mkFreshExprSyntheticOpaqueMVar (mk e)
  let mut h := mkAppN (mkConst ``KClaims.allMem_nil) #[α, p]
  let mut rest ← mkListLit α []
  for i in (List.range elems.size).reverse do
    h := mkAppN (mkConst ``KClaims.allMem_cons) #[α, p, elems[i]!, rest, ks[i]!, h]
    rest ← mkAppM ``List.cons #[elems[i]!, rest]
  let hne ← mkAppM ``List.cons_ne_nil #[elems[0]!, ← mkListLit α (elems.toList.drop 1)]
  g.assign (← mkAppM lem #[hl, hne, h])
  return some (ks.toList.map (·.mvarId!))

/-- The first non-literal Boolean in `e`, left to right. -/
partial def findBool (e : Expr) : MetaM (Option Expr) := do
  if e.hasLooseBVars || e.hasMVar then return none
  let ty ← whnfR (← inferType e)
  if ty.isConstOf ``Bool then
    if e.isConstOf ``Bool.true || e.isConstOf ``Bool.false then return none
    return some e
  if ← isLeafType ty then return none
  for a in e.getAppArgs do
    if let some b ← findBool a then return some b
  return none

/-- Peel `∃` (natural metavariables for the witnesses) and `∧` (one goal per conjunct). -/
partial def peel (g : MVarId) (ws : Array Expr) (gs : Array MVarId) :
    MetaM (Array Expr × Array MVarId) := do
  let t ← whnfD (← instantiateMVars (← g.getType))
  match t.getAppFnArgs with
  | (``Exists, #[α, p]) =>
    let w ← mkFreshExprMVar α
    let g' ← mkFreshExprSyntheticOpaqueMVar (p.beta #[w]).headBeta
    let u ← getLevel α
    g.assign (mkApp4 (mkConst ``Exists.intro [u]) α p w g')
    peel g'.mvarId! (ws.push w) gs
  | (``And, #[a, b]) =>
    let ga ← mkFreshExprSyntheticOpaqueMVar a
    let gb ← mkFreshExprSyntheticOpaqueMVar b
    g.assign (mkApp4 (mkConst ``And.intro) a b ga gb)
    peel gb.mvarId! ws (gs.push ga.mvarId!)
  | (``True, _) => g.assign (mkConst ``True.intro); return (ws, gs)
  | _ => return (ws, gs.push g)

/-- `whnfD e`, with `e`'s unassigned metavariables read as free variables of the same types while
it reduces: a `match` on the arity-indexed family (a collection's `toList`, design.md §2.1) is not
reduced while its scrutinee contains a metavariable, although every step that holds of a free
variable holds of any term in its place. The result has the metavariables back; when one's type
has a metavariable itself, plain `whnfD`. -/
def whnfDOpen (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  unless e.hasExprMVar do return ← whnfD e
  let ms ← getMVars e
  let mut decls : Array (Name × Expr) := #[]
  for m in ms do
    let ty ← instantiateMVars (← m.getType)
    if ty.hasExprMVar then return ← whnfD e
    decls := decls.push (`kcOpen, ty)
  withLocalDeclsDND decls fun xs => do
    let e' := e.replace fun x => match x with
      | .mvar m => (ms.idxOf? m).map (xs[·]!)
      | _ => none
    let w ← whnfD e'
    return w.replaceFVars xs (ms.map mkMVar)

/-- Assign metavariables by matching constructor structure; leaves are left for the closing
tactic. `false` when the two sides cannot be made equal by arithmetic at the leaves: different
constructors, or a non-leaf position where a side is neither a constructor application nor a
metavariable (a variable of the claim against a constructor, say). A function's value that does
not reduce (its arguments symbolic: `expectedOperand (x / 8 % 8)`) against a value without
metavariables is a leaf too, which the closing tactic may prove from the facts (`kc_index_split`
compares two tables at a symbolic index). -/
partial def structUnify (a b : Expr) : MetaM Bool := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  if a.getAppFn.isMVar || b.getAppFn.isMVar then
    return (← isDefEq a b)
  if ← isDefEq a b then return true
  if ← isLeafType (← inferType a) then return true
  let a' ← whnfDOpen a
  let b' ← whnfDOpen b
  let env ← getEnv
  let ctor (e : Expr) : Bool := match e.getAppFn with
    | .const n _ => (env.find? n matches some (.ctorInfo _))
    | _ => false
  let call (e : Expr) : Bool := e.getAppFn.isConst && !ctor e
  match a'.getAppFn, b'.getAppFn with
  | .const na _, .const nb _ =>
    match env.find? na, env.find? nb with
    | some (.ctorInfo ci), some (.ctorInfo _) =>
      if na != nb then return false
      let xs := a'.getAppArgs
      let ys := b'.getAppArgs
      if xs.size != ys.size then return false
      for i in [ci.numParams:xs.size] do
        unless ← structUnify xs[i]! ys[i]! do return false
      return true
    | _, _ => return (call a' || call b') && !a.hasExprMVar && !b.hasExprMVar
  | _, _ => return (call a' || call b') && !a.hasExprMVar && !b.hasExprMVar

/-- `concat (element k v) r`: `k`, `v`, `r` (a match of one binding of a map). -/
def elemConcat? (a : Expr) : Option (Expr × Expr × Expr) := do
  guard (a.isAppOf ``KPrelude.MapHook.concat)
  let x := a.getArg! (a.getAppNumArgs - 2)
  guard (x.isAppOf ``KPrelude.MapHook.element)
  return (x.getArg! (x.getAppNumArgs - 2), x.getArg! (x.getAppNumArgs - 1), a.appArg!)

/-- The description of the map `m` in the context before `before`: the first hypothesis
`concat A B = some m` (a claim's map pattern, or a rule's match located earlier). -/
def mapDesc? (m : Expr) (before? : Option FVarId := none) : MetaM (Option (LocalDecl × Expr × Expr)) := do
  for d in ← getLCtx do
    if before? == some d.fvarId then break
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    unless a.isAppOf ``KPrelude.MapHook.concat && b.isAppOfArity ``Option.some 2 do continue
    unless (← instantiateMVars b.appArg!) == m do continue
    return some (d, a.getArg! (a.getAppNumArgs - 2), a.appArg!)
  return none

/-- Apply `lem` to `g`; its new goals, or `none` (state restored) when it does not apply. -/
def applyOr (g : MVarId) (lem : Expr) : MetaM (Option (List MVarId)) := do
  let s ← saveState
  try return some (← g.apply lem) catch _ => s.restore; return none

/-- `WF m`, from how `m` is built or described. -/
partial def proveWF (g : MVarId) : MetaM Bool := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf ``KPrelude.MapHook.WF do
    return (← try g.assumption; pure true catch _ => pure false)
  let m ← instantiateMVars ty.appArg!
  let s ← saveState
  if m.isFVar then
    if let some (hd, _, _) ← mapDesc? m then
      if (← applyOr g (← mkAppM ``KClaims.MapLoc.wf_of_concat #[hd.toExpr])).isSome then return true
    try g.assumption; return true catch _ => s.restore; return false
  for (c, lem) in [(``KPrelude.MapHook.remove, ``KPrelude.MapHook.wf_remove),
      (``KPrelude.MapHook.update, ``KPrelude.MapHook.wf_update)] do
    if m.isAppOf c then
      let some gs ← applyOr g (← mkConstWithFreshMVarLevels lem) | return false
      for g' in gs do
        unless ← g'.isAssigned do
          unless ← proveWF g' do s.restore; return false
      return true
  -- one binding or none, also as the literal `kc_norm` evaluates them to
  for lem in [``KPrelude.MapHook.wf_element, ``KPrelude.MapHook.wf_unit] do
    if let some [] ← applyOr g (← mkConstWithFreshMVarLevels lem) then return true
  -- a literal: its executable check evaluates
  if let some [g'] ← applyOr g (← mkConstWithFreshMVarLevels ``KClaims.MapLoc.wf_of_wfb) then
    try g'.refl; return true catch _ => pure ()
  s.restore
  return false

/-- Apply `lem` to `g` and close its premises in order with `close`; `false` (state
restored) when one fails. -/
def applyWith (g : MVarId) (lem : Name) (close : MVarId → MetaM Bool) : MetaM Bool := do
  let s ← saveState
  let some gs ← applyOr g (← mkConstWithFreshMVarLevels lem) | return false
  for g' in gs do
    if ← g'.isAssigned then continue
    unless ← close g' do s.restore; return false
  return true

/-- The keys a map term binds as far as its syntax and descriptions show: `element`'s key, an
`update`'s key, and those of the descriptions of the maps it names (a description that names
its own map left out). Used only to choose which descriptions to try (`proveKeyNe`): every
binding is then proved by the lemmas. -/
partial def boundKeys (e : Expr) (depth : Nat := 8) : MetaM (Array Expr) := do
  if depth == 0 then return #[]
  let e ← instantiateMVars e
  if e.isAppOf ``KPrelude.MapHook.element then return #[e.getArg! (e.getAppNumArgs - 2)]
  if e.isAppOf ``KPrelude.MapHook.remove then
    return ← boundKeys (e.getArg! (e.getAppNumArgs - 2)) (depth - 1)
  if e.isAppOf ``KPrelude.MapHook.update then
    return (← boundKeys (e.getArg! (e.getAppNumArgs - 3)) (depth - 1)).push (e.getArg! (e.getAppNumArgs - 2))
  unless e.isFVar do return #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    unless a.isAppOf ``KPrelude.MapHook.concat && b.isAppOfArity ``Option.some 2 && b.appArg! == e do continue
    if (a.find? (· == e)).isSome then continue
    return (← boundKeys (a.getArg! (a.getAppNumArgs - 2)) (depth - 1))
      ++ (← boundKeys a.appArg! (depth - 1))
  return #[]

/-- `c x ≠ c y` for two keys built by one constructor (up to unfolding: `inj_Int x` and the
`Term.inj …` an evaluated literal holds) from values that differ by arithmetic, the functions
they apply read by their proved equations (`@[k2l_equation]`): the locations a declaration
allocates, `freshInt(C + 0)` and `freshInt(C + 1)`, where `freshInt(I) = I`. Proved apart from
the configuration's context, over the keys' variables only. -/
def proveKeyNeArith (g : MVarId) : MetaM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (_, i, j) := t.ne? | return false
  if t.hasExprMVar || !(i.hasFVar || j.hasFVar) then return false
  let env ← getEnv
  let eqns := t.getUsedConstants.foldl (fun acc f => acc ++ KPrelude.equationsOf env f) #[]
  -- over the keys' variables only, apart from the configuration's context
  let xs := (collectFVars {} t).fvarIds.map mkFVar
  let ty ← mkForallFVars xs t
  if ty.hasFVar then return false
  let m ← mkFreshExprMVarAt {} {} ty
  let s ← saveState
  try
    let gs ← Term.TermElabM.run' do
      let lemmas ← eqns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
      let tac ← `(tactic| (intros; intro $(mkIdent `kcne):ident; injections; (try simp only [$lemmas,*] at *); k2l_arith_omega))
      Tactic.run m.mvarId! (evalTactic tac)
    if gs.isEmpty then
      g.assign (mkAppN (← instantiateMVars m) xs)
      return true
  catch _ => pure ()
  s.restore
  return false

mutual

/-- `i ≠ j` for two keys: closed terms that differ (by evaluation), or keys bound on the two sides
of a description (`concat` is defined only on maps with no key in common, `MapLoc.key_ne`). The
descriptions tried are those whose sides bind the two keys syntactically (`boundKeys`), so a key
no description binds (a rule's variable, before its match is located) fails at once. Else by
arithmetic (`proveKeyNeArith`). -/
partial def proveKeyNe (g : MVarId) (fuel : Nat) : MetaM Bool := g.withContext do
  if fuel == 0 then return false
  let t ← instantiateMVars (← g.getType)
  let some (_, i, j) := t.ne? | return false
  if i.hasExprMVar || j.hasExprMVar then return false
  if !i.hasFVar && !j.hasFVar then
    let s ← saveState
    try
      let p ← mkEq i j
      let d ← synthInstance (mkApp (mkConst ``Decidable) p)
      if (← whnfD (mkApp2 (mkConst ``Decidable.decide) p d)).isConstOf ``Bool.false then
        g.assign (← mkAppOptM ``of_decide_eq_false #[p, d, ← mkEqRefl (mkConst ``Bool.false)])
        return true
    catch _ => pure ()
    s.restore
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    unless a.isAppOf ``KPrelude.MapHook.concat && b.isAppOfArity ``Option.some 2 do continue
    let ka ← boundKeys (a.getArg! (a.getAppNumArgs - 2))
    let kb ← boundKeys a.appArg!
    for (x, y, symm) in [(i, j, false), (j, i, true)] do
      unless ka.contains x && kb.contains y do continue
      let s ← saveState
      let ok ← observing? do
        let pf ← mkAppM ``KClaims.MapLoc.key_ne #[d.toExpr]
        -- `lookup A x = some ?v → lookup B y = some ?w → x ≠ y`
        let (ms, _, ty) ← forallMetaTelescope (← inferType pf)
        unless ← isDefEq ty (← mkAppM ``Ne #[x, y]) do failure
        for m in ms do
          unless ← isProp (← inferType m) do continue
          unless ← proveLookupF m.mvarId! none (fuel - 1) do failure
        let ne ← instantiateMVars (mkAppN pf ms)
        if ne.hasExprMVar then failure
        g.assign (← if symm then mkAppM ``Ne.symm #[ne] else pure ne)
      if ok.isSome then return true
      s.restore
  proveKeyNeArith g

/-- `lookup m k = some v`, `k` and `v` unified with a binding of `m`'s description (the first
that fits, depth first), through the `remove` and `update` a step built `m` with. -/
partial def proveLookupF (g : MVarId) (before? : Option FVarId) (fuel : Nat) : MetaM Bool := g.withContext do
  if fuel == 0 then return false
  let some (_, l, _) := (← instantiateMVars (← g.getType)).eq? | return false
  unless l.isAppOf ``KPrelude.MapHook.lookup do return false
  let m ← instantiateMVars (l.getArg! (l.getAppNumArgs - 2))
  let sub (g' : MVarId) : MetaM Bool := do
    let ty ← instantiateMVars (← g'.getType)
    if ty.isAppOf ``KPrelude.MapHook.WF then proveWF g'
    else if ty.ne?.isSome then proveKeyNe g' (fuel - 1)
    else proveLookupF g' before? (fuel - 1)
  if m.isAppOf ``KPrelude.MapHook.update then
    if (← applyOr g (← mkConstWithFreshMVarLevels ``KClaims.MapLoc.lookup_update_same)).isSome then
      return true
    return ← applyWith g ``KClaims.MapLoc.lookup_update sub
  if m.isAppOf ``KPrelude.MapHook.remove then
    return ← applyWith g ``KClaims.MapLoc.lookup_remove sub
  unless m.isFVar do
    -- one binding, also as the literal `kc_norm` evaluates it to
    if (← applyOr g (← mkConstWithFreshMVarLevels ``KClaims.MapLoc.lookup_self)).isSome then return true
    -- a literal at a key that compares (a closed term): the lookup evaluates
    let k ← instantiateMVars l.appArg!
    if k.hasFVar || k.hasExprMVar then return false
    let some (_, _, r) := (← instantiateMVars (← g.getType)).eq? | return false
    -- the value as a term (a projection of the evaluated pair reduced), then the evaluation
    let lk ← whnfD l
    unless lk.isAppOfArity ``Option.some 2 do return false
    let s ← saveState
    try
      unless ← isDefEq r (← mkAppM ``Option.some #[← whnfCore lk.appArg!]) do s.restore; return false
      g.refl; return true
    catch _ => s.restore; return false
  let some (hd, _, _) ← mapDesc? m before? | return false
  for lem in [``KClaims.MapLoc.lookup_left, ``KClaims.MapLoc.lookup_right] do
    let s ← saveState
    if let some [g'] ← applyOr g (← mkAppM lem #[hd.toExpr]) then
      if ← proveLookupF g' before? (fuel - 1) then return true
    s.restore
  return false

end

/-- The depth of the searches for a binding and a key disequality: a map's description, its
parts, and the `remove`/`update` steps built from it are each a level. -/
def lookupFuel : Nat := 24

/-- `lookup m k = some v` (see `proveLookupF`). -/
def proveLookup (g : MVarId) (before? : Option FVarId := none) : MetaM Bool :=
  proveLookupF g before? lookupFuel

/-- `lookup r k = none`: `r` is the empty map, a binding at another key, a `remove` at `k` or at
another key of a map without `k`, an `update` at another key of a map without `k`, a described
map neither of whose sides binds `k`, or a frame beside a map that binds `k` in a description
(`concat` is defined only on maps with no key in common). -/
partial def proveLookupNoneF (g : MVarId) (fuel : Nat) : MetaM Bool := g.withContext do
  if fuel == 0 then return false
  let some (_, l, _) := (← instantiateMVars (← g.getType)).eq? | return false
  unless l.isAppOf ``KPrelude.MapHook.lookup do return false
  let r ← instantiateMVars (l.getArg! (l.getAppNumArgs - 2))
  let k ← instantiateMVars l.appArg!
  let sub (g' : MVarId) : MetaM Bool := do
    let ty ← instantiateMVars (← g'.getType)
    if ty.isAppOf ``KPrelude.MapHook.WF then proveWF g'
    else if ty.ne?.isSome then proveKeyNe g' fuel
    else proveLookupNoneF g' (fuel - 1)
  if r.isAppOf ``KPrelude.MapHook.remove then
    if ← applyWith g ``KPrelude.MapHook.lookup_remove_self sub then return true
    return ← applyWith g ``KClaims.MapLoc.none_remove sub
  if r.isAppOf ``KPrelude.MapHook.update then
    return ← applyWith g ``KClaims.MapLoc.none_update sub
  if r.isAppOf ``KPrelude.MapHook.element then
    return ← applyWith g ``KClaims.MapLoc.none_element sub
  -- the empty map, also as the literal `kc_norm` evaluates it to
  if (← applyOr g (← mkConstWithFreshMVarLevels ``KClaims.MapLoc.lookup_unit)).isSome then return true
  -- a binding, as the literal `kc_norm` evaluates `element k v` to: read as `element`
  unless r.isFVar do
    let s ← saveState
    try
      let n ← forallTelescope (← getConstInfo ``KPrelude.MapHook.element).type fun xs _ => pure xs.size
      let ls := l.getAppArgs
      let k₀ ← mkFreshExprMVar (← inferType k)
      let v₀ ← mkFreshExprMVar ((← whnfR (← inferType l)).appArg!)
      let elemE ← mkAppOptM ``KPrelude.MapHook.element
        (#[some ls[0]!, some ls[1]!, some ls[2]!] ++ Array.replicate (n - 5) none ++ #[some k₀, some v₀])
      if ← isDefEq r elemE then
        let elemE ← instantiateMVars elemE
        let g' ← g.replaceTargetDefEq (← mkEq (← mkAppM ``KPrelude.MapHook.lookup #[elemE, k])
          (← mkAppOptM ``Option.none #[(← whnfR (← inferType l)).appArg!]))
        if ← applyWith g' ``KClaims.MapLoc.none_element sub then return true
    catch _ => pure ()
    s.restore
    return false
  if let some (hd, _, _) ← mapDesc? r then
    let s ← saveState
    if let some [ga, gb] ← applyOr g (← mkAppM ``KClaims.MapLoc.none_concat #[hd.toExpr]) then
      if (← proveLookupNoneF ga (fuel - 1)) && (← proveLookupNoneF gb (fuel - 1)) then return true
    s.restore
  -- a side of a description whose other side binds `k`
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    unless a.isAppOf ``KPrelude.MapHook.concat && b.isAppOfArity ``Option.some 2 do continue
    let x := a.getArg! (a.getAppNumArgs - 2)
    let y := a.appArg!
    for (side, other, lem) in [(y, x, ``KClaims.MapLoc.none_right), (x, y, ``KClaims.MapLoc.none_left)] do
      unless (← instantiateMVars side) == r do continue
      let s ← saveState
      let ok ← observing? do
        let lk ← mkAppM ``KPrelude.MapHook.lookup #[other, k]
        let .app _ vty ← whnfR (← inferType lk) | failure
        let v ← mkFreshExprMVar vty
        let hl ← mkFreshExprMVar (← mkEq lk (← mkAppM ``Option.some #[v]))
        unless ← proveLookupF hl.mvarId! none fuel do failure
        g.assign (← mkAppM lem #[d.toExpr, ← instantiateMVars hl])
      if ok.isSome then return true
      s.restore
  return false

def proveLookupNone (g : MVarId) : MetaM Bool := proveLookupNoneF g lookupFuel

/-- The values of a map pattern's bindings, where the map it is matched at is known: a pattern
`K₁ |-> ?V₁ K₂ |-> ?V₂ ?F` is `concat B ?F = some m` with `concat (element K₁ ?V₁) … = some B`
among the goals `gs`, and each `?Vᵢ` is `m`'s binding at `Kᵢ` (`proveLookup`, through the
descriptions of `m`). A claim applied at a configuration (a circularity) is matched so: the
binding block is then built (`kc_map`) and the frame is the rest (`kc_map_ext`). To a fixpoint,
since one map's values may be another's keys (`<env>`'s locations, `<store>`'s keys). -/
def matchMapValues (gs : Array MVarId) : MetaM Unit := do
  let mut progress := true
  let mut fuel := 8
  while progress && fuel > 0 do
    progress := false
    fuel := fuel - 1
    for g in gs do
      if ← g.isAssigned then continue
      let found ← g.withContext do
        let some (_, a, b) := (← instantiateMVars (← g.getType)).eq? | return false
        unless a.isAppOf ``KPrelude.MapHook.concat && b.isAppOfArity ``Option.some 2 do return false
        let m := b.appArg!
        if m.hasExprMVar then return false
        -- the block's bindings: its own, or those of the goal defining it
        let blk := a.getArg! (a.getAppNumArgs - 2)
        let mut parts := #[blk, a.appArg!]
        if blk.isMVar then
          for g' in gs do
            if ← g'.isAssigned then continue
            let some (_, a', b') := (← instantiateMVars (← g'.getType)).eq? | continue
            unless a'.isAppOf ``KPrelude.MapHook.concat && b'.isAppOfArity ``Option.some 2 do continue
            if b'.appArg! == blk then
              parts := #[a'.getArg! (a'.getAppNumArgs - 2), a'.appArg!]
        let mut found := false
        for e in parts do
          unless e.isAppOf ``KPrelude.MapHook.element do continue
          let k := e.getArg! (e.getAppNumArgs - 2)
          let v := e.appArg!
          unless !k.hasExprMVar && v.hasExprMVar do continue
          let s ← saveState
          let hl ← mkFreshExprMVar (← mkEq (← mkAppM ``KPrelude.MapHook.lookup #[m, k])
            (← mkAppM ``Option.some #[v]))
          if ← proveLookup hl.mvarId! then found := true else s.restore
        return found
      if found then progress := true

/-- Close goals `gs` with `closer`, in order; `false` (and nothing assigned) if one fails. -/
def closeAll (closer : TSyntax `tactic) (gs : Array MVarId) : TacticM Bool := do
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    -- metavariables only as the value of a partial function, `f args = some ?x`, which the
    -- closer finds (`kc_assumption`), or as the frame of a map pattern, `concat A ?F = some m`,
    -- which is what `m` binds besides `A`'s keys (`kc_map_ext`)
    if t.hasExprMVar then
      let some (_, a, b) := t.eq? | return false
      let frame := a.isAppOf ``KPrelude.MapHook.concat && a.appArg!.isMVar
        && !(a.getArg! (a.getAppNumArgs - 2)).hasExprMVar && !b.hasExprMVar
      unless frame || (!a.hasExprMVar && b.isAppOfArity ``Option.some 2 && b.appArg!.isMVar) do
        return false
    setGoals [g]
    try
      evalTactic closer
      unless (← getUnsolvedGoals).isEmpty do return false
    catch _ => return false
  return true

/-- A witness's equation `f args = some ?x` with `args` known, solved by the value it names: a
hypothesis with the same left-hand side (a partial function has one value), or, where `args`
are closed, the evaluation of `f args`, or, for a hook (`KPrelude.…`, whose definedness its
literal arguments decide: `tdiv x 8`), its value at symbolic arguments. `false` when none gives
it (nothing assigned). -/
def solveWitness (g : MVarId) : MetaM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (_, a, b) := t.eq? | return false
  unless !a.hasExprMVar && b.isAppOfArity ``Option.some 2 && b.appArg!.isMVar do return false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, a', b') := (← instantiateMVars d.type).eq? | continue
    unless (← instantiateMVars a') == a do continue
    let s ← saveState
    if ← isDefEq b b' then
      g.assign d.toExpr
      return true
    s.restore
  if a.hasFVar then
    let .const f _ := a.getAppFn | return false
    unless (`KPrelude).isPrefixOf f do return false
    let v ← whnfD a
    unless v.isAppOfArity ``Option.some 2 do return false
    let s ← saveState
    if ← isDefEq b v then
      g.assign (← mkEqRefl a)
      return true
    s.restore
    return false
  let s ← saveState
  if ← isDefEq a b then
    g.assign (← mkEqRefl a)
    return true
  s.restore
  return false

/-- Solve an existential/conjunctive goal (a target, or a claim instance): the witnesses that
partial functions' values name first, since the other equations may apply a function to them
(`f ?x` reduces only once `?x` is known); then unify equations, then close what remains. -/
def solveConj (closer : TSyntax `tactic) (g : MVarId) : TacticM Bool := do
  let s ← saveState
  let ok ← g.withContext do
    let (ws, gs) ← peel g #[] #[]
    -- to a fixpoint: one witness may be an argument of another's function (`tmod ?r 8`)
    let mut gs := gs
    let mut progress := true
    while progress do
      progress := false
      let mut left := #[]
      for gi in gs do
        if ← solveWitness gi then progress := true else left := left.push gi
      gs := left
    let mut rest := #[]
    for gi in gs do
      let t ← instantiateMVars (← gi.getType)
      match t.eq? with
      | some (_, a, b) =>
        if ← isDefEq a b then
          gi.assign (← mkEqRefl a)
        else if ← structUnify a b then
          rest := rest.push gi
        else if (← instantiateMVars a).isAppOf ``KPrelude.MapHook.concat then
          -- a map pattern of the target over a frame (`K |-> V REST`): `concat` does not
          -- evaluate on the frame, so the closer proves it (`kc_assumption`, `kc_map`)
          rest := rest.push gi
        else return false
      | none => rest := rest.push gi
    matchMapValues rest
    -- a witness may be chosen by the closer (the value of a partial function, `kc_assumption`)
    unless ← closeAll closer rest do return false
    for w in ws do
      if (← instantiateMVars w).hasExprMVar then return false
    return true
  unless ok do s.restore
  return ok

/-- Target: `P c`. -/
def tryDone (closer : TSyntax `tactic) (g : MVarId) : TacticM Bool := do
  let s ← saveState
  let t ← instantiateMVars (← g.getType)
  let lem ← match t.getAppFn with
    | .const ``KClaims.AF _ => pure ``KClaims.AF.here
    | .const ``KClaims.AFn _ => pure ``KClaims.AFn.here
    | .const ``KClaims.Reach _ => pure ``KClaims.Reach.here
    | _ => return false
  let ok ← g.withContext do
    let some (c, _) := configOf t | return false
    let P := t.getAppArgs[2]!
    let gp ← mkFreshExprSyntheticOpaqueMVar (P.beta #[c]).headBeta
    let as := t.getAppArgs
    if lem == ``KClaims.AFn.here then
      g.assign (mkAppN (mkConst lem) #[as[0]!, as[1]!, as[2]!, as[4]!, as[3]!, gp])
    else
      g.assign (mkAppN (mkConst lem) #[as[0]!, as[1]!, as[2]!, as[3]!, gp])
    solveConj closer gp.mvarId!
  unless ok do s.restore
  return ok

/-- The simp set that turns a Boolean condition `b = true` into a proposition. -/
syntax "kc_bool_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| kc_bool_simp $[$loc]?) => `(tactic| simp only [kc_simp, decide_eq_true_eq,
      decide_eq_false_iff_not, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.not_eq_false', beq_iff_eq, bne_iff_ne, ne_eq, Bool.false_eq_true, not_false_eq_true,
      Bool.true_eq_false, decide_not, Bool.not_not, Int.not_lt, Int.not_le] $[$loc]?)

/-- An application of an inductive predicate (with indices, not one of the logical connectives)
whose index arguments are all constructor applications. -/
def refutable (t : Expr) : MetaM Bool := do
  let .const n _ := t.getAppFn | return false
  if n == ``Eq || n == ``HEq || n == ``Exists || n == ``And || n == ``Or then return false
  let some (.inductInfo ii) := (← getEnv).find? n | return false
  if ii.numIndices == 0 then return false
  unless ← isProp t do return false
  let args := t.getAppArgs
  for a in args[ii.numParams:] do
    let w ← whnfD a
    unless w.getAppFn.isConst && (← isConstructorApp w) do return false
  return true


/-- Locate the binding of a rule's match `h : concat (element k v) r = some m` in the claim's
description of `m` (`KClaims.MapLoc`): against one binding, its key and value are the binding's
and the rest is empty; against `A B`, it is in one side, which the other does not bind (two
cases); the empty map has none. The equations this yields are then opened as any others. `none`
when `m` is not described (a frame of the claim, which the rule reads). -/
def locateMap (g : MVarId) (h : LocalDecl) (a b : Expr) : MetaM (Option (List MVarId)) := g.withContext do
  unless b.isAppOfArity ``Option.some 2 do return none
  let m ← instantiateMVars b.appArg!
  let note (pf : Expr) : MetaM (MVarId × FVarId) := do
    let g' ← g.assert `kcloc (← inferType pf) pf
    let (fv, g'') ← g'.intro1P
    return (g'', fv)
  if a.isAppOf ``KPrelude.MapHook.concat then
    let x := a.getArg! (a.getAppNumArgs - 2)
    let y := a.appArg!
    -- an empty side: the match is the other side
    if x.isAppOf ``KPrelude.MapHook.unit then
      return some [(← note (← mkAppM ``KClaims.MapLoc.of_unit_rest #[h.toExpr])).1]
    if y.isAppOf ``KPrelude.MapHook.unit then
      return some [(← note (← mkAppM ``KClaims.MapLoc.of_unit_right #[h.toExpr])).1]
  let some (k, v, _) := elemConcat? a | return none
  -- a key the description binds, found as `kc_map` finds it (unification of the keys): the
  -- value and the rest follow, with no case split
  let found ← do
    let s ← saveState
    let v₀ ← mkFreshExprMVar (← inferType v)
    let hl ← mkFreshExprMVar (← mkEq (← mkAppM ``KPrelude.MapHook.lookup #[m, k]) (← mkAppM ``Option.some #[v₀]))
    if ← proveLookup hl.mvarId! h.fvarId then
      pure (some (← mkAppM ``KClaims.MapLoc.of_found #[h.toExpr, ← instantiateMVars hl]))
    else s.restore; pure none
  if let some pf := found then return some [(← note pf).1]
  -- a literal map (`kc_norm` evaluates `element k v` to the carrier's list of one binding)
  let x := a.getArg! (a.getAppNumArgs - 2)
  let xs := x.getAppArgs
  let unitE := mkAppN (mkConst ``KPrelude.MapHook.unit x.getAppFn.constLevels!) xs[:xs.size - 2]
  let (m, h) ← do
    if m.isAppOf ``KPrelude.MapHook.element || m.isAppOf ``KPrelude.MapHook.unit || m.isFVar then
      pure (m, h.toExpr)
    else
      let k₀ ← mkFreshExprMVar (← inferType xs[xs.size - 2]!)
      let v₀ ← mkFreshExprMVar (← inferType xs[xs.size - 1]!)
      let elemE := mkAppN x.getAppFn (xs[:xs.size - 2] ++ #[k₀, v₀])
      let m' ← if ← isDefEq m elemE then instantiateMVars elemE
        else if ← isDefEq m unitE then pure unitE else pure m
      pure (m', ← mkExpectedTypeHint h.toExpr (← mkEq a (← mkAppM ``Option.some #[m'])))
  if m.isAppOf ``KPrelude.MapHook.element then
    return some [(← note (← mkAppM ``KClaims.MapLoc.of_element #[h])).1]
  if m.isAppOf ``KPrelude.MapHook.unit then
    g.assign (← mkFalseElim (← g.getType) (← mkAppM ``KClaims.MapLoc.of_unit #[h]))
    return some []
  -- a literal of several bindings: where the lookup at the rule's key evaluates, that is the
  -- binding (`of_lookup`); else one of its pairs (`kcmem`, split by `memStep`)
  unless m.isFVar do
    if !k.hasFVar && !k.hasExprMVar then
      let lk ← whnfD (← mkAppM ``KPrelude.MapHook.lookup #[m, k])
      if lk.isAppOf ``Option.some || lk.isAppOf ``Option.none then
        return some [(← note (← mkAppM ``KClaims.MapLoc.of_lookup #[h])).1]
    let tl ← mkAppM ``KPrelude.ListIso.toList #[m]
    let tl' ← whnfD tl
    unless tl'.isAppOfArity ``List.cons 3 do return none
    let pf ← mkAppM ``KClaims.MapLoc.of_list #[h, ← mkEqRefl tl]
    let g' ← g.assert `kcloc (← inferType pf) pf
    let (fv, g'') ← g'.intro1P
    let subs ← g''.cases fv
    let some sub := subs[0]? | return some []
    let g3 ← sub.mvarId.withContext do
      let mut g3 := sub.mvarId
      for d in ← getLCtx do
        if (← instantiateMVars d.type).isAppOf ``Membership.mem then
          g3 ← g3.withContext do
            let g4 ← g3.assert `kcmem d.type d.toExpr
            let (_, g5) ← g4.intro1P
            g5.clear d.fvarId
      pure g3
    return some [g3]
  if m.isFVar then
    let some (hd, _, _) ← mapDesc? m (h.getAppFn.fvarId?) | return none
    let (g', fv) ← note (← mkAppM ``KClaims.MapLoc.of_concat #[hd.toExpr, h])
    return some ((← g'.cases fv).toList.map (·.mvarId))
  return none

/-- A rule's list pattern `h : concat (element x) t = l` against a list `l` whose elements
evaluate (a cell's literal list): `x` is its first element and `t` the rest (`ListLoc.of_cons`),
and against the empty list there is no match (`ListLoc.of_nil`). -/
def locateList (g : MVarId) (h : LocalDecl) (a b : Expr) : MetaM (Option (List MVarId)) := g.withContext do
  unless a.isAppOf ``KPrelude.ListHook.concat do return none
  let x := a.getArg! (a.getAppNumArgs - 2)
  unless x.isAppOf ``KPrelude.ListHook.element do return none
  if b.isFVar then return none
  let tl ← mkAppM ``KPrelude.ListIso.toList #[b]
  let tl' ← whnfD tl
  if tl'.isAppOfArity ``List.nil 1 then
    let pf ← mkAppM ``KClaims.ListLoc.of_nil #[h.toExpr, ← mkEqRefl tl]
    g.assign (← mkFalseElim (← g.getType) pf)
    return some []
  if tl'.isAppOfArity ``List.cons 3 then
    let hl ← mkExpectedTypeHint (← mkEqRefl tl) (← mkEq tl tl')
    let pf ← mkAppM ``KClaims.ListLoc.of_cons #[h.toExpr, hl]
    let g' ← g.assert `kcloc (← inferType pf) pf
    let (_, g'') ← g'.intro1P
    return some [g'']
  return none

/-- `kcmem : p ∈ l` with `l` a literal list (a located binding, `locateMap`): `p` is its first
element, or in the rest; none of the empty list. -/
def memStep (g : MVarId) (h : LocalDecl) : MetaM (Option (List MVarId)) := g.withContext do
  unless h.userName == `kcmem do return none
  let t ← instantiateMVars h.type
  unless t.isAppOf ``Membership.mem do return none
  -- `Membership.mem l p` (the collection first)
  let l := t.getArg! (t.getAppNumArgs - 2)
  let l' ← whnfD l
  if l'.isAppOfArity ``List.nil 1 then
    let ne ← mkAppOptM ``List.not_mem_nil #[none, some t.appArg!]
    g.assign (← mkFalseElim (← g.getType) (mkApp ne h.toExpr))
    return some []
  unless l'.isAppOfArity ``List.cons 3 do return none
  let h' ← mkExpectedTypeHint h.toExpr (← mkAppM ``Membership.mem #[l', t.appArg!])
  let pf ← mkAppM ``List.eq_or_mem_of_mem_cons #[h']
  let g' ← g.assert `kcmemor (← inferType pf) pf
  let (fv, g'') ← g'.intro1P
  let g'' ← g''.clear h.fvarId
  let subs ← g''.cases fv
  let mut out := #[]
  for sub in subs do
    -- the second case's membership keeps the name, for the next split
    let g3 ← sub.mvarId.withContext do
      for d in ← getLCtx do
        if !d.isImplementationDetail && (← instantiateMVars d.type).isAppOf ``Membership.mem then
          return ← sub.mvarId.withContext do
            let g4 ← sub.mvarId.assert `kcmem d.type d.toExpr
            let (_, g5) ← g4.intro1P
            g5.clear d.fvarId
      pure sub.mvarId
    out := out.push g3
  return some out.toList

/-- `h : concat A B = some x` with an earlier `concat A B = some y`: one map has one value, so
`x = y` (a rule that reads a binding and writes it back leaves its map as it was). -/
def sameMap (g : MVarId) (h : LocalDecl) (a b : Expr) : MetaM (Option (List MVarId)) := g.withContext do
  unless a.isAppOf ``KPrelude.MapHook.concat && b.isAppOfArity ``Option.some 2 do return none
  let a ← instantiateMVars a
  for d in ← getLCtx do
    if d.fvarId == h.fvarId then break
    if d.isImplementationDetail then continue
    let some (_, a', b') := (← instantiateMVars d.type).eq? | continue
    unless b'.isAppOfArity ``Option.some 2 && (← instantiateMVars a') == a do continue
    if (← instantiateMVars b') == (← instantiateMVars b) then return none
    let pf ← mkAppM ``Option.some.inj #[← mkEqTrans (← mkEqSymm d.toExpr) h.toExpr]
    let g' ← g.assert `kcsame (← inferType pf) pf
    let (_, g'') ← g'.intro1P
    return some [g'']
  return none

/-- `lookup m k = none` where the description of `m` binds `k` (`proveLookup`): the binding is
there (a case of `MapLoc.of_concat` that puts a key on the side that does not bind it). -/
def lookupNoneContra (g : MVarId) (h : LocalDecl) (a b : Expr) : MetaM Bool := g.withContext do
  unless a.isAppOf ``KPrelude.MapHook.lookup && b.isAppOf ``Option.none do return false
  let s ← saveState
  let some vty := (← whnfR (← inferType b)).app1? ``Option | return false
  let v₀ ← mkFreshExprMVar vty
  let hl ← mkFreshExprMVar (← mkEq a (← mkAppM ``Option.some #[v₀]))
  unless ← proveLookup hl.mvarId! h.fvarId do s.restore; return false
  -- `some v₀ = none`
  let e ← mkEqTrans (← mkEqSymm (← instantiateMVars hl)) h.toExpr
  g.assign (← mkNoConfusion (← g.getType) e)
  return true

/-- `h : f args = v` where `f args` does not reduce (its arguments symbolic): `h` rewritten with a
proved equation of `f` (`@[k2l_equation]`) whose premises follow from the facts (`k2l_arith_omega`,
after the premises' own binders), as K evaluates a function by the equation whose `requires`
holds; its right-hand side then opens like any other value. An equation whose right-hand side
applies `f` again is not used, so that the opening ends. `none` when no equation applies. -/
def byEquation (g : MVarId) (h : LocalDecl) (a : Expr) : TacticM (Option MVarId) := g.withContext do
  let .const f _ := a.getAppFn | return none
  let goals ← getGoals
  try byEquationCore g h a f finally setGoals goals

where
  byEquationCore (g : MVarId) (h : LocalDecl) (a : Expr) (f : Name) : TacticM (Option MVarId) := do
  for thm in KPrelude.equationsOf (← getEnv) f do
    let s ← saveState
    let r ← observing? do
      let c ← mkConstWithFreshMVarLevels thm
      let (ms, _, ty) ← forallMetaTelescopeReducing (← inferType c)
      let some (_, lhs, rhs) := ty.eq? | failure
      if (rhs.find? (·.isConstOf f)).isSome then failure
      unless ← isDefEq lhs a do failure
      for m in ms do
        if ← m.mvarId!.isAssigned then continue
        -- a premise; a value the left-hand side does not determine is no use
        unless ← isProp (← inferType m) do failure
        setGoals [m.mvarId!]
        evalTactic (← `(tactic| (intros; k2l_arith_omega)))
        unless (← getUnsolvedGoals).isEmpty do failure
      return ← instantiateMVars (mkAppN c ms)
    match r with
    | some eqn =>
      if eqn.hasExprMVar then s.restore; continue
      -- `h' : rhs = v`
      let h' ← mkEqTrans (← mkEqSymm eqn) h.toExpr
      let g' ← g.assert h.userName (← inferType h') h'
      let g' ← g'.tryClear h.fvarId
      let (_, g'') ← g'.intro1P
      return some g''
    | none => s.restore
  return none

/-- One opening step on some hypothesis of `g`: `∃` and `∧` are destructured, an equation with
a variable side is substituted, an equation `f … = some x` is evaluated by `cases`, a Boolean
condition is simplified to a proposition. `none` if no hypothesis needs it. -/
def openStep (g : MVarId) (tried : Array FVarId) : TacticM (Option (List MVarId × Array FVarId)) :=
  g.withContext do
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail || tried.contains ldecl.fvarId then continue
    -- the assumed invariant stays folded (`kc_auto … inv`): it is opened on demand
    if ldecl.userName == `hinv then continue
    let t ← whnfD (← instantiateMVars ldecl.type)
    match t.getAppFnArgs with
    | (``Exists, _) | (``And, _) =>
      let subs ← g.cases ldecl.fvarId
      return some (subs.toList.map (·.mvarId), tried)
    | (``Eq, #[ty, a, b]) =>
      let mut substable := false
      if b.isFVar then
        if !(← exprDependsOn a b.fvarId!) then substable := true
      if a.isFVar then
        if !(← exprDependsOn b a.fvarId!) then substable := true
      if substable then
        try return some ([← Lean.Meta.subst g ldecl.fvarId], tried) catch _ => pure ()
      -- a rule's match of a map the claim describes (`locateMap`)
      if let some gs ← sameMap g ldecl a b then return some (gs, tried.push ldecl.fvarId)
      if let some gs ← locateMap g ldecl a b then return some (gs, tried.push ldecl.fvarId)
      if ← lookupNoneContra g ldecl a b then return some ([], tried)
      if let some gs ← locateList g ldecl a b then return some (gs, tried.push ldecl.fvarId)
      if (← whnfR ty).isConstOf ``Bool then
        setGoals [g]
        try
          evalTactic (← `(tactic| kc_bool_simp at $(mkIdent ldecl.userName):ident))
          return some (← getUnsolvedGoals, tried.push ldecl.fvarId)
        catch _ => return some ([g], tried.push ldecl.fvarId)
      let a' ← whnfD a
      let b' ← whnfD b
      let ctorA ← if a'.getAppFn.isConst then isConstructorApp a' else pure false
      let ctorB ← if b'.getAppFn.isConst then isConstructorApp b' else pure false
      if a'.isAppOf ``Option.some || a'.isAppOf ``Option.none || (ctorA && ctorB) then
        try
          let subs ← g.cases ldecl.fvarId
          return some (subs.toList.map (·.mvarId), tried)
        catch _ => pure ()
      -- a value bound by a partial call, `(g x).bind k = some v`: the call has a value `y`, and
      -- `k y = some v` (an equation's right-hand side, below)
      let ai ← instantiateMVars a
      if ai.isAppOf ``Option.bind && b.isAppOfArity ``Option.some 2 then
        let hs ← Term.exprToSyntax ldecl.toExpr
        let pf ← Term.elabTerm (← `(Option.bind_eq_some_iff.mp $hs)) none
        Term.synthesizeSyntheticMVarsNoPostponing
        let pf ← instantiateMVars pf
        let g' ← g.assert ldecl.userName (← inferType pf) pf
        let g' ← g'.tryClear ldecl.fvarId
        let (_, g'') ← g'.intro1P
        return some ([g''], tried)
      if let some g' ← byEquation g ldecl ai then return some ([g'], tried)
      return some ([g], tried.push ldecl.fvarId)
    | _ =>
      if let some gs ← memStep g ldecl then return some (gs, tried)
      -- an inductive predicate whose indices are constructor applications: inversion refutes
      -- the case when no constructor of the predicate has those indices
      if ← refutable t then
        let s ← saveState
        let closed ← try pure (← g.cases ldecl.fvarId).isEmpty catch _ => pure false
        if closed then return some ([], tried)
        s.restore
      continue
  return none

/-- Open every hypothesis of `g` (see `openStep`). -/
partial def openAll (g : MVarId) (tried : Array FVarId := #[]) (fuel : Nat := 200) :
    TacticM (List MVarId) := do
  if fuel == 0 then return [g]
  match ← openStep g tried with
  | none => return [g]
  | some (gs, tried) => return (← gs.mapM fun g => openAll g tried (fuel - 1)).flatten

/-- `kc_open`: `openAll` on the main goal (the premises of a case of a rule, opened as `tryRel`
opens them). -/
elab "kc_open" : tactic => do
  let g ← getMainGoal
  setGoals (← openAll g)

/-- Whether `ty` is a sort of the arity-indexed term family (`NS.Term t`, design.md §2.1), where
a sort's values are not the family's constructors: `familyCases` enumerates them. -/
def isFamilyType (ty : Expr) : MetaM Bool := do
  return (← whnfR ty).getAppFn.constName?.any (KPrelude.isFamilyName (← getEnv))

/-- Split single-constructor variables (cells) so that matchers on them reduce. On the
arity-indexed family a cell sort has one value form too, `familyCases` finds it. -/
def splitCells (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← whnfR ldecl.type
    if ← isFamilyType ty then
      let s ← saveState
      try
        match ← KPrelude.familyCases g ldecl.fvarId with
        -- not a collection sort, whose one form is its list model (`coll_… l`), as in the one type
        -- per sort encoding, where a collection has two constructors
        | #[(sg, args)] =>
          if ← sg.withContext (args.anyM fun a => return (← whnfR (← inferType a)).isAppOf ``List)
          then s.restore else g := sg
        | _ => s.restore
      catch _ => s.restore
      continue
    let .const n _ := ty.getAppFn | continue
    let some (.inductInfo ii) := (← getEnv).find? n | continue
    if ii.ctors.length != 1 || ii.numIndices != 0 || ii.isRec && false then continue
    if n == ``Exists || n == ``And || n == ``Eq || (← isProp ty) then continue
    if ii.ctors.length == 1 then
      if (Lean.getStructureInfo? (← getEnv) n).isSome then continue
      try
        let subs ← g.cases ldecl.fvarId
        if let #[s] := subs then g := s.mvarId
      catch _ => pure ()
  return g

/-- `kc_intro h`: open the claim instance `h`, split cells, normalize the configuration. -/
elab "kc_intro " h:ident : tactic => do
  let g ← getMainGoal
  let fv ← g.withContext do return (← getLocalDeclFromUserName h.getId).fvarId
  let _ := fv
  let gs ← openAll g
  let gs ← gs.mapM fun g => do let g ← splitCells g; normGoal g
  setGoals gs

/-- Close the goals whose arithmetic hypotheses contradict each other (`omega`), keep the others. -/
def pruneArith (gs : List MVarId) : TacticM (List MVarId) := do
  let mut out := []
  for g in gs do
    let s ← saveState
    setGoals [g]
    try
      evalTactic (← `(tactic| (exfalso; omega)))
      unless (← getUnsolvedGoals).isEmpty do s.restore; out := out ++ [g]
    catch _ => s.restore; out := out ++ [g]
  return out

/-- Split on the first non-literal Boolean of the configuration; with `prune`, drop the cases
whose arithmetic hypotheses are contradictory. -/
def trySplit (g : MVarId) (prune : Bool := false) : TacticM (Option (List MVarId)) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (c, _) := configOf t | return none
  let some b ← findBool c | return none
  setGoals [g]
  let fin (gs : List MVarId) : TacticM (List MVarId) := do
    let gs ← gs.mapM fun g => (normGoal g : MetaM MVarId)
    if prune then pruneArith gs else pure gs
  if b.isFVar then
    let subs ← g.cases b.fvarId!
    return some (← fin (subs.toList.map (·.mvarId)))
  let bs ← Term.exprToSyntax b
  try
    if (← invHyp?).isSome then
      -- the assumed invariant is about the same configuration: generalize it too
      evalTactic (← `(tactic| (generalize $(mkIdent `hkc) : $bs = $(mkIdent `bkc):ident at $(mkIdent `hinv):ident ⊢; cases $(mkIdent `bkc):ident <;> (try kc_bool_simp at $(mkIdent `hkc):ident))))
    else
      evalTactic (← `(tactic| (generalize $(mkIdent `hkc) : $bs = $(mkIdent `bkc):ident; cases $(mkIdent `bkc):ident <;> (try kc_bool_simp at $(mkIdent `hkc):ident))))
    let gs ← getUnsolvedGoals
    return some (← fin gs)
  catch _ => return none

/-- Apply a claim (a circularity with its index bound, or a proved claim) at the goal's
configuration; continue from its post-condition. `ap c Q : Inst c Q → AFn R Q n c`. -/
def tryClaim (closer : TSyntax `tactic) (g : MVarId) (ap : Expr → Expr → TacticM (Option Expr))
    (invP : Option Expr := none) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  let r ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some (c, _) := configOf t | return none
    let α ← inferType c
    let Q ← mkFreshExprMVar (← mkArrow α (mkSort Level.zero))
    let some f ← ap c Q | return none
    let fty ← whnfR (← inferType f)
    let .forallE _ instTy _ _ := fty | return none
    let gi ← mkFreshExprSyntheticOpaqueMVar instTy
    unless ← solveConj closer gi.mvarId! do return none
    let hQ := mkApp f gi
    let Qi ← instantiateMVars Q
    match invP with
    | some P =>
      -- the claim's target is `P ∧ Q`: continue with `hinv : P d` and `Q d`
      let contTy ← withLocalDeclD `d α fun d => do
        let body ← mkArrow (P.beta #[d]).headBeta (← mkArrow (Qi.beta #[d]).headBeta (configOf t |>.get!.2 d))
        mkForallFVars #[d] body
      let cont ← mkFreshExprSyntheticOpaqueMVar contTy
      let lem := if t.isAppOf ``KClaims.AFn then ``KClaims.AFn.trans_inv else ``KClaims.AF.trans_inv
      g.assign (← mkAppM lem #[hQ, cont])
      let old := (← invHyp?).map (·.fvarId)
      let (_, g1) ← cont.mvarId!.intro1
      let (_, g1) ← g1.intro `hinv
      let (_, g1) ← g1.intro1
      let g1 ← match old with
        | some o => (try g1.clear o catch _ => pure g1)
        | none => pure g1
      let gs ← openAll g1
      return some (← gs.mapM fun g => (normGoal g : MetaM MVarId))
    | none =>
      let contTy ← withLocalDeclD `d α fun d => do
        let body ← mkArrow (Qi.beta #[d]).headBeta (configOf t |>.get!.2 d)
        mkForallFVars #[d] body
      let cont ← mkFreshExprSyntheticOpaqueMVar contTy
      let lem := if t.isAppOf ``KClaims.AFn then ``KClaims.AFn.trans
        else if t.isAppOf ``KClaims.Reach then ``KClaims.Reach.trans else ``KClaims.AF.trans
      g.assign (← mkAppM lem #[hQ, cont])
      let (_, g1) ← cont.mvarId!.introN 2
      let gs ← openAll g1
      return some (← gs.mapM fun g => (normGoal g : MetaM MVarId))
  match r with
  | some gs => return some gs
  | none => s.restore; return none

/-- Prove `n < n0` by `omega`. -/
def provLt (ty : Expr) : TacticM (Option Expr) := do
  let g ← mkFreshExprSyntheticOpaqueMVar ty
  let s ← saveState
  setGoals [g.mvarId!]
  try
    evalTactic (← `(tactic| omega))
    return some g
  catch _ => s.restore; return none

structure Cfg where
  closer : TSyntax `tactic
  rules : Array Expr
  circs : Array Name
  /-- proved claims; a local hypothesis is kept by its name, since a case split replaces it -/
  lemmas : Array (Expr ⊕ Name)
  fuel : Nat
  /-- rule steps, splits, kept claim applications, configurations, frame refinements -/
  stats : IO.Ref (Array Nat)
  /-- the assumed invariant (`inv [hP]`): `hP : Preserved R P`, and `P` -/
  inv : Option (Expr × Expr) := none
  /-- split variables of small sum types when stuck (`split`) -/
  splitVars : Bool := false
  /-- the relation has an `ExecSucc` instance: a step by every successor when no single rule
  decides it (no `RuleSet`, so no determinism) -/
  succ : Bool := false

/-- A type whose values a case split enumerates cheaply: an inductive type without indices, with 2
to 8 constructors, none of which has a field of the type itself (so `SortK`, maps and lists are
excluded, and a split never produces a variable of the same type again); not a leaf type (`Int`,
`Bool`, which `trySplit` handles, …), and not a structure. -/
def splittable (ty : Expr) : MetaM Bool := do
  if ← isLeafType ty then return false
  let ty ← whnfR ty
  let .const n _ := ty.getAppFn | return false
  let env ← getEnv
  let some (.inductInfo ii) := env.find? n | return false
  if ii.numIndices != 0 || ii.ctors.length < 2 || ii.ctors.length > 8 then return false
  if (Lean.getStructureInfo? env n).isSome then return false
  -- `isRec` is set for every type of a `mutual` block, so look at the fields themselves
  for ctor in ii.ctors do
    let some (.ctorInfo ci) := env.find? ctor | return false
    let selfRef ← forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        if (← whnfR (← inferType x)).getAppFn.constName? == some n then return true
      return false
    if selfRef then return false
  return true

/-- The free variables of `e`, left to right, first occurrences. -/
partial def fvarsInOrder (e : Expr) (acc : Array FVarId := #[]) : Array FVarId :=
  match e with
  | .fvar f => if acc.contains f then acc else acc.push f
  | .app f a => fvarsInOrder a (fvarsInOrder f acc)
  | .mdata _ b => fvarsInOrder b acc
  | _ => acc

/-- The cases of a variable `x : Term t` of the arity-indexed family when they are few, as
`splittable` says of an inductive type: the sort `t` has 2 to 8 value forms (`familyCases`: its
constructors and the leaves it injects), none with an argument of sort `t`. -/
def familySplit (g : MVarId) (x : FVarId) : MetaM (Option (Array MVarId)) := do
  let s ← saveState
  try
    let ty ← g.withContext do whnfR (← x.getType)
    let cs ← KPrelude.familyCases g x
    if cs.size < 2 || cs.size > 8 then s.restore; return none
    for (sg, args) in cs do
      let self ← sg.withContext do
        args.anyM fun a => do isDefEq (← whnfR (← inferType a)) ty
      if self then s.restore; return none
    return some (cs.map (·.1))
  catch _ => s.restore; return none

/-- Split the first variable of the configuration whose type is `splittable` (on the arity-indexed
family, `familySplit`); each case is opened (a hypothesis about the variable that becomes false
closes the case). -/
def trySplitVar (g : MVarId) : TacticM (Option (List MVarId)) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (c, _) := configOf t | return none
  for f in fvarsInOrder c do
    let some d := (← getLCtx).find? f | continue
    if d.isLet then continue
    let fam ← isFamilyType d.type
    unless fam || (← splittable d.type) do continue
    let s ← saveState
    try
      let some subs ← if fam then familySplit g f
          else pure (some ((← g.cases f).map (·.mvarId)))
        | s.restore; continue
      let mut out := []
      for sg in subs do
        let gs ← openAll sg
        out := out ++ (← gs.mapM fun g => (normGoal g : MetaM MVarId))
      return some out
    catch _ => s.restore
  return none

/-- A projection `proj_A_B x` of a variable `x` of the configuration, in a hypothesis, with the
generated lemma `proj_eq_some_A_B` beside it. -/
partial def findProj (cfgVars : Array FVarId) (e : Expr) : MetaM (Option (Expr × Name)) := do
  if e.hasLooseBVars then
    -- look inside binders' bodies only through closed subterms
    for a in e.getAppArgs do
      if let some r ← findProj cfgVars a then return some r
    return none
  match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    if let .str pre last := n then
      if last.startsWith "proj_" && args.size == 1 && args[0]!.isFVar && cfgVars.contains args[0]!.fvarId! then
        let lem := Name.str pre ("proj_eq_some_" ++ (last.drop 5).toString)
        if (← getEnv).contains lem then return some (e, lem)
    for a in args do
      if let some r ← findProj cfgVars a then return some r
    return none
  | _ =>
    match e with
    | .app f a =>
      if let some r ← findProj cfgVars f then return some r
      findProj cfgVars a
    | .lam _ _ b _ | .forallE _ _ b _ => findProj cfgVars b
    | .mdata _ b => findProj cfgVars b
    | _ => return none

/-- Use the assumed invariant where no rule applies: open a copy of `hinv` with the `kc_inv` set
(the invariant's definitions and equations; collections become lists of their bindings), then
`kc_inv_fns` (the definitions of the functions it calls), and when it constrains a variable `x` of the configuration through a projection
(`proj_A_B x`, for example "the store value `x` is a `Value`"), split on that projection: the case
`none` is refuted by the opened invariant, and in the case `some y`, `x` is replaced by the
injection of `y` (`proj_eq_some_A_B`), whose sort a later split can enumerate. -/
def tryInvProj (g : MVarId) : TacticM (Option (List MVarId)) := g.withContext do
  let some _ ← invHyp? | return none
  let t ← instantiateMVars (← g.getType)
  let some (c, _) := configOf t | return none
  let s ← saveState
  setGoals [g]
  try
    evalTactic (← `(tactic| have $(mkIdent `hkcI) := $(mkIdent `hinv)))
    evalTactic (← `(tactic| simp only [kc_inv] at $(mkIdent `hkcI):ident))
    evalTactic (← `(tactic| try simp only [kc_inv, KPrelude.ListHook.ElemsOn, KPrelude.MapHook.values, KPrelude.ListIso.toList_ofList] at $(mkIdent `hkcI):ident))
    evalTactic (← `(tactic| try simp [kc_inv, KPrelude.ListIso.toList] at $(mkIdent `hkcI):ident))
    evalTactic (← `(tactic| try simp only [kc_inv_fns] at $(mkIdent `hkcI):ident))
  catch _ => s.restore; return none
  let gs ← getUnsolvedGoals
  let [g1] := gs | return some gs   -- the invariant is false here: the case closed

  let found ← g1.withContext do
    let vars := fvarsInOrder c
    -- the projections already decided by an earlier split (`hkcP : proj_A_B x = …`)
    let mut decided : Array Expr := #[]
    for d in ← getLCtx do
      if let some (_, l, _) := (← instantiateMVars d.type).eq? then decided := decided.push l
    let some d := (← getLCtx).findFromUserName? `hkcI | return none
    let mut best : Option (Nat × Expr × Name) := none
    let mut ty ← instantiateMVars d.type
    -- the first undecided projection, by the position of its variable in the configuration
    for _ in [0:16] do
      let some (p, lem) ← findProj vars ty | break
      if decided.contains p then
        ty := ty.replace fun e => if e == p then some (mkConst ``True) else none
        continue
      let i := (vars.idxOf? p.appArg!.fvarId!).getD vars.size
      if best.all (fun b => i < b.1) then best := some (i, p, lem)
      ty := ty.replace fun e => if e == p then some (mkConst ``True) else none
    return best
  let some (_, p, lem) := found | s.restore; return none
  try
    let ps ← g1.withContext (Term.exprToSyntax p)
    setGoals [g1]
    evalTactic (← `(tactic| cases $(mkIdent `hkcP):ident : $ps:term))
    let mut out := []
    for sg in ← getUnsolvedGoals do
      setGoals [sg]
      let isSome ← sg.withContext do
        let some d := (← getLCtx).findFromUserName? `hkcP | return false
        let ty ← instantiateMVars d.type
        return (ty.eq?.map (·.2.2.isAppOf ``Option.some)).getD false
      if isSome then
        evalTactic (← `(tactic| (have $(mkIdent `hkcX) := ($(mkIdent lem)).1 $(mkIdent `hkcP); subst $(mkIdent `hkcX); clear $(mkIdent `hkcI))))
      else
        evalTactic (← `(tactic| (simp [$(mkIdent `hkcP):ident] at $(mkIdent `hkcI):ident; try clear $(mkIdent `hkcI))))
      for g2 in ← getUnsolvedGoals do
        let gs ← openAll g2
        out := out ++ (← gs.mapM fun g => (normGoal g : MetaM MVarId))
    return some out
  catch _ => s.restore; return none

inductive Outcome where
  | done
  | next (gs : List MVarId) (kind : Nat)
  /-- No step applies; `g` is the goal to leave open (after the index split, a new goal). -/
  | stuck (g : MVarId)

/-- Run `tac` on `g` within `limit` thousand heartbeats; whether it closed `g`. A failure, or
running out of heartbeats, leaves the state as it was. -/
def closesWithin (g : MVarId) (tac : TSyntax `tactic) (limit : Nat := 400000) : TacticM Bool := do
  let s ← saveState
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := limit * 1000 }) do
      setGoals [g]
      evalTactic tac
      if (← getUnsolvedGoals).isEmpty then return true
      s.restore; return false)
    (fun _ => do s.restore; return false)

/-- `kc_whnf_contra`: close the goal when an equation hypothesis `a = b` relates two different
constructors once both sides are reduced (`whnfD`), as a rule's premise does when the executable
semantics evaluates it to the other value (`isKResult(1 + 2) = true`, a projection that is
`none`). -/
elab "kc_whnf_contra" : tactic => liftMetaFinishingTactic fun g => g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (ty, a, b) := (← instantiateMVars d.type).eq? | continue
    if ← isProp ty then continue
    let a' ← whnfD a
    let b' ← whnfD b
    let some ca := a'.getAppFn.constName? | continue
    let some cb := b'.getAppFn.constName? | continue
    unless ca != cb && (← isConstructorApp a') && (← isConstructorApp b') do continue
    let g' ← g.replaceLocalDeclDefEq d.fvarId (← mkEq a' b')
    if ← g'.contradictionCore {} then return
  throwError "kc_whnf_contra: no equation hypothesis relates two different constructors"

/-- `kc_list_contra`: close the goal when a hypothesis matches `ListItem(X) REST` against the
empty list (a stream rule's pattern at a `<k>`-less cell `.List`, after `kc_norm` evaluated it to
the carrier's empty literal): `ListLoc.concat_element_ne_unit`. -/
elab "kc_list_contra" : tactic => liftMetaFinishingTactic fun g => g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    unless a.isAppOf ``KPrelude.ListHook.concat do continue
    let x := a.getArg! (a.getAppNumArgs - 2)
    unless x.isAppOf ``KPrelude.ListHook.element do continue
    let ne ← mkAppM ``KClaims.ListLoc.concat_element_ne_unit #[x.appArg!, a.appArg!]
    let some (_, _, u) := (← instantiateMVars (← inferType ne)).ne? | continue
    unless ← isDefEq b u do continue
    g.assign (← mkFalseElim (← g.getType) (mkApp ne d.toExpr))
    return
  throwError "kc_list_contra: no list match against the empty list"

/-- A case of `cases` on a relation whose premises contradict each other (a rule whose left-hand
side unifies with the configuration but whose requires is false there). -/
def closeSpurious (g : MVarId) : TacticM Bool := do
  closesWithin g (← `(tactic| first
    | contradiction
    | kc_whnf_contra
    | kc_list_contra
    | (exfalso; simp_all; done)
    | (exfalso; simp_all [kc_simp]; done)
    | (exfalso; simp [kc_simp] at * <;> omega)))

/-- Whether `ty` is a priority premise `∀ j, j < i → ¬ A j c` (a rule of a later rank: no rule of
an earlier rank applies); its `A`. -/
def priorityApp? (ty : Expr) : MetaM (Option Name) :=
  -- exactly the two binders: a telescope through `¬ A j c` would open it as a third
  forallBoundedTelescope ty (some 2) fun xs b => do
    -- (the nested action would run before the size test: a separate test)
    unless xs.size == 2 do return none
    unless (← whnfR (← inferType xs[0]!)).isConstOf ``Nat do return none
    let some a := b.not? | return none
    return a.getAppFn.constName?

/-- The priority premise among `g`'s hypotheses, and its `App`. -/
def priorityHyp? (g : MVarId) : MetaM (Option (FVarId × Name)) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some app ← priorityApp? d.type then return some (d.fvarId, app)
  return none

/-- The rank `k` of a constructor `App k …` of `App`, a literal. -/
def ctorRank? (ctor : Name) : MetaM (Option Nat) := do
  let some ci := (← getEnv).find? ctor | return none
  forallTelescopeReducing ci.type fun _ b => do
    let some k := b.getAppArgs.find? (fun a => (a.rawNatLit? <|> a.nat?).isSome) | return none
    return k.rawNatLit? <|> k.nat?

/-- The first `next` result of a rule matcher's value (a `RuleResult`, or the list of them of a
rule matching several elements of a cell collection), reduced: the successor and its proof. -/
partial def nextOf? (r : Expr) : MetaM (Option (Expr × Expr)) := do
  let r ← whnfD r
  if r.isAppOfArity ``KPrelude.RuleResult.next 6 then return some (r.getArg! 4, r.getArg! 5)
  if r.isAppOfArity ``List.cons 3 then
    if let some x ← nextOf? (r.getArg! 1) then return some x
    return ← nextOf? (r.getArg! 2)
  return none

/-- The tactic for a priority premise `∀ j, j < i → ¬ App j c`: every case of `App j c` is
contradictory: by its rank, by its premises as they stand, or once they are opened as `Step`'s
cases are (`kc_open`: a stream rule's list pattern against the cell's list, say). -/
def priorityTac : TacticM (TSyntax `tactic) :=
  `(tactic| (intro j hj ha; cases ha <;> first | omega | contradiction | kc_whnf_contra | kc_list_contra | (kc_open <;> (first | contradiction | kc_whnf_contra | (exfalso; simp_all; done))) | (exfalso; simp_all; done) | (exfalso; simp_all [kc_simp]; done)))

/-- A step of `R` from `c` by rule `ctor` (a constructor of `R`, `NS.Step.x`) through its
executable matcher `NS.Rules.x`, when that reduces to a successor: the matcher's proof is of
`R c d`, or of `Step0 i c d`, lifted to `R` by `NS.Step0.lift` with no rule of an earlier rank
applying (`priorityTac`). -/
def progressByMatcher (R c : Expr) (ctor : Name) : TacticM (Option Expr) := do
  let .str (.str ns _) x := ctor | return none
  let m := (ns ++ `Rules).str x
  unless (← getEnv).contains m do return none
  let some (d, h) ← nextOf? (← mkAppM m #[c]) | return none
  let α ← inferType c
  let pLam ← withLocalDeclD `e α fun e => do mkLambdaFVars #[e] (mkApp2 R c e)
  let hty ← whnfR (← inferType h)
  if hty.getAppFn == R.getAppFn then return some (← mkAppOptM ``Exists.intro #[α, pLam, d, h])
  let lift := (ns ++ `Step0).str "lift"
  unless (← getEnv).contains lift do return none
  let lh ← mkAppM lift #[h]
  let .forallE _ hiTy _ _ ← whnfR (← inferType lh) | return none
  let hi ← mkFreshExprSyntheticOpaqueMVar hiTy
  unless ← closesWithin hi.mvarId! (← priorityTac) do return none
  let st := mkApp lh (← instantiateMVars hi)
  return some (← mkAppOptM ``Exists.intro #[α, pLam, d, st])

/-- A successor of a step by the cases of `R`, without the case's hypotheses about the
configuration it left: the priority premise (no rule of an earlier rank applies there), a match
against a map that is not a variable (a literal the case was located in: its bindings are
already the rule's variables), and closed propositions (conditions the case evaluated; `True`).
Each was used when the case was opened, and none constrains a variable of the successor, while
every later step and closer reads the whole context: kept, they grow with each step (IMP++,
`sum = n;`: 57 hypotheses after five steps, and the sixth step did not end). Dropping a
hypothesis is sound (the goal is only weakened). -/
def dropStepFacts (g : MVarId) (pri : Option FVarId) : MetaM MVarId := g.withContext do
  let mut drop := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if pri == some d.fvarId then drop := drop.push d.fvarId; continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    if !ty.hasFVar && !ty.hasMVar then drop := drop.push d.fvarId; continue
    if let some (_, a, b) := ty.eq? then
      if a.isAppOf ``KPrelude.MapHook.concat && b.isAppOfArity ``Option.some 2 && !b.appArg!.isFVar then
        drop := drop.push d.fvarId
  g.tryClearMany drop

/-- Step by the relation itself, where the executable successors do not reduce (a symbolic part
of the configuration is read by the rule index or a matcher before a position that decides).
`R` is an inductive relation with one constructor per rule; `cases` on `R c e` unifies every
rule's left-hand side with `c` at once, so a rule whose left-hand side clashes anywhere is
dropped whatever is symbolic elsewhere. A case whose premises are contradictory is closed
(`closeSpurious`); a case of a later rank is closed by an earlier-rank rule that applies (its
`App` constructor, of the same name). Progress: a remaining rule's matcher reduced to a
successor (`progressByMatcher`), else its constructor applied with its premises proved; if
neither works (a premise not proved, or the rule's result undefined), the configuration stays
open, with a message. The cases left are the successors.

Unification may instantiate variables of the configuration (the head of a symbolic `K` rest,
say): then a case covers only part of the configurations, and the cases together cover them
all. Such steps are counted (`frame refinements`), since they are an implicit case split.

What it does not decide: a rule matching a cell map states its left-hand side as `concat …`
premises, which unification does not see; where `openAll` and the closers cannot refute them,
the rule stays a candidate (IMP++'s thread map, for one). -/
def tryRel (cfg : Cfg) (g : MVarId) : TacticM (Option (List MVarId)) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (c, _) := configOf t | return none
  let (α, R, mkNext, lem) ← match t.getAppFnArgs with
    | (``KClaims.AFn, #[α, R, P, n, _]) =>
      let some n' := predIndex n | return none
      pure (α, R, fun e => mkAppN t.getAppFn #[α, R, P, n', e], ``KClaims.AFn.step)
    | (``KClaims.AF, #[α, R, P, _]) => pure (α, R, fun e => mkAppN t.getAppFn #[α, R, P, e], ``KClaims.AF.step)
    | _ => return none
  let .const rn us := R.getAppFn | return none
  let some (.inductInfo ri) := (← getEnv).find? rn | return none
  unless ri.numIndices == 2 && R.getAppArgs.size == ri.numParams do return none
  let vars := fvarsInOrder c
  let s ← saveState
  -- every successor: the cases of `R c e`
  let hallTy ← withLocalDeclD `e α fun e => do
    mkForallFVars #[e] (← mkArrow (mkApp2 R c e) (mkNext e))
  let hall ← mkFreshExprSyntheticOpaqueMVar hallTy
  let (fvs, g1) ← hall.mvarId!.introN 2
  -- the context the cases inherit, opened when it was introduced
  let inherited ← g1.withContext do pure (← getLCtx).getFVarIds
  let subs ← try g1.cases fvs[1]! catch _ => s.restore; return none
  -- the cases left: the rule, the goal, and whether unification instantiated a variable of `c`
  let mut left : Array (Name × MVarId × Bool) := #[]
  for sg in subs do
    let refined := vars.any fun v => !(sg.subst.get v).isFVar
    -- open the case's premises first (a rule matching a cell map states its left-hand side as
    -- `concat … = some m` premises, which `openAll` evaluates at the configuration's map); the
    -- inherited hypotheses are opened already, unless unification changed them (`cases`
    -- reintroduces those, as new variables)
    let tried ← sg.mvarId.withContext do
      pure ((← getLCtx).getFVarIds.filter inherited.contains)
    let gs ← try openAll sg.mvarId tried catch _ => pure [sg.mvarId]
    for g in gs do
      unless ← closeSpurious g do left := left.push (sg.ctorName.getD .anonymous, g, refined)
  -- a case of a later rank, when a rule of an earlier rank applies
  let mut early : Array Name := #[]
  for (n, sg, _) in left do
    if (← priorityHyp? sg).isNone then early := early.push n
  let mut out : Array (Name × MVarId × Bool) := #[]
  for (n, sg, r) in left do
    let some (h, app) ← priorityHyp? sg | out := out.push (n, sg, r); continue
    let sg ← sg.rename h `kcpri
    let mut closed := false
    for e in early do
      let ctor := app ++ Name.mkSimple e.getString!
      let some k ← ctorRank? ctor | continue
      let tac ← `(tactic| (exfalso; exact $(mkIdent `kcpri) $(Syntax.mkNumLit (toString k)) (by omega) (by apply $(mkIdent ctor) <;> ($(cfg.closer):tactic))))
      if ← closesWithin sg tac then closed := true; break
    unless closed do out := out.push (n, sg, r)
  if out.isEmpty then s.restore; return none
  -- progress: a remaining rule's matcher, else its constructor with its premises proved
  let pLam ← withLocalDeclD `e α fun e => do mkLambdaFVars #[e] (mkApp2 R c e)
  let mut hs? : Option Expr := none
  let names := out.foldl (fun acc (n, _, _) => if acc.contains n then acc else acc.push n) #[]
  for n in names do
    let s1 ← saveState
    match ← (try progressByMatcher R c n catch _ => pure none) with
    | some p => hs? := some p; break
    | none => s1.restore
  for n in names do
    if hs?.isSome then break
    let e ← mkFreshExprMVar α
    let hst ← mkFreshExprSyntheticOpaqueMVar (mkApp2 R c e)
    let s1 ← saveState
    try
      let prem ← hst.mvarId!.apply (mkAppN (mkConst n us) R.getAppArgs)
      let mut ok := true
      for p in prem do
        if ← p.isAssigned then continue
        let pt ← instantiateMVars (← p.getType)
        unless ← isProp pt do continue
        let tac ← if (← priorityApp? pt).isSome then priorityTac else pure cfg.closer
        unless ← closesWithin p tac do ok := false; break
      let pf ← instantiateMVars hst
      if ok && !pf.hasExprMVar then
        hs? := some (← mkAppOptM ``Exists.intro #[α, pLam, ← instantiateMVars e, pf])
        break
      s1.restore
    catch _ => s1.restore
  let some hs := hs? | do
    -- (after the restore, which would drop the message)
    s.restore
    logInfo m!"kc_auto: the rules {names} unify with{indentExpr c}\nbut none applies with its premises proved (a premise not proved, or the rule's result undefined); left open"
    return none
  g.assign (← mkAppM lem #[hs, hall])
  let mut res := []
  for (_, sg, _) in out do
    let pri ← sg.withContext do pure ((← getLCtx).findFromUserName? `kcpri |>.map (·.fvarId))
    res := res ++ [← normGoal (← dropStepFacts sg pri)]
  if out.any (·.2.2) then cfg.stats.modify (·.modify 4 (· + 1))
  return some res

/-- A lemma of `using […]` in the goal's context: a local hypothesis is looked up by its name. -/
def resolveLemma (l : Expr ⊕ Name) : MetaM (Option Expr) := do
  match l with
  | .inl e => return some e
  | .inr n => return ((← getLCtx).findFromUserName? n).map (·.toExpr)

mutual

/-- One configuration: target, claim, rule, or split (in this order). `kind`: 0 rule, 1 split,
2 claim. A claim application is kept only if the exploration of its continuation closes every
branch (within `fuel`); otherwise it is undone and the next option is tried. -/
partial def exploreOne (cfg : Cfg) (g : MVarId) (fuel : Nat) : TacticM Outcome := g.withContext do
  if ← tryDone cfg.closer g then return .done
  let t ← instantiateMVars (← g.getType)
  let mut aps : Array (Expr → Expr → TacticM (Option Expr)) := #[]
  if t.isAppOf ``KClaims.AFn then
    let n := t.getAppArgs[3]!
    for ihName in cfg.circs do
      let some ihDecl := (← getLCtx).findFromUserName? ihName | continue
      let ih := ihDecl.toExpr
      aps := aps.push fun c Q => do
        let ity ← whnfR (← inferType (mkApp ih n))
        let .forallE _ ltTy _ _ := ity | return none
        let some hlt ← provLt ltTy | return none
        match cfg.inv, ← invHyp? with
        | some _, some hd => return some (mkAppN ih #[n, hlt, c, Q, hd.toExpr])
        | some _, none => return none
        | none, _ => return some (mkAppN ih #[n, hlt, c, Q])
    for l in cfg.lemmas do
      aps := aps.push fun c Q => do
        let some l ← resolveLemma l | return none
        let lc ← mkAppM' l #[c, Q]
        let lc ← match cfg.inv, ← invHyp? with
          | some _, some hd => pure (mkApp lc hd.toExpr)
          | some _, none => return none
          | none, _ => pure lc
        let lty ← whnfR (← inferType lc)
        let .forallE nm instTy _ _ := lty | return none
        return some (← withLocalDeclD nm instTy fun hi => do
          mkLambdaFVars #[hi] (← mkAppM ``KClaims.AF.toAFn #[mkApp lc hi, n]))
  else
    for l in cfg.lemmas do
      aps := aps.push fun c Q => do
        let some l ← resolveLemma l | return none
        let lc ← mkAppM' l #[c, Q]
        match cfg.inv, ← invHyp? with
        | some _, some hd => return some (mkApp lc hd.toExpr)
        | some _, none => return none
        | none, _ => return some lc
  for ap in aps do
    let s ← saveState
    if let some gs ← tryClaim cfg.closer g ap (cfg.inv.map (·.2)) then
      let left ← explore cfg gs (fuel - 1)
      if left.isEmpty then
        cfg.stats.modify (·.modify 2 (· + 1))
        return .done
      s.restore
  let some g ← succIndex g | return .stuck g
  g.withContext do
  if let some g' ← tryRules cfg.rules g (cfg.inv.map (·.1)) then return .next [g'] 0
  if cfg.succ && cfg.inv.isNone then
    if let some gs ← trySucc g then return .next gs 0
    if let some gs ← tryRel cfg g then return .next gs 0
  if let some gs ← trySplit g cfg.splitVars then return .next gs 1
  if cfg.splitVars then
    if let some gs ← trySplitVar g then return .next gs 1
  if cfg.inv.isSome then
    if let some gs ← tryInvProj g then return .next gs 1
  return .stuck g

/-- The exploration loop (a work list, depth first). Returns the goals left open. -/
partial def explore (cfg : Cfg) (gs0 : List MVarId) (fuel : Nat) : TacticM (List MVarId) := do
  let mut work : List (MVarId × Nat) := gs0.map (·, fuel)
  let mut left : Array MVarId := #[]
  repeat
    match work with
    | [] => break
    | (g, f) :: rest =>
      work := rest
      if f == 0 then left := left.push g; continue
      cfg.stats.modify (·.modify 3 (· + 1))
      match ← exploreOne cfg g f with
      | .done => pure ()
      | .next gs k =>
        cfg.stats.modify (·.modify k (· + 1))
        work := gs.map (·, f - 1) ++ work
      | .stuck g' => left := left.push g'
  return left.toList

end

/-- `kc_map`: a rule's match of a map, `concat (element k v) r = some m`, proved from the map's
description. With `m` known (the left-hand side's map), the binding is one of the description's,
unified with `k` and `v`, and `r` is `remove m k` (`MapLoc.take`); with `m` to be found (the
right-hand side's map), the binding is put beside `r`, which does not bind `k`
(`MapLoc.build`). -/
elab "kc_map" : tactic => liftMetaFinishingTactic fun g => g.withContext do
  let some (_, a, b) := (← instantiateMVars (← g.getType)).eq? | throwError "kc_map: not a map match"
  let some _ := elemConcat? a | throwError "kc_map: not a map match"
  unless b.isAppOfArity ``Option.some 2 do throwError "kc_map: not a map match"
  let m ← instantiateMVars b.appArg!
  let lem := if m.isMVar then ``KClaims.MapLoc.build else ``KClaims.MapLoc.take
  let some gs ← applyOr g (← mkConstWithFreshMVarLevels lem) | throwError "kc_map: {lem} does not apply"
  for g' in gs do
    if ← g'.isAssigned then continue
    let ty ← instantiateMVars (← g'.getType)
    let ok ← if ty.isAppOf ``KPrelude.MapHook.WF then proveWF g'
      else if lem == ``KClaims.MapLoc.build then proveLookupNone g' else proveLookup g'
    unless ok do throwError "kc_map: no binding of the description fits{indentExpr ty}"

/-- The default closing tactic for target, map, arithmetic and `ensures` goals (its rules below,
after the closers it tries). -/
syntax "kc_close" : tactic

/-- The description `concat A B = some m` of a map `m` in the context that does not mention `m`
on its left (a rule's match `concat (element k v) (remove m k) = some m` does, and rewriting
`m`'s lookups with it would not end). -/
def mapDescNR? (m : Expr) : MetaM (Option LocalDecl) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    unless a.isAppOf ``KPrelude.MapHook.concat && b.isAppOfArity ``Option.some 2 do continue
    unless (← instantiateMVars b.appArg!) == m do continue
    let a ← instantiateMVars a
    if (a.find? (· == m)).isSome then continue
    return some d
  return none

/-- What `kc_map_ext` reads off the maps of its equation (`mapParts`). -/
structure MapParts where
  /-- the descriptions used -/
  ds : Array LocalDecl := #[]
  /-- the keys named, one term per key -/
  ks : Array Expr := #[]
  /-- the maps neither built nor described (frames) -/
  fs : Array Expr := #[]
  /-- equations by `rfl` that put a term in the form the others use: a literal of one binding as
  `element` (`kc_norm` evaluates `element k v` to the carrier's literal), a key as the term that
  names it elsewhere (`inj_Int x` and the `Term.inj …` a literal holds) -/
  eqs : Array Expr := #[]

/-- A term equal to `e` by unfolding, as a proof of `e = e'` that the kernel checks by `rfl`. -/
def rflEq (e e' : Expr) : MetaM Expr := do mkExpectedTypeHint (← mkEqRefl e') (← mkEq e e')

/-- `k` as a key of `st`: a key it names already (syntactically, or by unfolding, with the
equation), or a new one; and the term that names it. -/
def MapParts.addKey' (st : MapParts) (k : Expr) : MetaM (MapParts × Expr) := do
  if st.ks.contains k then return (st, k)
  for κ in st.ks do
    let s ← saveState
    if ← isDefEq κ k then return ({ st with eqs := st.eqs.push (← rflEq k κ) }, κ)
    s.restore
  return ({ st with ks := st.ks.push k }, k)

def MapParts.addKey (st : MapParts) (k : Expr) : MetaM MapParts := return (← st.addKey' k).1

/-- The maps and keys a map term is built from: through `element`, `remove`, `update` and the
descriptions of the maps it names, a literal of one binding read as `element`. `tys` are the
map, key and value types. -/
partial def mapParts (tys : Array Expr) (e : Expr) (st : MapParts) : MetaM MapParts := do
  let e ← instantiateMVars e
  if e.isAppOf ``KPrelude.MapHook.element then
    return ← st.addKey (e.getArg! (e.getAppNumArgs - 2))
  if e.isAppOf ``KPrelude.MapHook.remove then
    return ← mapParts tys (e.getArg! (e.getAppNumArgs - 2)) (← st.addKey e.appArg!)
  if e.isAppOf ``KPrelude.MapHook.update then
    return ← mapParts tys (e.getArg! (e.getAppNumArgs - 3)) (← st.addKey (e.getArg! (e.getAppNumArgs - 2)))
  if e.isAppOf ``KPrelude.MapHook.unit then return st
  unless e.isFVar do
    -- a literal of one binding (with its key in the form the other maps use)
    let s ← saveState
    try
      let n ← forallTelescope (← getConstInfo ``KPrelude.MapHook.element).type fun xs _ => pure xs.size
      let k₀ ← mkFreshExprMVar tys[1]!
      let v₀ ← mkFreshExprMVar tys[2]!
      let el ← mkAppOptM ``KPrelude.MapHook.element
        (#[some tys[0]!, some tys[1]!, some tys[2]!] ++ Array.replicate (n - 5) none ++ #[some k₀, some v₀])
      if ← isDefEq e el then
        let (st, k') ← st.addKey' (← instantiateMVars k₀)
        let el ← mkAppOptM ``KPrelude.MapHook.element
          (#[some tys[0]!, some tys[1]!, some tys[2]!] ++ Array.replicate (n - 5) none
            ++ #[some k', some (← instantiateMVars v₀)])
        return { st with eqs := st.eqs.push (← rflEq e el) }
    catch _ => pure ()
    s.restore
    return st
  if st.ds.any (fun d => d.type.appArg!.appArg! == e) || st.fs.contains e then return st
  let some d ← mapDescNR? e | return { st with fs := st.fs.push e }
  let d := d.setType (← instantiateMVars d.type)
  let some (_, a, _) := d.type.eq? | return st
  let st ← mapParts tys (a.getArg! (a.getAppNumArgs - 2)) { st with ds := st.ds.push d }
  mapParts tys a.appArg! st

/-- `kc_map_ext`: `concat A B = some m` where `m`, `A` and `B` are known by their bindings (built
by `element`, `remove` and `update` from maps a description gives): `A` and `B` bind no key in
common and `m` binds theirs (`MapLoc.concat_of_lookup`), at every key `k`. The keys the three maps
name are finitely many, so `k` is one of them or none: at each, every lookup is evaluated by the
descriptions (`lookup_concat`), the key disequalities (`proveKeyNe`) and the absence of a key from
a frame (`proveLookupNone`); at none, each lookup is that of a frame at `k`. A value left to compare
goes to `kc_close`. Where `B` is still to be chosen (the frame of a claim applied at a map), it is
what `m` binds besides `A`'s keys: `m` with them removed. -/
elab "kc_map_ext" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq? | throwError "kc_map_ext: not a map equation"
  unless lhs.isAppOf ``KPrelude.MapHook.concat && rhs.isAppOfArity ``Option.some 2 do
    throwError "kc_map_ext: not a map equation"
  let a ← instantiateMVars (lhs.getArg! (lhs.getAppNumArgs - 2))
  let b ← instantiateMVars lhs.appArg!
  let m ← instantiateMVars rhs.appArg!
  if a.hasExprMVar || m.hasExprMVar then throwError "kc_map_ext: metavariables"
  let tys := lhs.getAppArgs[:3].toArray
  -- the frame to be chosen: `m` without `A`'s keys
  if b.hasExprMVar then
    unless b.isMVar do throwError "kc_map_ext: metavariables"
    let mut r := m
    for k in (← mapParts tys a {}).ks do r ← mkAppM ``KPrelude.MapHook.remove #[r, k]
    unless ← isDefEq b r do
      unless ← isDefEq (← inferType b) (← inferType r) do throwError "kc_map_ext: frame"
      b.mvarId!.assign r
  let b ← instantiateMVars b
  let parts ← mapParts tys m (← mapParts tys b (← mapParts tys a {}))
  let (ds, ks, fs) := (parts.ds, parts.ks, parts.fs)
  -- the facts: key disequalities, a frame's absence at a key, the maps' well-formedness
  let mut facts : Array Expr := #[]
  for i in ks do
    for j in ks do
      if i == j then continue
      let neTy ← mkAppM ``Ne #[i, j]
      let ne ← mkFreshExprMVar neTy
      -- with its stated type: `simp` reads `i ≠ j` as `(i = j) = False`, but the `i = j → False`
      -- a proof term's own type shows as a rule with a premise
      if ← proveKeyNe ne.mvarId! lookupFuel then
        facts := facts.push (← mkExpectedTypeHint (← instantiateMVars ne) neTy)
  for f in fs do
    for k in ks do
      let lk ← mkAppM ``KPrelude.MapHook.lookup #[f, k]
      let .app _ vty ← whnfR (← inferType lk) | continue
      let hTy ← mkEq lk (← mkAppOptM ``Option.none #[vty])
      let h ← mkFreshExprMVar hTy
      if ← proveLookupNone h.mvarId! then facts := facts.push (← mkExpectedTypeHint (← instantiateMVars h) hTy)
  -- the maps' well-formedness: a described map's from its description, a frame's hypothesis
  let mut wfs : Array Expr ← ds.mapM fun d => mkAppM ``KClaims.MapLoc.wf_of_concat #[d.toExpr]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``KPrelude.MapHook.WF && fs.contains ty.appArg! then wfs := wfs.push d.toExpr
  let some gs ← applyOr g (← mkConstWithFreshMVarLevels ``KClaims.MapLoc.concat_of_lookup)
    | throwError "kc_map_ext: concat_of_lookup does not apply"
  let mut pointwise := #[]
  for g' in gs do
    if ← g'.isAssigned then continue
    let ty ← instantiateMVars (← g'.getType)
    if ty.isAppOf ``KPrelude.MapHook.WF then
      unless ← proveWF g' do throwError "kc_map_ext: not well formed{indentExpr ty}"
    else pointwise := pointwise.push g'
  let descs ← ds.mapM fun d => mkAppM ``KPrelude.MapHook.lookup_concat #[d.toExpr]
  let kv := mkIdent `kck
  -- the leaf: every lookup evaluated, then the values compared (the terms elaborated in the
  -- leaf's context, which `intro` and `subst` changed)
  let leaf (hs : Array Ident) : TacticM Unit := do (← getMainGoal).withContext do
    let simpArgs ← (parts.eqs ++ descs ++ facts ++ wfs).mapM fun e => do
      let s ← Term.exprToSyntax e
      `(Lean.Parser.Tactic.simpLemma| $s:term)
    let hsArgs ← hs.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
    evalTactic (← `(tactic| (simp only [$(simpArgs ++ hsArgs),*, KClaims.MapLoc.lookup_self,
        KPrelude.MapHook.lookup_element_ne, KPrelude.MapHook.lookup_remove_self,
        KPrelude.MapHook.lookup_remove_ne, KClaims.MapLoc.lookup_update_same,
        KPrelude.MapHook.lookup_update_ne, KClaims.MapLoc.lookup_unit, KPrelude.MapHook.wf_update,
        KPrelude.MapHook.wf_remove, KPrelude.MapHook.wf_element, Option.some_or, Option.none_or,
        ne_eq, not_false_eq_true, eq_self_iff_true, true_or, or_true]
      <;> first | done | rfl | kc_close)))
  for g' in pointwise do
    setGoals [g']
    evalTactic (← `(tactic| intro $kv:ident))
    let mut open_ : Array MVarId := #[]
    let mut hs : Array Ident := #[]
    -- one goal per key, and one for none of them
    for k in ks do
      let hk := mkIdent (Name.mkSimple s!"hkck{hs.size}")
      let k ← (← getMainGoal).withContext (Term.exprToSyntax k)
      evalTactic (← `(tactic| by_cases $hk:ident : $kv:ident = $k))
      let pos :: neg :: _ ← getGoals | throwError "kc_map_ext: by_cases"
      setGoals [pos]
      evalTactic (← `(tactic| subst $kv:ident))
      leaf hs
      open_ := open_ ++ (← getUnsolvedGoals)
      setGoals [neg]
      hs := hs.push hk
    leaf hs
    open_ := open_ ++ (← getUnsolvedGoals)
    unless open_.isEmpty do throwError "kc_map_ext: a key's binding differs"
  setGoals []

/-- `kc_assumption`: a hypothesis that is the goal (a map pattern of the target over a frame,
which the rule's match or the claim left as a hypothesis), for a goal without metavariables, or
`f args = some ?x` with `args` known: a partial function has one value, so the hypothesis gives
the only `?x`. Other goals with metavariables are left to the tactics that choose their values. -/
elab "kc_assumption" : tactic => liftMetaFinishingTactic fun g => g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (_, a, b) := t.eq? | throwError "kc_assumption: not an equation"
  if t.hasExprMVar then
    unless !a.hasExprMVar && b.isAppOfArity ``Option.some 2 && b.appArg!.isMVar do
      throwError "kc_assumption: metavariables"
  -- only a hypothesis with the same left-hand side (syntactically): unifying the goal with every
  -- hypothesis costs more than the rest of a step where the configuration is large
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, a', b') := (← instantiateMVars d.type).eq? | continue
    unless (← instantiateMVars a') == a do continue
    if ← isDefEq b b' then
      g.assign d.toExpr
      return
  throwError "kc_assumption: no hypothesis"

/-- `kc_index_split`: close the goal by cases on a table's index, a remainder `e % c` by a literal
`c` of at most 64 (a field of bits, `x / 8 % 8`), into its `c` values, each case closed by
evaluation (`simp_all`), splitting another index where one remains: two tables compared at a
symbolic index agree where they agree at each of its values. The remainders are first written as
`%` and `/` (`tmod`/`tdiv` of nonnegative values, shifts by literals). Fails, with nothing
changed, unless every case closes. -/
partial def indexSplit (fuel : Nat) : TacticM Unit := do
  let s ← saveState
  try
    evalTactic (← `(tactic| (simp_all [kc_simp]; done)))
    return
  catch _ => s.restore
  if fuel == 0 then throwError "kc_index_split: no case split closes the goal"
  let g ← getMainGoal
  let some (t, c) ← g.withContext do
      -- the remainders by a small literal, at `Int` (or a sort abbreviation of it)
      let cands ← IO.mkRef (#[] : Array Expr)
      for e in #[← g.getType] ++ (← getLCtx).decls.toArray.filterMap (fun d? => d?.bind fun d =>
          if d.isImplementationDetail then none else some d.type) do
        (← instantiateMVars e).forEach fun x => do
          if x.isAppOfArity ``HMod.hMod 6 && !x.hasLooseBVars
              && (x.getArg! 5).int?.any (fun c => 2 ≤ c && c ≤ 64) && (x.getArg! 4).int?.isNone then
            cands.modify (·.push x)
      for x in ← cands.get do
        if (← whnfR (x.getArg! 0)).isConstOf ``Int then
          return some (x, ((x.getArg! 5).int?.getD 0).toNat)
      return none
    | throwError "kc_index_split: no index"
  let ts ← g.withContext <| Term.exprToSyntax t
  let hk := mkIdent `hidx
  for k in [0:c] do
    let ks := Syntax.mkNumLit (toString k)
    evalTactic (← `(tactic| by_cases $hk:ident : $ts = $ks))
    let pos :: neg :: _ ← getGoals | throwError "kc_index_split: by_cases"
    setGoals [pos]
    evalTactic (← `(tactic| simp only [$hk:ident] at *))
    indexSplit (fuel - 1)
    setGoals [neg]
  evalTactic (← `(tactic| k2l_int_omega))

elab "kc_index_split" : tactic => do
  let s ← saveState
  try
    evalTactic (← `(tactic| try simp (disch := k2l_int_omega) only [Int.tdiv_eq_ediv_of_nonneg,
      Int.tmod_eq_emod_of_nonneg, Int.shiftRight_eq_div_pow, Int.reduceToNat, Int.reducePow,
      Nat.reducePow, Int.reduceNatCast, Nat.ToInt.natCast_ofNat, Int.cast_ofNat_Int, Int.ediv_one] at *))
    indexSplit 3
  catch e => s.restore; throw e

-- the rules of `kc_close`
macro_rules | `(tactic| kc_close) => `(tactic| first
  | kc_assumption
  | kc_map
  | kc_map_ext
  | rfl
  | decide
  | (kc_norm; simp only [kc_simp, Option.some.injEq, reduceCtorEq] at *; done)
  | (kc_norm; simp [kc_simp] at * <;> omega)
  | (kc_norm; simp_all [kc_simp]; done)
  | (kc_norm; simp [kc_simp] at *; grind [Int.tdiv_eq_ediv_of_nonneg, Int.mul_nonneg])
  | (kc_norm; kc_index_split))

syntax kcCircs := &" circ " "[" ident,* "]"
syntax kcLemmas := " using " "[" term,* "]"
syntax kcInv := &" inv " "[" term "]"
syntax kcSplit := " split"
syntax kcClose := &" close " "(" tactic ")"
syntax kcFuel := &" fuel " num

/-- `kc_auto [circ [ih]] [using [lemma, …]] [inv [hP]] [split] [close (tac)] [fuel n]`, on a goal
`AF R Q c`, `AFn R Q n c` or `Reach R Q c`.

- `circ [ih]`: circularities of an `AFn` goal (`AF.circularity_inst`), usable after a step;
- `using [l]`: proved claims `l : ∀ c Q, Inst c Q → AF R Q c` (with `inv`, `∀ c Q, P c → Inst c Q →
  AF R (P ∧ Q) c`), or, on a `Reach` goal, `∀ c Q, Inst c Q → Reach R Q c` (such as induction
  hypotheses, usable anywhere since `Reach` is inductive);
- `inv [hP]` with `hP : Preserved R P`: the claims are under the invariant `P`. The goal's target
  is `fun d => P d ∧ Q d` and the hypothesis `hinv : P c` is carried along every step
  (`AFn.of_rule_inv`), through Boolean splits and claim applications; when no rule applies the
  invariant is opened (`kc_inv`) to split on what it says about the configuration's variables;
- `split`: when no rule applies, split a variable of the configuration whose type has few
  constructors (`splittable`). -/
elab "kc_auto" c:(kcCircs)? l:(kcLemmas)? v:(kcInv)? sp:(kcSplit)? cl:(kcClose)? f:(kcFuel)? : tactic => do
  let closer ← match cl with
    | some stx => match stx with
      | `(kcClose| close ($t)) => pure t
      | _ => `(tactic| kc_close)
    | none => `(tactic| kc_close)
  -- the invariant conjunct of a target is `hinv` itself
  let closer ← if v.isSome then `(tactic| first | assumption | ($closer:tactic)) else pure closer
  let fuel := match f with
    | some stx => match stx with
      | `(kcFuel| fuel $n) => n.getNat
      | _ => 3000
    | none => 3000
  let g ← getMainGoal
  let (rules, circs, lemmas, succ) ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let R := t.getAppArgs[1]!
    -- a relation that is not a function has no `RuleSet` (its `det`), only `ExecSucc`
    let rules ← try getRules R catch _ => pure #[]
    let circs ← match c with
      | some stx => match stx with
        | `(kcCircs| circ [$ids,*]) => pure (ids.getElems.map (·.getId))
        | _ => pure #[]
      | none => pure #[]
    let lemmas ← match l with
      | some stx => match stx with
        | `(kcLemmas| using [$ts,*]) => ts.getElems.mapM fun t => do
          let e ← Term.elabTerm t none |>.run'
          if e.isFVar then return Sum.inr (← e.fvarId!.getUserName) else return Sum.inl e
        | _ => pure #[]
      | none => pure #[]
    -- only without a `RuleSet`: a deterministic relation keeps its one-rule steps and splits
    let succ := rules.isEmpty && (← getSucc? R).isSome
    return (rules, circs, lemmas, succ)
  let inv ← match v with
    | some stx => match stx with
      | `(kcInv| inv [$t]) => g.withContext do
        let hP ← Term.elabTerm t none |>.run'
        let hP ← instantiateMVars hP
        match (← instantiateMVars (← inferType hP)).getAppFnArgs with
        | (``KPrelude.Preserved, #[_, _, P]) => pure (some (hP, P))
        | _ => throwError "kc_auto: inv expects a proof of `Preserved R P`"
      | _ => pure none
    | none => pure none
  let stats ← IO.mkRef #[0, 0, 0, 0, 0]
  let cfg : Cfg := { closer, rules, circs, lemmas, fuel, stats, inv, splitVars := sp.isSome, succ }
  let rest ← explore cfg [g] cfg.fuel
  if kc.stats.get (← getOptions) then
    let st ← stats.get
    let decl := (← Term.getDeclName?).map toString |>.getD "?"
    -- frame refinements only when there are some, so that existing counts read as before
    let fr := if st[4]! > 0 then m!", {st[4]!} frame refinements" else m!""
    logInfo m!"kc_auto {decl}: {st[3]!} configurations, {st[0]!} rule steps, {st[1]!} splits, {st[2]!} claim applications, {rest.length} open{fr}"
  setGoals rest

end KClaims.Tactic

namespace KClaims.Tactic

open Lean Meta Elab Tactic

/-- `kc_refute h` with `h : AF R P c`, `c` closed and the goal `False`: follow the executable
step (`ExecDet`) from `c`; at each configuration prove `¬ P` (by opening a hypothesis `P c`
until a constructor clash or a false condition), and at the configuration without a successor
derive `P` from `h`. -/
elab "kc_refute " h:ident fu:(num)? : tactic => do
  let maxSteps := fu.map (·.getNat) |>.getD 5000
  let mut g ← getMainGoal
  let mut hv := (← g.withContext do return (← getLocalDeclFromUserName h.getId).toExpr)
  for _ in [:maxSteps] do
    let next? ← g.withContext do
      let ht ← instantiateMVars (← inferType hv)
      let (``KClaims.AF, #[α, R, P, c]) := ht.getAppFnArgs | throwError "kc_refute: AF hypothesis expected"
      let stepM ← mkFreshExprMVar (← mkArrow α (mkApp (mkConst ``KPrelude.Outcome) α))
      let inst ← synthInstance (mkAppN (mkConst ``KClaims.ExecDet) #[α, R, stepM])
      let stepF ← instantiateMVars stepM
      -- ¬ P c
      let notPTy := mkNot (P.beta #[c]).headBeta
      let np ← mkFreshExprSyntheticOpaqueMVar notPTy
      let (hp, g1) ← np.mvarId!.intro1
      let rest ← openAll g1
      for r in rest do
        setGoals [r]
        try evalTactic (← `(tactic| first | omega | (simp_all [kc_simp]; done) | decide))
        catch _ => throwError "kc_refute: could not show that the target does not hold at{indentExpr c}"
      let _ := hp
      let out ← whnfD (mkApp stepF c)
      if out.isAppOfArity ``KPrelude.Outcome.next 2 then
        let c' ← norm out.appArg!
        let hs ← mkExpectedTypeHint (← mkEqRefl (mkApp2 (mkConst ``KPrelude.Outcome.next) α c'))
          (← mkEq (mkApp stepF c) (mkApp2 (mkConst ``KPrelude.Outcome.next) α c'))
        let h' := mkAppN (mkConst ``KClaims.AF.next_inv) #[α, R, stepF, inst, P, c, c', hv, np, hs]
        return some h'
      else
        -- no successor: `step c` is `stuck` or `undefined`
        let noNext ← mkFreshExprSyntheticOpaqueMVar
          (← withLocalDeclD `c' α fun c' => do
            mkForallFVars #[c'] (mkNot (← mkEq (mkApp stepF c) (mkApp2 (mkConst ``KPrelude.Outcome.next) α c'))))
        setGoals [noNext.mvarId!]
        evalTactic (← `(tactic| (intro _ e; cases e)))
        let iff := mkAppN (mkConst ``KClaims.AF.of_no_next) #[α, R, stepF, inst, P, c, noNext]
        let pc ← mkAppM ``Iff.mp #[iff, hv]
        g.assign (mkApp np pc)
        return none
    match next? with
    | some h' => hv := h'
    | none => setGoals []; return
  throwError "kc_refute: out of fuel"

end KClaims.Tactic

/-! ## Replay: one named step at a time

A script produced from a prover's trace names each step; each tactic fails unless its step
applies, so elaborating the script checks the trace. -/

namespace KClaims.Tactic

open Lean Meta Elab Tactic

/-- `kc_rule r`: take the step of rule matcher `r` (a `KPrelude.Rule`). -/
elab "kc_rule " r:term : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  let some g ← succIndex g | throwError "kc_rule: not an AF/AFn goal"
  let re ← g.withContext do Term.elabTerm r none |>.run'
  match ← tryRules #[re] g with
  | some g' => setGoals (g' :: others)
  | none => throwError "kc_rule: rule {r} does not apply"

/-- `kc_split`: case split on the first non-literal Boolean of the configuration. -/
elab "kc_split" : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  match ← trySplit g with
  | some gs => setGoals (gs ++ others)
  | none => throwError "kc_split: no Boolean to split on"

/-- `kc_done`: the configuration satisfies the target. -/
elab "kc_done" : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  unless ← tryDone (← `(tactic| kc_close)) g do throwError "kc_done: target not reached"
  setGoals others

/-- `kc_claim ih`: apply the circularity `ih` here (the index must have decreased). -/
elab "kc_claim " ih:ident : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  let gs? ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let n := t.getAppArgs[3]!
    let ihE := (← getLocalDeclFromUserName ih.getId).toExpr
    let ap : Expr → Expr → TacticM (Option Expr) := fun c Q => do
      let ity ← whnfR (← inferType (mkApp ihE n))
      let .forallE _ ltTy _ _ := ity | return none
      let some hlt ← provLt ltTy | return none
      return some (mkAppN ihE #[n, hlt, c, Q])
    tryClaim (← `(tactic| kc_close)) g ap
  match gs? with
  | some gs => setGoals (gs ++ others)
  | none => throwError "kc_claim: {ih} does not apply"

end KClaims.Tactic

namespace KClaims.Tactic

open Lean Elab Command

/-- `kc_det_instances`, in a claims module with the semantics' namespace open: the `RuleSet` and
`ExecDet` instances of a deterministic semantics (one whose library states `Step.deterministic`
and has the unranked rule list `rules`), with which `kc_auto` steps by one rule at a time. A
semantics without them is explored by its `ExecSucc` instance (`successors_iff`). -/
elab "kc_det_instances" : command => do
  let has (n : Name) : CommandElabM Bool := liftTermElabM do
    try
      let _ ← realizeGlobalConstNoOverloadWithInfo (mkIdent n)
      pure true
    catch _ => pure false
  if (← has `Step.deterministic) && (← has `rules) && (← has `step_complete) then
    elabCommand (← `(instance : KClaims.RuleSet $(mkIdent `App) $(mkIdent `Step) :=
      ⟨$(mkIdent `rules), $(mkIdent `Step.deterministic)⟩))
    elabCommand (← `(instance : KClaims.ExecDet $(mkIdent `Step) $(mkIdent `step) :=
      ⟨$(mkIdent `step_sound), $(mkIdent `step_complete)⟩))

end KClaims.Tactic

namespace KClaims.Tactic

open Lean Elab Command

/-- `kc_simp_attr f g …`: each name in the `kc_simp` set, as `attribute [kc_simp] f g …` does, except
that a name whose registration fails is left out with a warning rather than failing the module.
Registering a definition produces its equation lemmas, under the heartbeats of the module that
defines it; on a large definition a few of them do not fit (KEVM: 2 of 1,487), and the claims
then do not unfold that definition by `simp`, which costs proofs, not correctness. -/
elab "kc_simp_attr " ids:ident* : command => do
  for id in ids do
    let n := id.getId
    let r ← liftCoreM do
      Core.tryCatchRuntimeEx
        (do
          let attr ← ofExcept <| getAttributeImpl (← getEnv) `kc_simp
          attr.add n (← `(Parser.Attr.simple| kc_simp)) AttributeKind.global
          pure none)
        (fun e => do pure (some (← e.toMessageData.toString)))
    if let some msg := r then logWarning m!"kc_simp: {n} left out ({msg})"

end KClaims.Tactic
