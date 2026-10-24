import Lean
import KClaims.RuleStep
import KClaims.Exec
import KClaims.SimpAttr
import KPrelude.Hooks
import KPrelude.Coll

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
3. **rule**: some rule matcher returns a successor — continue there (`AFn.of_rule`);
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
  | _ => none

def normGoal (g : MVarId) : MetaM MVarId := g.withContext do
  let t ← instantiateMVars (← g.getType)
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

def tryRules (rules : Array Expr) (g : MVarId) : MetaM (Option MVarId) := g.withContext do
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
      let k ← mkFreshExprSyntheticOpaqueMVar (mk c'')
      let rhs'' ← mkAppM ``Option.some #[c'']
      let h ← mkExpectedTypeHint (← mkEqRefl rhs'') (← mkEq lhs rhs'')
      let lem := if t.isAppOf ``KClaims.AFn then ``KClaims.AFn.of_rule else ``KClaims.AF.of_rule
      let pf ← mkAppM lem #[r, h, k]
      g.assign pf
      return some k.mvarId!
    s.restore
  return none

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

/-- Assign metavariables by matching constructor structure; leaves are left for the closing
tactic. `false` when the two sides cannot be made equal by arithmetic at the leaves: different
constructors, or a non-leaf position where a side is neither a constructor application nor a
metavariable (a variable of the claim against a constructor, say). -/
partial def structUnify (a b : Expr) : MetaM Bool := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  if a.getAppFn.isMVar || b.getAppFn.isMVar then
    return (← isDefEq a b)
  if ← isDefEq a b then return true
  if ← isLeafType (← inferType a) then return true
  let a' ← whnfD a
  let b' ← whnfD b
  match a'.getAppFn, b'.getAppFn with
  | .const na _, .const nb _ =>
    match (← getEnv).find? na, (← getEnv).find? nb with
    | some (.ctorInfo ci), some (.ctorInfo _) =>
      if na != nb then return false
      let xs := a'.getAppArgs
      let ys := b'.getAppArgs
      if xs.size != ys.size then return false
      for i in [ci.numParams:xs.size] do
        unless ← structUnify xs[i]! ys[i]! do return false
      return true
    | _, _ => return false
  | _, _ => return false

/-- Close goals `gs` with `closer`, in order; `false` (and nothing assigned) if one fails. -/
def closeAll (closer : TSyntax `tactic) (gs : Array MVarId) : TacticM Bool := do
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.hasExprMVar then return false
    setGoals [g]
    try
      evalTactic closer
      unless (← getUnsolvedGoals).isEmpty do return false
    catch _ => return false
  return true

/-- Solve an existential/conjunctive goal (a target, or a claim instance): unify equations
first, then close what remains. -/
def solveConj (closer : TSyntax `tactic) (g : MVarId) : TacticM Bool := do
  let s ← saveState
  let ok ← g.withContext do
    let (ws, gs) ← peel g #[] #[]
    let mut rest := #[]
    for gi in gs do
      let t ← instantiateMVars (← gi.getType)
      match t.eq? with
      | some (_, a, b) =>
        if ← isDefEq a b then
          gi.assign (← mkEqRefl a)
        else
          unless ← structUnify a b do return false
          rest := rest.push gi
      | none => rest := rest.push gi
    for w in ws do
      if (← instantiateMVars w).hasExprMVar then return false
    closeAll closer rest
  unless ok do s.restore
  return ok

/-- Target: `P c`. -/
def tryDone (closer : TSyntax `tactic) (g : MVarId) : TacticM Bool := do
  let s ← saveState
  let t ← instantiateMVars (← g.getType)
  let lem ← match t.getAppFn with
    | .const ``KClaims.AF _ => pure ``KClaims.AF.here
    | .const ``KClaims.AFn _ => pure ``KClaims.AFn.here
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

/-- One opening step on some hypothesis of `g`: `∃` and `∧` are destructured, an equation with
a variable side is substituted, an equation `f … = some x` is evaluated by `cases`, a Boolean
condition is simplified to a proposition. `none` if no hypothesis needs it. -/
def openStep (g : MVarId) (tried : Array FVarId) : TacticM (Option (List MVarId × Array FVarId)) :=
  g.withContext do
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail || tried.contains ldecl.fvarId then continue
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
      return some ([g], tried.push ldecl.fvarId)
    | _ => continue
  return none

/-- Open every hypothesis of `g` (see `openStep`). -/
partial def openAll (g : MVarId) (tried : Array FVarId := #[]) (fuel : Nat := 200) :
    TacticM (List MVarId) := do
  if fuel == 0 then return [g]
  match ← openStep g tried with
  | none => return [g]
  | some (gs, tried) => return (← gs.mapM fun g => openAll g tried (fuel - 1)).flatten

/-- Split single-constructor variables (cells) so that matchers on them reduce. -/
def splitCells (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← whnfR ldecl.type
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

/-- Split on the first non-literal Boolean of the configuration. -/
def trySplit (g : MVarId) : TacticM (Option (List MVarId)) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (c, _) := configOf t | return none
  let some b ← findBool c | return none
  setGoals [g]
  if b.isFVar then
    let subs ← g.cases b.fvarId!
    return some (← subs.toList.mapM fun s => (normGoal s.mvarId : MetaM MVarId))
  let bs ← Term.exprToSyntax b
  try
    evalTactic (← `(tactic| (generalize $(mkIdent `hkc) : $bs = $(mkIdent `bkc):ident; cases $(mkIdent `bkc):ident <;> (try kc_bool_simp at $(mkIdent `hkc):ident))))
    let gs ← getUnsolvedGoals
    return some (← gs.mapM fun g => (normGoal g : MetaM MVarId))
  catch _ => return none

/-- Apply a claim (a circularity with its index bound, or a proved claim) at the goal's
configuration; continue from its post-condition. `ap c Q : Inst c Q → AFn R Q n c`. -/
def tryClaim (closer : TSyntax `tactic) (g : MVarId) (ap : Expr → Expr → TacticM (Option Expr)) :
    TacticM (Option (List MVarId)) := do
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
    let P := t.getAppArgs[2]!
    let contTy ← withLocalDeclD `d α fun d => do
      let body ← mkArrow (Qi.beta #[d]).headBeta (configOf t |>.get!.2 d)
      mkForallFVars #[d] body
    let cont ← mkFreshExprSyntheticOpaqueMVar contTy
    let lem := if t.isAppOf ``KClaims.AFn then ``KClaims.AFn.trans else ``KClaims.AF.trans
    g.assign (← mkAppM lem #[hQ, cont])
    let _ := P
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
  lemmas : Array Expr
  fuel : Nat
  /-- rule steps, splits, kept claim applications, configurations -/
  stats : IO.Ref (Array Nat)

inductive Outcome where
  | done
  | next (gs : List MVarId) (kind : Nat)
  /-- No step applies; `g` is the goal to leave open (after the index split, a new goal). -/
  | stuck (g : MVarId)

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
        return some (mkAppN ih #[n, hlt, c, Q])
    for l in cfg.lemmas do
      aps := aps.push fun c Q => do
        let lc ← mkAppM' l #[c, Q]
        let lty ← whnfR (← inferType lc)
        let .forallE nm instTy _ _ := lty | return none
        return some (← withLocalDeclD nm instTy fun hi => do
          mkLambdaFVars #[hi] (← mkAppM ``KClaims.AF.toAFn #[mkApp lc hi, n]))
  else
    for l in cfg.lemmas do
      aps := aps.push fun c Q => do return some (← mkAppM' l #[c, Q])
  for ap in aps do
    let s ← saveState
    if let some gs ← tryClaim cfg.closer g ap then
      let left ← explore cfg gs (fuel - 1)
      if left.isEmpty then
        cfg.stats.modify (·.modify 2 (· + 1))
        return .done
      s.restore
  let some g ← succIndex g | return .stuck g
  g.withContext do
  if let some g' ← tryRules cfg.rules g then return .next [g'] 0
  if let some gs ← trySplit g then return .next gs 1
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

/-- The default closing tactic for target, map, arithmetic and `ensures` goals. -/
macro "kc_close" : tactic => `(tactic| first
  | rfl
  | decide
  | (kc_norm; simp only [kc_simp, Option.some.injEq, reduceCtorEq] at *; done)
  | (kc_norm; simp [kc_simp] at * <;> omega)
  | (kc_norm; simp_all [kc_simp]; done)
  | (kc_norm; simp [kc_simp] at *; grind [Int.tdiv_eq_ediv_of_nonneg, Int.mul_nonneg]))

syntax kcCircs := " circ " "[" ident,* "]"
syntax kcLemmas := " using " "[" term,* "]"
syntax kcClose := " close " "(" tactic ")"
syntax kcFuel := " fuel " num

/-- `kc_auto [circ [ih]] [using [lemma, …]] [close (tac)] [fuel n]`. -/
elab "kc_auto" c:(kcCircs)? l:(kcLemmas)? cl:(kcClose)? f:(kcFuel)? : tactic => do
  let closer ← match cl with
    | some stx => match stx with
      | `(kcClose| close ($t)) => pure t
      | _ => `(tactic| kc_close)
    | none => `(tactic| kc_close)
  let fuel := match f with
    | some stx => match stx with
      | `(kcFuel| fuel $n) => n.getNat
      | _ => 3000
    | none => 3000
  let g ← getMainGoal
  let (rules, circs, lemmas) ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let R := t.getAppArgs[1]!
    let rules ← getRules R
    let circs ← match c with
      | some stx => match stx with
        | `(kcCircs| circ [$ids,*]) => pure (ids.getElems.map (·.getId))
        | _ => pure #[]
      | none => pure #[]
    let lemmas ← match l with
      | some stx => match stx with
        | `(kcLemmas| using [$ts,*]) => ts.getElems.mapM fun t => Term.elabTerm t none |>.run'
        | _ => pure #[]
      | none => pure #[]
    return (rules, circs, lemmas)
  let stats ← IO.mkRef #[0, 0, 0, 0]
  let cfg : Cfg := { closer, rules, circs, lemmas, fuel, stats }
  let rest ← explore cfg [g] cfg.fuel
  if kc.stats.get (← getOptions) then
    let st ← stats.get
    let decl := (← Term.getDeclName?).map toString |>.getD "?"
    logInfo m!"kc_auto {decl}: {st[3]!} configurations, {st[0]!} rule steps, {st[1]!} splits, {st[2]!} claim applications, {rest.length} open"
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
