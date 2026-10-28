import Lean
import KPrelude.Coll
import KPrelude.Ext
import KPrelude.HookLaws
import KPrelude.FamilyCases

/-!
# Tactics used by generated proofs

`k2l_map_facts` replaces every hypothesis `MapHook.concat (MapHook.element k v) r = some m`
(the reading of a map pattern `k |-> v r`) by the two facts that determine `v` and `r` from
`m` and `k`: `MapHook.lookup m k = some v` and `MapHook.remove m k = r`. After it, `simp_all`
can identify the witnesses of two matches of the same pattern, which is what determinism
proofs need.
-/

namespace KPrelude

open Lean Meta Elab Tactic

elab "k2l_map_facts" : tactic => withMainContext do
  let mut facts : Array Expr := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let some (_, lhs, _) := ty.eq? | continue
    unless lhs.isAppOf ``KPrelude.MapHook.concat do continue
    let args := lhs.getAppArgs
    let some first := args[args.size - 2]? | continue
    unless first.isAppOf ``KPrelude.MapHook.element do continue
    try
      facts := facts.push (← mkAppM ``KPrelude.MapHook.lookup_of_concat_element #[ldecl.toExpr])
      facts := facts.push (← mkAppM ``KPrelude.MapHook.remove_of_concat_element #[ldecl.toExpr])
      facts := facts.push (← mkAppM ``KPrelude.MapHook.wfb_of_concat_element #[ldecl.toExpr])
    catch _ => pure ()
  liftMetaTactic fun g => do
    let mut g := g
    for p in facts do
      let g' ← g.assert `k2l_fact (← inferType p) p
      let (_, g'') ← g'.intro1P
      g := g''
    return [g]

/-- Case-split the first hypothesis that contains a `match` or `if` it can split (on a free
discriminant); fails when there is none. Used after `simp_all` when a rule's side condition is
stuck on a variable (for example a projection that holds only for some leaves). -/
elab "k2l_split_hyps" : tactic => do
  liftMetaTactic fun g => do
    for ldecl in (← g.getDecl).lctx do
      if ldecl.isImplementationDetail then continue
      if let some gs ← Lean.Meta.splitLocalDecl? g ldecl.fvarId then
        return gs
    throwError "k2l_split_hyps: nothing to split"

/-- `k2l_fuel_lift [h₁, …]`: for each hypothesis `h : F … = some v` that one of the implications
`hᵢ : ∀ xs v, F' … = some v → G … = some v` takes, add `G … = some v` (until none applies). The
soundness proof of the fuel twins of well-founded functions (`NS/Fuel.lean`) lifts a twin call's
value to the function's with it, the induction hypotheses being the `hᵢ`. -/
elab "k2l_fuel_lift" " [" ts:term,* "]" : tactic => do
  let es ← ts.getElems.filterMapM fun t => observing? (withMainContext (Term.elabTerm t none))
  let mut done : Array FVarId := #[]
  let mut changed := true
  while changed do
    changed := false
    let g ← getMainGoal
    let found ← g.withContext do
      for d in (← getLCtx) do
        if d.isImplementationDetail || done.contains d.fvarId then continue
        for e in es do
          let r ← observing? do
            let (ms, _, body) ← forallMetaTelescopeReducing (← inferType e)
            let some hm := ms.back? | throwError "no premise"
            unless ← isDefEq (← inferType hm) d.type do throwError "no match"
            hm.mvarId!.assign d.toExpr
            let pf ← instantiateMVars (mkAppN e ms)
            if pf.hasExprMVar then throwError "open"
            return (← instantiateMVars body, pf)
          if let some (ty, pf) := r then return some (d.fvarId, ty, pf)
      return none
    if let some (fv, ty, pf) := found then
      let (_, g') ← (← g.assert `hfuel ty pf).intro1P
      replaceMainGoal [g']
      done := done.push fv
      changed := true

/-- Split the first `match` of the goal, else of a hypothesis (the one `split` would pick there),
when all of its discriminants are free variables; fails otherwise. Such a split is directed by the
match's patterns: each case substitutes its pattern for the variable everywhere, and the last one
gets the premise that no earlier pattern matches. Run before `split`/`k2l_split_hyps` when the
context also has matches on compound discriminants (a translation `tr x` in a commutation proof):
splitting those first generalizes them, and inverting `tr x = pattern` cases `x` value by value
on the arity family, which loses the link between `x` and its pattern that a termination proof
reads. -/
elab "k2l_split_var" : tactic => liftMetaTactic fun g => g.withContext do
  let onVars (e : Expr) : MetaM Bool := do
    if e.isIte || e.isDIte then return false
    let some app ← matchMatcherApp? e | return false
    return app.discrs.all (·.isFVar)
  if let some e ← findSplit? (← instantiateMVars (← g.getType)) .match then
    if ← onVars e then
      if let some gs ← splitTarget? g (splitIte := false) then return gs
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    if let some e ← findSplit? (← instantiateMVars d.type) .match then
      if ← onVars e then
        if let some gs ← splitLocalDecl? g d.fvarId then return gs
  throwError "k2l_split_var: no match on free variables"

/-! ## Equations of recursive functions

The generated proof of a K equation of a well-founded recursive function (`k2l_eqn_r` in a
generated `Equations.lean`) unfolds the function once on the left-hand side and then cases with
these tactics until the cascade of the function's equations reduces (`k2l_case_call` also serves
the equations of functions that are not recursive, whose right-hand side binds partial calls). -/

/-- `k2l_case_rec [f₁, …]`: case on one application of a recursive (`Option`-valued) function
`fᵢ` that occurs outside binders in the goal or a hypothesis, innermost first. The hypotheses that
mention it are generalized with it, and `hc : fᵢ … = none` or `hc : fᵢ … = some r` is added. -/
elab "k2l_case_rec " "[" fs:ident,+ "]" : tactic => do
  let ns ← fs.getElems.mapM fun f => realizeGlobalConstNoOverloadWithInfo f
  let isCall (s : Expr) : Bool :=
    !s.hasLooseBVars && s.getAppNumArgs > 0 && ns.any fun n => s.getAppFn.isConstOf n
  -- `f … = r` records a call that was already cased on
  let recorded (ty : Expr) : Bool := ty.isAppOfArity ``Eq 3 && isCall ty.appFn!.appArg!
  let rec inner (fuel : Nat) (t : Expr) : Expr :=
    match fuel with
    | 0 => t
    | k + 1 => match t.getAppArgs.findSome? (fun a => a.find? isCall) with
      | some s => inner k s
      | none => t
  liftMetaTactic fun g => g.withContext do
    let mut cands := #[← instantiateMVars (← g.getType)]
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        let ty ← instantiateMVars d.type
        unless recorded ty do cands := cands.push ty
    let some t0 := cands.findSome? (fun e => e.find? isCall) | throwError "k2l_case_rec: no call"
    let t := inner 64 t0
    let mut fvs := #[]
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        let ty ← instantiateMVars d.type
        if (ty.find? (· == t)).isSome && !(ty.isAppOfArity ``Eq 3 && ty.appFn!.appArg! == t) then
          fvs := fvs.push d.fvarId
    let (_, g) ← g.revert fvs (preserveOrder := true)
    let (xs, g) ← g.generalize #[{ expr := t, xName? := `r, hName? := `hc }] (transparency := .default)
    let gs ← g.cases xs[0]!
    gs.toList.mapM fun s => do
      let (_, g') ← s.mvarId.introNP fvs.size
      pure g'

/-- `k2l_case_call`: case on the value of a partial call that a `match` in the goal inspects.
A generated definition binds each partial call of a right-hand side (a hook or a K function, whose
result type is `Option _`) by a `match` on its value, and the equation's statement binds the same
call with `Option.bind`; both sides are functions of that value, so casing on it (the call
generalized in the goal and in the hypotheses that mention it, with `hc : call = none` or
`hc : call = some r` added) reduces the `match` on either side. The call must be outside binders:
a call whose argument is the value of an earlier call becomes one after the case on that call.
Fails when the goal's matches inspect no such call. -/
elab "k2l_case_call" : tactic => do
  liftMetaTactic fun g => g.withContext do
    let env ← getEnv
    let tgt ← instantiateMVars (← g.getType)
    -- the discriminants of the goal's matches that are applications of a function
    let cands ← IO.mkRef (#[] : Array Expr)
    tgt.forEach fun e => do
      let .const n _ := e.getAppFn | pure ()
      let some info := Lean.Meta.Match.Extension.getMatcherInfo? env n | pure ()
      let args := e.getAppArgs
      for d in args.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs) do
        if d.hasLooseBVars then continue
        let .const c _ := d.getAppFn | continue
        if env.isConstructor c then continue
        if (Lean.Meta.Match.Extension.getMatcherInfo? env c).isSome then continue
        cands.modify (·.push d)
    -- a partial function's declared result type is `Option _` (`ite` and `dite`, whose result
    -- may be an `Option` too, are not calls of one)
    let partialFn (c : Name) : MetaM Bool := do
      let some ci := env.find? c | return false
      forallTelescopeReducing ci.type fun _ r => return r.isAppOfArity ``Option 1
    let mut found : Option Expr := none
    for d in (← cands.get) do
      if ← partialFn d.getAppFn.constName! then
        found := some d
        break
    let some t := found | throwError "k2l_case_call: no partial call that a match inspects"
    let mut fvs := #[]
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        let ty ← instantiateMVars d.type
        if (ty.find? (· == t)).isSome && !(ty.isAppOfArity ``Eq 3 && ty.appFn!.appArg! == t) then
          fvs := fvs.push d.fvarId
    let (_, g) ← g.revert fvs (preserveOrder := true)
    let (xs, g) ← g.generalize #[{ expr := t, xName? := `r, hName? := `hc }] (transparency := .default)
    let gs ← g.cases xs[0]!
    gs.toList.mapM fun s => do
      let (_, g') ← s.mvarId.introNP fvs.size
      pure g'

/-- A list built from `.List`, `ListItem` and concatenation (a list pattern of an equation's
left-hand side, or a part of one). -/
def k2lListCons (l : Expr) : Bool :=
  l.isAppOf ``ListHook.concat || l.isAppOf ``ListHook.element || l.isAppOf ``ListHook.unit

/-- The laws of `KPrelude.Ext` that evaluate `uncons` and `unsnoc` of such a list. -/
def k2lListLaws : MetaM SimpTheorems := do
  let mut s : SimpTheorems := {}
  for n in [``ListHook.uncons_concat_element, ``ListHook.unsnoc_concat_element,
      ``ListHook.uncons_element, ``ListHook.unsnoc_element, ``ListHook.uncons_unit,
      ``ListHook.unsnoc_unit, ``ListHook.uncons_concat, ``ListHook.unsnoc_concat,
      ``ListHook.concat_unit_left, ``ListHook.concat_unit_right] do
    s ← s.addConst n
  return s

/-- `d = v` for a discriminant `d` that is `uncons l` or `unsnoc l` of a list `l` built by the
list constructors, when the list laws evaluate it to `v`, `some _` or `none`. -/
def k2lListEval (d : Expr) : MetaM (Option Expr) := do
  unless d.isAppOf ``ListHook.uncons || d.isAppOf ``ListHook.unsnoc do return none
  unless k2lListCons d.appArg! do return none
  let ctx ← Simp.mkContext (simpTheorems := #[← k2lListLaws])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← Lean.Meta.simp d ctx
  let v := (← instantiateMVars r.expr).consumeMData
  unless v.isAppOfArity ``Option.some 2 || v.isAppOfArity ``Option.none 1 do return none
  return r.proof?

/-- Split the first `match` of the goal on `uncons l` or `unsnoc l` (`k2lListEval`), and decide
it: in each case, the case's equation `d = c` and `d = v` give `v = c`, which unifies the pattern's
variables with the values (`(x, t) = (X, L)`) or refutes the case. `none` when there is none. -/
def k2lListSplit (g : MVarId) : MetaM (Option (List MVarId)) := g.withContext do
  let env ← getEnv
  let tgt ← instantiateMVars (← g.getType)
  let cands ← IO.mkRef (#[] : Array (Expr × Expr))
  tgt.forEach fun e => do
    let .const n _ := e.getAppFn | pure ()
    let some info := Lean.Meta.Match.Extension.getMatcherInfo? env n | pure ()
    if e.hasLooseBVars then return
    let args := e.getAppArgs
    for d in args.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs) do
      if d.isAppOf ``ListHook.uncons || d.isAppOf ``ListHook.unsnoc then
        cands.modify (·.push (e, d))
  for (e, d) in (← cands.get) do
    let some pf ← k2lListEval d | continue
    let mut out := []
    for g' in ← Lean.Meta.Split.splitMatch g e do
      let r ← g'.withContext do
        for ld in (← getLCtx) do
          if ld.isImplementationDetail then continue
          let some (_, a, _) := (← instantiateMVars ld.type).eq? | continue
          unless a == d do continue
          let h ← mkEqTrans (← mkEqSymm pf) ld.toExpr
          let (hf, g2) ← (← g'.assert `k2l_l (← inferType h) h).intro1P
          return some ((← g2.cases hf).toList.map (·.mvarId))
        return none
      out := out ++ r.getD [g']
    return some out
  return none

/-- `k2l_case_list`: reduce the generated definition's matches on a list that the equation's
left-hand side gives as a list pattern (`ListItem(X) L`, `L ListItem(X)`, `ListItem(X)`, `.List`
and their combinations). The definition matches its argument by `uncons`, `unsnoc` and a test
against `.List`; on a list built by the list constructors these have known values (the laws above
`k2lListLaws`), so each such `match` is split and decided by its value (`k2lListSplit`), and
each such test is decided by `concat_eq_unit_iff` and `element_ne_unit`. Fails when the goal has
neither. -/
elab "k2l_case_list" : tactic => do
  if let some gs ← k2lListSplit (← getMainGoal) then
    replaceMainGoal gs
    return
  let tgt ← instantiateMVars (← getMainTarget)
  let test := tgt.find? fun e => e.isAppOfArity ``Eq 3 && e.appArg!.isAppOf ``ListHook.unit &&
    k2lListCons e.appFn!.appArg!
  if test.isNone then throwError "k2l_case_list: no list match or test on a list construction"
  evalTactic (← `(tactic| simp only [KPrelude.ListHook.concat_eq_unit_iff,
    KPrelude.ListHook.element_ne_unit, false_and, and_false, eq_self_iff_true, dite_true,
    dite_false]))

/-- `k2l_case_lvar`: split a list variable that the generated definition takes apart (a
discriminant `uncons l` or `unsnoc l` of a variable `l`, as in the equation of an `owise` rule,
whose left-hand side is a variable) into `.List` and a list with a first (`uncons`) or last
(`unsnoc`) element (`ListHook.cases_front`, `cases_back`), substituted for the variable, so that
`k2l_case_list` decides the matches on it. Fails when there is no such discriminant. -/
elab "k2l_case_lvar" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some d := tgt.find? fun e =>
      (e.isAppOfArity ``ListHook.uncons 4 || e.isAppOfArity ``ListHook.unsnoc 4) && e.appArg!.isFVar
    | throwError "k2l_case_lvar: no match on a list variable"
  let v ← Term.exprToSyntax d.appArg!
  if d.isAppOf ``ListHook.uncons then
    evalTactic (← `(tactic| rcases KPrelude.ListHook.cases_front $v with h | ⟨_, _, h⟩ <;> subst h))
  else
    evalTactic (← `(tactic| rcases KPrelude.ListHook.cases_back $v with h | ⟨_, _, h⟩ <;> subst h))

/-- `k2l_owise_arm`: close a case of an `owise` equation that another rule's arm reaches. The
statement's no-match premises (`∀ …, x = p → … → False`, one per rule tried before) see the
argument as the arm built it (`k2l_case_lvar`), and the pattern as the rule writes it; with the
list constructions of both normalized (`concat_assoc` and the unit laws: equal sequences of
elements and variables give the same term), the premise of the arm's rule refutes the case
(`k2l_no_arm`). -/
elab "k2l_owise_arm" : tactic => withMainContext do
  let mut hs := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isForall && ty.getForallBody.isConstOf ``False then hs := hs.push d.fvarId
  if hs.isEmpty then throwError "k2l_owise_arm: no no-match premise"
  let mut s : SimpTheorems := {}
  for n in [``ListHook.concat_assoc, ``ListHook.concat_unit_left, ``ListHook.concat_unit_right] do
    s ← s.addConst n
  let ctx ← Simp.mkContext (simpTheorems := #[s]) (congrTheorems := ← getSimpCongrTheorems)
  -- `simpGoal` fails when the constructions are already normal
  let g ← getMainGoal
  match ← (try (·.1) <$> simpGoal g ctx (simplifyTarget := false) (fvarIdsToSimp := hs)
      catch _ => pure (some (#[], g))) with
  | none => replaceMainGoal []
  | some (_, g) =>
    replaceMainGoal [g]
    evalTactic (← `(tactic| k2l_no_arm))

/-- `k2l_owise_apply`: close a case that a no-match premise `∀ xs, x = p → … → c = some true →
False` refutes once its last hypotheses are computed: apply the premise, unify its equations by
reflexivity (the case's argument is the pattern's instance), and close the rest by `simp_all` (a
`requires` over partial calls, such as `typeOf(E)`, which the case's own facts decide;
`k2l_no_arm` takes only a hypothesis as it stands). -/
elab "k2l_owise_apply" : tactic => withMainContext do
  let mut hs := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isForall && ty.getForallBody.isConstOf ``False then hs := hs.push d
  for d in hs do
    let s ← saveState
    try
      let t ← Term.exprToSyntax d.toExpr
      evalTactic (← `(tactic| (exfalso; apply $t <;> first | rfl | assumption | (simp_all; done))))
      if (← getGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "k2l_owise_apply: no no-match premise refutes the case"

/-- `k2l_case_choose`: from `h : MapHook.chooseFirst m hw f = some b` (the matcher of a
free-key map pattern found a binding), a binding `k |-> v` of `m`, its decomposition
`hc : (k |-> v) (remove m k) = some m`, and `f k v hc = some b` in place of `h`; an `owise`
equation's no-match premise refutes it with `hc` (`k2l_no_arm`). -/
elab "k2l_case_choose" : tactic => withMainContext do
  let some d ← (← getLCtx).findDeclM? fun d => do
      if d.isImplementationDetail then return none
      let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? | return none
      return if lhs.isAppOf ``MapHook.chooseFirst && rhs.isAppOf ``Option.some then some d else none
    | throwError "k2l_case_choose: no chosen binding"
  let t ← Term.exprToSyntax (← mkAppM ``MapHook.chooseFirst_eq_some #[d.toExpr])
  evalTactic (← `(tactic| obtain ⟨_, _, _, h⟩ := $t; try dsimp only at h))
  replaceMainGoal [← (← getMainGoal).tryClear d.fvarId]

/-- `k2l_case_discr`: case on a variable of a generated sort (an inductive type `Sort…`, or a
term of the arity-indexed family, split by `familyCases`) that a `match` in the goal inspects, so
that the cascade of a function's equations reduces. -/
elab "k2l_case_discr" : tactic => do
  liftMetaTactic fun g => g.withContext do
    let env ← getEnv
    let tgt ← instantiateMVars (← g.getType)
    let lctx ← getLCtx
    -- the family `Term`, or a sort's abbreviation `S := Term .S`
    let family (n : Name) : Bool := isFamilyName env n ||
      (match env.find? n with
        | some (.defnInfo v) => v.value.getAppFn.constName?.any (isFamilyName env)
        | _ => false)
    let sortVar (d : Expr) : Bool :=
      d.isFVar && (match lctx.find? d.fvarId! with
        | some decl => match decl.type.getAppFn with
          | .const n _ => ((match n with | .str _ s => s.startsWith "Sort" | _ => false) &&
              (match env.find? n with | some (.inductInfo _) => true | _ => false)) || family n
          | _ => false
        | none => false)
    let discrVar (s : Expr) : Option Expr := do
      let .const n _ := s.getAppFn | none
      let info ← Lean.Meta.Match.Extension.getMatcherInfo? env n
      let args := s.getAppArgs
      (args.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs)).find? sortVar
    let some d := tgt.find? (fun s => (discrVar s).isSome) >>= discrVar
      | throwError "k2l_case_discr: no match on a variable"
    return (← familyCases g d.fvarId!).toList.map (·.1)

/-- A variable that `isVar` accepts in `e` under constructors only, at most `fuel` deep. -/
private partial def underCtors (isVar : Expr → Bool) (fuel : Nat) (e : Expr) : MetaM (Option Expr) := do
  if isVar e then return some e
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    let e ← whnfR e
    let .const c _ := e.getAppFn | return none
    unless (← getEnv).isConstructor c do return none
    for a in e.getAppArgs do
      if let some v ← underCtors isVar fuel a then return some v
    return none

/-- `k2l_case_sub`: case on a variable of a generated sort that occurs inside a discriminant of a
`match` in the goal, a term of the family against a nested pattern (`inj_Exps a`, matched against
`inj_Exps (_,_ (inj_Id x) y)`), which `k2l_case_discr` does not split; run after it. A variable under a call is not cased: casing
it does not reduce the match, and would go on with the new variables. -/
elab "k2l_case_sub" : tactic => do
  liftMetaTactic fun g => g.withContext do
    let env ← getEnv
    let tgt ← instantiateMVars (← g.getType)
    let lctx ← getLCtx
    let family (n : Name) : Bool := isFamilyName env n ||
      (match env.find? n with
        | some (.defnInfo v) => v.value.getAppFn.constName?.any (isFamilyName env)
        | _ => false)
    let sortVar (d : Expr) : Bool :=
      d.isFVar && (match lctx.find? d.fvarId! with
        | some decl => match decl.type.getAppFn with
          | .const n _ => family n
          | _ => false
        | none => false)
    let apps ← IO.mkRef (#[] : Array Expr)
    tgt.forEachWhere (fun s => match s.getAppFn with
        | .const n _ => (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome
        | _ => false) fun s => apps.modify (·.push s)
    let mut found : Option Expr := none
    for s in ← apps.get do
      let .const n _ := s.getAppFn | continue
      let some info := Lean.Meta.Match.Extension.getMatcherInfo? env n | continue
      for a in s.getAppArgs.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs) do
        if found.isNone then found ← underCtors sortVar 16 a
    let some d := found
      | throwError "k2l_case_sub: no match on a constructor term with a variable"
    return (← familyCases g d.fvarId!).toList.map (·.1)

/-! ## Equations that need more than unfolding -/

/-- Close a generated equation statement with a law of `KPrelude.HookLaws`: an equation of
`domains.md` proved about the hook definitions, in the shape `Equations.lean` states it, whose
hypotheses are the statement's own. The match is syntactic (reducible transparency), so a
statement that is not one of the laws fails fast. -/
macro "k2l_hook_law" : tactic => `(tactic| first
  | (with_reducible apply KPrelude.IntHook.bitRange_eqn)
  | (with_reducible apply KPrelude.IntHook.signExtendBitRange_eqn)
  | (with_reducible apply KPrelude.IntHook.emod_tmod_abs)
  | (with_reducible apply KPrelude.IntHook.land_assoc)
  | (with_reducible apply KPrelude.StringHook.le_eqn)
  | (with_reducible apply KPrelude.StringHook.ge_eqn)
  | (with_reducible apply KPrelude.StringHook.rfindChar_eqn1 <;> assumption)
  | (with_reducible apply KPrelude.StringHook.replaceFirst_eqn1 <;> assumption)
  | (with_reducible apply KPrelude.StringHook.replaceFirst_eqn2 <;> assumption)
  | (with_reducible apply KPrelude.StringHook.countAllOccurrences_eqn1 <;> assumption)
  | (with_reducible apply KPrelude.SetHook.union_eqn <;> assumption)
  | (with_reducible apply KPrelude.MapHook.ceil_concat_element_eqn <;> assumption)
  | (with_reducible apply KPrelude.BytesHook.padRight_ceil)
  | (with_reducible apply KPrelude.BytesHook.padLeft_ceil))

/-- Refute a generated statement that is false in the model, with a refutation of the prelude
stated in the generator's shape (the mirror of `k2l_hook_law`; `NS/Refuted.lean`). -/
macro "k2l_hook_refute" : tactic => `(tactic| first
  | (with_reducible exact KPrelude.StringHook.countAllOccurrences_eqn2_false))

declare_syntax_cat k2lPat
syntax "_" : k2lPat
syntax ident : k2lPat
syntax "⟨" k2lPat,* "⟩" : k2lPat

/-- Apply the pattern `pat` to the term `e` in goal `g`: `_` leaves it, a name renames a variable,
`⟨p0, …⟩` cases on a variable by `familyCases` and applies `pi` to the `i`-th argument of each
remaining goal's constructor. -/
partial def applyK2lPat (g : MVarId) (e : Expr) (pat : TSyntax `k2lPat) : MetaM (List MVarId) := do
  match pat with
  | `(k2lPat| _) => return [g]
  | `(k2lPat| $n:ident) =>
    if e.isFVar then return [← g.rename e.fvarId! n.getId] else return [g]
  | `(k2lPat| ⟨$ps,*⟩) =>
    unless e.isFVar do return [g]
    let ps := ps.getElems
    let mut out := []
    for (g', args) in ← familyCases g e.fvarId! do
      let mut gs := [g']
      for i in [0:ps.size] do
        let some a := args[i]? | break
        let mut next := []
        for h in gs do
          next := next ++ (← applyK2lPat h a ps[i]!)
        gs := next
      out := out ++ gs
    return out
  | _ => throwUnsupportedSyntax

/-- `k2l_cases x` (or `k2l_cases x with ⟨p0, …⟩`): cases on `x`, nested as the pattern says, as
`rcases` does on a type with one constructor per value shape, but on the arity-indexed family
with the impossible constructors refuted (`familyCases`), so the goals left are exactly those
of the K constructors and leaves of `x`'s sort, as in the one type per sort encoding. -/
syntax (name := k2lCases) "k2l_cases " term (" with " k2lPat)? : tactic

elab_rules : tactic
  | `(tactic| k2l_cases $x $[with $p]?) => withMainContext do
    let e ← elabTerm x none
    let pat ← match p with
      | some p => pure p
      | none => `(k2lPat| ⟨⟩)
    replaceMainGoal (← applyK2lPat (← getMainGoal) e pat)

/-- `k2l_case_inj`: case on a variable of a generated sort that is the argument of an injection
function `inj_…` in the goal. An injection is defined by cases on its argument, so after the split
it reduces: a `match` of the cascade on the injected term (the pattern of another subsort) then
reduces too, which `simp` cannot do on the variable. Fails when there is no such variable.

A sort is an inductive type `Sort…`, or `Term t` of the arity-indexed family (every generated
sort); on the family the split is `familyCases` without the enumeration split. -/
elab "k2l_case_inj" : tactic => do
  liftMetaTactic fun g => g.withContext do
    let env ← getEnv
    let tgt ← instantiateMVars (← g.getType)
    let lctx ← getLCtx
    let sortVar (d : Expr) : MetaM Bool := do
      if !d.isFVar then return false
      let some decl := lctx.find? d.fvarId! | return false
      match decl.type.getAppFn with
      | .const n _ =>
        if (match n with | .str _ s => s.startsWith "Sort" | _ => false) &&
            (match env.find? n with | some (.inductInfo _) => true | _ => false) then
          return true
        let t ← whnfR decl.type
        return (match t.getAppFn with | .const m _ => isFamilyName env m | _ => false)
      | _ => return false
    let cands ← IO.mkRef (#[] : Array Expr)
    tgt.forEach fun e => match e.getAppFn with
      | .const n@(.str _ s) _ =>
        if s.startsWith "inj_" && e.getAppNumArgs == 1 &&
            (match env.find? n with | some (.defnInfo _) => true | _ => false) then
          cands.modify (·.push e.appArg!)
        else pure ()
      | _ => pure ()
    let mut found : Option FVarId := none
    for a in (← cands.get) do
      if ← sortVar a then
        found := some a.fvarId!
        break
    let some x := found | throwError "k2l_case_inj: no injected variable"
    return (← familyCases g x (splitEnum := false)).toList.map (·.1)

end KPrelude

namespace KPrelude

open Lean Elab Command

/-- `#k2l_assert_axioms a b …`: fail unless each declaration depends only on `propext`,
`Quot.sound` and `Classical.choice` (no `sorryAx`, no added axioms); print what each uses. -/
elab "#k2l_assert_axioms " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| Lean.collectAxioms n
    let allowed := [``propext, ``Quot.sound, ``Classical.choice]
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError m!"{n} depends on disallowed axioms {bad}"
    logInfo m!"{n} depends on axioms: {axs}"

/-- Fail unless the theorem `rn` proves the negation of the obligation `sn` (the statement's
closure over its own binders) and depends only on Lean's three axioms. -/
def checkRefuted (sn rn : Name) : CommandElabM Unit := do
  let s ← getConstInfo sn
  let some r := (← getEnv).find? rn | throwError m!"{rn}: no such theorem"
  let expected ← liftTermElabM <| Meta.forallTelescope s.type fun xs _ =>
    Meta.mkForallFVars xs (mkAppN (mkConst s.name (s.levelParams.map mkLevelParam)) xs)
  unless r.type == mkNot expected do
    throwError m!"{rn} : {r.type}, but the refutation of {sn} is {mkNot expected}"
  let axs ← liftCoreM <| Lean.collectAxioms rn
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError m!"{rn} depends on disallowed axioms {bad}"
  logInfo m!"{rn} refutes {sn}; depends on axioms: {axs}"

/-- `#k2l_refuted X`: fail unless `X.refuted` proves the negation of the obligation `X.statement`,
and depends only on `propext`, `Quot.sound` and `Classical.choice`. The obligation a library
states is the statement's closure over its own binders (its `[Hooks]` instance, when it reads the
library's parameters: the statement for every implementation), so the refutation's type must be
`¬ X.statement`, or `¬ ∀ [Hooks], X.statement` (written `omit [Hooks] in`; inside the section
`¬ X.statement` would be quantified over every instance, the negation of a weaker claim).
Compared structurally, not up to definitional unfolding: a refutation names the generated
statement instead of restating it. `#k2l_refuted S R`: the same for the statement constant `S`
and the theorem `R` (claims, whose statement constant is the claim itself). -/
elab "#k2l_refuted " id:ident : command => do
  let sn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent (id.getId ++ `statement))
  checkRefuted sn (sn.getPrefix ++ `refuted)

elab "#k2l_refuted " s:ident r:ident : command => do
  let sn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  let rn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo r
  checkRefuted sn rn

/-- Fail unless the theorem `pn` proves the obligation `sn` and depends only on Lean's three
axioms: its type is the statement's closure over its own binders (`∀ xs, S xs`), or the
statement's body written out (`∀ xs, body`), compared structurally (binder names aside). -/
def checkProves (sn pn : Name) : CommandElabM Unit := do
  let s ← getConstInfo sn
  let some p := (← getEnv).find? pn | throwError m!"{pn}: no such theorem"
  unless p matches .thmInfo _ do throwError m!"{pn} is not a theorem"
  let lvls := s.levelParams.map mkLevelParam
  let some v := s.value? | throwError m!"{sn} is not a definition"
  let (named, literal) ← liftTermElabM <| Meta.forallTelescope s.type fun xs _ => do
    let body := (v.instantiateLevelParams s.levelParams lvls).beta xs
    return (← Meta.mkForallFVars xs (mkAppN (mkConst sn lvls) xs), ← Meta.mkForallFVars xs body)
  unless p.type == named || p.type == literal do
    throwError m!"{pn} : {p.type}, but the obligation {sn} is {named}, or {literal}"
  let axs ← liftCoreM <| Lean.collectAxioms pn
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError m!"{pn} depends on disallowed axioms {bad}"
  logInfo m!"{pn} proves {sn}; depends on axioms: {axs}"

/-- `#k2l_proves X`: fail unless the theorem `X` proves the obligation `X.statement` as stated,
and depends only on `propext`, `Quot.sound` and `Classical.choice` (CT-3). The theorem is
`theorem X : X.statement`, or the statement written out, as the generator writes its proofs;
compared structurally, not up to definitional unfolding, so a theorem that states something else
(a weaker conclusion, an extra premise) is rejected even where it would unfold to the statement.
With `[Hooks]`, the statement's closure is over the instance, and so is the theorem's.
`#k2l_proves S P`: the same for the statement constant `S` and the theorem `P`. -/
elab "#k2l_proves " id:ident : command => do
  let sn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent (id.getId ++ `statement))
  checkProves sn sn.getPrefix

elab "#k2l_proves " s:ident p:ident : command => do
  let sn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  let pn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo p
  checkProves sn pn

end KPrelude

namespace KPrelude

open Lean Meta Elab Tactic

/-- Close a goal `∃ x ∈ MapHook.choose m _ f, P x` (a free-key map pattern of a matcher) with a
hypothesis `MapHook.concat (MapHook.element k v) r = some m'` of the relation whose map is `m`
(`rfl`) or equal to it (`simp_all`, for the rest of an earlier match), then introduce the
certificate and reduce the continuation. -/
elab "k2l_choose" : tactic => withMainContext do
  let goal ← getMainGoal
  let gty ← instantiateMVars (← goal.getType)
  unless (gty.find? (fun e => e.isAppOf ``KPrelude.MapHook.choose)).isSome do
    throwError "k2l_choose: no choose in the goal"
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let some (_, lhs, _) := ty.eq? | continue
    unless lhs.isAppOf ``KPrelude.MapHook.concat do continue
    let s ← saveState
    try
      let h ← Term.exprToSyntax ldecl.toExpr
      evalTactic (← `(tactic| refine KPrelude.MapHook.exists_mem_choose' $h ?k2lheq ?_))
      evalTactic (← `(tactic| case k2lheq => first | rfl | (simp_all; done)))
      evalTactic (← `(tactic| intro _))
      -- the continuation can already be in normal form, and `dsimp only` fails when it makes no
      -- progress
      evalTactic (← `(tactic| try dsimp only))
      return
    catch _ => s.restore
  throwError "k2l_choose: no hypothesis matches"

/-- Replace the rest variable of each map match by its value: for a hypothesis
`MapHook.remove m k = R` with `R` a variable, `subst R`. A matcher computes the rest of a
free-key match as `remove m k`; the relation names it. -/
partial def k2lRestLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let found ← withMainContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, lhs, rhs) := ty.eq? | continue
      unless lhs.isAppOf ``KPrelude.MapHook.remove && rhs.isFVar do continue
      let s ← saveState
      try
        let h ← Term.exprToSyntax ldecl.toExpr
        evalTactic (← `(tactic| subst $h:term))
        return true
      catch _ => s.restore
    return false
  if found then k2lRestLoop (fuel - 1)

elab "k2l_rest" : tactic => k2lRestLoop 32

/-- Destructure every conjunction hypothesis (`h : A ∧ B` becomes two hypotheses). -/
partial def k2lAndsLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let found ← withMainContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      unless ty.isAppOfArity ``And 2 do continue
      let s ← saveState
      try
        let h ← Term.exprToSyntax ldecl.toExpr
        evalTactic (← `(tactic| cases $h:term))
        return true
      catch _ => s.restore
    return false
  if found then k2lAndsLoop (fuel - 1)

elab "k2l_split_ands" : tactic => k2lAndsLoop 64

/-- Close a goal in the catch-all branch of a matcher's `match`: a hypothesis
`h : ∀ x₁ …, a₁ = x₁ → … → ¬ aₙ = xₙ` (the pattern does not match) is contradicted by the
values the relation gives (`apply h <;> rfl`). -/
elab "k2l_absurd_pattern" : tactic => withMainContext do
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    unless ty.isForall do continue
    let s ← saveState
    try
      let h ← Term.exprToSyntax ldecl.toExpr
      evalTactic (← `(tactic| (exfalso; apply $h:term <;> rfl)))
      if (← getGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "k2l_absurd_pattern: no contradicting pattern hypothesis"

end KPrelude


namespace KPrelude

/-- A property of every element of a list, proved element by element: generated proofs about a
long list of rules use it instead of a case split on a long disjunction (which overflows the
stack at about a hundred rules). -/
inductive AllMem {α : Type} (P : α → Prop) : List α → Prop where
  | nil : AllMem P []
  | cons {a : α} {l : List α} : P a → AllMem P l → AllMem P (a :: l)

theorem AllMem.mem {α : Type} {P : α → Prop} : ∀ {l : List α}, AllMem P l → ∀ a ∈ l, P a
  | _, .nil, _, h => by simp at h
  | _, .cons hp hl, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact hp
    · exact hl.mem a h

end KPrelude

/-- `k2l_mem`: `r ∈ l` where `l` is a list literal built with `mergeRank` (a rule-index bucket
reduced on a constructor term), by search through its spine. It never rewrites inside `l`, whose
unreduced parts may be large stuck matches. The generated `mem` proofs follow the rule's path
through the index instead; this is their fallback. -/
syntax "k2l_mem" : tactic
macro_rules
  | `(tactic| k2l_mem) => `(tactic| first
      | exact List.mem_cons_self
      | exact List.mem_cons_self ..
      | (apply KPrelude.mem_mergeRank_left; k2l_mem)
      | (apply KPrelude.mem_mergeRank_right; k2l_mem)
      | (apply List.mem_cons_of_mem; k2l_mem))

/-!
## Facts for the per-rule adequacy proofs

A rule's relation states a list pattern `ListItem(X) REST` as `ListHook.concat (ListHook.element x) t = l`,
while its matcher tests `ListHook.uncons l`. `k2l_list_facts` adds, for each such hypothesis, what
it says about `uncons l` (or `unsnoc l` for `REST ListItem(X)`): `uncons` of `concat (element x) t`
is `some (x, t)`, so after the matcher's split `simp_all` identifies the matcher's `x', t'` with
the relation's `x, t` (or refutes the `none` branch).

A rule that calls the same partial function on the same arguments twice (once in a guard, once in
the right-hand side) gets two hypotheses `f a = some r` and `f a = some r'` in its relation, and
the matcher adds a third after the split. A function has one value at `a`, so `r = r'`;
`k2l_fundep` eliminates it, for every pair of hypotheses `e = some r`, `e = some r'` with the same
`e`, and for every `some r = some r'` (which `split` leaves when it generalizes a discriminant
that an earlier split already decided), until none is left. `simp_all` alone rewrites one
hypothesis with the other and keeps `r = r'` as a rewrite rule, without substituting it into the
remaining hypotheses.
-/

namespace KPrelude

namespace ListHook

variable {L E : Type} [ListIso L E]

theorem uncons_of_concat_element {l t : L} {x : E} (h : concat (element x) t = l) : uncons l = some (x, t) := by
  subst h; exact uncons_concat_element x t

theorem unsnoc_of_concat_element {l t : L} {x : E} (h : concat t (element x) = l) : unsnoc l = some (t, x) := by
  subst h; exact unsnoc_concat_element t x

end ListHook

open Lean Meta Elab Tactic

/-- `k2l_list_facts`: for each hypothesis `concat (element x) t = l` (or `concat t (element x) = l`),
add `uncons l = some (x, t)` (or `unsnoc l = some (t, x)`). -/
elab "k2l_list_facts" : tactic => withMainContext do
  let mut facts : Array Expr := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let some (_, lhs, _) := ty.eq? | continue
    unless lhs.isAppOf ``KPrelude.ListHook.concat do continue
    let args := lhs.getAppArgs
    let some a := args[args.size - 2]? | continue
    let some b := args[args.size - 1]? | continue
    try
      if a.isAppOf ``KPrelude.ListHook.element then
        facts := facts.push (← mkAppM ``KPrelude.ListHook.uncons_of_concat_element #[ldecl.toExpr])
      if b.isAppOf ``KPrelude.ListHook.element then
        facts := facts.push (← mkAppM ``KPrelude.ListHook.unsnoc_of_concat_element #[ldecl.toExpr])
    catch _ => pure ()
  liftMetaTactic fun g => do
    let mut g := g
    for p in facts do
      let g' ← g.assert `k2l_fact (← inferType p) p
      let (_, g'') ← g'.intro1P
      g := g''
    return [g]

/-- Whether every hypothesis type of `tys` is still in the context (`k2lFundepOnce`). -/
def k2lStillThere (tys : List Expr) : TacticM Bool := do
  if (← getGoals).isEmpty then return false
  withMainContext do
    let lctx ← getLCtx
    let mut present : List Expr := []
    for ld in lctx do
      if ld.isImplementationDetail then continue
      present := (← instantiateMVars ld.type) :: present
    return tys.all fun t => present.any (· == t)

/-- One functional-dependency step (see above); `true` if it changed the goal. For hypotheses
`h₁ : e = some a`, `h₂ : e = some b` it adds `a = b` and eliminates it with `cases`, which
substitutes a variable side, or unifies constructor applications field by field (a pair
`(x', t') = (x, t)` from `uncons`, a cell pattern), or closes the goal on a constructor clash;
a hypothesis `some a = some b` is eliminated the same way. Pairs that `cases` cannot eliminate
(two different stuck terms) are left alone, and so is a step after which the hypotheses it
started from are still there unchanged (two values that are equal by definition but not
syntactically: `cases` then succeeds without changing anything), so the loop always ends. -/
def k2lFundepOnce : TacticM Bool := withMainContext do
  let mut seen : Array (Expr × Expr × LocalDecl) := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let some (_, e, rhs) := ty.eq? | continue
    unless rhs.isAppOfArity ``Option.some 2 do continue
    let v := rhs.appArg!
    -- `some a = some b` (a split that generalized a discriminant already split on)
    if e.isAppOfArity ``Option.some 2 && !(e.appArg! == v) then
      let s ← saveState
      try
        let h ← Term.exprToSyntax ldecl.toExpr
        evalTactic (← `(tactic| (have k2l_fd := Option.some.inj $h; cases k2l_fd)))
        if ← k2lStillThere [ty] then s.restore else return true
      catch _ => s.restore
      continue
    for (e', v', d') in seen do
      unless e == e' && !(v == v') do continue
      let s ← saveState
      try
        let h1 ← Term.exprToSyntax d'.toExpr
        let h2 ← Term.exprToSyntax ldecl.toExpr
        evalTactic (← `(tactic| (have k2l_fd := Option.some.inj (Eq.trans (Eq.symm $h1) $h2); cases k2l_fd)))
        if ← k2lStillThere [ty, ← instantiateMVars d'.type] then s.restore else return true
      catch _ => s.restore
    seen := seen.push (e, v, ldecl)
  return false

partial def k2lFundepLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  if (← getGoals).isEmpty then return
  if ← k2lFundepOnce then k2lFundepLoop (fuel - 1)

/-- `k2l_fundep1`: one step of `k2l_fundep`; fails if there is none. -/
elab "k2l_fundep1" : tactic => do
  unless ← k2lFundepOnce do throwError "k2l_fundep1: nothing to identify"

/-- `k2l_fundep`: the steps of `k2l_fundep1` until none applies (at most 64). -/
elab "k2l_fundep" : tactic => k2lFundepLoop 64

/-- `k2l_absurd`: close a goal with a hypothesis `h : ∀ x₁ …, a₁ = b₁ → … → False` (the
"no pattern matched" hypothesis of a matcher's fallback branch, after `simp_all` has split the
pattern equation into one equation per field) whose equations all hold by unification: each
`aᵢ = bᵢ` is unified (assigning the `xⱼ`) and proved by `rfl`. Unlike `apply h <;> rfl`, the
bound variables are never left as goals of their own. -/
elab "k2l_absurd" : tactic => withMainContext do
  let g ← getMainGoal
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    unless ty.isForall do continue
    let s ← saveState
    let ok ← try
      let (xs, _, body) ← forallMetaTelescopeReducing ty
      unless (← whnfD body).isConstOf ``False do throwError "not a refutation"
      for x in xs do
        let xt ← instantiateMVars (← inferType x)
        if let some (_, a, b) := xt.eq? then
          unless ← isDefEq a b do throwError "an equation does not hold"
          x.mvarId!.assign (← mkEqRefl a)
      let pf ← instantiateMVars (mkAppN ldecl.toExpr xs)
      if pf.hasExprMVar then throwError "a variable is not determined"
      g.assign (← mkFalseElim (← g.getType) pf)
      pure true
    catch _ => pure false
    if ok then
      replaceMainGoal []
      return
    s.restore
  throwError "k2l_absurd: no hypothesis refutes the goal"

end KPrelude
