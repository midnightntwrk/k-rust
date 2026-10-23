import Lean
import KPrelude.Coll
import KPrelude.Ext

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

/-! ## Equations of recursive functions

The generated proof of a K equation of a well-founded recursive function (`k2l_eqn_r` in a
generated `Equations.lean`) unfolds the function once on the left-hand side and then cases with
these two tactics until the cascade of the function's equations reduces. -/

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

/-- `k2l_case_discr`: case on a variable of a generated sort (an inductive type `Sort…`) that a
`match` in the goal inspects, so that the cascade of a function's equations reduces. -/
elab "k2l_case_discr" : tactic => do
  liftMetaTactic fun g => g.withContext do
    let env ← getEnv
    let tgt ← instantiateMVars (← g.getType)
    let lctx ← getLCtx
    let sortVar (d : Expr) : Bool :=
      d.isFVar && (match lctx.find? d.fvarId! with
        | some decl => match decl.type.getAppFn with
          | .const n _ => (match n with | .str _ s => s.startsWith "Sort" | _ => false) &&
              (match env.find? n with | some (.inductInfo _) => true | _ => false)
          | _ => false
        | none => false)
    let discrVar (s : Expr) : Option Expr := do
      let .const n _ := s.getAppFn | none
      let info ← Lean.Meta.Match.Extension.getMatcherInfo? env n
      let args := s.getAppArgs
      (args.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs)).find? sortVar
    let some d := tgt.find? (fun s => (discrVar s).isSome) >>= discrVar
      | throwError "k2l_case_discr: no match on a variable"
    let gs ← g.cases d.fvarId!
    pure (gs.toList.map (·.mvarId))

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
      evalTactic (← `(tactic| dsimp only))
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
