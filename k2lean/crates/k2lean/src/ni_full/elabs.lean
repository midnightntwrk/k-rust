open Lean Meta Elab Tactic in
/-- Case every variable of a cell sort the projections read. -/
scoped elab "k2l_cases_cells" : tactic => do
  let sorts := #[@CELLSORTS@]
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let some d ← g.withContext do
        (← getLCtx).findDeclM? fun d => do
          if d.isImplementationDetail then return none
          let t ← instantiateMVars d.type
          for s in sorts do
            if ← isDefEq t (mkConst s) then return some d
          return none
      | return
    g.withContext (KPrelude.Soundness.casesVar (mkFVar d.fvarId))
    go (fuel - 1)
  go 16

open Lean Meta Elab Tactic in
/-- Replace every expression variable `e` known to be a value (`isRes (inj e) = true`) by an
injected value. -/
scoped elab "k2l_values" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let some d ← g.withContext do
        (← getLCtx).findDeclM? fun d => do
          if d.isImplementationDetail then return none
          let t ← instantiateMVars d.type
          let some (_, l, r) := t.eq? | return none
          unless r.isConstOf ``Bool.true && l.isAppOf ``@NS@.isRes do return none
          let some a := l.getAppArgs[0]? | return none
          unless a.isAppOf ``@NA@.inj_@HS@_KItem && (a.getAppArgs.back?.map Expr.isFVar).getD false do
            return none
          return some d
      | return
    let h ← g.withContext (Term.exprToSyntax (mkFVar d.fvarId))
    evalTactic (← `(tactic| obtain ⟨_, rfl⟩ := (isRes_@HS@_iff _).1 $h))
    go (fuel - 1)
  go 8

