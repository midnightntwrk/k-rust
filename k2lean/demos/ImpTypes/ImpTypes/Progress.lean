import ImpTypes.Invariant

/-!
# Progress of well-typed kimp configurations (section 5 of the type soundness proof)

HAND-WRITTEN. A configuration with the runtime typing `WTc G` (`Invariant.lean`)
has terminated or has a rule that applies. It imports only the invariant's definitions, not the
preservation proof, so an edit to a rule that a preservation case depends on does not keep this
file from being checked.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ImpTypes

open KPrelude



/-! ## 5. Progress (template: the case split follows the shapes of the rules' left-hand sides;
`k2l_ctor_search` finds the rule; the store rule `CALC.var` is supplied by hand) -/

/-- A terminated configuration: nothing left to compute. -/
def Final : KImp.SortGeneratedTopCell → Prop
  | .«<generatedTop>» (.«<k>» .dotk) _ _ => True
  | _ => False

/-- Close a hypothesis of a rule: by unification, an assumption, or by computing `isKResult`. -/
macro "prog_close" : tactic => `(tactic| first
  | rfl
  | assumption
  | exact KImp.proj_inj_KItem_Expr _
  | (simp_all [KImp.K.isKResult, KImp.K.isKResult.rule1, KImp.proj_KItem_KResult, KImp.inj_Expr_KItem,
      KImp.proj_Expr_Value, BoolHook.and, BoolHook.not]; done))

/-- An ill-typed shape: the continuation's typing computes to `false`. -/
macro "prog_absurd" : tactic => `(tactic| first | (ty_simp; done) | (ty_simp; simp; done) | (intro _hk; simp at _hk; done) | (intro _hk; simp [kty_kseq, item_none, item, item0] at _hk; done))

open Lean Meta Elab Tactic in
/-- Case on the operands (variables of sort `Expr`) of the head item: whether an operand is a
value decides between heating and the operator's own rule. -/
partial def operandLoop (fuel : Nat) : TacticM Unit := do
  if (← getGoals).isEmpty || fuel = 0 then return
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let x? ← g.withContext do
    if let some it := t.find? (fun e => e.isAppOfArity ``KImp.SortKItem.inj_Expr 1 || e.isAppOfArity ``KImp.SortKItem.inj_Stmt 1) then
      for x in it.appArg!.getAppArgs do
        if x.isFVar && (← inferType x).isConstOf ``KImp.SortExpr then return some x
    return none
  let some x := x? | return
  let hx ← g.withContext (Term.exprToSyntax x)
  evalTactic (← `(tactic| cases $hx:term))
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    operandLoop (fuel - 1)
    out := out ++ (← getGoals)
  setGoals out.toList

elab "operand_cases" : tactic => operandLoop 2

open Lean Meta Elab Tactic in
/-- Case on the Boolean variables of the goal (a literal decides between `if-true` and `if-false`,
`true && B` and `false && B`). -/
partial def boolLoop (fuel : Nat) : TacticM Unit := do
  if (← getGoals).isEmpty || fuel = 0 then return
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let x? ← g.withContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      if (← whnfR ldecl.type).isConstOf ``Bool && (t.find? (· == ldecl.toExpr)).isSome then return some ldecl.toExpr
    return none
  let some x := x? | return
  let hx ← g.withContext (Term.exprToSyntax x)
  evalTactic (← `(tactic| cases $hx:term))
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    boolLoop (fuel - 1)
    out := out ++ (← getGoals)
  setGoals out.toList

elab "bool_cases" : tactic => boolLoop 3

open Lean Meta Elab Tactic in
/-- Case on the `SortK` arguments of freezers in the goal until they have the shape the cooling
rules match (`kseq y .dotk`); ill-typed shapes close by `prog_absurd`. -/
partial def frzCasesLoop (fuel : Nat) : TacticM Unit := do
  if (← getGoals).isEmpty || fuel = 0 then return
  evalTactic (← `(tactic| try prog_absurd))
  if (← getGoals).isEmpty then return
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let cand ← g.withContext do
    let mut out : Option Expr := none
    if let some f := t.find? (fun e => e.isAppOfArity ``KImp.SortKItem.inj_KItem 1) then
      for x in (f.appArg!).getAppArgs do
        let x' := if x.isAppOfArity ``KImp.SortK.kseq 2 then x.appArg! else x
        if x'.isFVar then
          if (← inferType x').isConstOf ``KImp.SortK then
            out := some x'; break
    return out
  let some x := cand | return
  let hx ← g.withContext (Term.exprToSyntax x)
  evalTactic (← `(tactic| cases $hx:term))
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    frzCasesLoop (fuel - 1)
    out := out ++ (← getGoals)
  setGoals out.toList

elab "frz_cases" : tactic => frzCasesLoop 6

open Lean Meta Elab Tactic in
/-- Case on the projections and typings the goal's hypothesis is stuck on (as `ty_cases`, plus
`proj_KItem_*` of a variable). -/
partial def progCasesLoop (fuel : Nat) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| try ty_simp))
  evalTactic (← `(tactic| try prog_absurd))
  if (← getGoals).isEmpty || fuel = 0 then return
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let isProj (e : Expr) : Bool :=
    (e.isAppOfArity ``KImp.proj_KItem_Expr 1 || e.isAppOfArity ``KImp.proj_KItem_Id 1 ||
      e.isAppOfArity ``KImp.proj_KItem_Stmt 1) && e.appArg!.isFVar
  let some e := t.find? (fun e => isProj e || e.isAppOfArity ``ImpTypes.tyOf 2 || e.isAppOfArity ``ImpTypes.wtS 2) | return
  let x ← g.withContext (Term.exprToSyntax e)
  let step ← if e.isAppOfArity ``ImpTypes.tyOf 2 then
      `(tactic| rcases _h : $x:term with _ | ⟨_ | _⟩)
    else
      `(tactic| rcases _h : $x:term with _ | _)
  evalTactic step
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    progCasesLoop (fuel - 1)
    out := out ++ (← getGoals)
  setGoals out.toList

elab "prog_cases" : tactic => progCasesLoop 4

/-- One shape of the head of `<k>`: compute what the typing says, then find the rule. -/
macro "prog_proj" : tactic => `(tactic| (simp only [KImp.proj_eq_some_KItem_Id, KImp.proj_eq_some_KItem_Stmt, KImp.proj_eq_some_KItem_Expr] at *; subst_vars))
macro "prog_leaf" : tactic => `(tactic| (prog_cases; all_goals (intro _hk; (try prog_proj); bool_cases; all_goals k2l_ctor_search KImp.App => prog_close)))

/-! ### HAND (rule `CALC.var`): the lookup rule applies to a typed identifier

The one place where progress depends on the shape of `CALC.var`: a K edit to that rule reopens
this lemma and no other part of `progress`. -/

theorem app_var {G : TEnv} {t : Ty} (x : KImp.SortId) (K : KImp.SortK) (g : KImp.SortGeneratedCounterCell)
    (E : KImp.SortMap) (he : envTy G E) (ht : tyOf G (.inj_Id x) = some t) :
    KImp.App (.«<generatedTop>» (.«<k>» (.kseq (.inj_Id x) K)) (.«<env>» E) g) := by
  obtain ⟨v, hl, -⟩ := he.2 x t ht
  exact KImp.App.«CALC.var» x K g E v _ (MapHook.concat_element_remove he.1 hl)

theorem progress {G : TEnv} (c : KImp.SortGeneratedTopCell) (hw : WTc G c) : Final c ∨ KImp.App c := by
  obtain ⟨⟨k⟩, ⟨E⟩, g⟩ := c
  obtain ⟨hk, he⟩ := hw
  simp only [kOf, envOf, envTyC] at hk he
  cases k with
  | dotk => exact Or.inl trivial
  | kseq it K =>
    right
    revert hk
    cases it
    -- a value at the head: the next item is a freezer waiting for it (a cooling rule applies)
    case inj_Int i | inj_Bool b =>
      cases K with
      | dotk => prog_absurd
      | kseq it₂ K₂ =>
        cases it₂ <;> (try prog_absurd)
        rename_i f
        cases f <;> (try prog_absurd) <;> frz_cases <;> prog_leaf
    -- HAND-WRITTEN: an identifier at the head; the store typing gives its value (`app_var`)
    case inj_Id x =>
      intro hk
      simp only [kty_kseq, item_none, item0_id] at hk
      cases ht : tyOf G (.inj_Id x) with
      | none => simp [ht] at hk
      | some t => exact app_var x K g E he ht
    -- an expression: an operand is not a value (heating), or the operator's rule applies
    case inj_Expr e₀ =>
      cases e₀ <;> operand_cases <;> prog_leaf
    -- a statement
    case inj_Stmt s =>
      cases s <;> operand_cases <;> prog_leaf
    all_goals prog_absurd

end ImpTypes
