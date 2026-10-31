import KPrelude.Ends
import KPrelude.Invariant
import KPrelude.InvAttr
import KPrelude.InvTactic
import KPrelude.Tactic

/-!
# A measure that every step lowers (`gen --measure`, `direction.md` §5)

In a finite execution "every run ends" is termination of the step relation, and a measure that
every step lowers proves it (`Ends.terminates_of_measure`). The author writes the measure in K, as
a function from a cell to `Int` (K has no `Nat`), and `gen --measure NAME@CELL` states, per rule,
that the rule's step lowers it (`Lower`): its value is defined at both ends, nonnegative at the
target and below its value at the source. A strictly decreasing sequence of nonnegative integers is
finite, and a first configuration with a negative value has no step at all, so `Lower` at every step
gives a `Nat` measure that every step lowers (`nat_lt`), and termination (`terminates`, and under a
preserved invariant `terminates_on`). That the value is defined is part of each obligation, since
K's `total` is the author's claim, which k2lean states and never assumes.

`k2l_measure [unfold] [lemmas]` proves one rule's obligation, `Step.Rel.r (Lower μ)`:
- it unfolds `Lower`, the measure and the functions it calls by their proved equations (`unfold`);
- it adds what the author's lemmas say at each call whose value the context knows: a lemma is a K
  simplification rule, stated by `gen` as `Option.bind (f xs) k = rhs` (`mu(app(A, B)) =>
  mu(A) +Int mu(B)`, `mu(C) >=Int 0 => true`), and where `f as = some v` (a rule's premise, or a case
  below), the lemma at `as` is `k v = rhs`; where `f as = none`, it is usually `False` (a lemma that
  says the call has a value), which closes the case (`k2l_measure_facts`);
- it cases on each call the goal's values still bind (`k2l_case_call`), adding the lemmas' facts in
  each case;
- then arithmetic (`k2l_measure_arith`): the hooks in Lean's arithmetic (`k2l_arith`), then
  `k2l_int_arith` (each `if` split, the sign of each product whose factors are bounded, then
  `k2l_int_omega`, then `grind`, which normalizes the products a measure over repetition has,
  `max(M, 0) * (μ(B) + 1)`).
-/

namespace KPrelude.Measure

universe u

variable {α : Type u}

/-- A step from `c` to `c'` lowers the measure `μ`: defined at both, nonnegative at `c'`, smaller
there than at `c`. -/
def Lower (μ : α → Option Int) (c c' : α) : Prop :=
  ∃ v v', μ c = some v ∧ μ c' = some v' ∧ 0 ≤ v' ∧ v' < v

/-- The measure as a natural number (`0` where it is undefined or negative). -/
def nat (μ : α → Option Int) (c : α) : Nat :=
  ((μ c).getD 0).toNat

theorem nat_lt {μ : α → Option Int} {c c' : α} (h : Lower μ c c') : nat μ c' < nat μ c := by
  obtain ⟨v, v', hv, hv', h0, hlt⟩ := h
  simp only [nat, hv, hv', Option.getD_some]
  omega

/-- Every step lowers the measure: no infinite path starts anywhere. -/
theorem terminates {S : α → α → Prop} (μ : α → Option Int)
    (h : ∀ {c c' : α}, S c c' → Lower μ c c') (c : α) : Paths.Terminates S c :=
  Ends.terminates_of_measure (nat μ) (fun _ _ hs => nat_lt (h hs)) c

/-- Every step from a configuration satisfying a preserved `H` lowers the measure: no infinite path
starts where `H` holds. -/
theorem terminates_on {S : α → α → Prop} {H : α → Prop} (hH : Preserved S H)
    (μ : α → Option Int) (h : ∀ {c c' : α}, H c → S c c' → Lower μ c c') :
    ∀ c, H c → Paths.Terminates S c :=
  Ends.terminates_of_measure_on hH (nat μ) (fun _ _ hc hs => nat_lt (h hc hs))

/-- A terminal configuration reachable from `a` is the first one on the way: a configuration with a
step is not terminal. -/
theorem firstReach_of_star {S : α → α → Prop} {a b : α} (h : Star S a b) (hb : Terminal S b) :
    Paths.FirstReach S (Terminal S) a b := by
  induction h with
  | refl => exact .here hb
  | step hs _ ih => exact .step (fun t => t _ hs) hs (ih hb)

/-- From a configuration that terminates, a run reaches a first terminal configuration: a segment
of a language with no rule at its ends (a coroutine's `yield`) ends. -/
theorem exists_firstReach_terminal {S : α → α → Prop} {a : α} (h : Paths.Terminates S a) :
    ∃ b, Paths.FirstReach S (Terminal S) a b := by
  obtain ⟨b, hs, ht⟩ := Ends.exists_terminal_of_terminates h
  exact ⟨b, firstReach_of_star hs ht⟩

open Lean Meta Elab Tactic

/-- The call `x` of `Option.bind x k` (`@Option.bind α β x k`). -/
def bindCall? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Option.bind 4 then some (e.getArg! 2) else none

/-- A hypothesis `f as = some v` or `f as = none`, `f` a constant that is no constructor: its call. -/
def knownCall? (ty : Expr) : MetaM (Option Expr) := do
  let some (_, l, r) := ty.eq? | return none
  unless r.isAppOf ``Option.some || r.isAppOf ``Option.none do return none
  let .const f _ := l.getAppFn | return none
  if (← getEnv).isConstructor f then return none
  return some l

/-- The author's lemma `L : ∀ xs, Option.bind (f xs) k = rhs` at the call `t` (`f as`), when its
binders are all determined by `t`: the instance's proof. -/
def lemmaAt (L t : Expr) : MetaM (Option Expr) := do
  let (xs, _, body) ← forallMetaTelescopeReducing (← inferType L)
  let some (_, lhs, _) := body.eq? | return none
  let some x := bindCall? lhs | return none
  unless x.getAppFn == t.getAppFn do return none
  unless ← isDefEq x t do return none
  let p ← instantiateMVars (mkAppN L xs)
  if p.hasExprMVar then return none
  return some p

/-- Simplify the hypothesis `h` with the calls whose values the context knows (`f as = some v`,
`f as = none`) and the reductions of `Option.bind`: a fact stated over a call becomes one over its
value. Returns the goal, `none` when the fact is `False`. -/
def simpKnown (g : MVarId) (h : FVarId) : MetaM (Option MVarId) := g.withContext do
  let mut thms ← ({} : SimpTheorems).addConst ``Option.bind_some
  thms ← thms.addConst ``Option.bind_none
  thms ← thms.addConst ``Option.bind_fun_some
  thms ← thms.addConst ``Option.some.injEq
  for d in ← getLCtx do
    if d.isImplementationDetail || d.fvarId == h then continue
    if (← knownCall? (← instantiateMVars d.type)).isSome then
      thms ← thms.add (.fvar d.fvarId) #[] d.toExpr
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simpGoal g ctx #[← Simp.getSimprocs] (simplifyTarget := false) (fvarIdsToSimp := #[h])
  return r.map (·.2)

/-- `k2l_measure_facts [L, …]`: for each hypothesis `f as = some v` (or `none`) and each lemma `L`
about `f`, the lemma at `as` with the call's value put in and reduced (`k v = rhs`, or `False`, which
closes the goal). Repeated until no new fact appears: a fact may give a call's value. -/
syntax (name := measureFacts) "k2l_measure_facts" " [" ident,* "]" : tactic

@[tactic measureFacts] def evalMeasureFacts : Tactic := fun stx => do
  let ls ← stx[2].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  let mut seen : Array Expr := #[]
  let mut fuel := 32
  let mut progress := true
  while progress && fuel > 0 do
    progress := false
    fuel := fuel - 1
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let found ← g.withContext do
      let mut out : Array (Expr × Expr) := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let some t ← knownCall? (← instantiateMVars d.type) | continue
        for n in ls do
          let L ← mkConstWithFreshMVarLevels n
          let some p ← lemmaAt L t | continue
          let ty ← instantiateMVars (← inferType p)
          if seen.any (· == ty) then continue
          -- the call's value put in: rewrite the instance with the hypothesis
          let r ← g.rewrite ty d.toExpr
          out := out.push (ty, ← mkEqMP r.eqProof p)
      return out
    for (ty, p) in found do
      if seen.any (· == ty) then continue
      seen := seen.push ty
      if (← getGoals).isEmpty then return
      let g ← getMainGoal
      let nm ← mkFreshUserName `hm
      let (h, g') ← (← g.assert nm (← inferType p) p).intro nm
      match ← (try simpKnown g' h catch _ => pure (some g')) with
      | none => replaceMainGoal []; return
      | some g'' => replaceMainGoal [g'']
      progress := true

/-- `k2l_measure_case`: case on the value of a call of a partial function (a hook or a K function,
whose result type is `Option _`) in the goal, outside binders: a measure's value is a chain of binds
over the calls of its equations, and once a value is known the goal may state it directly
(`f as = some x`). The call is generalized in the goal and in the hypotheses that mention it (a
lemma's fact about it), with `hc : call = none` or `hc : call = some r` added. -/
elab "k2l_measure_case" : tactic => liftMetaTactic fun g => g.withContext do
  let env ← getEnv
  let tgt ← instantiateMVars (← g.getType)
  let partialFn (c : Name) : MetaM Bool := do
    let some ci := env.find? c | return false
    forallTelescopeReducing ci.type fun _ r => return r.isAppOfArity ``Option 1
  let cands ← IO.mkRef (#[] : Array Expr)
  tgt.forEach fun e => do
    if e.hasLooseBVars then return
    let .const f _ := e.getAppFn | return
    if env.isConstructor f || f == ``Option.bind || f == ``Option.some then return
    if (Lean.Meta.Match.Extension.getMatcherInfo? env f).isSome then return
    if ← partialFn f then
      unless (← isDefEq (← inferType e) (← inferType e)) do return
      if (← inferType e).isAppOfArity ``Option 1 then
        cands.modify fun a => if a.contains e then a else a.push e
  let some t := (← cands.get)[0]? | throwError "k2l_measure_case: no call of a partial function"
  let mut fvs := #[]
  for d in ← getLCtx do
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

/-- `k2l_measure_norm [e, …]`: the goal and every hypothesis but the known calls simplified with the
equations `e` (the measure's unfolding set), the known calls (`f as = some v`, `f as = none`) and the
reductions of `Option.bind`, so that every fact is over the values found so far. -/
syntax (name := measureNorm) "k2l_measure_norm" " [" ident,* "]" : tactic

@[tactic measureNorm] def evalMeasureNorm : Tactic := fun stx => do
  let us ← stx[2].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  liftMetaTactic fun g => g.withContext do
    let mut thms ← ({} : SimpTheorems).addConst ``Option.bind_some
    for n in [``Option.bind_none, ``Option.bind_fun_some, ``Option.some.injEq] do
      thms ← thms.addConst n
    for n in us do
      -- a definition (the measure's projections) is unfolded, a theorem rewrites
      thms ← if (← getEnv).find? n |>.any (·.isTheorem) then thms.addConst n
        else thms.addDeclToUnfold n
    let mut fvs := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← knownCall? (← instantiateMVars d.type)).isSome then
        thms ← thms.add (.fvar d.fvarId) #[] d.toExpr
      else if ← isProp d.type then
        fvs := fvs.push d.fvarId
    let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
    let (r, _) ← simpGoal g ctx #[← Simp.getSimprocs] (fvarIdsToSimp := fvs)
    return match r with
      | none => []
      | some (_, g') => [g']

/-- `k2l_measure_cells`: the rule's variables that stand for a cell or another value of one form
(`{ B }`, on the arity-indexed family too) taken apart, as the invariant tactic does
(`casesCells`): a measure's equations match the constructors inside (`loop(M, _)` holds a `{ B }`). -/
elab "k2l_measure_cells" : tactic => KPrelude.K2LPreserve.casesCells

/-- `k2l_measure_arith`: the obligation's arithmetic once the measure's values are known: the hooks
in Lean's arithmetic (`k2l_arith`, `maxInt` and `minInt` unfolded), then `k2l_int_arith` (each `if`
split, the sign of each product of nonnegative factors, `k2l_int_omega`, `grind`), on the
obligation or on each of its two parts. -/
macro "k2l_measure_arith" : tactic => `(tactic| (
  (try simp only [k2l_arith, IntHook.max, IntHook.min, decide_eq_true_eq, Option.some.injEq,
    exists_and_left, exists_eq_left', exists_eq', and_true, true_and] at *)
  first
  | k2l_int_arith
  | (refine ⟨?_, ?_⟩ <;> k2l_int_arith)))

/-- `k2l_measure [unfold] [lemmas]`: one rule's obligation `Step.Rel.r (Lower μ)` (module doc). -/
macro "k2l_measure" " [" us:ident,* "]" " [" ls:ident,* "]" : tactic =>
  `(tactic| (
    repeat intro
    k2l_measure_cells
    all_goals simp only [KPrelude.Measure.Lower] at *
    (try k2l_measure_norm [$us,*])
    all_goals k2l_measure_facts [$ls,*]
    all_goals (try k2l_measure_norm [$us,*])
    all_goals (repeat' (k2l_measure_case <;> (try k2l_measure_norm [$us,*]) <;>
      k2l_measure_facts [$ls,*] <;> (try k2l_measure_norm [$us,*])))
    all_goals k2l_measure_arith))

end KPrelude.Measure
