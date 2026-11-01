import KPrelude.Ends
import KPrelude.MeasureSum
import KPrelude.Invariant
import KPrelude.InvAttr
import KPrelude.InvTactic
import KPrelude.Tactic

/-!
# A measure that every step lowers (`gen --measure`, `direction.md` §5)

In a finite execution "every run ends" is termination of the step relation, and a measure that
every step lowers proves it (`Ends.terminates_of_measure`). The author writes the measure in K, as
a function from a cell to `Int` (K has no `Nat`), and `gen --measure NAME@CELL` states, per rule,
that the rule's step lowers it (`Lower`): where its value is defined at the source, it is defined at
the target, nonnegative there and below its value at the source. A strictly decreasing sequence of
nonnegative integers is finite, and a first configuration with a negative value has no step at all,
so `Lower` at every step gives a `Nat` measure that every step from a configuration where the
measure is defined lowers (`nat_lt`), definedness is preserved (`isSome_preserved`), and no infinite
run starts where the measure is defined (`terminates`, and under a preserved invariant
`terminates_on`). That the target's value is defined is part of each obligation, since K's `total`
is the author's claim, which k2lean states and never assumes. The source's is a hypothesis: a
measure over a cell map is a fold whose equations read a binding's key twice (a cell map binds each
element under its own id), so on a Lean map that binds an element under another key, which no run
builds but a rule's instance ranges over, it has no value (`MeasureSum`).

`k2l_measure [unfold] [lemmas] [sums] [weights]` proves one rule's obligation, `Step.Rel.r (Lower μ)`:
- it unfolds `Lower`, the measure and the functions it calls by their proved equations (`unfold`);
- it reads each sum over a map by its generated `iff` (`sums`, `Measure.F_eq`: defined exactly on a
  well-formed map whose bindings pass the fold's test with defined weights, and then `sumOf`), the
  measure's value taken apart into each fold's where it combines several (`F(M) +Int G(N)`), splits
  each map the rule matches or builds as `M₁ M₂` into its operands (the sum, the bindings'
  definedness, the well-formedness), and bounds each sum left over a map (the rest the rule leaves)
  below by `0`, its weight being nonnegative wherever it is defined (`weights`, `Measure.F_g_nonneg`,
  stated once by `gen` and proved by `k2l_measure_weight`: the weight unfolded to its rules' matches,
  split, the calls of functions with rule matchers unfolded and split in turn, each value left
  bounded by the lemmas) (`k2l_measure_sum`);
- it adds what the author's lemmas say at each call whose value the context knows: a lemma is a K
  simplification rule, stated by `gen` as `Option.bind (f xs) k = rhs` (`mu(app(A, B)) =>
  mu(A) +Int mu(B)`, `mu(C) >=Int 0 => true`), and where `f as = some v` (a rule's premise, or a case
  below), the lemma at `as` is `k v = rhs`; where `f as = none`, it is usually `False` (a lemma that
  says the call has a value), which closes the case (`k2l_measure_facts`);
- it cases on each call the goal's values still bind (`k2l_case_call`), adding the lemmas' facts in
  each case;
- then arithmetic (`k2l_measure_arith`): the hooks in Lean's arithmetic (`k2l_arith`), the values
  known by an equation substituted, then `k2l_int_arith` (each `if` split, the sign of each product
  whose factors are bounded, then `k2l_int_omega`, then `grind`, which normalizes the products a
  measure over repetition has, `max(M, 0) * (μ(B) + 1)`); where that fails, the calls of functions
  with rule matchers left in the hypotheses unfolded and split (`k2l_measure_calls`), and again.
-/

namespace KPrelude.Measure

universe u

variable {α : Type u}

/-- A step from `c` to `c'` lowers the measure `μ`: where it is defined at `c`, it is defined at `c'`,
nonnegative there and smaller than at `c`. -/
def Lower (μ : α → Option Int) (c c' : α) : Prop :=
  (μ c).isSome → ∃ v v', μ c = some v ∧ μ c' = some v' ∧ 0 ≤ v' ∧ v' < v

/-- The measure as a natural number (`0` where it is undefined or negative). -/
def nat (μ : α → Option Int) (c : α) : Nat :=
  ((μ c).getD 0).toNat

theorem nat_lt {μ : α → Option Int} {c c' : α} (h : Lower μ c c') (hc : (μ c).isSome) :
    nat μ c' < nat μ c := by
  obtain ⟨v, v', hv, hv', h0, hlt⟩ := h hc
  simp only [nat, hv, hv', Option.getD_some]
  omega

/-- Where the measure is defined, a step keeps it defined. -/
theorem isSome_preserved {S : α → α → Prop} {μ : α → Option Int}
    (h : ∀ {c c' : α}, S c c' → Lower μ c c') : Preserved S fun c => (μ c).isSome := by
  intro c c' hc hs
  obtain ⟨_, _, _, hv', _⟩ := h hs hc
  rw [hv']; rfl

/-- Every step lowers the measure: no infinite path starts where it is defined. -/
theorem terminates {S : α → α → Prop} (μ : α → Option Int)
    (h : ∀ {c c' : α}, S c c' → Lower μ c c') : ∀ c, (μ c).isSome → Paths.Terminates S c :=
  Ends.terminates_of_measure_on (isSome_preserved h) (nat μ) (fun _ _ hc hs => nat_lt (h hs) hc)

/-- Every step from a configuration satisfying a preserved `H` lowers the measure: no infinite path
starts where `H` holds and the measure is defined. -/
theorem terminates_on {S : α → α → Prop} {H : α → Prop} (hH : Preserved S H)
    (μ : α → Option Int) (h : ∀ {c c' : α}, H c → S c c' → Lower μ c c') :
    ∀ c, H c → (μ c).isSome → Paths.Terminates S c := fun c hc hs =>
  Ends.terminates_of_measure_on (H := fun c => H c ∧ (μ c).isSome)
    (fun c c' ⟨hc, hs⟩ hst => ⟨hH c c' hc hst, by
      obtain ⟨_, _, _, hv', _⟩ := h hc hst hs
      rw [hv']; rfl⟩)
    (nat μ) (fun _ _ ⟨hc, hs⟩ hst => nat_lt (h hc hst) hs) c ⟨hc, hs⟩

/-- Under `H`, a step from `c` to `c'` lowers the measure `μ`: where `H` holds at `c` and the measure
is defined there, it is defined at `c'` and smaller there. Nonnegativity is not part of it: under an
invariant it is a property of the invariant's configurations, stated once (`terminates_inv`'s
`hb`), not shown again at each rule's target. -/
def Dec (H : α → Prop) (μ : α → Option Int) (c c' : α) : Prop :=
  H c → (μ c).isSome → ∃ v v', μ c = some v ∧ μ c' = some v' ∧ v' < v

/-- Under a preserved `H` the measure is nonnegative where it is defined, and every step from a
configuration satisfying `H` lowers it (`Dec`): no infinite path starts where `H` holds and the
measure is defined. Along a run from there, `H` holds (`hH`) and the measure stays defined (`Dec`),
so it is nonnegative at both ends of every step (`hb`), and its `toNat` decreases. -/
theorem terminates_inv {S : α → α → Prop} {H : α → Prop} (hH : Preserved S H) (μ : α → Option Int)
    (hb : ∀ c, H c → (μ c).isSome → ∃ v, μ c = some v ∧ 0 ≤ v)
    (h : ∀ {c c' : α}, S c c' → Dec H μ c c') :
    ∀ c, H c → (μ c).isSome → Paths.Terminates S c := fun c hc hs =>
  Ends.terminates_of_measure_on (H := fun c => H c ∧ (μ c).isSome)
    (fun c c' ⟨hc, hs⟩ hst => ⟨hH c c' hc hst, by
      obtain ⟨_, _, _, hv', _⟩ := h hst hc hs
      rw [hv']; rfl⟩)
    (nat μ) (fun a b ⟨ha, hs⟩ hst => by
      obtain ⟨v, v', hv, hv', hlt⟩ := h hst ha hs
      obtain ⟨w, hw, h0⟩ := hb b (hH a b ha hst) (by rw [hv']; rfl)
      rw [hv', Option.some.injEq] at hw
      subst hw
      simp only [nat, hv, hv', Option.getD_some]
      omega)
    c ⟨hc, hs⟩

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
binders are all determined by `t`, and its instance binders (`[Hooks]`, which a lemma of a
definition with parameters takes even where `f` does not) by synthesis: the instance's proof. -/
def lemmaAt (L t : Expr) : MetaM (Option Expr) := do
  let (xs, bis, body) ← forallMetaTelescopeReducing (← inferType L)
  let some (_, lhs, _) := body.eq? | return none
  let some x := bindCall? lhs | return none
  unless x.getAppFn == t.getAppFn do return none
  unless ← isDefEq x t do return none
  for x in xs, bi in bis do
    if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
      let some i ← synthInstance? (← inferType x) | return none
      unless ← isDefEq x i do return none
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
    for n in [``Option.bind_none, ``Option.bind_fun_some, ``Option.some.injEq, ``Option.isSome_some,
        ``Option.isSome_none, ``Option.getD_some, ``Option.getD_none, ``eq_self_iff_true] do
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

/-- `k2l_measure_coll [unfold]`: under an invariant over every element of a collection (`EntriesOn Q
m`, the invariant at a rule's source), its facts at what the rule matches (`K2LPreserve.forwardColl`):
`Q (k, v)` at a matched binding, `EntriesOn Q r` at the rest, each normalized by the unfolding set
(`unfold`, which then holds the invariant's). Nothing where no such hypothesis is in the context. -/
syntax (name := measureColl) "k2l_measure_coll" " [" ident,* "]" : tactic

@[tactic measureColl] def evalMeasureColl : Tactic := fun stx => do
  let us : Array Ident := stx[2].getSepArgs.map (⟨·⟩)
  K2LPreserve.forwardColl (fun _ => do evalTactic (← `(tactic| try k2l_measure_norm [$[$us],*]))) 4

/-- `k2l_measure_cells`: the rule's variables that stand for a cell or another value of one form
(`{ B }`, on the arity-indexed family too) taken apart, as the invariant tactic does
(`casesCells`): a measure's equations match the constructors inside (`loop(M, _)` holds a `{ B }`). -/
elab "k2l_measure_cells" : tactic => KPrelude.K2LPreserve.casesCells

/-- `k2l_measure_arith`: the obligation's arithmetic once the measure's values are known: the hooks
in Lean's arithmetic (`k2l_arith`, with `maxInt` and `minInt` by `IntHook.max_eq` and `min_eq`),
then `k2l_int_arith` (each `if` split, the sign of each product of nonnegative factors,
`k2l_int_omega`, `grind`), on the obligation or, where it is a conjunction, on each of its two
parts (`And.intro`, which fails on anything else; an anonymous constructor would be elaborated
against the structure of an `Int` comparison, and its error logged rather than thrown). A call's
value known by an equation (`v = e`, from the author's lemma at the call) is substituted first, so
that the `if`s of `e` are the goal's. -/
macro "k2l_measure_arith" : tactic => `(tactic| (
  (try simp only [k2l_arith, IntHook.max_eq, IntHook.min_eq, decide_eq_true_eq, Option.some.injEq,
    exists_and_left, exists_eq_left', exists_eq', and_true, true_and] at *)
  (try subst_vars)
  first
  | k2l_int_arith
  | (apply And.intro <;> k2l_int_arith)))

/-- An identifier as a `simp` argument. -/
def simpArgOf (i : Ident) : MetaM K2LPreserve.SimpArg := do
  return ⟨(← `(Lean.Parser.Tactic.simpLemma| $i:ident)).raw⟩

/-- The K functions a weight's fact `h : g k v = some a` applies, each with its rules' matchers
(`withRules`); for a function with no rule matchers (a recursive one), the function alone. -/
def weightFuns (ty : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let acc ← IO.mkRef (#[] : Array Name)
  ty.forEach fun e => do
    let .const c _ := e.getAppFn | return
    if (← acc.get).contains c then return
    if env.contains (c ++ `rule1) then
      acc.modify (· ++ #[c])
  let mut fs ← acc.get
  if fs.isEmpty then
    if let some (_, l, _) := ty.eq? then
      if let .const c _ := l.getAppFn then
        if (env.find? c).any (·.isDefinition) then fs := #[c]
  let mut out := #[]
  for c in fs do
    out := out ++ (← K2LPreserve.withRules c)
  return out

/-- In each goal, the K functions with rule matchers (`withRules`: not recursive) that a hypothesis
not in `base` applies, unfolded to their rules' matches and those split (`splitHypMatches`); true
when a goal had one. -/
def unfoldCalls (base : Array FVarId) : TacticM Bool := do
  let env ← getEnv
  let mut any := false
  let mut out : Array MVarId := #[]
  for g in ← getGoals do
    if ← g.isAssigned then continue
    -- each hypothesis not in `base` with the functions it applies
    let hs ← g.withContext do
      let mut hs : Array (FVarId × Array Name) := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail || base.contains d.fvarId then continue
        let acc ← IO.mkRef (#[] : Array Name)
        (← instantiateMVars d.type).forEach fun e => do
          let .const c _ := e.getAppFn | return
          unless (← acc.get).contains c do
            if env.contains (c ++ `rule1) then acc.modify (·.push c)
        let fs ← acc.get
        unless fs.isEmpty do hs := hs.push (d.fvarId, fs)
      return hs
    setGoals [g]
    unless hs.isEmpty do
      any := true
      let mut g := g
      for (h, fs) in hs do
        for c in fs do
          for u in ← K2LPreserve.withRules c do
            g ← (try unfoldLocalDecl g h u catch _ => pure g)
      setGoals [g]
      K2LPreserve.splitHypMatches fun d => !base.contains d.fvarId
    out := out ++ (← getGoals).toArray
  setGoals out.toList
  return any

/-- `k2l_measure_weight [unfold] [lemmas]`: a weight is nonnegative wherever it is defined,
`∀ k v a, g k v = some a → 0 ≤ a`: the weight unfolded (`unfold`: its definition and the
projections it reads), the K functions it applies unfolded to their rules' matches and those split
(`splitHypMatches`, the cases that cannot hold refuted), then in each case the value is a rule's
right-hand side. A call that right-hand side makes to a function with rule matchers (not recursive:
`kw(I:Instr) => iw(I)`) is unfolded and split the same way, a few rounds, so what is left is calls
of recursive functions, bounded by the author's lemmas, and arithmetic. -/
syntax (name := measureWeight) "k2l_measure_weight" " [" ident,* "]" " [" ident,* "]" : tactic

/-- `k2l_measure_weight_on [unfold] [lemmas]`: a weight is nonnegative wherever it is defined at a
binding where an invariant over every element holds, `∀ k v a, Q (k, v) → g k v = some a → 0 ≤ a`
(`MapHook.sumOf_nonneg_on`'s premise): as `k2l_measure_weight`, with the binding's cells taken
apart (`casesCells`), so that the measure's projections and the invariant's read the same contents,
and the invariant's fact at the binding (`Q (k, v)`, unfolded by `unfold`) read by the arithmetic. -/
syntax (name := measureWeightOn) "k2l_measure_weight_on" " [" ident,* "]" " [" ident,* "]" : tactic

/-- `k2l_measure_weight`, and with `on` `k2l_measure_weight_on`. -/
def measureWeightCore (us ls : Array Ident) (on : Bool) : TacticM Unit := do
  let hw := mkIdent `k2l_w
  let hq := mkIdent `k2l_q
  let base ← (← getMainGoal).withContext do return (← getLCtx).getFVarIds
  let usA ← us.mapM (fun i => (simpArgOf i : TacticM _))
  if on then
    evalTactic (← `(tactic| intro _ _ _ $hq:ident $hw:ident))
    K2LPreserve.casesCells
    evalTactic (← `(tactic| all_goals (try simp only [$[$usA],*] at $hq:ident)))
  else
    evalTactic (← `(tactic| intro _ _ _ $hw:ident))
  evalTactic (← `(tactic| all_goals (try simp only [$[$usA],*] at $hw:ident)))
  let g ← getMainGoal
  let fs ← g.withContext do
    let some d := (← getLCtx).findFromUserName? `k2l_w | return #[]
    weightFuns (← instantiateMVars d.type)
  unless fs.isEmpty do
    let ids := fs.map mkIdent
    evalTactic (← `(tactic| unfold $[$ids]* at $hw:ident))
  -- one hypothesis split per goal and round: a weight's rules nest their matches (a K sequence,
  -- an injection, a constructor, a call), so more rounds than the default
  K2LPreserve.splitHypMatches (fun _ => true) (rounds := 12)
  -- the calls the cases make to functions with rule matchers, unfolded and split in turn
  for _ in [0:3] do
    unless ← unfoldCalls base do break
  evalTactic (← `(tactic| all_goals (try subst_vars)))
  evalTactic (← `(tactic| all_goals (try simp only [Option.some.injEq, reduceCtorEq] at *)))
  evalTactic (← `(tactic| all_goals (try subst_vars)))
  evalTactic (← `(tactic| all_goals k2l_measure_facts [$[$ls],*]))
  evalTactic (← `(tactic| all_goals k2l_measure_arith))

@[tactic measureWeight] def evalMeasureWeight : Tactic := fun stx =>
  measureWeightCore (stx[2].getSepArgs.map (⟨·⟩)) (stx[5].getSepArgs.map (⟨·⟩)) false

@[tactic measureWeightOn] def evalMeasureWeightOn : Tactic := fun stx =>
  measureWeightCore (stx[2].getSepArgs.map (⟨·⟩)) (stx[5].getSepArgs.map (⟨·⟩)) true

/-- `have n : ty := by tac` on the main goal, with `tac` run on a goal of its own: true when it closes
it, with no error logged and no `sorry` in the proof. An error inside a nested `by` is logged rather
than thrown, so a `have` whose proof fails would stand on `sorry`; here a failure restores the
state, so that the caller can try something else. -/
def haveBy (n : Name) (ty : Term) (tac : TSyntax `tactic) : TacticM Bool := do
  let g ← getMainGoal
  let errors : TacticM Nat := do
    return (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
  let e0 ← errors
  K2LPreserve.tryRec (g.withContext do
    let tyE ← Term.elabTermAndSynthesize ty (some (.sort .zero))
    let mv ← mkFreshExprSyntheticOpaqueMVar tyE
    let gs ← Tactic.run mv.mvarId! (evalTactic tac)
    let pf ← instantiateMVars mv
    unless gs.isEmpty && !pf.hasSorry && (← errors) == e0 do throwError "haveBy: not proved"
    let (_, g') ← g.note n pf tyE
    replaceMainGoal [g']
    pure true) (pure false)

/-- The sums `MapHook.sumOf g m` in `e`, outside binders: their weights and maps. -/
def sumAtoms (e : Expr) : MetaM (Array (Expr × Expr)) := do
  let n := (← getConstInfo ``MapHook.sumOf).type.getForallArity
  let acc ← IO.mkRef (#[] : Array (Expr × Expr))
  e.forEach fun s => do
    if s.isAppOfArity ``MapHook.sumOf n && !s.hasLooseBVars then
      let x := (s.getArg! (n - 2), s.getArg! (n - 1))
      unless (← acc.get).contains x do acc.modify (·.push x)
  acc.get

/-- The lemma of `ws` that bounds the weight `w`: its statement `∀ k v a, g k v = some a → 0 ≤ a`
with `g` the weight itself. -/
def weightLemma (ws : Array Ident) (w : Expr) : TacticM (Option Name) := do
  for i in ws do
    let n ← realizeGlobalConstNoOverload i
    let some c := (← getEnv).find? n | continue
    let ok ← (← getMainGoal).withContext do withNewMCtxDepth do
      -- the telescope takes the implication's hypothesis last: `g k v = some a`
      let (xs, _, _) ← forallMetaTelescope c.type
      let some h := xs.back? | return false
      let some (_, l, _) := (← instantiateMVars (← inferType h)).eq? | return false
      unless l.getAppNumArgs ≥ 2 do return false
      isDefEq l.appFn!.appFn! w
    if ok then return some n
  return none

/-- `k2l_measure_sum [sums] [unfold] [lemmas] [weights]`: the sums over a map in a rule's obligation (a
measure that adds a weight per binding, `MeasureSum`). Each fold's call is read by its generated
`iff` (`sums`: defined exactly where the map is well formed and every binding matches with a defined
weight, and then `sumOf g m`), and split along the maps the rule matches and builds, by the hooks
too (`K2LPreserve.sumSplit`, shared with invariants); and each sum left over a map (the rest) is
nonnegative, its weight being so: by the lemma of `weights` (`∀ k v a, g k v = some a → 0 ≤ a`)
whose weight is the sum's, else by `k2l_measure_weight` there, else, where an invariant holds at
every binding of the map (`EntriesOn Q m`, under the invariant), by `MapHook.sumOf_nonneg_on` and
`k2l_measure_weight_on`. -/
syntax (name := measureSum) "k2l_measure_sum" " [" ident,* "]" " [" ident,* "]" " [" ident,* "]"
  " [" ident,* "]" : tactic

@[tactic measureSum] def evalMeasureSum : Tactic := fun stx => do
  let ss : Array Ident := stx[2].getSepArgs.map (⟨·⟩)
  let us : Array Ident := stx[5].getSepArgs.map (⟨·⟩)
  let ls : Array Ident := stx[8].getSepArgs.map (⟨·⟩)
  let ws : Array Ident := stx[11].getSepArgs.map (⟨·⟩)
  if ss.isEmpty then return
  -- the folds' calls read as sums and split along the maps the rule matches and builds
  K2LPreserve.sumSplit ss
  if (← getGoals).isEmpty then return
  -- each sum left over a map is nonnegative: its weight is, wherever it is defined
  let g ← getMainGoal
  let atoms ← g.withContext do
    let mut a ← sumAtoms (← instantiateMVars (← g.getType))
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        for x in ← sumAtoms (← instantiateMVars d.type) do
          unless a.contains x do a := a.push x
    return a
  let mut weights : Array (Expr × Name) := #[]
  for (w, m) in atoms do
    if (← getGoals).isEmpty then return
    let hn ← match weights.find? (·.1 == w) with
      | some (_, n) => pure (some n)
      | none =>
        if let some l ← weightLemma ws w then
          weights := weights.push (w, l)
          pure (some l)
        else
          let n := Name.mkSimple s!"k2l_wn{weights.size}"
          let wt ← (← getMainGoal).withContext (Term.exprToSyntax w)
          let ok ← haveBy n (← `(∀ k v a, $wt k v = some a → 0 ≤ a))
            (← `(tactic| k2l_measure_weight [$[$us],*] [$[$ls],*]))
          weights := weights.push (w, n)
          pure (if ok then some n else none)
    match hn with
    | some hn =>
      let mt ← (← getMainGoal).withContext (Term.exprToSyntax m)
      K2LPreserve.tryRec (evalTactic (← `(tactic|
        have := MapHook.sumOf_nonneg $(mkIdent hn):ident $mt))) (pure ())
    | none =>
      -- an invariant over every element of the map (`EntriesOn Q m`, a measure under the
      -- invariant): the weight nonnegative where it holds
      let es ← (← getMainGoal).withContext do
        let mut es : Array (Expr × Expr) := #[]
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          if let some (q, m') := K2LPreserve.entriesOn? (← instantiateMVars d.type) then
            if m' == m then es := es.push (d.toExpr, q)
        return es
      for (e, q) in es do
        let (et, qt, wt) ← (← getMainGoal).withContext do
          return (← Term.exprToSyntax e, ← Term.exprToSyntax q, ← Term.exprToSyntax w)
        let hq := mkIdent `k2l_wq
        if ← haveBy `k2l_wq (← `(∀ k v a, $qt (k, v) → $wt k v = some a → 0 ≤ a))
            (← `(tactic| k2l_measure_weight_on [$[$us],*] [$[$ls],*])) then
          evalTactic (← `(tactic| have := MapHook.sumOf_nonneg_on $et $hq:ident))
          break
  -- what is left to show, part by part; the parts the source gives are its facts
  evalTactic (← `(tactic| try and_intros))
  evalTactic (← `(tactic| all_goals (try assumption)))

/-- `k2l_measure_calls`: each value `h : f x = some v` of a call to a function with rule matchers
(not recursive: `iw(I)` at a variable instruction), unfolded to its rules' matches and those split
(`unfoldCalls`), so that the value is a rule's right-hand side; fails when there is none. -/
elab "k2l_measure_calls" : tactic => do
  let g ← getMainGoal
  let env ← getEnv
  let base ← g.withContext do
    let mut base : Array FVarId := #[]
    for d in ← getLCtx do
      let call := match (← instantiateMVars d.type).eq? with
        | some (_, l, r) =>
          r.isAppOfArity ``Option.some 2 && (match l.getAppFn with
            | .const c _ => env.contains (c ++ `rule1)
            | _ => false)
        | none => false
      unless call do base := base.push d.fvarId
    return base
  unless ← unfoldCalls base do throwError "k2l_measure_calls: no call to unfold"

/-- `k2l_measure [unfold] [lemmas] [sums] [weights]`: one rule's obligation `Step.Rel.r (Lower μ)` (module doc). -/
macro "k2l_measure" " [" us:ident,* "]" " [" ls:ident,* "]" " [" ss:ident,* "]"
    " [" ws:ident,* "]" : tactic =>
  `(tactic| (
    repeat intro
    k2l_measure_cells
    all_goals (try simp only [KPrelude.Measure.Lower, KPrelude.Measure.Dec] at *)
    (try k2l_measure_norm [$us,*])
    all_goals (try k2l_measure_coll [$us,*])
    all_goals k2l_measure_sum [$ss,*] [$us,*] [$ls,*] [$ws,*]
    all_goals (try k2l_measure_norm [$us,*])
    all_goals k2l_measure_facts [$ls,*]
    all_goals (try k2l_measure_norm [$us,*])
    all_goals (repeat' (k2l_measure_case <;> (try k2l_measure_norm [$us,*]) <;>
      k2l_measure_facts [$ls,*] <;> (try k2l_measure_norm [$us,*])))
    all_goals first
      | k2l_measure_arith
      | (k2l_measure_calls; all_goals (try subst_vars); all_goals k2l_measure_facts [$ls,*]
         all_goals (try k2l_measure_norm [$us,*]); all_goals k2l_measure_arith)))

end KPrelude.Measure
