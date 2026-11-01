import KPrelude.Invariant
import KPrelude.InvAttr
import KPrelude.Hooks
import KPrelude.EqBase
import KPrelude.FamilyCases
import KPrelude.InvDisjoint
import KPrelude.MeasureSum

/-!
# `k2l_preserve`: one case per rule, closed generically or left tagged by the rule

`k2l_preserve` proves a goal `Preserved S P` where `S` is an inductive relation (a generated
`Step`). It introduces the step, reverts `P c`, and does `cases` on the step: one goal
`P lhs → P rhs` per `Step` constructor, tagged with the constructor's name (`«CALC.var»`).
On each goal it runs, in order, until one closes the goal completely:

1. *untouched*: unfold `P` and `exact` the hypothesis (a rule that does not touch the cells
   `P` reads keeps it as it is; for `OnCell proj Q`, `proj lhs` and `proj rhs` reduce to the
   same cell);
2. *compute*, only with `split [f, …]`: simp with the unfolding set and the hypotheses; if that
   does not close the goal, case on the first application of one of the functions `f` in the
   goal (with an equation, and on enumeration-typed fields of the result) and repeat, at most
   `fuel` cases deep (default 5);
2b. *sums*, only with `sums [F_eq, …]`: each sum over a map that `P` reads (`MeasureSum`: a fold
   `F(.Map) => 0`, `F((K |-> V) R) => g(K, V) +Int F(R)`) is read through its generated `iff`
   (`F m = some s` exactly where `m` is well formed and every binding matches with a defined
   weight, and then `s = sumOf g m`), each map the rule matches or builds split into its operands
   down to the bindings it writes (`k2l_sum_split`), and what is left closed by the arithmetic of
   5: the sums of the rest the rule leaves are atoms on both sides (a transfer between two
   bindings conserves the total whatever the amount);
3. *collections*: substitute the rule's equations `x = t` (a list pattern binds its list so);
   split conjunctions; add the facts read off the rule's matched collections
   (for `EntriesOn Q m` and a match `concat a b = some m`: `Q (k, v)` for an operand
   `element k v`, `EntriesOn Q x` for another operand `x`, each normalized by the unfolding set,
   for up to 4 rounds, so the invariant of a matched `<thread>` of a cell map becomes facts about
   its cells); then close each conjunct from the hypotheses or by `apply` of a `@[k2l_coll]` lemma
   (a predicate on keys, values or entries kept by `update`, `remove`, a map pattern, ...), the
   lemma's premises by the hypotheses or by simp; a goal no lemma applies to is normalized by the
   unfolding set and attacked again (at most twice on a path: `Q (k, v)` of a rebuilt element
   unfolds to goals on the collections inside it). Where such a predicate applies a K function
   that looks a value up (`M[K] orDefault D`, `M[K]`) to a map the rule matches or builds as
   `K |-> V REST` (twoparam's outputs behind their process's count in `<procs>`), the closer
   first runs with the lookups in each such map (`V` at `K`, `REST` elsewhere, the default in
   `REST` at `K`: `InvColl`'s `lookupOrDefault_of_concat_element` and its group) and, at a
   binding whose fact applies a K function to its key or value, that function's matches split
   in the fact (which binds the key to the pattern of the case that holds and refutes the
   others), the lookups rewritten, the goal's `if`s split, and the goals left closed by a fact,
   a refutation or arithmetic (`3b`); 3 as above runs when that fails;
4. *simp*: `simp_all` with the unfolding set; failing that, the same on each branch of the
   disjunctions among the rule's hypotheses (at most three split along a path), which an
   invariant with `orBool` or `impliesBool` at its top leaves (`B impliesBool hasZero(L)` is
   `b = false ∨ ElemsSome Q L`), each branch closed by `simp_all` or then by the arithmetic of 5:
   a hypothesis `A ∨ B` proves the goal when each branch does;
5. *arithmetic*: rewrite the hypotheses and the goal with the unfolding set and the
   `@[k2l_arith]` lemmas, which state the `Int` and `Bool` hooks in Lean's arithmetic
   (`IntHook.add a b` is `a + b`, `IntHook.ge a b = true` is `a ≥ b`), then `omega` on what
   is left (nothing, when the rewriting alone proves the goal: a test of a constant). The same
   step ends the leaf discharger of 3, so a conjunct such as the count test `0 ≤ N + 1` of a
   rebuilt map entry, from the matched entry's `0 ≤ N`, is closed there;
6. *injections*: for a variable `x` of the rule that is the argument of a generated injection
   `inj_S_T x` in the goal (a definition by cases on `x`, which blocks every function that
   matches on its result, such as `f (inj_Expr_KItem HOLE)` in a heating rule), `cases x`,
   reduce the injection on each constructor, and run 1–6 on each case; at most two such splits
   along one path. A case split is complete, so the cases together prove the rule's goal.

Before 2–6, the hypotheses that were in context before `k2l_preserve` (and are not named in its
simp list) are cleared, so that `simp [*]` and `simp_all` see only the rule's own hypotheses;
a residual goal has them back. Also before 2–6, a hypothesis `proj_A_B y = some x` of the rule (a sort projection, from a sorted
variable of the rule) is rewritten to `y = inj_B_A x` by the generated lemma `proj_eq_some_A_B`
when it exists, and substituted.

A goal that none of them closes is restored to its state right after `cases`, so the residual
goal of rule `r` is exactly `P lhs → P rhs` with `r`'s variables and side conditions in context,
and is addressed with `case r x₁ … xₙ => …`. The tactic logs how many rules it closed and the
names of the others.

*Per-case mode.* On a goal `Step.Case.r P` (one hypothesis of a generated `Step.preserves_of`,
`{ns}/Preserves.lean`), `k2l_preserve` unfolds the case, introduces the rule's variables and side
conditions under their own names, and runs the same closers on `P lhs → P rhs`. A goal it cannot
close is left in that state, tagged `r`, and the tactic logs
`k2l_preserve: rule r not closed; …`. So `apply Step.preserves_of` followed by
`all_goals k2l_preserve` closes what it can and leaves the other rules as named goals. The
per-case mode logs nothing when it closes the case, so the `N of M rules closed` lines of the
`Preserved` mode are the only counts in a build log.

*Hand mode* (kind 2 invariants, written in Lean). `k2l_preserve … hand NS` on `Preserved S P`
applies the generated `S.preserves_of` (`{ns}/Preserves.lean`), which leaves one goal
`Step.Case.r P` per rule. For rule `r`, when the constant `NS.r` exists (with `NS` read as
written, then relative to the enclosing namespaces), the goal is closed by `apply NS.r`: a
hand-written theorem `NS.r : Step.Case.r P` (its parameters are unified with `P`'s). Otherwise
the per-case closers run on it. The tactic logs
`k2l_preserve: N of M rules closed; hand: [...]; open: [...]`, where `N` counts the rules closed
by the closers, `hand` the rules taken from `NS`, and `open` the rules left as goals (tagged by
the rule, with its variables introduced). A hand case whose statement does not unify with the
rule's case is an error naming it, and its rule is left open. Because `NS.r` is stated by
reference to the generated `Step.Case.r`, a K edit to rule `r` changes the statement the hand
proof must prove, and so reopens that hand case and no other.

*Heartbeats.* In every mode, each rule's closers run with a fresh heartbeat count and the budget
`k2l.preserve.maxHeartbeats` (by default `maxHeartbeats`), as `maxHeartbeats` bounds one per-case
theorem of a kind 1 `Invariants.lean`, so a definition with many rules (SIMPLE's 169) does not
need a larger limit per rule, and `all_goals k2l_preserve` after `apply Step.preserves_of` bounds
each rule as the `Preserved` mode does (with the theorem's count, a rule's budget would be what the
rules before it left). The elaboration of the proof after the tactic counts every rule's
heartbeats, so a proof with many rules sets `maxHeartbeats 0` and bounds the rules by
`k2l.preserve.maxHeartbeats`. A closer that reaches the budget (a runtime exception, which
`try … catch` rethrows) leaves its rule open, restored, with
the log line `k2l_preserve: rule r reached the heartbeat limit …`; the other rules are still
attempted, and in the per-case mode the case is reported not closed. A per-case theorem has
spent its whole budget by then, so its elaboration after the tactic times out too (a second
error, at the theorem); the log line names the rule. A closer step that reaches the recursion-depth
limit (`maxRecDepth`, the other runtime exception) fails like any other step (`tryRec`).

The unfolding set is: the head constant of `P` (for `OnCell proj Q`, also the heads of `proj`
and `Q`; for `fun c => A c ∧ B c`, the heads of `A` and `B`), the `@[k2l_pres]` simp set, and
the lemmas given in `[…]`.

Syntax: `k2l_preserve [simp lemmas]? (split [f, …])? (sums [F_eq, …])? (fuel n)? (hand NS)?`.
-/

namespace KPrelude

namespace K2LPreserve

open Lean Meta Elab Tactic

/-- The definitions an invariant's statement is made of, to unfold. -/
partial def predHeads (P : Expr) : MetaM (Array Name) := do
  let P ← instantiateMVars P
  match P with
  | .lam _ _ b _ => body b
  | _ => app P
where
  isDef (n : Name) : MetaM Bool := do
    return match (← getEnv).find? n with
      | some (.defnInfo _) => true
      | _ => false
  app (P : Expr) : MetaM (Array Name) := do
    match P.getAppFn with
    | .const n _ =>
      if n == ``KPrelude.OnCell then
        let args := P.getAppArgs
        let mut acc := #[n]
        if h : 3 < args.size then
          acc := acc ++ (← predHeads args[2]) ++ (← predHeads args[3])
        return acc
      else if ← isDef n then return #[n] else return #[]
    | _ => return #[]
  body (b : Expr) : MetaM (Array Name) := do
    if b.isAppOfArity ``And 2 || b.isAppOfArity ``Or 2 || b.isAppOfArity ``Iff 2 then
      return (← body b.appFn!.appArg!) ++ (← body b.appArg!)
    match b.getAppFn with
    | .const n _ =>
      if n == ``KPrelude.OnCell then app (b.lowerLooseBVars 1 1)
      else if ← isDef n then return #[n] else return #[]
    | _ => return #[]

/-- The identifiers occurring in a piece of syntax. -/
partial def identsOf (s : Syntax) : Array Name :=
  if s.isIdent then #[s.getId] else s.getArgs.foldl (fun acc a => acc ++ identsOf a) #[]

abbrev SimpArg := TSyntax [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
  `Lean.Parser.Tactic.simpLemma]

def simpArgOfName (n : Name) : MetaM SimpArg := do
  let stx ← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  return ⟨stx.raw⟩

/-- Check that every name in the simp list of `k2l_preserve` denotes something `simp` can use: a
hypothesis of the goal's context, a global constant (a theorem, a definition to unfold, a
simproc), or a simp set (`k2l_pres`). The closers run inside `try`, where `simp` failing on an
unknown name would only make the unfolding set weaker; so an unknown name is an error here,
before any closer runs, and the error names it. Terms other than identifiers are left to `simp`. -/
def checkSimpNames (g : MVarId) (args : Array SimpArg) : TacticM Unit := g.withContext do
  for a in args do
    let t : Syntax :=
      if a.raw.isOfKind ``Lean.Parser.Tactic.simpLemma then a.raw[2]
      else if a.raw.isOfKind ``Lean.Parser.Tactic.simpErase then a.raw[1]
      else Syntax.missing
    unless t.isIdent do continue
    let n := t.getId
    if (← getLCtx).findFromUserName? n |>.isSome then continue
    -- a name written in a macro (`k2l_inv`) carries the macro's scopes; global names and simp
    -- sets are resolved without them, as `simp` resolves them
    let n' := n.eraseMacroScopes
    -- a constant named exactly (not a constant followed by field accesses)
    if (← resolveGlobalName n').any (·.2.isEmpty) then continue
    if (← getSimpExtension? n').isSome then continue
    if (← Simp.getSimprocExtension? n').isSome then continue
    throwErrorAt t "k2l_preserve: unknown name `{n'}` in the simp list (not a hypothesis, a constant or a simp set)"

/-- `x`, or `h` from the state before `x` when `x` fails, the recursion-depth limit
(`maxRecDepth`) included. That limit is a runtime exception, which `try … catch` rethrows, so
without this a closer step that recurses too deeply (a unification or a simp call on a large
term) would end `k2l_preserve` with an error instead of failing like any other step, and the
steps after it would not be tried. The heartbeat limit and interrupts are still rethrown: the
heartbeat limit leaves the whole rule open (`closeRule`), since every step after it would reach
it too. -/
def tryRec {α : Type} (x : TacticM α) (h : TacticM α) : TacticM α := do
  let s ← saveState
  tryCatchRuntimeEx x fun e => do
    if e.isMaxHeartbeat || e.isInterrupt then throw e
    s.restore
    h

/-- Run `tac` on the main goal; true when it closes every goal it produced. Restores the state
otherwise. -/
def closes (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  let ok ← tryRec (do evalTactic tac; pure (← getGoals).isEmpty) (pure false)
  unless ok do s.restore
  return ok

/-- Rewrite each hypothesis `proj_A_B y = some x` with the generated `proj_eq_some_A_B`, then
substitute. -/
def projToEq : TacticM Unit := do
  let lems ← withMainContext do
    let mut acc : Array Name := #[]
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, l, r) := ty.eq? | continue
      unless r.isAppOfArity ``Option.some 2 do continue
      let .const fn _ := l.getAppFn | continue
      let last := fn.getString!
      unless last.startsWith "proj_" do continue
      let lem := fn.getPrefix ++ Name.mkSimple ("proj_eq_some_" ++ (last.drop 5))
      if (← getEnv).contains lem && !acc.contains lem then acc := acc.push lem
    return acc
  unless lems.isEmpty do
    let args : Array SimpArg ← lems.mapM fun n => (simpArgOfName n : TacticM SimpArg)
    tryRec (evalTactic (← `(tactic| simp only [$args,*] at *))) (pure ())
    tryRec (evalTactic (← `(tactic| subst_vars))) (pure ())

/-- Is `ty` an enumeration type (an inductive whose constructors have no fields)? -/
def isEnumType (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  let .const n _ := ty.getAppFn | return false
  let some (.inductInfo info) := (← getEnv).find? n | return false
  if info.numIndices != 0 then return false
  for c in info.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? c | return false
    if ci.numFields != 0 then return false
  return true

/-- On the arity-indexed family (design.md §2.1), an enumeration sort is a family term whose value
forms all have no arguments: the cases of `x` when that holds (`familyCases`), else none. -/
def familyEnumCases (g : MVarId) (x : FVarId) : MetaM (Option (Array MVarId)) := do
  let fam ← g.withContext do
    return (← whnfR (← x.getType)).getAppFn.constName?.any (isFamilyName (← getEnv))
  unless fam do return none
  let s ← saveState
  try
    let cs ← familyCases g x
    if cs.all (·.2.isEmpty) then return some (cs.map (·.1)) else s.restore; return none
  catch _ => s.restore; return none

/-- On the arity-indexed family `fam` (design.md §2.1): whether the sort whose tag is `t` (a tag
constructor) has exactly one value form, as a K sort with one constructor does: one value of one
enumeration `Ck t`, no leaf injection (`hasLeaves t` is `false`), and no builtin carrier or
collection constructor at `t`. -/
def familyOneForm (fam : Name) (t : Expr) : MetaM Bool := do
  let some (.inductInfo iv) := (← getEnv).find? fam | return false
  let mut n := 0
  for c in iv.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? c | return false
    let .str _ cs := c | return false
    if cs.startsWith "c" && (cs.drop 1).toNat?.isSome then
      -- `ck {s} (c : Ck s) …`: the values of `Ck t`
      let k ← forallTelescope ci.type fun as _ => do
        if as.size < 2 then return none
        let e ← whnfD ((← inferType as[1]!).replaceFVar as[0]! t)
        let .const en _ := e.getAppFn | return none
        let some (.inductInfo ev) := (← getEnv).find? en | return none
        return if ev.numIndices == 0 then some ev.ctors.length else none
      let some k := k | return false
      n := n + k
    else if cs == "inj" then
      -- `inj {s} (hs : hasLeaves s = true) …`: a form when `hasLeaves t` is not `false`
      let leaves ← forallTelescope ci.type fun as _ => do
        if as.size < 2 then return true
        let some (_, lhs, _) := ((← inferType as[1]!).replaceFVar as[0]! t).eq? | return true
        return !(← whnfD lhs).isConstOf ``Bool.false
      if leaves then return false
    else
      -- a builtin carrier's or a collection's constructor, at its own tag
      let r ← forallTelescope ci.type fun _ r => do
        if r.isApp then return some (← whnfD r.appArg!) else return none
      if r == some t then return false
  return n == 1

/-- Case each variable whose type has one constructor and no indices (an inductive type), or that is a term of the arity-indexed family at a sort with one value form
(`familyOneForm`, split by `familyCases`): the variable is that constructor applied to fresh
variables, so the split is complete, and the rule's terms then show the cell's content, which
equations matching inside the cell need (SIMPLE's frames save a `<control>` fragment whose
`<xstack>` is a rule variable). A constructor with an argument of its own sort is not split (the
splits would not end). -/
def casesCells : TacticM Unit := do
  let mut oneForm : Std.HashMap Name Bool := {}
  for _ in [0:64] do
    let g ← getMainGoal
    let mut pick : Option (FVarId × Option Expr) := none
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      let ty ← g.withContext do whnfR (← instantiateMVars d.type)
      let .const n _ := ty.getAppFn | continue
      if isFamilyName (← getEnv) n then
        -- the family: a sort index that computes to a tag with one value form
        unless ty.getAppNumArgs == 1 do continue
        let t ← g.withContext do whnfD ty.appArg!
        let .const tn _ := t.getAppFn | continue
        let ok ← match oneForm[tn]? with
          | some b => pure b
          | none => do
            let b ← g.withContext (familyOneForm n t)
            oneForm := oneForm.insert tn b
            pure b
        if ok then pick := some (d.fvarId, some t); break
        continue
      let some (.inductInfo info) := (← getEnv).find? n | continue
      if info.numIndices != 0 || info.ctors.length != 1 then continue
      -- not a class instance (`[Hooks]`): every generated statement is stated over the instance,
      -- and a lemma with an instance argument (a K function's equation) does not apply where the
      -- instance is replaced by its fields
      if d.binderInfo.isInstImplicit || isClass (← getEnv) n then continue
      -- not a type whose constructor holds a value of the type itself (the split would not end)
      let some (.ctorInfo ci) := (← getEnv).find? info.ctors[0]! | continue
      if ← g.withContext do forallTelescope ci.type fun as _ => as.anyM fun a => do
          return (← inferType a).getAppFn.isConstOf n then continue
      if ← g.withContext (isProp ty) then continue
      pick := some (d.fvarId, none); break
    let some (x, t?) := pick | return
    match t? with
    | none =>
      let gs ← g.cases x
      setGoals (gs.map (·.mvarId)).toList
    | some t =>
      let s ← saveState
      let gs ← try familyCases g x catch _ => pure #[]
      let selfArg ← match gs with
        | #[(sg, args)] => sg.withContext do
          args.anyM fun a => do
            let aty ← whnfR (← inferType a)
            if aty.getAppNumArgs == 0 then return false
            return (← whnfD aty.appArg!) == t
        | _ => pure true
      if selfArg then
        s.restore
        if let .const tn _ := t.getAppFn then oneForm := oneForm.insert tn false
      else
        setGoals (gs.map (·.1)).toList

/-- Split conjunctions among the hypotheses. -/
def splitAnds : TacticM Unit := do
  tryRec (liftMetaTactic fun g => return [← g.casesAnd]) (pure ())

/-- Split the disjunctions among the hypotheses of each goal, and the conjunctions of each branch,
at most `n` disjunctions along a path. -/
partial def splitOrs (n : Nat) : TacticM Unit := do
  if n = 0 then return
  let mut out := #[]
  for g in ← getGoals do
    let h? ← g.withContext do
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        if (← instantiateMVars d.type).isAppOfArity ``Or 2 then return some d.fvarId
      return none
    match h? with
    | none => out := out.push g
    | some h =>
      for sg in ← g.cases h do
        setGoals [sg.mvarId]
        splitAnds
        splitOrs (n - 1)
        out := out ++ (← getGoals)
  setGoals out.toList

/-- `EntriesOn Q m` (a `KPrelude.MapHook.EntriesOn` application): `(Q, m)`. -/
def entriesOn? (ty : Expr) : Option (Expr × Expr) :=
  let n := ty.getAppNumArgs
  if ty.isAppOf `KPrelude.MapHook.EntriesOn && n ≥ 2 then some (ty.getArg! (n - 2), ty.getArg! (n - 1))
  else none

/-- The K functions `c` (those with a generated `c.rule1`) applied in `e` to a local variable or a
component of one. -/
def kFunsOnVars (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let acc ← IO.mkRef (#[] : Array Name)
  e.forEach fun s => do
    let .const c _ := s.getAppFn | return
    unless env.contains (c ++ `rule1) do return
    -- a variable, or a component of one (`p.1` of a binding `p`)
    let onVar (a : Expr) : Bool := a.isFVar ||
      ((a.isAppOfArity ``Prod.fst 3 || a.isAppOfArity ``Prod.snd 3) && a.appArg!.isFVar) ||
      (match a with | .proj _ _ b => b.isFVar | _ => false)
    unless s.getAppArgs.any onVar do return
    unless (← acc.get).contains c do acc.modify (·.push c)
  acc.get

/-- The K function `c` and the matchers of its rules (`c.rule1`, …): what unfolds a call of it to
its rules' matches. -/
def withRules (c : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut us := #[c]
  let mut i := 1
  while env.contains (c ++ Name.mkSimple s!"rule{i}") do
    us := us.push (c ++ Name.mkSimple s!"rule{i}")
    i := i + 1
  return us

/-- In every goal, split the matches of the hypotheses `keep` admits, then those of what each split
leaves (a match on the scrutinee of a match the split generalized), up to `rounds` times; a case
that `contradiction` closes is dropped. -/
def splitHypMatches (keep : LocalDecl → Bool) (rounds : Nat := 8) : TacticM Unit := do
  for _ in [0:rounds] do
    let mut out : Array MVarId := #[]
    let mut progress := false
    for g in ← getGoals do
      let r ← g.withContext do
        for d in (← getLCtx) do
          if d.isImplementationDetail || !keep d then continue
          let ty ← instantiateMVars d.type
          unless ← isProp ty do continue
          let env ← getEnv
          unless (ty.find? fun e => (isMatcherAppCore? env e).isSome).isSome do continue
          if let some gs ← Lean.Meta.splitLocalDecl? g d.fvarId then return some gs
        return none
      match r with
      | some gs =>
        progress := true
        for g' in gs do
          let c ← tryRec (do setGoals [g']; evalTactic (← `(tactic| contradiction)); pure true) (pure false)
          unless c do out := out.push g'
      | none => out := out.push g
    setGoals out.toList
    unless progress do break

/-- Closer 3b's leaf: the goal `Q' p` under `hp : Q p`, the last two locals, for a binding `p`
whose test the unfolding set does not decide (it matches on the binding's key: `taken(o(P, M),
PS)` and an `owise` case). The binding is split into its key and value; each K function the fact
applies to one of them is unfolded, in the fact and the goal, to the matches of its rules; the
matches of the fact are split (`split at`), which binds the key to the pattern of the case the
fact holds in and refutes the others; then the facts and the goal are normalized with `U`, which
holds the lookups of the rule's matched maps (`forwardLookups`), and the `if`s of the goal are
split. A goal left that is a fact, refuted by one, or arithmetic over them is closed here; the
others go back to the collections closer. -/
partial def testLeaf (U : Array SimpArg) : TacticM Unit := do
  let simpNamed (U : Array SimpArg) (names : Array Name) : TacticM Unit := do
    for n in names do
      if (← getGoals).isEmpty then return
      let present ← (← getMainGoal).withContext do return ((← getLCtx).findFromUserName? n).isSome
      if present then
        tryRec (evalTactic (← `(tactic| simp only [$U,*] at $(mkIdent n):ident))) (pure ())
    if (← getGoals).isEmpty then return
    tryRec (evalTactic (← `(tactic| simp only [$U,*]))) (pure ())
  -- the binding's fact named, the binding split
  liftMetaTactic fun g => do
    let ids := (← g.getDecl).lctx.getFVarIds
    let some hp := ids.back? | return [g]
    let g ← g.rename hp `k2l_hp
    let some p := ids.pop.back? | return [g]
    if (← whnfR (← p.getType)).isAppOf ``Prod then
      return (← g.cases p).toList.map (·.mvarId)
    return [g]
  let hpId := mkIdent `k2l_hp
  tryRec (evalTactic (← `(tactic| (try dsimp only at $hpId:ident ⊢); (try simp only [$U,*] at $hpId:ident)))) (pure ())
  if (← getGoals).isEmpty then return
  -- the K functions the fact applies to the key or the value: their rules' matches
  let g ← getMainGoal
  let fs ← g.withContext do
    let some d := (← getLCtx).findFromUserName? `k2l_hp | return #[]
    kFunsOnVars (← instantiateMVars d.type)
  if fs.isEmpty then return
  let mut us : Array Name := #[]
  for c in fs do
    us := us ++ (← withRules c)
  let base ← g.withContext do return (← getLCtx).getFVarIds
  let ua : Array SimpArg ← us.mapM (fun n => simpArgOfName n)
  evalTactic (← `(tactic| simp only [$ua,*] at $hpId:ident ⊢))
  if (← getGoals).isEmpty then return
  -- split the matches of the fact, then of what each split leaves, refuting the cases that hold
  -- no `true`
  splitHypMatches fun d => !base.contains d.fvarId || d.userName == `k2l_hp
  -- the facts the splits left, named; the lookups rewritten; the `if`s of the goal split
  let mut out : Array MVarId := #[]
  for g in ← getGoals do
    setGoals [g]
    tryRec (evalTactic (← `(tactic| try subst_vars))) (pure ())
    if (← getGoals).isEmpty then continue
    let g ← getMainGoal
    let (g, hs) ← g.withContext do
      let mut g := g
      let mut hs : Array Name := #[]
      let mut i := 0
      for d in (← getLCtx) do
        if d.isImplementationDetail || base.contains d.fvarId then continue
        unless ← isProp d.type do continue
        let n := Name.mkSimple s!"k2l_t{i}"
        g ← g.rename d.fvarId n
        hs := hs.push n
        i := i + 1
      return (g, hs)
    setGoals [g]
    let names := hs.push `k2l_hp
    simpNamed U names
    -- each `if` of the goal: its two cases, the condition's equation substituted
    for _ in [0:4] do
      let mut next : Array MVarId := #[]
      for g in ← getGoals do
        let before ← g.withContext do return (← getLCtx).getFVarIds
        match ← tryRec (Lean.Meta.splitTarget? g) (pure none) with
        | none => next := next.push g
        | some gs =>
          for g' in gs do
            -- the case's condition, named, rewrites the same condition in the facts
            let (g', cs) ← g'.withContext do
              let mut g' := g'
              let mut cs : Array Name := #[]
              for d in (← getLCtx) do
                if d.isImplementationDetail || before.contains d.fvarId then continue
                unless ← isProp d.type do continue
                let n := Name.mkSimple s!"k2l_c{cs.size}"
                g' ← g'.rename d.fvarId n
                cs := cs.push n
              return (g', cs)
            setGoals [g']
            tryRec (evalTactic (← `(tactic| (try injections); try subst_vars))) (pure ())
            if (← getGoals).isEmpty then continue
            let mut Uc := U
            for c in cs do
              let present ← (← getMainGoal).withContext do return ((← getLCtx).findFromUserName? c).isSome
              if present then Uc := Uc.push ⟨(← `(Lean.Parser.Tactic.simpLemma| $(mkIdent c):ident)).raw⟩
            simpNamed Uc names
            next := next ++ (← getGoals).toArray
      setGoals next.toList
    -- each goal left: the fact itself, or arithmetic on the facts the leaf named
    for g in ← getGoals do
      setGoals [g]
      if ← closes (← `(tactic| first | assumption | contradiction)) then continue
      let ua : Array SimpArg := #[⟨(← `(Lean.Parser.Tactic.simpLemma| k2l_arith)).raw⟩]
      let s ← saveState
      simpNamed ua names
      if (← getGoals).isEmpty then continue
      if ← closes (← `(tactic| omega)) then continue
      s.restore
      out := out.push g
  setGoals out.toList

/-- The *collections* closer: conjunctions, hypotheses, `@[k2l_coll]` lemmas, and a
discharger for the leaves. When no lemma applies to a goal, it is normalized by `norm` (the
unfolding set, `simp only`) and the closer starts again on the result, at most `norms` times on
one path: a goal about one element of a collection (`Q (k, v)`, the invariant of a thread) unfolds
to a goal about a collection inside it (the thread's `<holds>` map), which the lemmas address. -/
partial def collClose (disch : TSyntax `tactic) (lemmas : Array Name) (norm : TSyntax `tactic)
    (U : Array SimpArg) (norms : Nat) (leaf : Bool := false) : Nat → TacticM Bool
  | depth => do
    if (← getGoals).isEmpty then return true
    splitAnds
    -- reduce the matches on constructors an element lemma leaves (`match (k, v).snd with …`), so
    -- that the goal states the binding's parts as the hypotheses do
    tryRec (evalTactic (← `(tactic| dsimp only))) (pure ())
    if (← getGoals).isEmpty then return true
    if ← closes (← `(tactic| assumption)) then return true
    let g ← getMainGoal
    let tgt ← whnfR (← instantiateMVars (← g.getType))
    -- a goal with a metavariable is a side condition of the lemma just applied (`update ?l ?i ?x =
    -- some l`, `kAll (fun x => f x ?S = some true) k`): a hypothesis fits it or nothing does, and a
    -- search on it renews the depth at every lemma that applies
    if tgt.hasExprMVar then return ← closes disch
    -- the claims of a rule's rebuilt map defined and without repetition (`KPrelude.InvDisjoint`):
    -- the claims it writes, counted, are no more than those it removes
    if tgt.isAppOf `KPrelude.MapHook.ClaimsOK then
      if ← closes (← `(tactic| k2l_claims [$U,*])) then return true
    -- every goal of `gs` closed by the closer at `depth`
    let all (gs : List MVarId) (depth : Nat) : TacticM Bool := do
      for g' in gs do
        if ← g'.isAssigned then continue
        setGoals [g']
        unless ← collClose disch lemmas norm U norms leaf depth do return false
      return true
    if tgt.isAppOfArity ``And 2 then
      let s ← saveState
      let ok ← tryRec (do
          evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
          all (← getGoals) depth) (pure false)
      if ok then
        setGoals []
        return true
      s.restore
    -- monotonicity: a goal `EntriesOn Q' m` from a hypothesis `EntriesOn Q m` on the same map
    -- (the pre-state's, where a rule changes what the predicate reads, not the map), by
    -- `entriesOn_mono`: `Q' p` from `Q p` for a binding `p`, by this closer one level down
    if depth > 0 && (← getEnv).contains `KPrelude.MapHook.entriesOn_mono then
      if let some (_, m) := entriesOn? tgt then
        let hyps ← g.withContext do
          let mut acc : Array FVarId := #[]
          for d in (← getLCtx) do
            if d.isImplementationDetail then continue
            if let some (_, m') := entriesOn? (← instantiateMVars d.type) then
              if m' == m then acc := acc.push d.fvarId
          return acc
        for h in hyps do
          let s ← saveState
          let ok ← tryRec (do
              let gs ← g.apply (← mkConstWithFreshMVarLevels `KPrelude.MapHook.entriesOn_mono)
                { newGoals := .nonDependentOnly }
              let [gh, gq] := gs | return false
              let fits ← gh.withContext do isDefEq (← gh.getType) (← inferType (.fvar h))
              unless fits do return false
              gh.assign (.fvar h)
              setGoals [gq]
              -- closer 3b: a fact that applies a K function to the binding (its test matches on
              -- the key), by the cases of that function's matches
              if leaf then
                let sq ← saveState
                evalTactic (← `(tactic| (intro p hp; try dsimp only at hp ⊢; try simp only [$U,*] at hp)))
                let onVars ← (← getMainGoal).withContext do
                  let some d := (← getLCtx).lastDecl | return false
                  return !(← kFunsOnVars (← instantiateMVars d.type)).isEmpty
                sq.restore
                if onVars then
                  evalTactic (← `(tactic| intro p hp))
                  testLeaf U
                  return ← all (← getGoals) (depth - 1)
              -- the binding's fact, normalized as the goal will be (its parts are what closes it)
              evalTactic (← `(tactic| (intro p hp; try dsimp only at hp ⊢; try simp only [$U,*] at hp)))
              splitAnds
              collClose disch lemmas norm U norms leaf (depth - 1)) (pure false)
          if ok then
            setGoals []
            return true
          s.restore
    -- first a lemma whose premises are all hypotheses (one step, no search below it), then the
    -- search: a lemma that closes from the context is not missed behind one that searches deep.
    -- The step matches the lemma's conclusion up to reducible unfolding only: it looks for a
    -- syntactic fit, and unfolding a recursive function of the goal (`writesK x k = false` against
    -- a lemma concluding `inKeys x S = true`) cost ImpWrites a rule's whole budget
    if depth > 0 then
      for L in lemmas do
        if ← closes (← `(tactic| (with_reducible apply $(mkIdent L):ident) <;> assumption)) then
          return true
      for L in lemmas do
        let s ← saveState
        let ok ← tryRec (do
            evalTactic (← `(tactic| apply $(mkIdent L):ident))
            all (← getGoals) (depth - 1)) (pure false)
        if ok then
          setGoals []
          return true
        s.restore
    if norms > 0 then
      let s ← saveState
      -- without progress too: the goal is then attacked again with the depth renewed (a goal on
      -- one collection, reached at depth 0 through another, needs the lemmas again)
      let ok ← tryRec (do
          tryRec (evalTactic norm) (pure ())
          if (← getGoals).isEmpty then return true
          collClose disch lemmas norm U (norms - 1) leaf 3) (pure false)
      if ok then
        setGoals []
        return true
      s.restore
    closes disch

/-- `MapHook.concat a b = some m`: `(a, b, m)`. -/
def concatEq? (ty : Expr) : Option (Expr × Expr × Expr) := do
  let some (_, l, r) := ty.eq? | none
  let n := l.getAppNumArgs
  unless l.isAppOf `KPrelude.MapHook.concat && n ≥ 2 && r.isAppOfArity ``Option.some 2 do none
  some (l.getArg! (n - 2), l.getArg! (n - 1), r.appArg!)

/-- *Matched patterns*, used forwards: for a hypothesis `EntriesOn Q m` and a hypothesis
`MapHook.concat a b = some m` (a rule's match of a map, a set or a cell map: `K |-> V REST`, a
free-key match of one `<thread>`), add the facts on the parts: `Q (k, v)` for an operand
`element k v`, `EntriesOn Q x` for any other operand `x`. Each new fact is normalized by `norm`
(the unfolding set), so the invariant of a matched element becomes the facts about its cells,
which take part in the next round (a thread's `<holds>` map and its own match). At most `rounds`
rounds. The facts follow from `entry_of_concat_element(_right)` and `entriesOn_of_concat_left`,
`_right` (`KPrelude.InvColl`): a binding of an operand of a defined `concat` is a binding of
its result. -/
partial def forwardColl (norm : Array Name → TacticM Unit) (rounds : Nat)
    (done : Array (FVarId × FVarId × Bool) := #[]) (next : Nat := 0) : TacticM Unit := do
  if rounds = 0 then return
  let env ← getEnv
  unless env.contains `KPrelude.MapHook.entriesOn_of_concat_left do return
  let g ← getMainGoal
  let (new, done) ← g.withContext do
    let mut ents : Array (FVarId × Expr) := #[]
    let mut cats : Array (FVarId × Expr × Expr × Expr) := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if let some (_, m) := entriesOn? ty then ents := ents.push (d.fvarId, m)
      if let some (a, b, m) := concatEq? ty then cats := cats.push (d.fvarId, a, b, m)
    let mut out : Array (Expr × Expr) := #[]
    let mut done := done
    for (he, m) in ents do
      for (hc, a, b, m') in cats do
        unless m == m' do continue
        for (left, x) in [(true, a), (false, b)] do
          if done.contains (he, hc, left) then continue
          done := done.push (he, hc, left)
          let lem : Name :=
            if x.isAppOf `KPrelude.MapHook.element then
              if left then `KPrelude.MapHook.entry_of_concat_element
              else `KPrelude.MapHook.entry_of_concat_element_right
            else if left then `KPrelude.MapHook.entriesOn_of_concat_left
            else `KPrelude.MapHook.entriesOn_of_concat_right
          let fact ← tryRec (do
              let pf ← mkAppM lem #[.fvar hc, .fvar he]
              pure (some (← instantiateMVars (← inferType pf), pf))) (pure none)
          if let some f := fact then out := out.push f
    return (out, done)
  if new.isEmpty then return
  let hs : Array Hypothesis := new.mapIdx fun i (ty, pf) =>
    { userName := Name.mkSimple s!"k2l_fact_{next + i}", type := ty, value := pf }
  let (_, g') ← g.assertHypotheses hs
  setGoals [g']
  norm (hs.map (·.userName))
  if (← getGoals).isEmpty then return
  -- a normalized fact is often a conjunction (the parts of an element's invariant): split it, so
  -- that its collection facts take part in the next round
  splitAnds
  forwardColl norm (rounds - 1) done (next + new.size)

/-- `KeysIncl m m'` and `KeysIncl m' m` for each two hypotheses `concat (element k w) r = some m`,
`concat (element k v) r = some m'` with the same `k` and `r`: a map rebound at one key has the same
keys (prototype, INV-8). -/
def forwardKeysIncl : TacticM Unit := do
  let env ← getEnv
  unless env.contains `KPrelude.MapHook.keysIncl_rebind do return
  let g ← getMainGoal
  let new ← g.withContext do
    let mut cats : Array (FVarId × Expr × Expr × Expr) := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if let some (a, b, m) := concatEq? (← instantiateMVars d.type) then
        if a.isAppOf `KPrelude.MapHook.element then cats := cats.push (d.fvarId, a, b, m)
    let mut out : Array (Expr × Expr) := #[]
    -- each operand of a defined `concat` has its keys in the result
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if (concatEq? (← instantiateMVars d.type)).isSome then
        for lem in [`KPrelude.MapHook.keysIncl_concat_left, `KPrelude.MapHook.keysIncl_concat_right,
            `KPrelude.MapHook.inKeys_of_concat_element_self] do
          let fact ← tryRec (do
              let pf ← mkAppM lem #[.fvar d.fvarId]
              pure (some (← instantiateMVars (← inferType pf), pf))) (pure none)
          if let some f := fact then out := out.push f
    for (h1, a1, b1, m1) in cats do
      for (h2, a2, b2, m2) in cats do
        if h1 == h2 || m1 == m2 || b1 != b2 then continue
        let n := a1.getAppNumArgs
        unless n ≥ 2 && a2.getAppNumArgs == n && a1.getArg! (n - 2) == a2.getArg! (n - 2) do continue
        let fact ← tryRec (do
            let pf ← mkAppM `KPrelude.MapHook.keysIncl_rebind #[.fvar h1, .fvar h2]
            pure (some (← instantiateMVars (← inferType pf), pf))) (pure none)
        if let some f := fact then out := out.push f
    return out
  if new.isEmpty then return
  let hs : Array Hypothesis := new.mapIdx fun i (ty, pf) =>
    { userName := Name.mkSimple s!"k2l_incl_{i}", type := ty, value := pf }
  let (_, g') ← g.assertHypotheses hs
  setGoals [g']

/-- Does a K function look a value up in a map: does one of its rules (`c.rule1`, `c.rule2`, …)
apply `MapHook.lookupOrDefault` or `MapHook.lookup`? -/
def looksUp (c : Name) : MetaM Bool := do
  let env ← getEnv
  let mut i := 1
  while env.contains (c ++ Name.mkSimple s!"rule{i}") do
    if let some v := (env.find? (c ++ Name.mkSimple s!"rule{i}")).bind (·.value?) then
      if (v.find? fun e => e.isConstOf `KPrelude.MapHook.lookupOrDefault ||
          e.isConstOf `KPrelude.MapHook.lookup).isSome then
        return true
    i := i + 1
  return false

/-- Does a predicate over a collection's bindings (`EntriesOn Q m`, in the goal or a hypothesis)
apply a K function that looks values up in a map (`looksUp`) to a map that a hypothesis
`concat (element k v) r = some m'` of the rule matches or builds (`m'` an argument)? Then the test
reads the value the rule may have changed at `k` (closer 3b). A test that reads such a map only
through its keys (`in_keys`) is closer 3's (`KeysIncl`). -/
def readsMatchedMap : TacticM Bool := do
  let g ← getMainGoal
  g.withContext do
    let mut ms : Array Expr := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if let some (a, _, m) := concatEq? (← instantiateMVars d.type) then
        if a.isAppOf `KPrelude.MapHook.element then ms := ms.push m
    if ms.isEmpty then return false
    let env ← getEnv
    -- the K functions applied to a matched map inside an `EntriesOn` predicate
    let fs ← IO.mkRef (#[] : Array Name)
    let scan (e : Expr) : MetaM Unit := e.forEach fun s => do
      unless s.isAppOf `KPrelude.MapHook.EntriesOn && s.getAppNumArgs ≥ 2 do return
      (s.getArg! (s.getAppNumArgs - 2)).forEach fun t => do
        let .const c _ := t.getAppFn | return
        if env.contains (c ++ `rule1) && t.getAppArgs.any (ms.contains ·) then
          unless (← fs.get).contains c do fs.modify (·.push c)
    scan (← instantiateMVars (← g.getType))
    for d in (← getLCtx) do
      unless d.isImplementationDetail do scan (← instantiateMVars d.type)
    let fs ← fs.get
    for c in fs do
      if ← looksUp c then return true
    return false

/-- For each hypothesis `concat (element k v) r = some m` (a rule's match of `K |-> V REST`, or a
map it builds so): the lookups in `m` at every key, as the bound value at `k` and a lookup in `r`
elsewhere, and in `r` at `k` (`KPrelude.MapHook.lookupOrDefault_of_concat_element` and the
others of its group in `InvColl`). Returns the names of the facts added (closer 3b). -/
def forwardLookups : TacticM (Array Name) := do
  let env ← getEnv
  unless env.contains `KPrelude.MapHook.lookupOrDefault_of_concat_element do return #[]
  let g ← getMainGoal
  let new ← g.withContext do
    let mut out : Array (Expr × Expr) := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let some (a, _, _) := concatEq? (← instantiateMVars d.type) | continue
      unless a.isAppOf `KPrelude.MapHook.element do continue
      for lem in [`KPrelude.MapHook.lookupOrDefault_of_concat_element,
          `KPrelude.MapHook.lookupOrDefault_rest_of_concat_element,
          `KPrelude.MapHook.lookup_of_concat_element_ite,
          `KPrelude.MapHook.lookup_rest_of_concat_element,
          `KPrelude.MapHook.inKeys_of_concat_element_ite,
          `KPrelude.MapHook.inKeys_rest_of_concat_element] do
        let fact ← tryRec (do
            let pf ← mkAppM lem #[.fvar d.fvarId]
            pure (some (← instantiateMVars (← inferType pf), pf))) (pure none)
        if let some f := fact then out := out.push f
    return out
  if new.isEmpty then return #[]
  let hs : Array Hypothesis := new.mapIdx fun i (ty, pf) =>
    { userName := Name.mkSimple s!"k2l_lk_{i}", type := ty, value := pf }
  let (_, g') ← g.assertHypotheses hs
  setGoals [g']
  return hs.map (·.userName)

/-- The *compute* closer. -/
partial def splitLoop (simpU : TSyntax `tactic) (simpAllU : TSyntax `tactic)
    (heads : Array Name) : Nat → TacticM Unit
  | fuel => do
    if (← getGoals).isEmpty then return
    tryRec (evalTactic simpU) (pure ())
    tryRec (evalTactic (← `(tactic| (intro _hw; $simpAllU; done)))) (pure ())
    if (← getGoals).isEmpty || fuel = 0 then return
    let g ← getMainGoal
    let tgt ← instantiateMVars (← g.getType)
    let some e := tgt.find? (fun e => !e.hasLooseBVars && heads.any (e.isAppOf ·)) | return
    let before ← g.withContext do return (← getLCtx).getFVarIds
    let x ← g.withContext (Term.exprToSyntax e)
    evalTactic (← `(tactic| cases _h : $x:term))
    -- also case on enumeration-typed fields of the result
    let gs ← getGoals
    let mut gs' : Array MVarId := #[]
    for g in gs do
      let enumFields ← g.withContext do
        let mut acc := #[]
        for d in (← getLCtx) do
          if d.isImplementationDetail || before.contains d.fvarId then continue
          if (← isProp d.type) then continue
          if ← isEnumType d.type then acc := acc.push (d.fvarId, false)
          else if (← whnfR d.type).getAppFn.constName?.any (isFamilyName (← getEnv)) then
            acc := acc.push (d.fvarId, true)
        return acc
      let mut cur := #[g]
      for (f, fam) in enumFields do
        let mut next := #[]
        for c in cur do
          if fam then
            next := next ++ ((← familyEnumCases c f).getD #[c])
          else
            next := next ++ (← tryRec (do return (← c.cases f).map (·.mvarId)) (pure #[c]))
        cur := next
      gs' := gs' ++ cur
    let mut out := #[]
    for g in gs' do
      setGoals [g]
      splitLoop simpU simpAllU heads (fuel - 1)
      out := out ++ (← getGoals)
    setGoals out.toList

/-- An identifier as a `simp` argument. -/
def simpArgOfIdent (i : Ident) : MetaM SimpArg := do
  return ⟨(← `(Lean.Parser.Tactic.simpLemma| $i:ident)).raw⟩

/-- The local hypotheses of the main goal whose type, instantiated, satisfies `p`. -/
def hypsWhere (p : Expr → MetaM Bool) : TacticM (Array (Name × Expr)) := do
  (← getMainGoal).withContext do
    let mut acc := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ← p ty then acc := acc.push (d.userName, ty)
    return acc

/-- The maps `m` and keys `k` of the terms `MapHook.remove m k` in the main goal and its hypotheses,
outside binders. -/
def removeAtoms : TacticM (Array (Expr × Expr)) := do
  let g ← getMainGoal
  g.withContext do
    let acc ← IO.mkRef (#[] : Array (Expr × Expr))
    let visit (e : Expr) : MetaM Unit := e.forEach fun s => do
      if s.isAppOf ``MapHook.remove && !s.hasLooseBVars && s.getAppNumArgs ≥ 2 then
        let x := (s.getArg! (s.getAppNumArgs - 2), s.getArg! (s.getAppNumArgs - 1))
        unless (← acc.get).contains x do acc.modify (·.push x)
    visit (← instantiateMVars (← g.getType))
    for d in ← getLCtx do
      unless d.isImplementationDetail do visit (← instantiateMVars d.type)
    acc.get

/-- The sums over a map in a rule's case (`KPrelude.MeasureSum`), split along the maps the rule
reads and writes; shared by `k2l_measure_sum` and closer 2b of `k2l_preserve`.
- Each fold's call is read by its generated `iff` (`ss`, `F_eq`: defined exactly where the map is
  well formed and every binding matches with a defined weight, and then `sumOf g m`), so the
  source's value gives every binding's definedness, and the target's is what is left to show.
- Each map the rule matches or builds as `M₁ M₂` (`concat M₁ M₂ = some M`) splits its sum, its
  bindings' definedness and its well-formedness into the operands', down to the elements the rule
  writes and the rest it leaves.
- A map the rule writes by the hooks (`M[K <- V]`, `M[K <- undef]`) at a well-formed `M` is the
  binding at `K` beside the rest of `M` (`sumOf_update`, `claimsDef_update`), and the rest relates
  to `M` by what `M` binds at `K`: the binding the rule looked up (`lookup M K = some V`), none (a
  `requires` that `K` is not a key; `M[K <- undef]` is then `M`), or, where the rule says
  neither, both cases. -/
def sumSplit (ss : Array Ident) : TacticM Unit := do
  if ss.isEmpty then return
  evalTactic (← `(tactic| try subst_vars))
  let ssA ← ss.mapM (fun i => (simpArgOfIdent i : MetaM _))
  -- the folds' calls read as sums, the source's definedness taken apart (an expression that
  -- combines several folds, `F(M) +Int G(N)`, binds their calls: each is defined, with its value)
  evalTactic (← `(tactic| try simp only [$[$ssA],*, Option.isSome_iff_exists, Option.bind_eq_some_iff,
    Option.some.injEq, exists_and_left,
    exists_and_right, exists_eq_left, exists_eq_right, exists_eq', exists_eq_left', and_assoc] at *))
  splitAnds
  if (← getGoals).isEmpty then return
  -- the maps the rule matches and builds, named, split into their operands; a map written by the
  -- hooks, at each well-formed map
  let g ← getMainGoal
  let (g, cs, ws) ← g.withContext do
    let mut g := g
    let mut cs : Array Name := #[]
    let mut ws : Array Name := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isAppOf ``MapHook.WF then
        let n := Name.mkSimple s!"k2l_sw{ws.size}"
        g ← g.rename d.fvarId n
        ws := ws.push n
        continue
      let some (_, l, r) := ty.eq? | continue
      unless l.isAppOf ``MapHook.concat && r.isAppOfArity ``Option.some 2 do continue
      let n := Name.mkSimple s!"k2l_cc{cs.size}"
      g ← g.rename d.fvarId n
      cs := cs.push n
    return (g, cs, ws)
  setGoals [g]
  let mut args : Array SimpArg := #[]
  for n in cs do
    let i := mkIdent n
    args := args.push ⟨(← `(Lean.Parser.Tactic.simpLemma| MapHook.sumOf_concat $i:ident)).raw⟩
    args := args.push ⟨(← `(Lean.Parser.Tactic.simpLemma| MapHook.claimsDef_concat $i:ident)).raw⟩
    args := args.push ⟨(← `(Lean.Parser.Tactic.simpLemma| eq_true (MapHook.wf_of_concat $i:ident))).raw⟩
    args := args.push ⟨(← `(Lean.Parser.Tactic.simpLemma| eq_true (MapHook.wf_operands_of_concat $i:ident).1)).raw⟩
    args := args.push ⟨(← `(Lean.Parser.Tactic.simpLemma| eq_true (MapHook.wf_operands_of_concat $i:ident).2)).raw⟩
  for n in ws do
    let i := mkIdent n
    args := args.push ⟨(← `(Lean.Parser.Tactic.simpLemma| MapHook.sumOf_update $i:ident)).raw⟩
    args := args.push ⟨(← `(Lean.Parser.Tactic.simpLemma| MapHook.claimsDef_update $i:ident)).raw⟩
    args := args.push ⟨(← `(Lean.Parser.Tactic.simpLemma| eq_true (MapHook.wf_update $i:ident))).raw⟩
    args := args.push ⟨(← `(Lean.Parser.Tactic.simpLemma| eq_true (MapHook.wf_remove $i:ident))).raw⟩
  evalTactic (← `(tactic| try simp only [$[$args],*, MapHook.sumOf_element, MapHook.sumOf_unit,
    MapHook.claimsDef_element, MapHook.claimsDef_unit, Option.getD_some, MapHook.wf_unit,
    and_true, true_and, and_assoc] at *))
  splitAnds
  if (← getGoals).isEmpty then return
  -- the rest of a map written by the hooks: what the map binds at the key
  for (m, k) in ← removeAtoms do
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let (ms, ks) ← g.withContext do return (← Term.exprToSyntax m, ← Term.exprToSyntax k)
    let wf ← hypsWhere fun ty => do
      return ty.isAppOf ``MapHook.WF && ty.appArg!.isFVar && m.isFVar && ty.appArg! == m
    let some (hw, _) := wf[0]? | continue
    let hwI := mkIdent hw
    -- the binding the rule looked up, else a key the rule requires absent, else both cases
    let found ← hypsWhere fun ty => do
      let some (_, l, r) := ty.eq? | return false
      return l.isAppOf ``MapHook.lookup && r.isAppOfArity ``Option.some 2 &&
        (← isDefEq l (← mkAppM ``MapHook.lookup #[m, k]))
    let hl := mkIdent (Name.mkSimple "k2l_sl")
    if let some (h, _) := found[0]? then
      evalTactic (← `(tactic| try simp only [MapHook.sumOf_remove_eq $hwI:ident $(mkIdent h):ident] at *))
      continue
    let absent ← tryRec (do
        evalTactic (← `(tactic| have $hl:ident : MapHook.lookup $ms $ks = none := by
          first
          | assumption
          | (cases k2l_sq : MapHook.lookup $ms $ks <;>
              simp_all [MapHook.inKeys, MapHook.lookup, BoolHook.not]; done)))
        pure true) (pure false)
    if absent then
      evalTactic (← `(tactic| try simp only [MapHook.remove_of_lookup_none $hl:ident] at *))
      continue
    -- both cases: the rest is the map, or the map less the binding at the key
    evalTactic (← `(tactic| rcases $hl:ident : MapHook.lookup $ms $ks with _ | _))
    let gs ← getGoals
    let some g₁ := gs[0]? | continue
    let some g₂ := gs[1]? | continue
    setGoals [g₁]
    evalTactic (← `(tactic| try simp only [MapHook.remove_of_lookup_none $hl:ident] at *))
    let r₁ ← getGoals
    setGoals [g₂]
    evalTactic (← `(tactic| try simp only [MapHook.sumOf_remove_eq $hwI:ident $hl:ident] at *))
    setGoals (r₁ ++ (← getGoals) ++ gs.drop 2)
  splitAnds

/-- `k2l_sum_split [F_eq, …]`: `sumSplit` on the main goal, the split of closer 2b (for a hand case
of an invariant that reads a sum over a map). -/
elab "k2l_sum_split" " [" ss:ident,* "]" : tactic => sumSplit ss.getElems

syntax splitHeads := " split " "[" ident,* "]"
syntax sumsArg := &" sums " "[" ident,* "]"
syntax fuelArg := &" fuel " num
syntax handArg := &" hand " ident

/-- See the module documentation. -/
syntax (name := k2lPreserve) "k2l_preserve"
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),* "]")? (splitHeads)? (sumsArg)? (fuelArg)? (handArg)? : tactic

/-- The closers of one rule's goal `P lhs → P rhs`, as `k2l_preserve` builds them. -/
structure Closers where
  unfoldBoth : TSyntax `tactic
  /-- The unfolding set and `k2l_arith` everywhere, then `omega` on each goal left. -/
  arith : TSyntax `tactic
  /-- `simp only` with the unfolding set, on the goal. -/
  norm : TSyntax `tactic
  /-- The unfolding set, for `simp only … at h`. -/
  U : Array SimpArg
  disch : TSyntax `tactic
  simpU : TSyntax `tactic
  simpAllU : TSyntax `tactic
  coll : Array Name
  heads : Array Name
  /-- The `iff`s of the sums over a map that the predicate reads (closer 2b). -/
  sums : Array Ident := #[]
  fuel : Nat
  ambient : Array FVarId

/-- Is `c` a generated injection `inj_S_T` (`{ns}/Terms.lean`): a definition, not a constructor,
whose name is `inj_…`? It is defined by cases on its argument, so `f (inj_S_T x)` does not reduce
while `x` is a variable. -/
def isInjection (c : Name) : MetaM Bool := do
  let .str _ s := c | return false
  unless s.startsWith "inj_" do return false
  return match (← getEnv).find? c with
    | some (.defnInfo _) => true
    | _ => false

/-- The local variables `x` that occur in `e` as the argument of a generated injection
`inj_S_T x`, each with the injection, in order of first occurrence. -/
partial def injVars (e : Expr) (acc : Array (FVarId × Name) := #[]) :
    MetaM (Array (FVarId × Name)) := do
  match e with
  | .app .. =>
    let mut acc := acc
    if let .const c _ := e.getAppFn then
      let x := e.appArg!
      if x.isFVar && !acc.any (·.1 == x.fvarId!) && (← isInjection c) then
        acc := acc.push (x.fvarId!, c)
    for a in e.getAppArgs do acc ← injVars a acc
    return acc
  | .forallE _ d b _ | .lam _ d b _ => injVars b (← injVars d acc)
  | .letE _ t v b _ => injVars b (← injVars v (← injVars t acc))
  | .mdata _ b | .proj _ _ b => injVars b acc
  | _ => return acc

/-- The leaf discharger and the normalization of the collections closer, with the unfolding set
`U` (as `mkClosers` builds them). -/
def collTactics (U : Array SimpArg) : TacticM (TSyntax `tactic × TSyntax `tactic) := do
  let Ustar : Array SimpArg := U.push ⟨(← `(Lean.Parser.Tactic.simpStar| *)).raw⟩
  let Ua : Array SimpArg := U.push ⟨(← `(Lean.Parser.Tactic.simpLemma| k2l_arith)).raw⟩
  let arith ← `(tactic| ((try simp only [$Ua,*] at *) <;> omega))
  let disch ← `(tactic| first
    | assumption | rfl | decide
    | (simp only [$U,*]; done) | (simp [$U,*]; done) | (simp [$Ustar,*]; done) | $arith:tactic)
  return (disch, ← `(tactic| simp only [$U,*]))

/-- Run the closers on the main goal `P lhs → P rhs` (the only goal); true when one of them
closes it. Otherwise the goal is restored to its state on entry. `depth` bounds the case splits
of closer 6 along one path. -/
partial def closeRuleAux (k : Closers) (depth : Nat := 2) : TacticM Bool := do
  let s0 ← saveState
  -- 1. untouched
  if ← closes (← `(tactic| (intro h; $(k.unfoldBoth); first | exact h | assumption))) then
    return true
  -- the rule's sort projections, as equations
  unless k.ambient.isEmpty do
    liftMetaTactic fun g => return [← g.tryClearMany k.ambient]
  projToEq
  let s1 ← saveState
  let mut ok := false
  -- 2. compute (first when `split` heads are given: it is the closer the user asked for)
  unless k.heads.isEmpty do
    ok ← tryRec (do splitLoop k.simpU k.simpAllU k.heads k.fuel; pure (← getGoals).isEmpty)
      (pure false)
    unless ok do s1.restore
  -- 2b. sums over maps (only with `sums [...]`): read as `sumOf`, split along the rule's maps,
  -- then each part from the source's facts or by arithmetic
  unless ok || k.sums.isEmpty do
    ok ← tryRec (do
        evalTactic (← `(tactic| (intro h; try subst_vars; $(k.unfoldBoth))))
        -- the cells the invariant reads, as constructors (a rule's cell variable `<fees> F`)
        casesCells
        tryRec (evalTactic (← `(tactic| all_goals (try dsimp only at *)))) (pure ())
        -- the invariant's equations again, now that its cells are constructors
        let U := k.U
        evalTactic (← `(tactic| all_goals (try simp only [$U,*] at *)))
        -- the rule's `==K` tests as equations of terms, and those taken apart and substituted
        -- (`drop`'s looked-up value `0`), so a weight read at them evaluates
        evalTactic (← `(tactic| all_goals (try simp only [KEqHook.eq, decide_eq_true_eq] at *)))
        evalTactic (← `(tactic| all_goals (try injections)))
        evalTactic (← `(tactic| all_goals (try subst_vars)))
        for g in ← getGoals do
          setGoals [g]
          sumSplit k.sums
          if (← getGoals).isEmpty then continue
          -- the weights of the bindings the rule wrote, evaluated before the arithmetic reads
          -- the comparisons (`decide` of a comparison keeps the instance of its unevaluated form)
          let mut Uw := k.U
          for n in [``Option.getD_some, ``Option.isSome_some] do Uw := Uw.push (← simpArgOfName n)
          evalTactic (← `(tactic| all_goals (try simp only [$Uw,*] at *)))
          evalTactic (← `(tactic| all_goals (try and_intros)))
          evalTactic (← `(tactic| all_goals first
            | assumption
            | (apply MapHook.claimsDef_remove; assumption)
            | $(k.arith):tactic
            | $(k.disch):tactic))
          unless (← getGoals).isEmpty do return false
        pure true) (pure false)
    if ok then setGoals [] else s1.restore
  -- 3. collections (with the facts read off the rule's matched collections)
  unless ok do
    ok ← tryRec (do
        -- a list pattern binds its list by an equation (`hli : concat (element x) t = l`):
        -- substitute it, so the invariant of `l` reads as that of its parts
        evalTactic (← `(tactic| (intro h; try subst_vars; $(k.unfoldBoth))))
        casesCells
        tryRec (evalTactic (← `(tactic| dsimp only at *))) (pure ())
        splitAnds
        let U := k.U
        forwardColl (fun hs => do
          for h in hs do
            tryRec (evalTactic (← `(tactic| simp only [$U,*] at $(mkIdent h):ident))) (pure ())
            if (← getGoals).isEmpty then return) 4
        forwardKeysIncl
        if (← getGoals).isEmpty then return true
        -- 3b. where a test over a collection's bindings looks a value up in a map the rule
        -- matched or built as `K |-> V REST` (`readsMatchedMap`: an output's process count in
        -- `<procs>`), first the same closer with the lookups in each such map (`forwardLookups`)
        -- and, at a binding whose fact applies a K function to its key or value, the cases of
        -- that function's matches (`testLeaf`): 3 alone can spend the rule's budget on such a
        -- leaf. 3 runs when 3b fails.
        if ← readsMatchedMap then
          let s ← saveState
          let ok ← tryRec (do
              let lk ← forwardLookups
              let mut U' := U
              for n in lk do
                U' := U'.push ⟨(← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)).raw⟩
              for n in [``eq_self_iff_true, ``decide_eq_true_eq, ``Option.some.injEq, ``ite_true,
                  ``ite_false] do
                U' := U'.push (← simpArgOfName n)
              let (disch, norm) ← collTactics U'
              collClose disch k.coll norm U' 2 true 3) (pure false)
          if ok then return true
          s.restore
        collClose k.disch k.coll k.norm k.U 2 false 3) (pure false)
    if ok then setGoals [] else s1.restore
  -- 4. simp, then on each branch of the hypotheses' disjunctions
  unless ok do
    ok ← closes (← `(tactic| (intro h; $(k.simpAllU); done)))
  unless ok do
    ok ← tryRec (do
        evalTactic (← `(tactic| (intro h; $(k.unfoldBoth))))
        splitAnds
        splitOrs 3
        -- each branch: `simp_all`, or the arithmetic of 5 after it or alone
        for g in ← getGoals do
          setGoals [g]
          if ← closes (← `(tactic| ($(k.simpAllU); done))) then continue
          let s ← saveState
          tryRec (evalTactic k.simpAllU) (pure ())
          if (← getGoals).isEmpty then continue
          if ← closes k.arith then continue
          s.restore
          unless ← closes k.arith do return false
        pure true) (pure false)
    if ok then setGoals [] else s1.restore
  -- 5. arithmetic
  unless ok do
    ok ← closes (← `(tactic| (intro h; $(k.arith))))
  -- 6. injections: case on a variable under a generated injection, reduce the injection on
  -- each constructor, and run the closers on each case
  if !ok && depth > 0 then
    s1.restore
    let g ← getMainGoal
    let cands ← g.withContext do injVars (← instantiateMVars (← g.getType))
    for (x, inj) in cands do
      let s ← saveState
      let closed ← tryRec (do
          -- on the arity-indexed family, only the cases of the sort's values (`familyCases`)
          let sgs ← familyCases g x
          let mut all := true
          for (sg, _) in sgs do
            setGoals [sg]
            tryRec (evalTactic (← `(tactic| simp only [$(mkCIdent inj):ident] at *))) (pure ())
            if (← getGoals).isEmpty then continue
            unless ← closeRuleAux k (depth - 1) do
              all := false
              break
          pure all) (pure false)
      if closed then
        setGoals []
        ok := true
        break
      s.restore
  unless ok do s0.restore
  return ok

/-- `closeRuleAux`, where a closer that reaches the heartbeat limit (`maxHeartbeats`) leaves the
goal open instead of ending the tactic: the limit is a runtime exception, which `try … catch`
rethrows, so without this one expensive rule would end the proof of every rule after it (in
the `Preserved` and hand modes, and under `all_goals` in the per-case mode) and turn a per-case
theorem's "not closed" into a timeout. The goal is restored to its state on entry, as for any
rule the closers do not close. -/
def closeRule (k : Closers) : TacticM Bool := do
  let s0 ← saveState
  tryCatchRuntimeEx (closeRuleAux k) fun e => do
    unless e.isMaxHeartbeat do throw e
    s0.restore
    logInfo m!"k2l_preserve: rule {← (← getMainGoal).getTag} reached the heartbeat limit in its closers; it is left open"
    return false

/-- Run `x`, one rule's work in the `Preserved` and hand modes, with a fresh heartbeat count and
the budget `k2l.preserve.maxHeartbeats` (`maxHeartbeats` when it is `0`). -/
def withRuleBudget {α : Type} (x : TacticM α) : TacticM α := do
  let n := k2l.preserve.maxHeartbeats.get (← getOptions)
  let now ← IO.getNumHeartbeats
  withTheReader Core.Context
    (fun ctx => { ctx with initHeartbeats := now
                           maxHeartbeats := if n == 0 then ctx.maxHeartbeats else n * 1000 }) x

/-- A goal `Step.Case.r P` of a generated `Preserves.lean` (any constant `….Step.Case.r` applied
to `P` last): the constant, the rule name `r`, and `P`. -/
def caseGoal? (ty : Expr) : Option (Name × Name × Expr) :=
  match ty.getAppFn with
  | .const n@(.str (.str (.str _ "Step") "Case") r) _ =>
    if ty.getAppNumArgs > 0 then some (n, Name.mkSimple r, ty.appArg!) else none
  | _ => none

/-- The hand case of rule `r` in the namespace `ns` written in the tactic (`hand ns`): the
constant `ns.r`, with `ns` read as written and then relative to each enclosing namespace of the
current one, innermost first (as name resolution reads a namespace). -/
def handCase? (ns : Name) (r : String) : TacticM (Option Name) := do
  let env ← getEnv
  let mut pre := ← getCurrNamespace
  repeat
    let c := (pre ++ ns).str r
    if env.contains c then return some c
    if pre.isAnonymous then break
    pre := pre.getPrefix
  return none

/-- The per-case closers on one goal `Step.Case.r P` (the constant `n`, tagged `r`): unfold the
case, introduce the rule's variables and side conditions under their own names, run
`closeRule`. True when the case is closed; otherwise the goal is left as `P lhs → P rhs` in that
context, tagged `r`, and is the only goal. -/
def perCase (k : Closers) (n : Name) (r : Name) (g : MVarId) : TacticM Bool := do
  let some (.defnInfo info) := (← getEnv).find? n
    | throwError "k2l_preserve: {n} is not a definition"
  -- the rule's variables and side conditions: every binder of the case but the last, `P lhs`
  let nvars ← lambdaTelescope info.value fun _ body => forallTelescope body fun xs _ =>
    pure (xs.size - 1)
  let g ← g.deltaTarget (· == n)
  let (_, g) ← g.introNP nvars
  -- `P lhs → P rhs` with `P` applied, not a β-redex, when `P` is a `fun`
  let g ← g.replaceTargetDefEq (← Core.betaReduce (← instantiateMVars (← g.getType)))
  g.setTag r
  setGoals [g]
  closeRule k

/-- The closers of `k2l_preserve` and `k2l_close` on goal `g`: the unfolding set (`headNames`, the
predicate's heads, then `k2l_pres`, `↓reduceIte` and the user's lemmas) and the tactics built on it;
the hypotheses of `g`'s context not named in the user's list are ambient. -/
def mkClosers (g : MVarId) (headNames : Array Name) (userArgs : Array SimpArg) (heads : Array Name)
    (fuel : Nat) (keepCtx : Bool := false) (sums : Array Ident := #[]) : TacticM Closers := do
  let mut U : Array SimpArg := #[]
  for n in headNames do U := U.push (← simpArgOfName n)
  U := U.push ⟨(← `(Lean.Parser.Tactic.simpLemma| k2l_pres)).raw⟩
  U := U.push ⟨(← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte)).raw⟩
  U := U ++ userArgs
  let Ustar : Array SimpArg := U.push ⟨(← `(Lean.Parser.Tactic.simpStar| *)).raw⟩
  let coll ← labelled `k2l_coll
  let unfoldBoth ← `(tactic| (try simp only [$U,*] at h ⊢))
  let Ua : Array SimpArg := U.push ⟨(← `(Lean.Parser.Tactic.simpLemma| k2l_arith)).raw⟩
  let arith ← `(tactic| ((try simp only [$Ua,*] at *) <;> omega))
  let disch ← `(tactic| first
    | assumption | rfl | decide
    | (simp only [$U,*]; done) | (simp [$U,*]; done) | (simp [$Ustar,*]; done) | $arith:tactic)
  let simpU ← `(tactic| simp only [$Ustar,*])
  let Ul : Array (TSyntax [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma]) :=
    U.map (⟨·.raw⟩)
  let simpAllU ← `(tactic| simp_all [$Ul,*])
  -- ambient hypotheses (not the rule's): kept out of the closers' `simp [*]` and `simp_all`,
  -- unless named in the simp list, and restored in residual goals
  let named : Array Name := userArgs.foldl (init := #[]) fun acc a =>
    acc ++ identsOf a.raw
  let ambient : Array FVarId ← if keepCtx then pure #[] else g.withContext do
    let mut acc := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail || named.contains d.userName then continue
      if ← isProp d.type then acc := acc.push d.fvarId
    return acc
  let norm ← `(tactic| simp only [$U,*])
  return { unfoldBoth, arith, norm, U, disch, simpU, simpAllU, coll, heads, sums, fuel, ambient }

@[tactic k2lPreserve] def evalK2LPreserve : Tactic := fun stx => do
  -- an optional multi-token group is a null node holding the tokens themselves
  let userArgs : Array SimpArg :=
    if stx[1].getNumArgs > 0 then stx[1][1].getSepArgs.map (⟨·⟩) else #[]
  let heads : Array Name ←
    match stx[2].getOptional? with
    | some a => a[2].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
    | none => pure #[]
  let sums : Array Ident :=
    match stx[3].getOptional? with
    | some a => a[2].getSepArgs.map (⟨·⟩)
    | none => #[]
  let fuel : Nat :=
    match stx[4].getOptional? with
    | some a => a[1].isNatLit?.getD 5
    | none => 5
  let handNs : Option Name :=
    match stx[5].getOptional? with
    | some a => some a[1].getId
    | none => none
  let g ← getMainGoal
  checkSimpNames g userArgs
  let ty0 ← instantiateMVars (← g.getType)
  let case? := caseGoal? ty0
  let ty ← whnfR ty0
  let P ← match case?, ty.getAppFnArgs with
    | some (_, _, P), _ => pure P
    | none, (``KPrelude.Preserved, #[_, _, P]) => pure P
    | _, _ => throwError "k2l_preserve: the goal must be `Preserved S P` or a rule case `Step.Case.r P`"
  let k ← mkClosers g (← predHeads P) userArgs heads fuel (sums := sums)
  -- per-case mode: one rule's case `Step.Case.r P`, as `Step.preserves_of` asks for it
  if let some (n, r, _) := case? then
    if handNs.isSome then
      throwError "k2l_preserve: `hand` needs the goal `Preserved S P`, not one rule's case"
    unless ← withRuleBudget (perCase k n r g) do
      logInfo m!"k2l_preserve: rule {r} not closed; the goal is its case, with the rule's variables and side conditions introduced"
    return
  -- hand mode (kind 2 invariants): `S.preserves_of`, one goal `Step.Case.r P` per rule; the
  -- case of rule `r` is the hand-written `ns.r` when it exists, else the closers
  if let some ns := handNs then
    let .const sName _ := (ty.getArg! 1).getAppFn
      | throwError "k2l_preserve: `hand` needs a relation that is a constant (a generated `Step`)"
    let pres := sName ++ `preserves_of
    unless (← getEnv).contains pres do
      throwError "k2l_preserve: no {pres} (the generated `Preserves.lean` of {sName}) is imported"
    let gs ← g.apply (← mkConstWithFreshMVarLevels pres)
    let mut closed : Nat := 0
    let mut residual : Array MVarId := #[]
    let mut openNames : Array Name := #[]
    let mut handNames : Array Name := #[]
    for cg in gs do
      if ← cg.isAssigned then continue
      let cty ← instantiateMVars (← cg.getType)
      let some (n, r, _) := caseGoal? cty
        | throwError "k2l_preserve: {pres} has a hypothesis that is not a rule case: {cty}"
      let rStr := match n with | .str _ s => s | _ => r.toString
      match ← handCase? ns rStr with
      | some c =>
        handNames := handNames.push r
        let ok ← try
            let rest ← withRuleBudget do cg.apply (← mkConstWithFreshMVarLevels c)
            pure rest.isEmpty
          catch e =>
            logError m!"k2l_preserve: the hand case {c} does not prove the case of rule {r}: {e.toMessageData}"
            pure false
        unless ok do
          cg.setTag r
          residual := residual.push cg
          openNames := openNames.push r
      | none =>
        if ← withRuleBudget (perCase k n r cg) then
          closed := closed + 1
        else
          residual := residual ++ (← getGoals).toArray
          openNames := openNames.push r
    setGoals residual.toList
    let handPart := if handNames.isEmpty then "" else s!"; hand: {handNames.toList}"
    let openPart := if openNames.isEmpty then "" else s!"; open: {openNames.toList}"
    logInfo m!"k2l_preserve: {closed} of {gs.length} rules closed{handPart}{openPart}"
    return
  -- one goal per rule
  evalTactic (← `(tactic| (unfold KPrelude.Preserved; intro c c' hP hS; revert hP; cases hS)))
  let goals ← getGoals
  let mut closed : Nat := 0
  let mut residual : Array MVarId := #[]
  let mut openNames : Array Name := #[]
  for rg in goals do
    let tag ← rg.getTag
    setGoals [rg]
    if ← withRuleBudget (closeRule k) then
      closed := closed + 1
    else
      residual := residual.push rg
      openNames := openNames.push tag
  setGoals residual.toList
  let total := goals.length
  if openNames.isEmpty then
    logInfo m!"k2l_preserve: {closed} of {total} rules closed"
  else
    logInfo m!"k2l_preserve: {closed} of {total} rules closed; open: {openNames.toList}"

/-- `k2l_close [simp lemmas] split [f, …] fuel n`: the closers of `k2l_preserve` (1–6 of the
module documentation) on the current goal, any implication `A → B` (one thread's step, after
`k2l_thread_case`), with the given unfolding set; an error when they do not close it. -/
syntax (name := k2lClose) "k2l_close"
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),* "]")? (splitHeads)? (fuelArg)? : tactic

@[tactic k2lClose] def evalK2LClose : Tactic := fun stx => do
  let userArgs : Array SimpArg :=
    if stx[1].getNumArgs > 0 then stx[1][1].getSepArgs.map (⟨·⟩) else #[]
  let heads : Array Name ←
    match stx[2].getOptional? with
    | some a => a[2].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
    | none => pure #[]
  let fuel : Nat :=
    match stx[3].getOptional? with
    | some a => a[1].isNatLit?.getD 5
    | none => 5
  let g ← getMainGoal
  checkSimpNames g userArgs
  -- the context is the rule's (`k2l_thread_case` introduced it): nothing is ambient
  let k ← mkClosers g #[] userArgs heads fuel (keepCtx := true)
  unless ← withRuleBudget (closeRule k) do
    throwError "k2l_close: the closers do not close the goal"

/-- `k2l_thread_case [defs]` on a rule's case `Step.Case.r P`, where `P` holds of a configuration
when a predicate `Q` holds of every binding of one cell map (`WF m ∧ EntriesOn Q m` once `defs`
are unfolded: `P`, the projections to the map): introduce the rule's variables, side conditions and
`P lhs`; when the rule rewrites one binding `k |-> v` into bindings `b` and keeps the rest `d`
(hypotheses `concat (element k v) d = some m` and `concat b d = some r`, `m` the map of the
left-hand side and `r` of the right-hand side: a thread's step, which may start other threads),
reduce the goal to one goal `Q (k, v) → Q (k', v')` per binding `k' |-> v'` of `b`
(`MapHook.entriesOn_rebuild`). Fails on any other rule. -/
syntax (name := k2lThreadCase) "k2l_thread_case" " [" ident,* "]" : tactic

@[tactic k2lThreadCase] def evalK2LThreadCase : Tactic := fun stx => do
  let g ← getMainGoal
  let ty0 ← instantiateMVars (← g.getType)
  let some (n, _, _) := caseGoal? ty0
    | throwError "k2l_thread_case: the goal must be a rule case `Step.Case.r P`"
  let g ← g.deltaTarget (· == n)
  let (_, g) ← g.intros
  setGoals [g]
  let defs : Array Ident := stx[2].getSepArgs.map (⟨·⟩)
  let hw ← g.withContext do
    let some d := (← getLCtx).lastDecl | throwError "k2l_thread_case: no hypothesis"
    pure d.userName
  let hwI := mkIdent hw
  let args ← defs.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  evalTactic (← `(tactic| simp only [$args,*] at $hwI:ident ⊢))
  let g ← getMainGoal
  -- the rewritten binding: the pair of matches with one key and one rest
  let pair? ← g.withContext do
    let ds := (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail then acc else acc.push d
    for d1 in ds do
      let some (a1, b1, m) := concatEq? (← instantiateMVars d1.type) | continue
      unless a1.isAppOf `KPrelude.MapHook.element do continue
      for d2 in ds do
        if d1.fvarId == d2.fvarId then continue
        let some (_, b2, r) := concatEq? (← instantiateMVars d2.type) | continue
        unless ← isDefEq b1 b2 do continue
        if ← isDefEq m r then continue
        let gt ← instantiateMVars (← g.getType)
        unless gt.containsFVar r.fvarId! || !r.isFVar do continue
        return some (d1.userName, d2.userName)
    return none
  let some (h1, h2) := pair? | throwError "k2l_thread_case: the rule does not rewrite one binding of the map"
  let h1I := mkIdent h1
  let h2I := mkIdent h2
  -- the lemmas of `KPrelude.InvColl`, which the file using the tactic imports
  let wf := mkIdent `KPrelude.MapHook.wf_of_concat
  let reb := mkIdent `KPrelude.MapHook.entriesOn_rebuild
  let el := mkIdent `KPrelude.MapHook.entriesOn_element
  let cc := mkIdent `KPrelude.MapHook.entriesOn_concat
  evalTactic (← `(tactic| refine ⟨$wf $h2I, $reb $h1I $h2I ($hwI).2 ?_⟩))
  -- the new bindings, one goal each, from the old binding's `Q`
  evalTactic (← `(tactic| intro hq))
  evalTactic (← `(tactic| repeat' (first | (apply $el:ident) | (refine $cc (by assumption) ?_ ?_))))
  evalTactic (← `(tactic| all_goals revert hq))

/-- `k2l_coll_close [simp lemmas]`: the *collections* closer of `k2l_preserve` on its own, for
a residual case (split conjunctions, hypotheses, `@[k2l_coll]` lemmas, simp on the leaves). -/
syntax (name := k2lCollClose) "k2l_coll_close"
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),* "]")? : tactic

@[tactic k2lCollClose] def evalK2LCollClose : Tactic := fun stx => do
  let U0 : Array SimpArg :=
    if stx[1].getNumArgs > 0 then stx[1][1].getSepArgs.map (⟨·⟩) else #[]
  let presArg : SimpArg := ⟨(← `(Lean.Parser.Tactic.simpLemma| k2l_pres)).raw⟩
  let U := U0.push presArg
  let Ustar : Array SimpArg := U.push ⟨(← `(Lean.Parser.Tactic.simpStar| *)).raw⟩
  let Ua : Array SimpArg := U.push ⟨(← `(Lean.Parser.Tactic.simpLemma| k2l_arith)).raw⟩
  let disch ← `(tactic| first
    | assumption | rfl | decide
    | (simp only [$U,*]; done) | (simp [$U,*]; done) | (simp [$Ustar,*]; done)
    | ((try simp only [$Ua,*] at *) <;> omega))
  let coll ← labelled `k2l_coll
  let norm ← `(tactic| simp only [$U,*])
  unless ← collClose disch coll norm U 2 false 3 do
    throwError "k2l_coll_close: failed"

end K2LPreserve

/-- `IntHook.neg` as Lean's negation, a theorem for the reason of `KPrelude.EqBase`'s. -/
theorem IntHook.neg_eq (a : Int) : IntHook.neg a = -a := by rw [IntHook.neg]

/- The `Int` and `Bool` hooks in Lean's arithmetic and logic, for `omega` (closer 5). Each hook is
a definition whose body is the Lean operation (`KPrelude.Hooks`). The comparisons are unfolded by
their definitions, the `Int`-valued operations by theorems (`IntHook.add_eq`, `KPrelude.EqBase`):
an operation unfolded by its definition inside a comparison's `decide` is rewritten in the
proposition alone, its `Decidable` instance left behind, so `decide_eq_true_eq` no longer applies
and `omega` sees an atom; a theorem's rewrite rebuilds the instance. The partial hooks (`/Int`,
`%Int`, shifts, powers) are `Option`-valued and are not unfolded. -/
attribute [k2l_arith] IntHook.add_eq IntHook.sub_eq IntHook.mul_eq IntHook.neg_eq IntHook.lt
  IntHook.le IntHook.gt
  IntHook.ge IntHook.eq IntHook.ne BoolHook.not BoolHook.and BoolHook.or BoolHook.implies
  KEqHook.eq KEqHook.ne decide_eq_true_eq decide_eq_false_iff_not Bool.not_eq_true'
  Bool.and_eq_true Bool.or_eq_true Bool.not_eq_eq_eq_not Bool.not_true

-- a comparison of an operation reads as arithmetic in one `simp` (twoparam's `below(M, N +Int 1)`)
example (M N : Int) (h : IntHook.lt M (IntHook.add N 1) = true) : M ≤ N := by
  simp only [k2l_arith] at h; omega
example (M N : Int) (h : M ≤ N) : IntHook.le (IntHook.neg N) (IntHook.sub 0 M) = true := by
  simp only [k2l_arith]; omega

/- Generic normalization used when computing an invariant through a rule's right-hand side. -/
attribute [k2l_pres] Option.map_some Option.map_none Option.bind_some Option.bind_none
  Bool.and_true Bool.true_and Bool.and_false Bool.false_and Bool.or_true Bool.true_or
  Bool.or_false Bool.false_or ite_true ite_false and_self and_true true_and
  or_true true_or or_false false_or implies_true
  Bool.and_eq_true Bool.or_eq_false_iff

end KPrelude
