import KPrelude.Invariant
import KPrelude.InvAttr
import KPrelude.Hooks
import KPrelude.FamilyCases

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
3. *collections*: substitute the rule's equations `x = t` (a list pattern binds its list so);
   split conjunctions; add the facts read off the rule's matched collections
   (for `EntriesOn Q m` and a match `concat a b = some m`: `Q (k, v)` for an operand
   `element k v`, `EntriesOn Q x` for another operand `x`, each normalized by the unfolding set,
   for up to 4 rounds, so the invariant of a matched `<thread>` of a cell map becomes facts about
   its cells); then close each conjunct from the hypotheses or by `apply` of a `@[k2l_coll]` lemma
   (a predicate on keys, values or entries kept by `update`, `remove`, a map pattern, ...), the
   lemma's premises by the hypotheses or by simp; a goal no lemma applies to is normalized by the
   unfolding set and attacked again (at most twice on a path: `Q (k, v)` of a rebuilt element
   unfolds to goals on the collections inside it);
4. *simp*: `simp_all` with the unfolding set;
5. *arithmetic*: rewrite the hypotheses and the goal with the unfolding set and the
   `@[k2l_arith]` lemmas, which state the `Int` and `Bool` hooks in Lean's arithmetic
   (`IntHook.add a b` is `a + b`, `IntHook.ge a b = true` is `a ≥ b`), then `omega`. The same
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

*Heartbeats.* In the `Preserved` and hand modes every rule's closers run with a fresh heartbeat
count (`withCurrHeartbeats`), so `maxHeartbeats` bounds the work on one rule, as it bounds one
per-case theorem of a kind 1 `Invariants.lean`, and a definition with many rules (SIMPLE's 169)
does not need a larger limit for the whole proof.

The unfolding set is: the head constant of `P` (for `OnCell proj Q`, also the heads of `proj`
and `Q`; for `fun c => A c ∧ B c`, the heads of `A` and `B`), the `@[k2l_pres]` simp set, and
the lemmas given in `[…]`.

Syntax: `k2l_preserve [simp lemmas]? (split [f, …])? (fuel n)? (hand NS)?`.
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

/-- Run `tac` on the main goal; true when it closes every goal it produced. Restores the state
otherwise. -/
def closes (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try
    evalTactic tac
    if (← getGoals).isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

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
    try evalTactic (← `(tactic| simp only [$args,*] at *)) catch _ => pure ()
    try evalTactic (← `(tactic| subst_vars)) catch _ => pure ()

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

/-- Split conjunctions among the hypotheses. -/
def splitAnds : TacticM Unit := do
  try liftMetaTactic fun g => return [← g.casesAnd] catch _ => pure ()

/-- The *collections* closer: conjunctions, hypotheses, `@[k2l_coll]` lemmas, and a
discharger for the leaves. When no lemma applies to a goal, it is normalized by `norm` (the
unfolding set, `simp only`) and the closer starts again on the result, at most `norms` times on
one path: a goal about one element of a collection (`Q (k, v)`, the invariant of a thread) unfolds
to a goal about a collection inside it (the thread's `<holds>` map), which the lemmas address. -/
partial def collClose (disch : TSyntax `tactic) (lemmas : Array Name) (norm : TSyntax `tactic)
    (norms : Nat) : Nat → TacticM Bool
  | depth => do
    if (← getGoals).isEmpty then return true
    splitAnds
    if ← closes (← `(tactic| assumption)) then return true
    let g ← getMainGoal
    let tgt ← whnfR (← instantiateMVars (← g.getType))
    if tgt.isAppOfArity ``And 2 then
      let s ← saveState
      try
        evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
        let gs ← getGoals
        let mut ok := true
        for g' in gs do
          setGoals [g']
          unless ← collClose disch lemmas norm norms depth do
            ok := false
            break
        if ok then
          setGoals []
          return true
        s.restore
      catch _ => s.restore
    if depth > 0 then
      for L in lemmas do
        let s ← saveState
        try
          evalTactic (← `(tactic| apply $(mkIdent L):ident))
          let gs ← getGoals
          let mut ok := true
          for g' in gs do
            if ← g'.isAssigned then continue
            setGoals [g']
            unless ← collClose disch lemmas norm norms (depth - 1) do
              ok := false
              break
          if ok then
            setGoals []
            return true
          s.restore
        catch _ => s.restore
    if norms > 0 then
      let s ← saveState
      try
        evalTactic norm
        if (← getGoals).isEmpty then return true
        if ← collClose disch lemmas norm (norms - 1) 3 then
          setGoals []
          return true
        s.restore
      catch _ => s.restore
    closes disch

/-- `EntriesOn Q m` (a `KPrelude.MapHook.EntriesOn` application): `(Q, m)`. -/
def entriesOn? (ty : Expr) : Option (Expr × Expr) :=
  let n := ty.getAppNumArgs
  if ty.isAppOf `KPrelude.MapHook.EntriesOn && n ≥ 2 then some (ty.getArg! (n - 2), ty.getArg! (n - 1))
  else none

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
          try
            let pf ← mkAppM lem #[.fvar hc, .fvar he]
            let ty ← instantiateMVars (← inferType pf)
            out := out.push (ty, pf)
          catch _ => pure ()
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

/-- The *compute* closer. -/
partial def splitLoop (simpU : TSyntax `tactic) (simpAllU : TSyntax `tactic)
    (heads : Array Name) : Nat → TacticM Unit
  | fuel => do
    if (← getGoals).isEmpty then return
    try evalTactic simpU catch _ => pure ()
    evalTactic (← `(tactic| try (intro _hw; $simpAllU; done)))
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
          if ← isEnumType d.type then acc := acc.push d.fvarId
        return acc
      let mut cur := #[g]
      for f in enumFields do
        let mut next := #[]
        for c in cur do
          try
            let r ← c.cases f
            next := next ++ r.map (·.mvarId)
          catch _ => next := next.push c
        cur := next
      gs' := gs' ++ cur
    let mut out := #[]
    for g in gs' do
      setGoals [g]
      splitLoop simpU simpAllU heads (fuel - 1)
      out := out ++ (← getGoals)
    setGoals out.toList

syntax splitHeads := " split " "[" ident,* "]"
syntax fuelArg := &" fuel " num
syntax handArg := &" hand " ident

/-- See the module documentation. -/
syntax (name := k2lPreserve) "k2l_preserve"
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),* "]")? (splitHeads)? (fuelArg)? (handArg)? : tactic

/-- The closers of one rule's goal `P lhs → P rhs`, as `k2l_preserve` builds them. -/
structure Closers where
  unfoldBoth : TSyntax `tactic
  /-- The unfolding set and `k2l_arith` everywhere, then `omega`. -/
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

/-- Run the closers on the main goal `P lhs → P rhs` (the only goal); true when one of them
closes it. Otherwise the goal is restored to its state on entry. `depth` bounds the case splits
of closer 6 along one path. -/
partial def closeRule (k : Closers) (depth : Nat := 2) : TacticM Bool := do
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
    try
      splitLoop k.simpU k.simpAllU k.heads k.fuel
      ok := (← getGoals).isEmpty
    catch _ => ok := false
    unless ok do s1.restore
  -- 3. collections (with the facts read off the rule's matched collections)
  unless ok do
    try
      -- a list pattern binds its list by an equation (`hli : concat (element x) t = l`): substitute
      -- it, so the invariant of `l` reads as that of its parts
      evalTactic (← `(tactic| (intro h; try subst_vars; $(k.unfoldBoth))))
      splitAnds
      let U := k.U
      forwardColl (fun hs => do
        for h in hs do
          try evalTactic (← `(tactic| simp only [$U,*] at $(mkIdent h):ident)) catch _ => pure ()
          if (← getGoals).isEmpty then return) 4
      if (← getGoals).isEmpty then ok := true
      else
        ok ← collClose k.disch k.coll k.norm 2 3
      if ok then setGoals []
    catch _ => pure ()
    unless ok do s1.restore
  -- 4. simp
  unless ok do
    ok ← closes (← `(tactic| (intro h; $(k.simpAllU); done)))
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
      let closed ← try
          -- on the arity-indexed family, only the cases of the sort's values (`familyCases`)
          let sgs ← familyCases g x
          let mut all := true
          for (sg, _) in sgs do
            setGoals [sg]
            try evalTactic (← `(tactic| simp only [$(mkCIdent inj):ident] at *)) catch _ => pure ()
            if (← getGoals).isEmpty then continue
            unless ← closeRule k (depth - 1) do
              all := false
              break
          pure all
        catch _ => pure false
      if closed then
        setGoals []
        ok := true
        break
      s.restore
  unless ok do s0.restore
  return ok

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

@[tactic k2lPreserve] def evalK2LPreserve : Tactic := fun stx => do
  -- an optional multi-token group is a null node holding the tokens themselves
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
  let handNs : Option Name :=
    match stx[4].getOptional? with
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
  let headNames ← predHeads P
  let mut U : Array SimpArg := #[]
  for n in headNames do U := U.push (← simpArgOfName n)
  U := U.push ⟨(← `(Lean.Parser.Tactic.simpLemma| k2l_pres)).raw⟩
  U := U.push ⟨(← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte)).raw⟩
  U := U ++ userArgs
  let Ustar : Array SimpArg := U.push ⟨(← `(Lean.Parser.Tactic.simpStar| *)).raw⟩
  let coll ← labelled `k2l_coll
  let unfoldBoth ← `(tactic| (try simp only [$U,*] at h ⊢))
  let Ua : Array SimpArg := U.push ⟨(← `(Lean.Parser.Tactic.simpLemma| k2l_arith)).raw⟩
  let arith ← `(tactic| ((try simp only [$Ua,*] at *); omega))
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
  let ambient : Array FVarId ← g.withContext do
    let mut acc := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail || named.contains d.userName then continue
      if ← isProp d.type then acc := acc.push d.fvarId
    return acc
  let norm ← `(tactic| simp only [$U,*])
  let k : Closers := { unfoldBoth, arith, norm, U, disch, simpU, simpAllU, coll, heads, fuel, ambient }
  -- per-case mode: one rule's case `Step.Case.r P`, as `Step.preserves_of` asks for it
  if let some (n, r, _) := case? then
    if handNs.isSome then
      throwError "k2l_preserve: `hand` needs the goal `Preserved S P`, not one rule's case"
    unless ← perCase k n r g do
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
            let rest ← withCurrHeartbeats do cg.apply (← mkConstWithFreshMVarLevels c)
            pure rest.isEmpty
          catch e =>
            logError m!"k2l_preserve: the hand case {c} does not prove the case of rule {r}: {e.toMessageData}"
            pure false
        unless ok do
          cg.setTag r
          residual := residual.push cg
          openNames := openNames.push r
      | none =>
        if ← withCurrHeartbeats (perCase k n r cg) then
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
    if ← withCurrHeartbeats (closeRule k) then
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
    | ((try simp only [$Ua,*] at *); omega))
  let coll ← labelled `k2l_coll
  let norm ← `(tactic| simp only [$U,*])
  unless ← collClose disch coll norm 2 3 do
    throwError "k2l_coll_close: failed"

end K2LPreserve

/- The `Int` and `Bool` hooks in Lean's arithmetic and logic, for `omega` (closer 5). Each hook is
a definition whose body is the Lean operation (`KPrelude.Hooks`), so these are its unfoldings;
the partial hooks (`/Int`, `%Int`, shifts, powers) are `Option`-valued and are not unfolded. -/
attribute [k2l_arith] IntHook.add IntHook.sub IntHook.mul IntHook.neg IntHook.lt IntHook.le IntHook.gt
  IntHook.ge IntHook.eq IntHook.ne BoolHook.not BoolHook.and BoolHook.or BoolHook.implies
  KEqHook.eq KEqHook.ne decide_eq_true_eq decide_eq_false_iff_not Bool.not_eq_true'
  Bool.and_eq_true Bool.or_eq_true Bool.not_eq_eq_eq_not Bool.not_true

/- Generic normalization used when computing an invariant through a rule's right-hand side. -/
attribute [k2l_pres] Option.map_some Option.map_none Option.bind_some Option.bind_none
  Bool.and_true Bool.true_and Bool.and_false Bool.false_and Bool.or_true Bool.true_or
  Bool.or_false Bool.false_or ite_true ite_false and_self and_true true_and
  Bool.and_eq_true Bool.or_eq_false_iff

end KPrelude
