import KPrelude.Rules
import KPrelude.Tactic
import KPrelude.Logic

/-!
# Determinism modulo overlapping rules, and the closers of the generated determinism proofs

A generated `Determinism` module states determinism of `Step` at every configuration where no
listed pair of rules applies at once (`noOverlap c = true`); with an empty list that is every
configuration. A pair `(r, r')` is in the list when the generator could not show that the two
rules never both apply; every pair that is not listed is proved not to (the kernel checks a
small proof per pair), so the list is a hypothesis of the theorem, never an assumption about
the classifier.

The closers below are the certificates the generator chooses per surviving goal of a rule's
inversion (`k2l_case tag => tac`); each one is a small search over the hypotheses that the
kernel checks, not a decision procedure.
-/

/-- The injection algebra of a generated definition (`inj_A_C (inj_B_A x) = inj_B_C x`,
`proj_A_C (inj_B_A x) = some (inj_B_C x)`), tagged in its `Determinism` module. -/
register_simp_attr k2l_det_alg

namespace KPrelude

/-- Two rules of one priority rank (same applicability and step relations). -/
structure Overlap (α : Type) where
  {A : α → Prop}
  {R : α → α → Prop}
  fst : Rule α A R
  snd : Rule α A R

/-- Both rules of the pair apply at `c` (their left-hand sides match and requires are `true`). -/
def Overlap.both {α : Type} (o : Overlap α) (c : α) : Bool :=
  (o.fst.run c).applies && (o.snd.run c).applies

/-- No pair of the list applies at `c` with both of its rules. -/
def noOverlapIn {α : Type} (os : List (Overlap α)) (c : α) : Bool :=
  os.all fun o => !o.both c

theorem noOverlapIn_fst {α : Type} {os : List (Overlap α)} {c : α} (h : noOverlapIn os c = true)
    {o : Overlap α} (hm : o ∈ os) (h₁ : (o.fst.run c).applies = true) : (o.snd.run c).applies = false := by
  have := List.all_eq_true.1 h o hm
  simp only [Overlap.both, h₁, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this

theorem noOverlapIn_snd {α : Type} {os : List (Overlap α)} {c : α} (h : noOverlapIn os c = true)
    {o : Overlap α} (hm : o ∈ os) (h₂ : (o.snd.run c).applies = true) : (o.fst.run c).applies = false := by
  have := List.all_eq_true.1 h o hm
  simp only [Overlap.both, h₂, Bool.and_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this

@[simp] theorem noOverlapIn_nil {α : Type} (c : α) : noOverlapIn ([] : List (Overlap α)) c = true := rfl

open Lean Meta Elab Tactic

register_option k2l.det.verbose : Bool := {
  defValue := false
  descr := "k2l_case: report the predicted goals that inversion already closed"
}

/-- `k2l_case tag => tac`: run the certificate `tac` on the goal whose tag ends with `tag` (a
constructor name of the inverted relation), which `tac` must close. When no goal has that tag
(the inversion already closed it) this does nothing. When `tac` fails, the goal is kept, with a
warning, for the closers that follow (`k2l_default`), so a wrong prediction costs time and is
reported, but never decides the proof. -/
syntax (name := k2lCase) "k2l_case " ident " => " tacticSeq : tactic

@[tactic k2lCase] def evalK2lCase : Tactic := fun stx => do
  let tag := stx[1].getId
  let tac := stx[3]
  let verbose := k2l.det.verbose.get (← getOptions)
  let gs ← getUnsolvedGoals
  let mut found : Option MVarId := none
  for g in gs do
    if tag.isSuffixOf (← g.getTag) then
      found := some g
      break
  let some g := found
    | if verbose then logInfo m!"k2l_case {tag}: no such goal"
  if verbose then logInfo m!"k2l_case {tag}: goal"
  let rest := gs.filter (· != g)
  let s ← saveState
  setGoals [g]
  try
    evalTactic tac
    unless (← getUnsolvedGoals).isEmpty do throwError "the certificate left goals"
    setGoals rest
  catch e =>
    s.restore
    logWarning m!"k2l_case {tag}: certificate failed ({e.toMessageData}); left to the default closer"
    setGoals gs

/-- Report, as a warning, that the main goal reached the fallback closers (a goal the pair
classification did not predict, or whose certificate failed). -/
elab "k2l_warn_fallback" : tactic => do
  logWarning m!"k2l_fallback: {← getMainTag}"

/-- With `k2l.det.verbose`, report the goals that reach the default closer (for counting). -/
elab "k2l_note_default" : tactic => do
  if k2l.det.verbose.get (← getOptions) then logInfo m!"k2l_default: {← getMainTag}"

/-- Close the goal by `cases` on one equation hypothesis whose two sides reduce to different
constructors: a requires that evaluates to `false`, a projection into the wrong sort, a literal
that differs. -/
elab "k2l_refute_eqs" : tactic => withMainContext do
  let lctx ← getLCtx
  -- the lemma's own (named) hypotheses first, then the partner's (inaccessible) ones
  let ds := lctx.decls.toArray.reverse.filterMap id
  let named := ds.filter (fun d => !d.userName.hasMacroScopes)
  let anon := ds.filter (fun d => d.userName.hasMacroScopes)
  for ldecl in named ++ anon do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    unless ty.isEq do continue
    let s ← saveState
    try
      let h ← Term.exprToSyntax ldecl.toExpr
      evalTactic (← `(tactic| cases $h:term))
      if (← getGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "k2l_refute_eqs: no refutable equation"

/-- For each hypothesis `h : proj_A_B y = some x` with `y` a variable, replace `y` by
`inj_B_A x` (by the generated `inj_proj_A_B`). -/
elab "k2l_proj_inv" : tactic => do
  let mut progress := true
  let mut fuel := 16
  while progress && fuel > 0 do
    progress := false
    fuel := fuel - 1
    let found ← withMainContext do
      for ldecl in (← getLCtx) do
        if ldecl.isImplementationDetail then continue
        let ty ← instantiateMVars ldecl.type
        let some (_, lhs, _) := ty.eq? | continue
        let .const fn _ := lhs.getAppFn | continue
        let .str ns last := fn | continue
        unless last.startsWith "proj_" do continue
        let some y := lhs.getAppArgs.back? | continue
        unless y.isFVar do continue
        let lem := Name.str ns ("inj_" ++ last)
        unless (← getEnv).contains lem do continue
        let s ← saveState
        try
          let h ← Term.exprToSyntax ldecl.toExpr
          evalTactic (← `(tactic| (have k2l_e := $(mkIdent lem) $h; subst k2l_e)))
          return true
        catch _ => s.restore
      return false
    if found then progress := true

partial def k2lBoolAtoms (conn : List Name) (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let fn := e.getAppFn
  if let .const n _ := fn then
    if conn.contains n then
      let mut a := acc
      for x in e.getAppArgs do a ← k2lBoolAtoms conn x a
      return a
    if n == ``Bool.true || n == ``Bool.false then return acc
  if (← whnf (← inferType e)).isConstOf ``Bool && !e.hasLooseBVars && e.hasFVar then return acc.push e
  return acc

/-- Complementary Boolean conditions, propositionally: decompose the connectives of every
hypothesis into atoms that are `true` or `false`, and let each fact rewrite the others. -/
macro "k2l_bool_prop" : tactic => `(tactic| (
  simp_all only [KPrelude.BoolHook.and, KPrelude.BoolHook.or, KPrelude.BoolHook.not, KPrelude.BoolHook.xor,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_false', Bool.and_eq_false_iff,
    Bool.or_eq_false_iff, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_true,
    Bool.true_or, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, true_and, and_true, false_and, and_false, or_false, false_or, not_true_eq_false,
    not_false_eq_true, reduceCtorEq]
  done))

/-- Case-split a Boolean atom (an application that is not a connective) that occurs in two
hypotheses `… = true`, simplifying the connectives in each case (complementary conditions). -/
elab "k2l_bool_cases1" : tactic => withMainContext do
  let conn := [``KPrelude.BoolHook.and, ``KPrelude.BoolHook.or, ``KPrelude.BoolHook.not, ``KPrelude.BoolHook.xor, ``KPrelude.BoolHook.eq, ``KPrelude.BoolHook.ne]
  let mut seen : Array (Expr × Nat) := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let some (t, lhs, _) := ty.eq? | continue
    unless (← whnf t).isConstOf ``Bool do continue
    for a in (← k2lBoolAtoms conn lhs #[]) do
      match seen.findIdx? (fun p => p.1 == a) with
      | some i => seen := seen.modify i (fun p => (p.1, p.2 + 1))
      | none => seen := seen.push (a, 1)
  for (a, n) in seen do
    if n < 2 then continue
    let s ← saveState
    try
      let t ← Term.exprToSyntax a
      evalTactic (← `(tactic| (cases k2l_hb : $t <;> simp only [k2l_hb, KPrelude.BoolHook.and, KPrelude.BoolHook.or, KPrelude.BoolHook.not, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, reduceCtorEq] at * <;> done)))
      if (← getGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "k2l_bool_cases: no complementary atom"

macro "k2l_bool_cases" : tactic => `(tactic| first | k2l_bool_cases1 | k2l_bool_prop)

/-- `k2l_det_fundep` (the determinism closers' variant of `k2l_fundep` of `KPrelude.Tactic`, for
any non-variable left-hand side, not only `some`): identify what two hypotheses `e = a` and `e = b` with the same left-hand side `e` (not a
variable) determine: the results of one partial call made twice (`e = some a`), the rest of one map
match (`remove m k = r`), the head and tail of one list match (`uncons l = some (x, t)`). Derives
`a = b`, drops the second hypothesis, and lets `cases` unify (it closes the goal when `a` and `b`
are different constructors). -/
partial def k2lDetFundepLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let found ← withMainContext do
    let mut seen : Array (Expr × Expr) := #[]
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, lhs, rhs) := ty.eq? | continue
      if lhs.isFVar || lhs.isMVar then continue
      if rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false then continue
      match seen.find? (fun p => p.1 == lhs) with
      | some (_, h0) =>
        let s ← saveState
        try
          let h0s ← Term.exprToSyntax h0
          let h1s ← Term.exprToSyntax ldecl.toExpr
          let h1i := mkIdent ldecl.userName
          if ldecl.userName.hasMacroScopes then
            evalTactic (← `(tactic| (have k2l_fd := (Eq.symm $h0s).trans $h1s; cases k2l_fd)))
          else
            evalTactic (← `(tactic| (have k2l_fd := (Eq.symm $h0s).trans $h1s; clear $h1i; cases k2l_fd)))
          return true
        catch _ => s.restore
      | none => seen := seen.push (lhs, ldecl.toExpr)
    return false
  if found then k2lDetFundepLoop (fuel - 1)

elab "k2l_det_fundep" : tactic => k2lDetFundepLoop 32

/-- The certificate of a rule against itself: both inversions give the same binders, except
the results of partial calls and map matches, which are functions of them. -/
macro "k2l_self" : tactic => `(tactic| first
  | rfl
  | (k2l_det_fundep; rfl)
  | (k2l_list_facts; k2l_det_fundep; k2l_map_facts; k2l_det_fundep; first | rfl | (simp_all; done))
  | (k2l_map_facts; simp_all; done))

/-- `k2l_omega [f, …]`: integer side conditions that exclude each other. Unfold the `INT`/`BOOL`
hooks (and `f, …`) to `decide` of linear facts, then `omega` (other subterms are atoms). -/
syntax "k2l_omega" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| k2l_omega) => `(tactic| k2l_omega [])
  | `(tactic| k2l_omega [$xs,*]) => `(tactic| (
    simp only [KPrelude.IntHook.lt, KPrelude.IntHook.le, KPrelude.IntHook.gt, KPrelude.IntHook.ge,
      KPrelude.IntHook.eq, KPrelude.IntHook.ne, KPrelude.IntHook.add, KPrelude.IntHook.sub,
      KPrelude.BoolHook.and, KPrelude.BoolHook.or, KPrelude.BoolHook.not, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, Bool.or_eq_false_iff,
      Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, $xs,*] at *
    omega))

open Lean Meta Elab Tactic in
/-- `cases` on the variable `x`, then on each field of an enumeration type it introduces (the
constructor tag of a sort's nullary constructors). -/
def k2lCasesEnum (g : MVarId) (x : FVarId) : MetaM (List MVarId) := do
  let subs ← g.cases x
  let mut out : List MVarId := []
  for s in subs.toList do
    let mut cur : List MVarId := [s.mvarId]
    for f in s.fields do
      let .fvar fid := f | continue
      let mut next : List MVarId := []
      for g' in cur do
        let isEnum ← g'.withContext do
          let some d := (← getLCtx).find? fid | return false
          let ty ← whnfD d.type
          let .const n _ := ty.getAppFn | return false
          let some (.inductInfo iv) := (← getEnv).find? n | return false
          iv.ctors.allM fun c => do
            let some (.ctorInfo ci) := (← getEnv).find? c | return false
            return ci.numFields == 0
        if isEnum then
          next := next ++ ((← g'.cases fid).toList.map (·.mvarId))
        else
          next := next ++ [g']
      cur := next
    out := out ++ cur
  return out

/-- The free variables of an expression outside binders. -/
partial def k2lFVars (e : Expr) (acc : Array FVarId) : Array FVarId :=
  match e with
  | .fvar x => if acc.contains x then acc else acc.push x
  | .app f a => k2lFVars a (k2lFVars f acc)
  | .mdata _ b => k2lFVars b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- The variables of term type that occur as arguments in a Boolean equation hypothesis. -/
def k2lSplitCandidates : TacticM (Array FVarId) := withMainContext do
  let mut out : Array FVarId := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let some (t, lhs, _) := ty.eq? | continue
    let t ← whnf t
    unless t.isConstOf ``Bool || t.isAppOf ``Option do continue
    for x in k2lFVars lhs #[] do
      if out.contains x then continue
      let xty ← whnfR (← inferType (.fvar x))
      if xty.getAppFn.isConst && !(xty.isConstOf ``Bool) && !(xty.isConstOf ``Int) then
        out := out.push x
  return out

/-- `k2l_split_cases [f, …]`: conditions that exclude each other once a variable they test is
fixed to a constructor. Case-split one such variable (and the constructor tag it introduces),
then refute every case by evaluation or arithmetic. -/
syntax "k2l_split_cases" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| k2l_split_cases) => do evalTactic (← `(tactic| k2l_split_cases []))
  | `(tactic| k2l_split_cases [$xs,*]) => do
    -- the functions' own matches: unfold them, split the hypotheses on their discriminants,
    -- refute each branch
    let s0 ← saveState
    try
      evalTactic (← `(tactic| simp only [$xs,*] at *))
      evalTactic (← `(tactic| repeat' (k2l_split_hyps <;> try (first | k2l_refute_eqs | (simp only [reduceCtorEq, Option.some.injEq, Bool.false_eq_true, Bool.true_eq_false] at *; done)))))
      if (← getUnsolvedGoals).isEmpty then return
      s0.restore
    catch _ => s0.restore
    let close ← `(tactic| first
      | k2l_refute_eqs
      | (simp only [$xs,*] at *; done)
      | (simp only [$xs,*] at *; k2l_refute_eqs)
      | k2l_omega [$xs,*])
    for x in (← k2lSplitCandidates) do
      let s ← saveState
      let mg ← getMainGoal
      let ok ← try
          let gs ← k2lCasesEnum mg x
          let mut ok := true
          for g in gs do
            -- most cases of a leaf tag contradict the leaf condition at once
            if (← try g.contradiction; pure true catch _ => pure false) then continue
            setGoals [g]
            let closed ← try (do evalTactic close; return (← getUnsolvedGoals).isEmpty) catch _ => pure false
            unless closed do
              ok := false
              break
          pure ok
        catch _ => pure false
      if ok then
        setGoals []
        return
      s.restore
    throwError "k2l_split_cases: no variable whose cases all close"

/-- For each hypothesis `e = some x` (a partial call bound by a rule) whose `e` evaluates to a
constructor, substitute `x` by its value (`cases`, kept only when it leaves one goal). -/
partial def k2lBindsLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let found ← withMainContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, lhs, rhs) := ty.eq? | continue
      unless rhs.isAppOfArity ``Option.some 2 && rhs.appArg!.isFVar && !lhs.isFVar do continue
      let s ← saveState
      try
        let h ← Term.exprToSyntax ldecl.toExpr
        evalTactic (← `(tactic| cases $h:term))
        if (← getGoals).length == 1 then return true
        s.restore
      catch _ => s.restore
    return false
  if found then k2lBindsLoop (fuel - 1)

elab "k2l_eval_binds" : tactic => k2lBindsLoop 16

/-- Two literals that differ: substitute the variables equated to literals, then refute an
equation between literals by `decide`. -/
elab "k2l_lits" : tactic => do
  evalTactic (← `(tactic| subst_vars))
  withMainContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      unless ty.isEq && !ty.hasFVar && !ty.hasMVar do continue
      let s ← saveState
      try
        let h ← Term.exprToSyntax ldecl.toExpr
        withoutRecover <| evalTactic (← `(tactic| exact absurd $h (by decide)))
        if (← getGoals).isEmpty then return
        s.restore
      catch _ => s.restore
    throwError "k2l_lits: no equation between different literals"

/-- `k2l_eval [f, …]`: a requires that evaluates to `false` under the other rule's match.
Refute it by `cases` on an equation hypothesis; otherwise replace projected variables by
injections and evaluate with the injection algebra, the Boolean connectives and the definitions
`f, …` (the functions the two requires call), then refute. -/
syntax "k2l_eval" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| k2l_eval) => `(tactic| k2l_eval [])
  | `(tactic| k2l_eval [$xs,*]) => `(tactic| first
    | k2l_refute_eqs
    | (k2l_eval_binds; k2l_refute_eqs)
    | (k2l_eval_binds; k2l_lits)
    | (k2l_proj_inv; first
        | k2l_refute_eqs
        | (simp only [k2l_det_alg, KPrelude.BoolHook.and, KPrelude.BoolHook.not, KPrelude.BoolHook.or,
            Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_true, Bool.true_or,
            Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false,
            Bool.false_eq_true, Bool.true_eq_false, reduceCtorEq, Option.some.injEq, $xs,*] at *; done)
        | (simp only [k2l_det_alg, $xs,*] at *; k2l_refute_eqs)
        | (simp only [k2l_det_alg, Option.some.injEq, $xs,*] at *; subst_vars;
           simp only [KPrelude.BoolHook.and, KPrelude.BoolHook.not, KPrelude.BoolHook.or, Bool.and_true,
             Bool.true_and, Bool.and_false, Bool.false_and, Bool.not_true, Bool.not_false,
             Bool.false_eq_true, Bool.true_eq_false, reduceCtorEq] at *; done)))

/-- `k2l_smt [f, …]`: side conditions the classifier separated by arithmetic (z3, every other
subterm an atom): `omega` after the hooks are unfolded, after identifying repeated partial calls,
then with `f, …` unfolded too, then evaluation. -/
syntax "k2l_smt" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| k2l_smt) => `(tactic| k2l_smt [])
  | `(tactic| k2l_smt [$xs,*]) => `(tactic| first
    | k2l_omega
    | (k2l_det_fundep; k2l_omega)
    | (k2l_det_fundep; k2l_omega [$xs,*])
    | k2l_eval [$xs,*]
    | k2l_bool_cases
    | (k2l_det_fundep; k2l_bool_cases)
    | (simp_all [KPrelude.KEqHook.eq, KPrelude.KEqHook.ne, KPrelude.IntHook.eq, KPrelude.IntHook.ne,
        KPrelude.IntHook.lt, KPrelude.IntHook.le, KPrelude.IntHook.gt, KPrelude.IntHook.ge, $xs,*]; done)
    | (simp_all [KPrelude.KEqHook.eq, KPrelude.KEqHook.ne, KPrelude.IntHook.eq, KPrelude.IntHook.ne,
        KPrelude.IntHook.lt, KPrelude.IntHook.le, KPrelude.IntHook.gt, KPrelude.IntHook.ge, $xs,*]; omega))

end KPrelude
