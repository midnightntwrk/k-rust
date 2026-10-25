import Lean
import KPrelude.Coll
import KPrelude.Ext
import KPrelude.HookLaws

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
  | (with_reducible apply KPrelude.StringHook.countAllOccurrences_eqn1 <;> assumption))

/-! ## Cases on the arity-indexed family

`cases` on a variable `x : Term t` of the arity-indexed family (design.md §2.1) gives one goal per
constructor of the family whose index can be `t`: every `ck (c : Ck t)`, also those whose
enumeration `Ck t` is empty, and the leaf injection `inj hs l h a`, whose leaf tag `l` is a
variable constrained only by `h : leafOK t l = true` (and `hs : hasLeaves t = true`). A value of
sort `t` is one of `t`'s constructors applied to arguments or one injection of a leaf of `t`, so
those goals are the cases of `t`'s values only once the empty enumerations, the false `hasLeaves`
and the leaf tags with a false `leafOK` are refuted. `familyCases` does that; in the one type per
sort encoding it is plain `cases`. -/

/-- Whether `n` is the arity-indexed family of a generated library (`NS.Term`). -/
def isFamilyName (env : Environment) (n : Name) : Bool :=
  (match n with | .str _ "Term" => true | _ => false) &&
    (match env.find? n with | some (.inductInfo _) => true | _ => false)

/-- Close goal `m` when it has a hypothesis `leafOK t l = true` or `hasLeaves t = true` whose
left-hand side evaluates to `false`. -/
def refuteLeaf (m : MVarId) : MetaM Bool := m.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? | continue
    unless rhs.isConstOf ``Bool.true do continue
    unless (match lhs.getAppFn with
      | .const (.str _ f) _ => f == "leafOK" || f == "hasLeaves" | _ => false) do continue
    let v ← try whnfD lhs catch _ => pure lhs
    if v.isConstOf ``Bool.false then
      m.assign (← mkAbsurd (← m.getType) d.toExpr (mkConst ``Bool.false_ne_true))
      return true
  return false

/-- When the term `a` of the family has a builtin carrier's tag (its only possible constructor is
`b_… v`): the goal after splitting it, and `v`. -/
def builtinLeaf (g : MVarId) (a : FVarId) : MetaM (Option (MVarId × Expr)) := do
  let st ← saveState
  let gs ← try g.cases a catch _ => st.restore; return none
  let mut kept := #[]
  for sg in gs do
    match sg.ctorName with
    | some (.str _ "inj") => unless ← refuteLeaf sg.mvarId do kept := kept.push sg
    | some (.str _ c) =>
      if c.startsWith "b_" then kept := kept.push sg
      else unless ← (try (do sg.mvarId.contradiction; pure true) catch _ => pure false) do
        kept := kept.push sg
    | _ => kept := kept.push sg
  match kept with
  | #[sg] =>
    if (match sg.ctorName with | some (.str _ c) => c.startsWith "b_" | _ => false) &&
        sg.fields.size == 1 then
      return some (sg.mvarId, sg.fields[0]!)
    st.restore; return none
  | _ => st.restore; return none

/-- One level of cases on `x`, with each remaining goal and the arguments of its constructor. On a
variable of the family: the constructors `ck` with an empty enumeration are refuted, the others
are split on their enumeration (one goal per constructor of the sort of arity `k`, whose arguments
are `a0 … a(k-1)`), and an injection is refuted by a false `hasLeaves` or split on its leaf tag,
each tag with a false `leafOK` refuted (its argument is the injected term). When `splitEnum` is
false the enumeration is not split and the arguments of `ck` are `c, a0, …`. On another inductive
type it is `cases`, the arguments being the constructor's fields. -/
def familyCases (g : MVarId) (x : FVarId) (splitEnum := true) :
    MetaM (Array (MVarId × Array Expr)) := g.withContext do
  let env ← getEnv
  let fam := (← whnfR (← x.getType)).getAppFn.constName?.any (isFamilyName env)
  let gs ← g.cases x
  unless fam do return gs.map fun sg => (sg.mvarId, sg.fields)
  let mut out := #[]
  for sg in gs do
    let n := sg.fields.size
    match sg.ctorName with
    | some (.str p "inj") =>
      if isFamilyName env p && n ≥ 4 && sg.fields[n - 3]!.isFVar then
        if ← refuteLeaf sg.mvarId then continue
        for lg in ← sg.mvarId.cases sg.fields[n - 3]!.fvarId! do
          unless ← refuteLeaf lg.mvarId do
            let a := lg.subst.apply sg.fields[n - 1]!
            -- a leaf of a builtin carrier has one form, `b_… v`: split it when enumerating
            -- (`splitEnum`), so the case shows the carrier's value as the one type per sort
            -- encoding does (`inj_Int v`), and functions of it reduce
            let leafCase ← if splitEnum && a.isFVar then builtinLeaf lg.mvarId a.fvarId!
              else pure none
            match leafCase with
            | some (bg, v) => out := out.push (bg, #[v])
            | none => out := out.push (lg.mvarId, #[a])
      else
        out := out.push (sg.mvarId, sg.fields)
    | some (.str p c) =>
      let k := if isFamilyName env p && c.startsWith "c" then (c.drop 1).toNat? else none
      match k with
      | some k =>
        -- `ck`: its enumeration `Ck t` is empty at most indices
        if ← (try (do sg.mvarId.contradiction; pure true) catch _ => pure false) then continue
        let args := sg.fields.extract (n - k) n
        let e := sg.fields[n - k - 1]!
        if splitEnum && e.isFVar then
          for eg in ← sg.mvarId.cases e.fvarId! do
            -- an argument of a builtin carrier's tag is `b_… v`: split it, so the case is the
            -- constructor applied to the carrier's values, as in the one type per sort encoding
            let mut g' := eg.mvarId
            let mut args' := #[]
            for a in args.map eg.subst.apply do
              if a.isFVar then
                if let some (bg, v) ← builtinLeaf g' a.fvarId! then
                  g' := bg
                  args' := args'.push v
                  continue
              args' := args'.push a
            out := out.push (g', args')
        else
          out := out.push (sg.mvarId, sg.fields.extract (n - k - 1) n)
      | none => out := out.push (sg.mvarId, sg.fields)
    | _ => out := out.push (sg.mvarId, sg.fields)
  return out

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

A generated sort is an inductive type `Sort…` (one type per sort), or `Term t` of the
arity-indexed family; on the family the split is `familyCases` without the enumeration split. -/
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
