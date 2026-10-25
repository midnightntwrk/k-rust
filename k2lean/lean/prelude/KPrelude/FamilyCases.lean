import Lean

/-!
# Case splits on the arity-indexed term family

Used by the tactics of generated proofs (`KPrelude.Tactic`, `KPrelude.InvTactic`,
`KPrelude.Relate`); kept apart so that importing it adds no lemma to any simp set.
-/

namespace KPrelude

open Lean Meta

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

end KPrelude
