import KPrelude.InvDisjoint
import KPrelude.Tactic

/-! Two bindings of a map that claim one thing are one binding, under a legality stated in K as a
fold of claims (`noDup(F(M))`, `KPrelude.InvDisjoint`). A confluence slot under that invariant
(`confluence --assume-invariant`) often has two steps at two bindings of one map that a rule's
pattern cannot tell apart, and the legality says they are one: `k2l_one_binding` finds them and
makes their keys one, after which the slot is one instance (`k2l_det`). -/

namespace KPrelude

open Lean Meta Elab Tactic

/-- `concat (element k v) D = some m`: the key `k` and the map `m`. -/
def bindingOf? (t : Expr) : Option (Expr × Expr) := do
  let some (_, l, r) := t.consumeMData.eq? | none
  unless l.isAppOf ``MapHook.concat && l.getAppNumArgs ≥ 2 && r.isAppOfArity ``Option.some 2 do none
  let e := l.appFn!.appArg!
  unless e.isAppOf ``MapHook.element && e.getAppNumArgs ≥ 2 do none
  return (e.appFn!.appArg!, r.appArg!)

/-- What computes the claims of a binding in `e`: the definitions of the namespace `ns` (the
generated invariant's projections and claims, `Invariant.F_g`) and the proved equations
(`@[k2l_equation]`) of the functions that occur. -/
def claimsLemmas (ns : Name) (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for c in e.getUsedConstants do
    if ns.isPrefixOf c then
      if let some (.defnInfo _) := env.find? c then out := out.push c
    out := out ++ equationsOf env c
  return out

/-- Each pair of hypotheses `concat (element k₁ v₁) D₁ = some m`, `concat (element k₂ v₂) D₂ = some m`
with `k₁`, `k₂` different terms, and a hypothesis `h` that a `@[k2l_claims_apart]` theorem
(`Invariant.F_apart`) applies to: the theorem gives `k₁ = k₂` from a claim of both bindings. Each
binding's claims are computed with the definitions and the proved equations of the functions that
occur, round by round as the unfolding reveals them, an equation's premises from the hypotheses
(`k2l_arith_omega`: the rule's side conditions). When the claims share an element the keys are made
one (`cases`). Repeats while a pair is found; fails if none is. -/
elab "k2l_one_binding" : tactic => do
  let thms := claimsApartTheorems (← getEnv)
  let mut any := false
  for _ in [0:16] do
    let progress ← withMainContext do
      let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
        if d.isImplementationDetail then acc else acc.push d
      let binds := hyps.filterMap fun d => (bindingOf? d.type).map (d, ·)
      for thm in thms do
        for hinv in hyps do
          unless ← isProp hinv.type do continue
          if (bindingOf? hinv.type).isSome then continue
          for i in [0:binds.size] do
            for j in [i+1:binds.size] do
              let (b₁, k₁, _) := binds[i]!
              let (b₂, k₂, _) := binds[j]!
              if k₁ == k₂ then continue
              let saved ← saveState
              try
                let e ← mkAppM thm #[hinv.toExpr, b₁.toExpr, b₂.toExpr]
                let ty ← instantiateMVars (← inferType e)
                let (_, g) ← (← getMainGoal).assert `k2l_ob ty e >>= (·.intro1P)
                replaceMainGoal [g]
                let mut lemmas := #[]
                for _ in [0:8] do
                  let cur ← (← getMainGoal).withContext do
                    instantiateMVars ((← getLCtx).findFromUserName? `k2l_ob |>.map (·.type) |>.getD (mkConst ``True))
                  if cur.consumeMData.isEq then break
                  let ls := (← claimsLemmas thm.getPrefix cur).filter (!lemmas.contains ·)
                  if ls.isEmpty then break
                  lemmas := lemmas ++ ls
                  let ids := lemmas.map mkIdent
                  evalTactic (← `(tactic| try simp (disch := k2l_arith_omega) only
                    [$[$ids:ident],*, ListHook.element, ListHook.unit, ListIso.toList_ofList, Option.map_some,
                     Option.bind_some, Option.bind_fun_some, Option.getD_some, List.mem_cons, List.mem_singleton,
                     List.not_mem_nil, forall_eq, forall_eq', true_implies, or_false, false_or]
                    at $(mkIdent `k2l_ob):ident))
                let isEq ← (← getMainGoal).withContext do
                  let t ← instantiateMVars ((← getLCtx).findFromUserName? `k2l_ob |>.map (·.type) |>.getD (mkConst ``True))
                  return t.consumeMData.isEq
                if isEq then
                  evalTactic (← `(tactic| cases $(mkIdent `k2l_ob):ident))
                  return true
                restoreState saved
              catch _ => restoreState saved
      return false
    unless progress do break
    any := true
  unless any do throwError "k2l_one_binding: no two bindings of a map claim one thing"

end KPrelude
