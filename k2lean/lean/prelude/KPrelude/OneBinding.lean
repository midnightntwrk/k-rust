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

/-- A proof of an equation that is `h`, or one of its conjuncts (`h : t`, nested `∧`). -/
partial def eqConjunct? (h t : Expr) : MetaM (Option Expr) := do
  let t ← whnfR t
  if t.consumeMData.isEq then return some h
  if let some (a, b) := t.consumeMData.and? then
    if let some e ← eqConjunct? (mkProj ``And 0 h) a then return some e
    return ← eqConjunct? (mkProj ``And 1 h) b
  return none

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
(`k2l_arith_omega`: the rule's side conditions). A binding with several claims gives a premise
`x = a ∨ x = b ∨ …`, taken apart claim by claim (`forall_eq_or_imp`), so the result is a conjunction,
one conjunct per claim of the first binding, and a conjunct whose claim the other binding shares is
the keys' equation. When the claims share an element the keys are made one (`cases`). Repeats while
a pair is found; fails if none is. -/
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
                     List.not_mem_nil, ListHook.concat, List.mem_append, forall_eq_or_imp, forall_eq, forall_eq',
                     true_implies, or_false, false_or, eq_self_iff_true, true_or, or_true, and_true,
                     true_and, and_self, reduceCtorEq]
                    at $(mkIdent `k2l_ob):ident))
                let eq? ← (← getMainGoal).withContext do
                  let some d := (← getLCtx).findFromUserName? `k2l_ob | return none
                  eqConjunct? d.toExpr (← instantiateMVars d.type)
                if let some e := eq? then
                  let (_, g) ← (← getMainGoal).withContext do
                    (← getMainGoal).assert `k2l_eq (← inferType e) e >>= (·.intro1P)
                  replaceMainGoal [g]
                  evalTactic (← `(tactic| (clear $(mkIdent `k2l_ob):ident; cases $(mkIdent `k2l_eq):ident)))
                  return true
                restoreState saved
              catch _ => restoreState saved
      return false
    unless progress do break
    any := true
  unless any do throwError "k2l_one_binding: no two bindings of a map claim one thing"

namespace MapHook

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V] [Std.TransOrd K]
  [Std.LawfulEqOrd K] [DecidableEq K]

/-- A lookup in a matched `K |-> V REST` at its key `K` is `V`. -/
theorem lookupOrDefault_bound {k : K} {v : V} {r m : M} (h : concat (element k v) r = some m)
    (d : V) : lookupOrDefault m k d = v := by
  rw [lookupOrDefault_of_concat_element h, if_pos rfl]

end MapHook

/-- The goal refuted by what the invariant says of one binding. For a hypothesis `h` and a binding
`concat (element k v) D = some m` that a `@[k2l_entries]` theorem (`Invariant.w_entry`: each binding
of the map a walk reads passes its test) applies to, the theorem gives the test of `k |-> v`. The
test is computed with the definitions and the proved equations of the functions that occur, round
by round as the unfolding reveals them, with every lookup in a matched map at a matched key
rewritten to the bound value (`MapHook.lookupOrDefault_bound`; a map that two steps match has two
bindings, each read at its own key); a test that computes to `False`, directly or as arithmetic
over the hypotheses (`k2l_arith_omega`), closes the goal. Fails when no binding's test does. In a
confluence slot it refutes two keys' equation once substituted (`k2l_keyed hk refute (…)`), and
closes a case where two steps' keys are one: an output that the invariant places below its
process's count is not the output that process writes next. -/
elab "k2l_entry_refute" : tactic => withMainContext do
  let thms := entriesTheorems (← getEnv)
  let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d
  let binds := hyps.filterMap fun d => (bindingOf? d.type).map (d, ·)
  -- the lookups of every matched map, as rewrite rules
  let mut looks : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) :=
    #[← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte)]
  for (b, _) in binds do
    try
      let t ← Term.exprToSyntax (← mkAppM ``MapHook.lookupOrDefault_bound #[b.toExpr])
      looks := looks.push (← `(Lean.Parser.Tactic.simpLemma| $t:term))
    catch _ => pure ()
  for thm in thms do
    for hinv in hyps do
      unless ← isProp hinv.type do continue
      if (bindingOf? hinv.type).isSome then continue
      for (b, _) in binds do
        let saved ← saveState
        try
          let e ← mkAppM thm #[hinv.toExpr, b.toExpr]
          let ty ← instantiateMVars (← inferType e)
          let (_, g) ← (← getMainGoal).assert `k2l_ef ty e >>= (·.intro1P)
          replaceMainGoal [g]
          let ef := mkIdent `k2l_ef
          let mut lemmas := #[]
          for _ in [0:8] do
            if (← getGoals).isEmpty then break
            let cur ← (← getMainGoal).withContext do
              instantiateMVars ((← getLCtx).findFromUserName? `k2l_ef |>.map (·.type) |>.getD (mkConst ``True))
            let ls := (← claimsLemmas thm.getPrefix cur).filter (!lemmas.contains ·)
            if ls.isEmpty then break
            lemmas := lemmas ++ ls
            let args ← lemmas.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
            let args := args ++ looks
            evalTactic (← `(tactic| try simp only [$args,*] at $ef:ident))
          unless (← getGoals).isEmpty do
            evalTactic (← `(tactic| first | (simp at $ef:ident; done) | k2l_arith_omega))
          if (← getGoals).isEmpty then return
          restoreState saved
        catch _ => restoreState saved
  throwError "k2l_entry_refute: no binding's test refutes the goal"

end KPrelude
