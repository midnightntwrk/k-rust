import KPrelude.OneBinding
import KPrelude.InvFold

/-! The generic attempt of `k2lean refine` at a part whose rule has no counterpart but a rule of the
same name on the other side (its namesake, `docs/design.md` section 3.5, "Under a legality"): the
two differ in what they read (a check dropped, a cache read in place of what it caches, an `owise`
rule against one that reads a flag), and the legality decides where they agree. The generator
splits the configuration by the rules' patterns; each case is closed by one of three closers, tried
in turn: the legality refutes the case (`k2l_inv_absurd`), the namesake steps there (its side
conditions from the rule's hypotheses or the legality's facts, `k2l_inv_facts`), or an earlier rule
of the stepping side applies (against its priority hypothesis). Each closer runs under
`k2l_strict`, so that a closer that does not apply fails instead of being admitted. -/

namespace KPrelude

open Lean Meta Elab Tactic

/-- `k2l_strict tac`: `tac` without error recovery. Under `first`, a term that does not elaborate
inside an alternative (a nested `by`, an application that does not typecheck) is otherwise logged
and admitted as `sorry`, and the alternative succeeds; here it fails, and the next is tried. -/
elab "k2l_strict " t:tacticSeq : tactic =>
  Term.withoutErrToSorry <| withoutRecover <| evalTactic t

/-- The names of an unfolding set, each resolved in the library namespace `ns` first (the
`invariant-unfold.txt` of `gen --invariant` names the library's own declarations relative to it,
`Invariant.f`, `Eqn.«…»`), else as written (`Option.bind_fun_some`). -/
def resolveUnfold (ns : Name) (xs : Array Ident) : MetaM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  let env ← getEnv
  xs.mapM fun x => do
    let n := x.getId
    let full := ns ++ n
    let id := if env.contains full then mkIdent full else x
    `(Lean.Parser.Tactic.simpLemma| $id:ident)

/-- The proofs of the conjuncts of `h : t` (nested `∧`), each with its type. -/
partial def conjunctsOf (h t : Expr) : MetaM (Array (Expr × Expr)) := do
  let t ← whnfR t
  if let some (a, b) := t.consumeMData.and? then
    return (← conjunctsOf (mkProj ``And 0 h) a) ++ (← conjunctsOf (mkProj ``And 1 h) b)
  return #[(h, t)]

/-- `k2l_inv_absurd h in NS [x, …]`: the case is impossible, since the legality `h` at its
configuration, unfolded by the set (`invariant-unfold.txt`, names resolved in `NS`), is false. -/
elab "k2l_inv_absurd " h:ident " in " ns:ident " [" xs:ident,* "]" : tactic => withMainContext do
  let ls ← resolveUnfold ns.getId xs.getElems
  evalTactic (← `(tactic| (exfalso; simp only [$ls,*] at $h:ident <;> first | done | (simp at $h:ident; done))))

/-- `k2l_inv_facts h in NS [x, …]`: what the legality `h` says at the case's configuration, as
hypotheses: `h` unfolded by the set and by the walks' forms (`@[k2l_pres]`: a walk over a map's
values is a test of each binding, `ListHook.elemsOn_values_iff`), split into its conjuncts, and for
each conjunct that tests every binding of a map (`MapHook.EntriesOn`) and each binding the rule
matched in that map (`concat (element k v) D = some m`), the test of that binding, unfolded too.
Never fails: it only adds hypotheses, for the arithmetic that follows. -/
elab "k2l_inv_facts " h:ident " in " ns:ident " [" xs:ident,* "]" : tactic => withMainContext do
  let ls ← resolveUnfold ns.getId xs.getElems
  let some d := (← getLCtx).findFromUserName? h.getId | throwError "k2l_inv_facts: no {h}"
  let (_, g) ← (← getMainGoal).assert `k2l_i d.type d.toExpr >>= (·.intro1P)
  replaceMainGoal [g]
  let ki := mkIdent `k2l_i
  evalTactic (← `(tactic| try simp only [$ls,*, ListHook.elemsOn_values_iff] at $ki:ident))
  withMainContext do
    let lctx ← getLCtx
    let some i := lctx.findFromUserName? `k2l_i | return
    let facts ← conjunctsOf i.toExpr (← instantiateMVars i.type)
    let binds := lctx.foldl (init := #[]) fun acc d =>
      if !d.isImplementationDetail && (bindingOf? d.type).isSome then acc.push d else acc
    for (f, t) in facts do
      unless t.consumeMData.isAppOf ``MapHook.EntriesOn do continue
      for b in binds do
        try
          let e ← mkAppM ``MapHook.entry_of_concat_element #[b.toExpr, f]
          let (_, g) ← (← getMainGoal).assert `k2l_e (← inferType e) e >>= (·.intro1P)
          replaceMainGoal [g]
          evalTactic (← `(tactic| try simp only [$ls,*] at $(mkIdent `k2l_e):ident))
        catch _ => pure ()

end KPrelude
