import KPrelude.Scaffold
import KPrelude.Ext

/-!
# Confluence modulo an equivalence the author states (`k2lean confluence --equiv`)

`confluence --equiv CELL=REL,…` states its theorem modulo `Equiv`, generated per definition: two
configurations are related when every cell is equal but those named, each compared by its `REL`:
`any`, not compared, or `perm`, a list compared up to the order of its items (`ListHook.Perm`).

- `ListHook.Perm`: two lists with the same items, in any order; an equivalence.
- `DiamondMod.of_eq`: a join into equal configurations is a join modulo any reflexive relation.
- `k2l_perm`: closes `ListHook.Perm a b` where `a` and `b` are built from lists by
  `ListHook.concat`, `element`, `unit` and `push`, from the hypotheses `ListHook.Perm x y` in the
  context, by the items' counts (`List.perm_iff_count`, `omega`).
- `k2l_equiv_close`: closes a conjunction of equalities (`k2l_join_eq`) and `ListHook.Perm`s
  (`k2l_perm`), the unfolded `Equiv` of two configurations the rules built.
-/

set_option autoImplicit false

namespace KPrelude

universe u

namespace ListHook

open ListIso

variable {L E : Type} [ListIso L E]

/-- Two lists with the same items, in any order. -/
def Perm (a b : L) : Prop := (toList a).Perm (toList b)

theorem Perm.refl (a : L) : Perm a a := List.Perm.refl _

theorem Perm.symm {a b : L} (h : Perm a b) : Perm b a := List.Perm.symm h

theorem Perm.trans {a b c : L} (h₁ : Perm a b) (h₂ : Perm b c) : Perm a c := List.Perm.trans h₁ h₂

end ListHook

theorem DiamondMod.of_eq {α : Type u} {S : α → α → Prop} {E : α → α → Prop} (hE : ∀ a, E a a)
    {a b : α} (h : DiamondMod S Eq a b) : DiamondMod S E a b := by
  obtain ⟨a', b', ha, hb, rfl⟩ := h
  exact ⟨a', a', ha, hb, hE _⟩

open Lean Meta in
/-- `ListHook.Perm a b` with `a` and `b` in weak head normal form at reducible transparency: a
projection of a configuration's cell (`@[reducible]`, by a match) applied to a configuration built
by constructors is its content. -/
def ListHook.permWhnfR (t : Expr) : MetaM (Option Expr) := do
  let t ← instantiateMVars t
  unless t.isAppOfArity ``ListHook.Perm 5 do return none
  let args := t.getAppArgs
  let a ← whnfR args[3]!
  let b ← whnfR args[4]!
  return some (mkAppN t.getAppFn (args.set! 3 a |>.set! 4 b))

open Lean Elab Tactic Meta in
/-- Close `ListHook.Perm a b` by the items' counts: each list built by `ListHook.concat`, `element`,
`unit` and `push` is unfolded to a list expression, the goal and each hypothesis
`ListHook.Perm x y` of the context become counts at one item, and `omega` decides. -/
elab "k2l_perm" : tactic => withMainContext do
  let mut hyps := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some t ← ListHook.permWhnfR d.type then
      let g ← getMainGoal
      replaceMainGoal [← g.replaceLocalDeclDefEq d.fvarId t]
      hyps := hyps.push d.fvarId
  if let some t ← ListHook.permWhnfR (← getMainTarget) then
    replaceMainGoal [← (← getMainGoal).replaceTargetDefEq t]
  withMainContext do
  let ids : Array Ident ← hyps.mapM fun h => do return mkIdent (← h.getUserName)
  let unfold ← `(Lean.Parser.Tactic.simpLemma| KPrelude.ListHook.Perm)
  let lemmas := #[unfold] ++ (← #[``ListHook.concat, ``ListHook.element, ``ListHook.unit,
    ``ListHook.push, ``ListIso.toList_ofList, ``List.perm_iff_count].mapM fun n =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident))
  for i in ids do
    evalTactic (← `(tactic| simp only [$lemmas,*] at $i:ident))
  evalTactic (← `(tactic| simp only [$lemmas,*]))
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| intro k2l_a))
  for i in ids do
    evalTactic (← `(tactic| have := $i k2l_a))
  evalTactic (← `(tactic| try simp only [List.count_append, List.count_cons, List.count_nil] at *))
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| omega))

/-- Close the unfolded `Equiv` of two configurations: each equality by `k2l_join_eq`, each
`ListHook.Perm` by `k2l_perm`. -/
macro "k2l_equiv_close" : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals first | k2l_join_eq | k2l_perm))

end KPrelude
