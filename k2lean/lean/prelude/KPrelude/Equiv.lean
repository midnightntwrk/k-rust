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

/-! ## Changes of relaxed cells (`confluence --threads` with `--equiv`)

No rule reads a relaxed cell (its left-hand side has a variable there, used nowhere else), so a
step changes one by a function of what it holds, wherever the step is taken: the step has no
precondition there, and two steps' changes of it commute up to the cell's relation. For `any`
that holds of any two functions; for `perm`, of two that add items (`f x` is `x` and some `δ`, up
to order), as a log's appends. -/

/-- A change of a cell `any` compares: none, or a function of what it holds. -/
abbrev ACh (α : Type) := Option (α → α)

/-- A change of a cell `perm` compares: none, or a function that adds items to what it holds. -/
abbrev PCh (L : Type) {E : Type} [ListIso L E] :=
  Option {f : L → L // ∃ δ, ∀ x, ListHook.Perm (f x) (ListHook.concat x δ)}

def ACh.pre {α : Type} (_ : ACh α) (_ : α) : Prop := True
def ACh.apply {α : Type} (c : ACh α) (x : α) : α := match c with | some f => f x | none => x
def ACh.Compat {α : Type} (_ _ : ACh α) : Prop := True

theorem ACh.pre_none {α : Type} {x : α} : ACh.pre (none : ACh α) x := trivial
theorem ACh.pre_apply {α : Type} {a b : ACh α} {x : α} (_ : ACh.Compat a b) (_ : a.pre x)
    (_ : b.pre x) : b.pre (a.apply x) := trivial
theorem ACh.Compat.symm {α : Type} {a b : ACh α} (_ : ACh.Compat a b) : ACh.Compat b a := trivial

section PCh

variable {L E : Type} [ListIso L E]

def PCh.pre (_ : PCh L) (_ : L) : Prop := True
def PCh.apply (c : PCh L) (x : L) : L := match c with | some f => f.1 x | none => x
def PCh.Compat (_ _ : PCh L) : Prop := True

theorem PCh.pre_none {x : L} : PCh.pre (none : PCh L) x := trivial
theorem PCh.pre_apply {a b : PCh L} {x : L} (_ : PCh.Compat a b) (_ : a.pre x) (_ : b.pre x) :
    b.pre (a.apply x) := trivial
theorem PCh.Compat.symm {a b : PCh L} (_ : PCh.Compat a b) : PCh.Compat b a := trivial

open ListIso in
/-- A change that adds items: what it makes is what it got and its items, up to order. -/
theorem PCh.apply_perm (c : PCh L) : ∃ δ, ∀ x, ListHook.Perm (c.apply x) (ListHook.concat x δ) := by
  rcases c with _ | ⟨f, δ, h⟩
  · refine ⟨ListHook.unit, fun x => ?_⟩
    simp only [PCh.apply, ListHook.Perm, ListHook.concat, ListHook.unit, toList_ofList,
      List.append_nil]
    exact List.Perm.refl _
  · exact ⟨δ, h⟩

open ListIso in
/-- Two changes that add items commute up to the order of the items. -/
theorem PCh.apply_comm (a b : PCh L) (x : L) :
    ListHook.Perm (b.apply (a.apply x)) (a.apply (b.apply x)) := by
  obtain ⟨δa, ha⟩ := a.apply_perm
  obtain ⟨δb, hb⟩ := b.apply_perm
  have e₁ : ListHook.Perm (b.apply (a.apply x)) (ListHook.concat (ListHook.concat x δa) δb) := by
    refine ListHook.Perm.trans (hb _) ?_
    have := ha x
    simp only [ListHook.Perm, ListHook.concat, toList_ofList] at this ⊢
    exact this.append_right _
  have e₂ : ListHook.Perm (a.apply (b.apply x)) (ListHook.concat (ListHook.concat x δb) δa) := by
    refine ListHook.Perm.trans (ha _) ?_
    have := hb x
    simp only [ListHook.Perm, ListHook.concat, toList_ofList] at this ⊢
    exact this.append_right _
  refine ListHook.Perm.trans e₁ (ListHook.Perm.symm (ListHook.Perm.trans e₂ ?_))
  simp only [ListHook.Perm, ListHook.concat, toList_ofList, List.append_assoc]
  exact List.Perm.append_left _ List.perm_append_comm

end PCh

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
