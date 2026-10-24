import Lean
import KPrelude.Coll
import KPrelude.Ext
import KPrelude.Hooks

/-!
# Termination of generated recursive functions

A recursive K function becomes a well-founded definition (`termination_by`, `decreasing_by`):
its decreasing argument is a `sizeOf` or an integer measure (with the arity-indexed term universe
no recursion at a fixed sort is structural, so every one is). This module gives the facts those
proofs need and the tactic the generator emits:

* `ListSizeOf`: a collection carrier whose `sizeOf` is its list's plus one constructor; the
  generator proves it for each collection sort of the arity-indexed universe (`Term.coll_S l`).
  From it, the hooks that
  destructure a collection give smaller pieces: `ListHook.uncons`, `ListHook.unsnoc`, and the
  value and the rest of a map pattern `K |-> V REST` (`MapHook.lookup`, `MapHook.remove`).
  `MapHook.choose` is not covered: function equations do not use it (the generator rejects a map
  pattern with a free key in a function equation).
* Facts about defined partial hooks, for `omega`: an index accepted by `BytesHook.get` or
  `BytesHook.substr` is in range, and a defined `IntHook.tdiv`/`IntHook.emod` by a literal is a
  Euclidean division (`tdiv` of a nonnegative dividend).
* `k2l_facts` adds these facts for every matching hypothesis of a goal, a copy of every Boolean
  hypothesis (a requires), and the value of every failed earlier equation (`he : e = none` with
  `e` a local definition), so that `simp` can rewrite them even where a recursive call's proof
  depends on the original.
* `k2l_split_hyp` splits a `match`/`if` in some hypothesis; repeated after unfolding a generated
  function in `h : f x = some r`, it enumerates the function's cases (used by hand-written
  facts about generated functions, e.g. in a `--termination` file).
* `k2l_decreasing [r₁, …]` closes a goal of `decreasing_by`: the facts, each failed guard
  (`(if h : c then … else none) = none`) turned into `¬ c`, the integer and Boolean hooks unfolded, lexicographic goals split by `Prod.lex_def`, the given rank functions unfolded,
  then `omega`.

No statement here depends on the exact `sizeOf` of an injection (`Term.inj`): the size laws are
about collection constructors only.
-/

set_option linter.unusedSectionVars false

namespace KPrelude

open ListIso

/-- A collection carrier whose `sizeOf` is one more than the `sizeOf` of its list. -/
class ListSizeOf (M : Type) (E : outParam Type) [ListIso M E] [SizeOf M] [SizeOf E] : Prop where
  sizeOf_ofList : ∀ l : List E, sizeOf (ofList l : M) = 1 + sizeOf l

section
variable {M E : Type} [ListIso M E] [SizeOf M] [SizeOf E] [ListSizeOf M E]

theorem sizeOf_eq_toList (m : M) : sizeOf m = 1 + sizeOf (toList m) := by
  conv => lhs; rw [← ofList_toList m]
  exact ListSizeOf.sizeOf_ofList _

end

theorem sizeOf_dropLast_lt {E : Type} [SizeOf E] : ∀ (xs : List E), xs ≠ [] → sizeOf xs.dropLast < sizeOf xs
  | [], h => absurd rfl h
  | [_], _ => by simp only [List.dropLast, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
  | a :: b :: t, _ => by
    have ih := sizeOf_dropLast_lt (b :: t) (by simp)
    simp only [List.dropLast_cons_cons, List.cons.sizeOf_spec] at ih ⊢
    omega

namespace ListHook
variable {L E : Type} [ListIso L E] [SizeOf L] [SizeOf E] [ListSizeOf L E]

/-- The pieces of `ListItem(X) REST` are smaller than the list. -/
theorem sizeOf_uncons {l t : L} {x : E} (h : uncons l = some (x, t)) :
    sizeOf x < sizeOf l ∧ sizeOf t < sizeOf l := by
  unfold uncons at h
  split at h
  · simp at h
  · next y ys hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [sizeOf_eq_toList l, hl, ListSizeOf.sizeOf_ofList]
    simp only [List.cons.sizeOf_spec]
    omega

/-- The pieces of `REST ListItem(X)` are smaller than the list. -/
theorem sizeOf_unsnoc {l t : L} {x : E} (h : unsnoc l = some (t, x)) :
    sizeOf x < sizeOf l ∧ sizeOf t < sizeOf l := by
  unfold unsnoc at h
  split at h
  · simp at h
  · next y hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hne : toList l ≠ [] := by intro e; simp [e] at hl
    have hmem : y ∈ toList l := List.mem_of_getLast? hl
    rw [sizeOf_eq_toList l, ListSizeOf.sizeOf_ofList]
    have h1 := List.sizeOf_lt_of_mem hmem
    have h2 := sizeOf_dropLast_lt (toList l) hne
    omega

end ListHook

namespace SAL
variable {α β : Type} [Ord α] [SizeOf α] [SizeOf β]

theorem sizeOf_erase_lt {k : α} {v : β} : ∀ {m : List (α × β)}, lookup k m = some v → sizeOf (erase k m) < sizeOf m
  | [], h => by simp [lookup] at h
  | (k', v') :: t, h => by
    unfold lookup at h
    unfold erase
    split at h
    · simp at h
    · simp only [List.cons.sizeOf_spec]; omega
    · have := sizeOf_erase_lt h
      simp only [List.cons.sizeOf_spec]
      omega

end SAL

namespace MapHook
variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V] [SizeOf M] [SizeOf K] [SizeOf V]
  [ListSizeOf M (K × V)] [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- The value of `K |-> V REST` is smaller than the map. -/
theorem sizeOf_lookup {m : M} {k : K} {v : V} (h : lookup m k = some v) : sizeOf v < sizeOf m := by
  rw [lookup_def] at h
  have h1 := List.sizeOf_lt_of_mem (SAL.lookup_mem h)
  rw [sizeOf_eq_toList m]
  simp only [Prod.mk.sizeOf_spec] at h1
  omega

/-- The rest of `K |-> V REST` is smaller than the map. -/
theorem sizeOf_remove {m : M} {k : K} {v : V} (h : lookup m k = some v) : sizeOf (remove m k) < sizeOf m := by
  rw [lookup_def] at h
  rw [remove_def, sizeOf_eq_toList m, ListSizeOf.sizeOf_ofList]
  have := SAL.sizeOf_erase_lt h
  omega

end MapHook

namespace BytesHook

/-- An index `B[I]` accepts is in range. -/
theorem get_facts {b : List UInt8} {i v : Int} (h : get b i = some v) : 0 ≤ i ∧ i < length b := by
  unfold get at h
  split at h
  · next hi =>
    refine ⟨hi, ?_⟩
    cases hb : b[i.toNat]? with
    | none => simp [hb] at h
    | some x =>
      have := (List.getElem?_eq_some_iff.1 hb).1
      unfold length; omega
  · simp at h

/-- The bounds `substrBytes(B, I, J)` accepts, and the length of its result. -/
theorem substr_facts {b r : List UInt8} {i j : Int} (h : substr b i j = some r) :
    0 ≤ i ∧ i ≤ j ∧ j ≤ length b ∧ length r = j - i := by
  unfold substr at h
  split at h
  · next hb =>
    simp only [Option.some.injEq] at h
    subst h
    unfold length
    simp only [List.length_take, List.length_drop]
    omega
  · simp at h

end BytesHook

namespace IntHook

/-- A defined `/Int`: the divisor is not zero, and on a nonnegative dividend it is `Int.ediv`
(which `omega` knows for a literal divisor). -/
theorem tdiv_facts {a b r : Int} (h : tdiv a b = some r) : b ≠ 0 ∧ (0 ≤ a → r = a / b) := by
  unfold tdiv at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨by assumption, fun ha => Int.tdiv_eq_ediv_of_nonneg ha⟩

/-- A defined `modInt` is `Int.emod`. -/
theorem emod_facts {a b r : Int} (h : emod a b = some r) : b ≠ 0 ∧ r = a % b := by
  unfold emod at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    exact ⟨by assumption, h.symm⟩

end IntHook

open Lean Meta Elab Tactic

/-- The fact lemmas `k2l_facts` applies, keyed by the head of an equation's left-hand side. -/
private def factLemmas : List (Name × List Name) :=
  [(``ListHook.uncons, [``ListHook.sizeOf_uncons]),
   (``ListHook.unsnoc, [``ListHook.sizeOf_unsnoc]),
   (``MapHook.lookup, [``MapHook.sizeOf_lookup, ``MapHook.sizeOf_remove]),
   (``BytesHook.get, [``BytesHook.get_facts]),
   (``BytesHook.substr, [``BytesHook.substr_facts]),
   (``IntHook.tdiv, [``IntHook.tdiv_facts]),
   (``IntHook.emod, [``IntHook.emod_facts])]

/-- Add the facts a termination goal needs from its hypotheses (see the module comment). -/
elab "k2l_facts" : tactic => withMainContext do
  let mut facts : Array Expr := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (eqTy, lhs, rhs) := ty.eq? | continue
    if eqTy.isConstOf ``Bool then
      facts := facts.push d.toExpr
    if rhs.isAppOf ``Option.none && lhs.isFVar then
      if let some v ← lhs.fvarId!.getValue? then
        facts := facts.push (← mkExpectedTypeHint d.toExpr (← mkEq v rhs))
    for (head, lemmas) in factLemmas do
      unless lhs.isAppOf head do continue
      for l in lemmas do
        try facts := facts.push (← mkAppM l #[d.toExpr]) catch _ => pure ()
  liftMetaTactic fun g => do
    let mut g := g
    for p in facts do
      let (_, g') ← (← g.assert `k2l_fact (← inferType p) p).intro1P
      g := g'
    return [g]

/-- Split the first `match` or `if` found in a hypothesis (for facts about a generated function,
proved by unfolding it in a hypothesis `f x = some r` and splitting its cascade). -/
elab "k2l_split_hyp" : tactic => liftMetaTactic fun g => do
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    if let some gs ← splitLocalDecl? g d.fvarId then return gs
  throwError "k2l_split_hyp: nothing to split"

/-- Close a `decreasing_by` goal of a generated function; the identifiers are rank functions of
the measure to unfold. -/
syntax "k2l_decreasing" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| k2l_decreasing) => `(tactic| k2l_decreasing [])
  | `(tactic| k2l_decreasing [$ids,*]) => do
    let ranks : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ids.getElems.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
    `(tactic| (
      simp_wf
      first | done | (
      (try subst_vars)
      k2l_facts
      -- a failed guard's condition is extracted before the hooks are unfolded: unfolding a hook
      -- inside the condition of a `dite` leaves its `Decidable` instance stated for the folded
      -- condition, and on Lean v4.34.0 `dite_eq_right_iff` no longer rewrites such a `dite`
      (try simp only [dite_eq_right_iff, ite_eq_right_iff, reduceCtorEq, imp_false] at *)
      (try simp only [IntHook.le, IntHook.lt, IntHook.ge, IntHook.gt, IntHook.eq, IntHook.ne,
        IntHook.add, IntHook.sub, IntHook.mul, BoolHook.not, BoolHook.and, BoolHook.or,
        BytesHook.length, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true',
        Bool.and_eq_true, Bool.or_eq_true, dite_eq_right_iff, ite_eq_right_iff, reduceCtorEq,
        imp_false] at *)
      (try simp only [Prod.lex_def] at ⊢)
      (try dsimp only [$ranks,*] at ⊢)
      (try simp only [true_and, and_true, Nat.lt_irrefl, false_or, or_false] at ⊢)
      first | done | omega)))

end KPrelude
