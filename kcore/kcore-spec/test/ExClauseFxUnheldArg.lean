/-
  The fixture e3-eq-exists-unheld-arg-ml (a binder whose variable the body does not hold, the
  argument being of the binder's sort, q not `total`): the clause the reader gives for its text and
  the results of `q`, for every hook interpretation.
  Run from the package root: `lake env lean -j1 test/ExClauseFxUnheldArg.lean`.

  `rule q(X) => #Exists Z:Int. X`, the one equation of its text (`f2-examples/e3-eq-exists-unheld-arg-ml.kompile.kore`,
  its axiom 252).

  From the sentence: Z occurs nowhere in X, and X, a free variable of the sentence, is an element
  of Int under every valuation the sentence is stated at, so Int has an element there and
  `∃Z:Int. X = X`: `q(x) = x` for every element x of Int.

  The statements are on `defn`, the definition the reader gives for the text, each for every hook
  interpretation H:
  - The clause read is `clQ` (`read`): `[X:Int]`, the pattern X, `rhs X`, no existential variable,
    no `requires`, no `ensures`, `post ⊤`; `q` has no other clause and is not `total`.
  - `q_value`: `q(n)` has the result n, for every Int n, by `Eval.clause` at X := n.
  - `q_alone`: `q(n)` has no other result.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

namespace ExClauseFixtures.UnheldArg

open GroundTerm

definition_of defn from "f2-examples/e3-eq-exists-unheld-arg-ml.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fQ : Sym := 384

/-- `q(X) => X`, X of Int: the binder left out. -/
def clQ : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none }

def fnQ : Fn := { label := fQ, args := [Srt.int], result := Srt.int, clauses := [clQ] }

/-- **The reading**: the text's one function is `q`, with the one clause `clQ`. -/
theorem read : c.fns = [fnQ] := by kernel_rfl

theorem names : c.symName fQ = "Lblq" ∧ c.sortName Srt.int = "Int" := by decide +kernel

theorem lookupF : c.lookupFn fQ = some fnQ := by rw [Semantics.lookupFn_eq]; rfl

/-! ### The clause in a semantics that reads it -/

section Clause

variable {d : Semantics}

/-- A substitution giving X a value of Int is well sorted for the clause. -/
theorem sortedQ {σ : Subst} {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.int) :
    d.WellSorted clQ.vars σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | i + 1, hs => simp [clQ] at hs

/-- **`q(x)` is x**, x of Int, by `Eval.clause` at X := x. -/
theorem value (hfn : d.lookupFn fQ = some fnQ) {x : GroundTerm} (hx : d.sortOf x = some Srt.int) :
    Eval d fQ [x] (some x) :=
  .clause (cl := clQ) (σ := [(0, x)]) hfn (List.mem_singleton_self _) (sortedQ rfl hx) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnQ, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t ht => nomatch ht) .top

/-- **`q(x)` has no other result.** -/
theorem alone (hfn : d.lookupFn fQ = some fnQ) {x : GroundTerm} (hx : d.sortOf x = some Srt.int)
    {r : Option GroundTerm} (h : Eval d fQ [x] r) : r = some x := by
  have hcl : ∀ {cl fn'}, d.lookupFn fQ = some fn' → cl ∈ fn'.clauses → cl = clQ := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnQ] using h2
  have hx0 : ∀ {σ : Subst}, PatVals d σ clQ.pats [x] → σ.lookup 0 = some x := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs =>
    obtain rfl := hcl hfn' hmem
    rw [EvalTerm.var_inv hrhs]
    exact hx0 hmatch
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clQ (List.mem_singleton_self _) with
    | intro hF =>
      cases hF _ ((sortedQ (σ := [(0, x)]) rfl hx).at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ _ ht => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

end Clause

/-! ### The expectations, for every H -/

theorem lookupFH (H : HookParams) : (cH H).lookupFn fQ = some fnQ := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF

/-- **`q(n) = n`, for every H and every Int n.** -/
theorem q_value (H : HookParams) (n : Int) : Eval (cH H) fQ [int n] (some (int n)) :=
  value (lookupFH H) (rmS_sortOf_int _ n)

/-- **`q(n)` has no result but n, for every H**: not another value, and not none. -/
theorem q_alone (H : HookParams) (n : Int) {r : Option GroundTerm} (h : Eval (cH H) fQ [int n] r) :
    r = some (int n) :=
  alone (lookupFH H) (rmS_sortOf_int _ n) h

end ExClauseFixtures.UnheldArg

/-- info: 'ExClauseFixtures.UnheldArg.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.UnheldArg.read
/-- info: 'ExClauseFixtures.UnheldArg.q_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.UnheldArg.q_value
/-- info: 'ExClauseFixtures.UnheldArg.q_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.UnheldArg.q_alone
