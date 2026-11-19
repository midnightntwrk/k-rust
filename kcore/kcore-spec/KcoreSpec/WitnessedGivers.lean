/-
  KCore. Ways to give and to read `Clause.Witnessed` whose statements do not spell out its body.

  A clause is witnessed where some well-sorted values of its condition variables make its `requires`
  true with no other result and make its predicate true with no other truth value. The givers state their premises as facts
  about such values:
  - `Clause.witnessed_of_top`: the predicate is `\top`, which has no truth value but true
    (`Holds.top_eq`);
  - `Clause.witnessed_of_coherent`: the predicate is true there, and under `CoherentAll` a
    condition has one truth value at each substitution (`Holds.functional`).
  `Clause.Witnessed.conds` reads off the values and the three facts about them.
  `Clause.pre_not_false_of_only_true`: a condition whose only truth value under σ is true is not
  false under any σ' that agrees with σ on the variables the condition reads (`Holds.congr_NI`).
-/
import KcoreSpec.Statements
import KcoreSpec.EvalFunctional

namespace KCore

/-- A clause whose predicate is `\top` is witnessed by values that are well sorted at its
condition variables and at which its `requires` is true and has no other result. -/
theorem Clause.witnessed_of_top {c : Semantics} {cl : Clause} (ht : cl.pre = .top) {σ : Subst}
    (hw : c.WellSortedAt cl.vars cl.condVars σ)
    (hr : ∀ t, cl.req = some t →
      EvalTerm c σ t (some (bool true)) ∧ ∀ r, EvalTerm c σ t r → r = some (bool true)) :
    cl.Witnessed c :=
  ⟨σ, hw, hr, by rw [ht]; exact ⟨.top, fun _ hb => hb.top_eq⟩⟩

/-- Where the clauses that compete are coherent, a clause is witnessed by values that are well
sorted at its condition variables, at which its `requires` is true and has no other result, and at
which its predicate is true. -/
theorem Clause.witnessed_of_coherent {c : Semantics} (hco : CoherentAll c) {cl : Clause} {σ : Subst}
    (hw : c.WellSortedAt cl.vars cl.condVars σ)
    (hr : ∀ t, cl.req = some t →
      EvalTerm c σ t (some (bool true)) ∧ ∀ r, EvalTerm c σ t r → r = some (bool true))
    (hp : Holds c cl.vars.length σ cl.pre true) :
    cl.Witnessed c :=
  ⟨σ, hw, hr, hp, fun _ hb => Holds.functional hco hb hp⟩

/-- A witnessed clause has values well sorted at its condition variables at which its `requires`
is true and has no other result, and at which its predicate is true. -/
theorem Clause.Witnessed.conds {c : Semantics} {cl : Clause} (h : cl.Witnessed c) :
    ∃ σ, c.WellSortedAt cl.vars cl.condVars σ ∧
      (∀ t, cl.req = some t →
        EvalTerm c σ t (some (bool true)) ∧ ∀ r, EvalTerm c σ t r → r = some (bool true)) ∧
      Holds c cl.vars.length σ cl.pre true :=
  let ⟨σ, hw, hr, hp, _⟩ := h
  ⟨σ, hw, hr, hp⟩

/-- A condition whose only truth value under σ is true is not false under a substitution that
looks up every variable the condition reads as σ does. -/
theorem Clause.pre_not_false_of_only_true {c : Semantics} {n : Nat} {σ σ' : Subst} {p : Cond}
    (hu : ∀ b, Holds c n σ p b → b = true)
    (hag : ∀ j ∈ varOccsCond n p, σ.lookup j = σ'.lookup j) :
    ¬ Holds c n σ' p false :=
  fun hf => Bool.noConfusion (hu false (hf.congr_NI fun j hj => (hag j hj).symm))

end KCore
