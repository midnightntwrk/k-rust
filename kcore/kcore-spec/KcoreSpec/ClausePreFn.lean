/-
  KCore. The function lemmas at clauses with a predicate in the premise (`Clause.pre`).

  `Eval.functional`, `fnDet_of_coherent`, `solves_of_parts`, `fnSolves_of_parts_lookup`,
  `eval_resultRH`, `eval_defined` and `Eval.of_clause` read a clause's predicate through
  `Holds … cl.pre` alone: no hypothesis of theirs says what the predicate is.

  `PrioDecided` asks, of each matching clause of a smaller priority, that its predicate has a truth
  value. Where every function has a result at arguments of its sorts, a predicate with `condOK` has
  one at every σ that gives its variables values of their sorts (`holds_decided`), and a clause's
  `leftVars` hold its predicate's variables:
  - `prioDecided_of_total_pre`: `PrioDecided` from `condOK` of each clause's predicate, with no
    reading of the predicate as `\top`;
  - `fnSolves_of_total_pre`: `FnSolves` likewise.
  - `clausePre_decided_of_total`: the predicate of one clause has a truth value at each σ well
    sorted on its `leftVars`.

  `ClausePreDecided` asks that of each clause's own predicate, wherever its patterns match:
  - `clausePreDecided_of_isTop`: it holds where every clause's predicate is `\top`;
  - `clausePreDecided_of_total`: it holds where every function has a result at arguments of its
    sorts and each clause's predicate is well sorted.
-/
import KcoreSpec.HoldsDecided

set_option autoImplicit false

namespace KCore

/-- **Every clause's predicate has a truth value wherever its patterns match**: at each σ that
gives the variables of the clause's patterns and conditions values of their sorts and matches its
patterns against an argument list, the clause's predicate holds or fails. `PrioDecided` asks this
of the clauses of a smaller priority than one that applies; this asks it of every clause. -/
def ClausePreDecided (c : Semantics) : Prop :=
  ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, ∀ σ vs, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats vs →
    ∃ b, Holds c cl.vars.length σ cl.pre b

/-- `ClausePreDecided` where every clause's predicate is `\top`: `\top` holds at every σ. -/
theorem clausePreDecided_of_isTop {c : Semantics}
    (h : (c.fns.all fun f => f.clauses.all fun cl => cl.pre.isTop) = true) : ClausePreDecided c := by
  intro fn hfn cl hcl σ _ _ _
  have ht : cl.pre = .top := Cond.eq_top_of_isTop (List.all_eq_true.mp (List.all_eq_true.mp h fn hfn) cl hcl)
  exact ⟨true, by rw [ht]; exact Holds.top⟩

namespace Faithful

namespace Model

variable {c : Semantics}

/-- **A clause's predicate has a truth value** at every σ that gives the variables of its patterns
and conditions values of their sorts, where the predicate is well sorted over the clause's
variables and every function has a result at arguments of its sorts. -/
theorem clausePre_decided_of_total (hs : HypSoundCore c) (ht : FnTerminates c) {cl : Clause}
    (hok : c.condOK cl.vars cl.pre = true) {σ : Subst} (hσ : c.WellSortedAt cl.vars cl.leftVars σ) :
    ∃ b, Holds c cl.vars.length σ cl.pre b :=
  holds_decided hs ht cl.pre hok (hσ.mono Clause.pre_leftVarsRH)

/-- **`ClausePreDecided` where every function has a result** at arguments of its sorts and each
clause's predicate is well sorted over the clause's variables. -/
theorem clausePreDecided_of_total (hs : HypSoundCore c) (ht : FnTerminates c)
    (hpre : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.condOK cl.vars cl.pre = true) : ClausePreDecided c :=
  fun fn hfn cl hcl _ _ hσ _ => clausePre_decided_of_total hs ht (hpre fn hfn cl hcl) hσ

/-- Each clause's predicate is well sorted over the clause's variables, in a semantics with
`sortedOK`. -/
theorem _root_.KCore.Semantics.sortedOK_preOK (h : c.sortedOK = true) :
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.condOK cl.vars cl.pre = true :=
  fun _ hfn _ hcl => (Semantics.sortedOK_clausePre h hfn hcl).1

/-- **`ClausePreDecided` where every function has a result** at arguments of its sorts, in a
semantics with `sortedOK`. -/
theorem clausePreDecided_of_terminates (hs : HypSoundCore c) (ht : FnTerminates c) : ClausePreDecided c :=
  clausePreDecided_of_total hs ht (Semantics.sortedOK_preOK hs.1)

/-- **`PrioDecided` where each clause's predicate is well sorted**: each `requires` of a clause has
a result at each match well sorted on its patterns and conditions, and its predicate a truth value
there, where every function has a result at arguments of its sorts. The predicate is read through
`condOK` alone. -/
theorem prioDecided_of_total_pre (hs : HypSoundCore c) (ht : FnTerminates c)
    (hpre : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.condOK cl.vars cl.pre = true) : PrioDecided c := by
  intro fn hfn vs cl σ _ _ cl' hcl' _ _ σ' hσ' _
  refine ⟨fun t hq => ?_, clausePre_decided_of_total hs ht (hpre fn hfn cl' hcl') hσ'⟩
  obtain ⟨-, -, L, hL, hreqs, -⟩ := clause_ctxOccE hs.1 (List.mem_append_left _ hfn) hcl'
  exact evalTerm_total_atMP hs ht hL hσ' (Clause.req_leftVarsRH hq) (hreqs t hq)

/-- **Evaluation solves the equations** where every function has at most one result and a result
at arguments of its sorts, no clause binds a variable by `\exists`, and each clause's predicate is
well sorted. The predicate is read through `condOK` alone. -/
theorem fnSolves_of_total_pre (hs : HypSoundCore c) (hnoEx : c.FnsNoExs) (hd : FnDet c) (ht : FnTerminates c)
    (hpre : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.condOK cl.vars cl.pre = true) : FnSolves c :=
  fnSolves_of_parts_lookup (fun _ hfn => lookupFn_of_sound hs (List.mem_append_left _ hfn)) hd
    (fun fn hfn => Semantics.sortedOK_plainCl_of_noExs hs.1 hnoEx fn (List.mem_append_left _ hfn))
    (prioDecided_of_total_pre hs ht hpre) (coDefined_of_total hs hnoEx ht)

end Model

end Faithful

end KCore
