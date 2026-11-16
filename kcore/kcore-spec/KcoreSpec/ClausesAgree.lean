/-
  KCore. What a function's equations must satisfy for `Eval`, which reads no order among the
  equations of one priority, to give one result: each two of one priority are coherent
  (`ClausesAgree`, `Coherent`), in both orders. `Semantics.fnExclusiveOK` (DefinitionWf.lean)
  decides it for many functions (`Det.fnExclusiveOK_sound`, FnExclusive.lean); for the others it is
  a named obligation (`Semantics.agreeObligations`, `Obligations` in Statements.lean).
-/
import KcoreSpec.EvalFunctional

set_option autoImplicit false

namespace KCore

/-- Each two equations of f that compete are coherent, in both orders: wherever both decide at one
argument list, they are the same instance of one right-hand side or their right-hand sides have one
result (`Coherent`). Two equations compete where they are of one priority, or where the one of the
smaller priority is `aside` (no priority premise reads it); otherwise the one of the smaller
priority blocks the other (`Eval.clause`). -/
def ClausesAgree (c : Semantics) (f : Fn) : Prop :=
  ∀ cl cl', (cl, cl') ∈ pairs f.clauses →
    (cl.prio = cl'.prio ∨ (cl.aside = true ∧ cl.prio < cl'.prio) ∨
      (cl'.aside = true ∧ cl'.prio < cl.prio)) →
    Coherent c cl cl' ∧ Coherent c cl' cl

/-- Two clauses of different priorities, neither `aside`, do not compete: the one of the smaller
priority blocks the other. -/
theorem not_compete {cl cl' : Clause} (h : (cl.prio != cl'.prio && !cl.aside && !cl'.aside) = true) :
    ¬ (cl.prio = cl'.prio ∨ (cl.aside = true ∧ cl.prio < cl'.prio) ∨
      (cl'.aside = true ∧ cl'.prio < cl.prio)) := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  rintro (h1 | ⟨h1, -⟩ | ⟨h1, -⟩) <;> simp_all

/-- The generated sort predicates' equations agree: their two clauses are of different
priorities, and none is `aside`. -/
theorem sortPreds_agree {c : Semantics} {fn : Fn} (hfn : fn ∈ c.sortPreds) : ClausesAgree c fn := by
  simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with rfl | rfl | ⟨X, -, _, _, rfl⟩ <;> intro cl cl' hp hprio <;>
    simp [pairs] at hp <;> (obtain ⟨rfl, rfl⟩ := hp) <;> simp at hprio

/-- Two clauses of a list, distinct, are a pair of it in one order or the other. -/
theorem mem_pairs_of_ne {α : Type} {a b : α} : ∀ {l : List α}, a ∈ l → b ∈ l → a ≠ b →
    (a, b) ∈ pairs l ∨ (b, a) ∈ pairs l
  | [], h, _, _ => nomatch h
  | x :: l, ha, hb, hne => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq]
    by_cases hax : a = x
    · subst hax
      have hb' : b ∈ l := by
        rcases List.mem_cons.mp hb with h | h
        · exact absurd h.symm hne
        · exact h
      exact .inl (.inl ⟨b, hb', rfl, rfl⟩)
    · have ha' : a ∈ l := (List.mem_cons.mp ha).resolve_left hax
      by_cases hbx : b = x
      · subst hbx
        exact .inr (.inl ⟨a, ha', rfl, rfl⟩)
      · have hb' : b ∈ l := (List.mem_cons.mp hb).resolve_left hbx
        rcases mem_pairs_of_ne ha' hb' hne with h | h
        · exact .inl (.inr h)
        · exact .inr (.inr h)

/-- Clauses that compete are coherent where each clause is match independent and each function's
equations agree. -/
theorem coherentAll_of_parts {c : Semantics} (hmi : MatchIndependentAll c)
    (hag : ∀ f fn, c.lookupFn f = some fn → ClausesAgree c fn) : CoherentAll c := by
  intro f fn hfn cl hcl cl' hcl' hprio
  by_cases he : cl = cl'
  · subst he; exact hmi f fn hfn cl hcl
  · rcases mem_pairs_of_ne hcl hcl' he with hp | hp
    · exact (hag f fn hfn cl cl' hp hprio).1
    · refine (hag f fn hfn cl' cl hp ?_).2
      rcases hprio with h | h | h
      · exact .inl h.symm
      · exact .inr (.inr h)
      · exact .inr (.inl h)

end KCore
