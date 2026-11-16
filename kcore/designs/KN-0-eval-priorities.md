# KN-0: `Eval` with priorities and without clause order

Delivers ticket KN-0 of `TICKETS-2026-11-11.toml` (decision D2).
Two Lean files beside this one are kernel-checked against the library at `938ddde1` and depend on propext, Classical.choice and Quot.sound only:

- `EvalFunctional.lean`: today's first-match `Eval` has one result, from `MatchIndependentAll` alone.
  TH-3 moves it into `KcoreSpec/`.
- `PrioEval.lean`: the relation of §2 as a prototype (`KCore.Proto`, with `prio : Clause → Nat` standing for the new field), and its functionality from `CoherentAll`.
  KN-2 makes it the kernel's `Eval`.

## 1. Data

```lean
structure Clause where
  vars : List Srt
  pats : List Term
  req  : Option Term
  rhs  : Term
  prio : Nat := 50

structure Fn where
  label : Sym
  args : List Srt
  result : Srt
  clauses : List Clause
  total : Bool := false
```

`Owise`, `Fn.owise`, `Fn.owiseLast` and `Fn.eqClauses` are removed.
An `[owise]` equation is a clause of priority 200, whether its arguments are variables or patterns.
`[priority(n)]` on a function rule gives the clause priority n.
The catch-all of a sort predicate (`sortPreds`) is `⟨[Srt.k], [.var 0], none, ff, 200⟩`.
The order of `clauses` carries no meaning; the reader keeps the file's order so that printing is stable.

## 2. The relation

```lean
| clause (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hprio : ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → Fails c vs cl')
    (hrhs : EvalTerm c σ cl.rhs r) : Eval c f vs r
| undef (hfn : c.lookupFn f = some fn) (hnone : ∀ cl ∈ fn.clauses, Fails c vs cl) : Eval c f vs none
```

`Fails`, `ReqFails`, `EvalTerm` and `EvalTerms` are unchanged.
This is `Step.rule` and `NotApplies` for clauses: a clause decides where it applies and no clause of a smaller priority applies.
`Fails` stays a positive statement (the `requires` evaluates to something other than `true`), so the definition stays inductive.

Why this is K's meaning and first match is not.
K's equations of one priority are unordered, so a relation that reads their order gives a meaning to something K does not.
First match is equal to the unordered reading only when clauses of one priority never disagree, which is what `wf` used to demand syntactically and what blocked KEVM.
Here the relation is the unordered one, and agreement is a property proved about it.

## 3. Functionality

The relation is not functional by construction: two clauses of one priority, or two matches of one clause, may both apply.

```lean
def Fun (σ) (u : Term) : Prop := ∀ r r', EvalTerm c σ u r → EvalTerm c σ u r' → r = r'
def HDet (σ) (t : Term) : Prop := ∀ u ∈ subterms t, Fun c σ u

def Coherent (cl cl' : Clause) : Prop :=
  ∀ vs σ σ', AppliesAt c cl σ vs → AppliesAt c cl' σ' vs →
    (∀ t, cl.req = some t → HDet c σ t) → HDet c σ cl.rhs →
    (cl.rhs = cl'.rhs ∧ ∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∨
    ∀ r r', EvalTerm c σ cl.rhs r → EvalTerm c σ' cl'.rhs r' → r = r'

def CoherentAll : Prop :=
  ∀ f fn, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, ∀ cl' ∈ fn.clauses, cl.prio = cl'.prio → Coherent c cl cl'

theorem Eval.functional (hco : CoherentAll c) : Eval c f vs r → Eval c f vs r' → r = r'
```

The theorem takes no sorting hypothesis, no `matchReady`, and does not go through the executable evaluator.
The proof is an induction on the first derivation (`PrioEval.lean`).

The shape of `Coherent` is forced by that induction, and each part is needed:

- **The first alternative** (the same instance of one right-hand side) is what a syntactic check can show.
  Turning it into equal results needs functionality of evaluation, which is the theorem being proved; the induction supplies it for the first derivation's right-hand side.
  `clauseFixed` gives this alternative for a clause against itself; `clausesAgree` gives it for two clauses.
- **The second alternative** is the semantic statement, for a pair no check confirms. It is what a user proves.
- **The `HDet` hypotheses** are what a check that two `requires` exclude each other reads (`litExcluded_sound` calls `evalTerm_det` on terms inside the `requires`).
  They hold for the first clause under its match because evaluation is strict: a derivation for a term holds one for every term inside it, so the induction hypothesis covers them.
  Nothing is available for the second clause's terms; a check must compare at terms inside the first clause, which a term common to both is.

Names kept from wave 1, as instances:
`MatchIndependent c cl := Coherent c cl cl`;
`ClausesAgree c fn := ∀ cl cl' ∈ fn.clauses, cl.prio = cl'.prio → Coherent c cl cl'`.
`Obligations` lists the pairs (and single clauses) the deciders do not confirm, each as `Coherent`.

## 4. The executable evaluator

`firstClause` reads `fn.clauses` sorted by priority (a stable insertion sort; `Fn` does not store the sorted list).

- **Soundness** (a result of the evaluator is an `Eval` derivation) needs no coherence.
  The evaluator returned from clause `cl` after every clause before it in sorted order failed; those include every clause of a smaller priority, which is `hprio`.
- **Completeness** (an `Eval` result is computed with some fuel) needs more than today.
  First match makes the failure of each earlier clause part of the derivation, so the evaluator's work on them is bounded by it.
  The unordered relation says nothing about clauses of the same priority that the evaluator tries first: their `requires` or right-hand side may not terminate.
  Completeness therefore takes `CoherentAll c` and that evaluation terminates on well-sorted arguments (TM-1's `Terminates` for every function, with subject reduction to keep arguments sorted).
  This is a property of sequential evaluation, not a defect of the statement: a backend that tries the same clause first loops there too.

KN-2 therefore comes after TM-1.

## 5. What changes, and the lemma each needs

| file | change | needs |
|---|---|---|
| Core | `Clause.prio`; `Owise`, `Fn.owise`, `owiseLast`, `eqClauses` removed; `sortPreds` | — |
| Evaluation | `Eval.clause`, `Eval.undef` as §2 | — |
| EvalFunctional | replaced by `PrioEval.lean`'s proof | — |
| Parse, Definition | an `[owise]` equation is a clause of priority 200; `priority` read on equations; `OwisePres` folds into `ClausePres` | — |
| Emit, Statements | a clause's premise excludes the clauses of smaller priority (today: the owise premise excludes all); `fnOwiseDisjunct` goes | FA-0 states Γ_D from `Semantics`, so the tie's agreement is a separate lemma |
| DefinitionWf, TablesChecked | `owiseOK` folds into `clauseOK`; `totalOK`'s cover check reads all clauses; deciders of `Coherent` range over equal-priority pairs | `clauseFixed_sound`, `fnExclusiveOK_sound` restated to conclude `Coherent` |
| FnExclusive | `evalTerm_det` at terms inside a `requires` is replaced by the `HDet` hypothesis | each use is at a term inside the first clause's `requires` |
| Exec | `firstClause` over the sorted clauses, no owise branch | sorted list is a permutation; before `cl` in it lie all smaller priorities |
| EvalSound | as §4 | — |
| EvalComplete | as §4, with `CoherentAll` and termination | `Eval.functional`; every well-sorted term has a result when every function terminates |
| SubjectReduction | the owise case goes | — |
| DetSound (`:635`, `:706`), Determinism (`:149`) | patterns on `fn.owise` become patterns on a priority-200 clause | — |
| Features | `owiseFns` reads `prio` | — |
| KcoreGen | prints `prio`; lists the `Coherent` obligations | — |

## 6. Not decided here

The translation of clause priorities into Γ_D, and the function-closure axioms that make a partial function under a priority sound, are FA-0's.

## 7. Correction to §4 (2026-11-12)

§4's completeness claim is false: termination of every function does not make a sequential evaluator complete for the unordered relation.
Take `f(x) = 1 requires g(x)`, `f(x) = 1` (one priority) and `g(x) = f(x) ==Int 1`.
Relationally every call has a result: `f(x) = 1` by the second clause, so `g(x) = true`.
An evaluator that tries the first clause first evaluates `g(x)`, which calls `f(x)`, and never returns.

The evaluator therefore does not commit to the first clause of a priority.
Per priority, in increasing order, it evaluates every candidate clause and match with the fuel it has and takes the first whose `requires` is true and whose right-hand side has a value.
A candidate that runs out of fuel is skipped, not fatal.
Its completeness needs `CoherentAll` only: no termination and no `clausesFixed`.

Consequences in statements: `step_iff` and the stuck-check soundness take `CoherentAll` where they took `clausesFixed`; the determinism theorems take `CoherentAll` where they took `MatchIndependentAll`, because under the unordered relation two clauses of one priority can only give one result if they agree.
`ClausesAgree` ranges over pairs of distinct clauses in both orders; a clause against itself is `MatchIndependent`.
