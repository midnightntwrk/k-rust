/-
  Reading functions over `RawEqn` for an equation's right side that holds a matching-logic
  connective, beside the landed reader (Parse.lean). `clauseBody` calls none of them: a text is
  read as before, and no account changes. Each is structurally recursive and reduces in the kernel
  (test/RhsReader.lean checks an instance of each by `kernel_rfl`).

  - `frRead`: `\or` on the right side of an equation of a function whose `functional` sentence the
    text holds, as n+1 clauses with a premise predicate (`Clause.pre`).
-/
import KcoreSpec.Parse

set_option autoImplicit false

namespace KCore.Parse

open KoreAML (Var)

/-! ## Shared -/

/-- The conjunction of the conditions, `\top` for none. -/
def conjC : List Cond → Cond
  | [] => .top
  | [p] => p
  | p :: ps => .and p (conjC ps)

/-- The Bool literal `b`. -/
def boolT (b : Bool) : Term := .dv Srt.bool (.bool b)

/-- `\equals{Bool,_}(b, true)`: the Bool term b is true. -/
def isTrueC (b : Term) : Cond := .equals Srt.bool b (boolT true)

/-- The text holds the `functional` sentence of the equation's function: the function has exactly
one element at every argument list. -/
def eqnFnl (N : Names) (e : RawEqn) : Bool := N.fnlSyms.contains (e.fn, false)

/-- The result sort of the equation's function (`Names.keyFns`). -/
def resSort (N : Names) (e : RawEqn) : Rd Srt := do
  let f ← N.symE e.fn
  N.srtE (← need (N.keyFns.lookup f) .unknownSymbol e.fn)

/-- An equation's head as `clauseBody` reads it: the patterns, the `requires`, the `ensures`, the
variables they hold, and how many of those the patterns hold. -/
def eqnHead (N : Names) (e : RawEqn) : Rd (List Term × Option Term × Option Term × List Var × Nat) := do
  let (pats, vs) ← svinPats N e
  let np := vs.length
  let (req, vs) ← match e.req with
    | none => pure (none, vs)
    | some r => do let (t, vs) ← eqnCondTerm N vs r; pure (some t, vs)
  let (ens, vs) ← match e.ens with
    | none => pure (none, vs)
    | some c => do let (t, vs) ← eqnCondTerm N vs c; pure (some t, vs)
  pure (pats, req, ens, vs, np)

/-- The first variable among `used` that the patterns do not hold (its index is `np` or more):
`manyValuedRightSide` naming it. Clauses split from one sentence each carry the sentence's
variables; one that the arguments do not bind would stand in a clause's premise predicate, where
no value of the arguments decides it. -/
def boundByArgs (vs : List Var) (np : Nat) (conn : String) (used : List Nat) : Rd Unit :=
  match used.find? (np ≤ ·) with
  | some i => fail .manyValuedRightSide
      s!"{conn}: Var{(vs.getD i default).name}: in an alternative or the ensures, not bound by the arguments"
  | none => pure ()

/-! ## `\or` on the right side of an equation of a function with its `functional` sentence

The sentence is `premise → f(X̄) = ⋁ₖ (aₖ ∧ Pₖ)`, Pₖ the predicates of alternative k. With f's
`functional` sentence the right side is one element where it is not empty, so each alternative
that is defined where its predicates hold is that element, and where none is the sentence has no
model. The clauses state `preₖ → f(X̄) = aₖ` for each k, with `preₖ := ⌈aₖ⌉ ∧ Pₖ`, and
`f(X̄) = ⊥` where no `preₖ` holds. Without the `functional` sentence the text has a model where
`f(x̄)` is several elements, which no clause states. -/

/-- The clauses of the alternatives `(aₖ, Pₖ)` of a right side at the sort `s` (one alternative or
more): for each k `pre := ⌈aₖ⌉ ∧ Pₖ`, `rhs := aₖ`; and one more with `pre := ⋀ₖ ¬preₖ`, the first
alternative as its `rhs` and the `ensures` false. -/
def frClauses (s : Srt) (vars : List Srt) (pats : List Term) (req : Option Term) (prio : Nat) (aside : Bool)
    (alts : List (Term × List Cond)) : List Clause :=
  let pres := alts.map fun a => conjC (Cond.ceil s a.1 :: a.2)
  let each := (alts.zip pres).map fun x =>
    ({ vars, pats, req, rhs := x.1.1, ens := none, prio, aside, pre := x.2 } : Clause)
  each ++ [{ vars, pats, req, rhs := (alts.headD (boolT false, [])).1, ens := some (boolT false), prio, aside,
             pre := conjC (pres.map Cond.not) }]

/-- One alternative: its term and the `{B #Equals true}` conjuncts `hoist` lifts out of it, as
conditions; `none` where it is empty. A connective with several elements or none in it is refused
`manyValuedRightSide`, a conjunction of two terms `patternConnective`. -/
def altOf (N : Names) (vs : List Var) (a : Kore.Pattern) : Rd (Option (Term × List Cond) × List Var) := do
  let (r, conds, empty) := hoist a
  if empty then pure (none, vs) else
  if let some c := manyValued? r then fail .manyValuedRightSide c
  unless conds.all (fun c => match c with | .isTrue b => eqnCondOK N b | .same .. => false) do
    fail .patternConnective "\\and"
  let (t, vs) ← term N vs r
  let (cs, vs) ← sideConds N vs conds
  pure (some (t, cs.map isTrueC), vs)

/-- The alternatives that are not empty, in order. -/
def altsOf (N : Names) : List Var → List Kore.Pattern → Rd (List (Term × List Cond) × List Var)
  | vs, [] => pure ([], vs)
  | vs, a :: as => do
    let (x, vs) ← altOf N vs a
    let (xs, vs) ← altsOf N vs as
    pure (x.toList ++ xs, vs)
  termination_by structural _ as => as

/-- The detail of `manyValuedRightSide` for an `\or` in an equation of a function without its
`functional` sentence. -/
def orNotFunctional : String :=
  "\\or: the sentence gives the function every element of each side; the function is not declared total, so where the sides differ that is more than one element, which no clause states"

/-- An equation whose right side, after `hoist`, holds `\or` under applications and conjunctions:
the clauses of its alternatives (`orAlts`, the `\or` distributed over applications), each read
through `hoist`, the equation's `ensures` and the `{B #Equals true}` conjuncts lifted at the top
among the predicates of every alternative.
`none` where the right side is empty or holds no `\or`, or where fewer than two alternatives are
not empty: the reading is not this function's.
Refused `manyValuedRightSide`: the text does not hold the function's `functional` sentence; more
than 8 alternatives; an alternative, a lifted conjunct or the `ensures` holds a variable the
arguments do not bind; an alternative holds `\top`, `\not` or `\exists`. -/
def frRead (N : Names) (e : RawEqn) : Rd (Option (List Clause × List Var)) := do
  let (r, conds, empty) := hoist e.rhs
  if empty || !hasOr r then pure none else
  let (pats, req, ens, vs, np) ← eqnHead N e
  unless eqnFnl N e do fail .manyValuedRightSide orNotFunctional
  let as := orAlts r
  if as.length > 8 then fail .manyValuedRightSide s!"\\or: {as.length} alternatives, more than 8"
  unless conds.all (fun c => match c with | .isTrue b => eqnCondOK N b | .same .. => false) do
    fail .patternConnective "\\and"
  let (cs, vs) ← sideConds N vs conds
  let (alts, vs) ← altsOf N vs as
  if alts.length < 2 then pure none else
  let common := ens.toList ++ cs
  boundByArgs vs np "\\or"
    (alts.flatMap (fun a => varOccs a.1 ++ a.2.flatMap (varOccsCond vs.length)) ++ common.flatMap varOccs)
  let s ← resSort N e
  let alts := alts.map fun a => (a.1, common.map isTrueC ++ a.2)
  pure (some (frClauses s (← varSorts N vs) pats req (eqnPrio e).2 (nonExec e) alts, vs))

end KCore.Parse
