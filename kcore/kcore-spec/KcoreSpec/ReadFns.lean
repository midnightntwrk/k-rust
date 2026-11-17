/-
  Reading functions over `RawEqn` for an equation's right side that holds a matching-logic
  connective, beside the landed reader (Parse.lean). `clauseBody` calls none of them: a text is
  read as before, and no account changes. Each is structurally recursive and reduces in the kernel
  (test/RhsReader.lean and test/ExClauseReader.lean check an instance of each by `kernel_rfl`).

  - `frRead`: `\or` on the right side of an equation of a function whose `functional` sentence the
    text holds, as n+1 clauses with a premise predicate (`Clause.pre`).
  - `exRead` (`existsAsCases`): `\exists` over one Bool variable on the right side of an equation
    of such a function, as the clauses of its two instances; `condOf`, a predicate pattern as a
    `Cond`.
  - `ceRead`: `\exists` on an equation's right side as the clause's existential variables
    (`Clause.exs`), the body's predicates as its right-side predicate (`Clause.post`); `cutAnd`, a
    conjunction of terms at a term position as a fresh existential variable with its memberships.
-/
import KcoreSpec.Parse

set_option autoImplicit false

namespace KCore.Parse

open KoreAML.Parse (sortName?)
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

/-! ## Predicates as conditions -/

mutual
  /-- `p` with the free occurrences of the element variable `x` replaced by the closed pattern `v`. -/
  def substVal (x : Kore.EVar) (v : Kore.Pattern) : Kore.Pattern → Kore.Pattern
    | .var (.evar z) => if decide (z = x) then v else .var (.evar z)
    | .app h ss ps => .app h ss (substValList x v ps)
    | .and s ps => .and s (substValList x v ps)
    | .or s ps => .or s (substValList x v ps)
    | .not s p => .not s (substVal x v p)
    | .exist s z p => if decide (z = x) then .exist s z p else .exist s z (substVal x v p)
    | .forall s z p => if decide (z = x) then .forall s z p else .forall s z (substVal x v p)
    | .ceil s r p => .ceil s r (substVal x v p)
    | .floor s r p => .floor s r (substVal x v p)
    | .equals s r p q => .equals s r (substVal x v p) (substVal x v q)
    | .in s r p q => .in s r (substVal x v p) (substVal x v q)
    | .implies s p q => .implies s (substVal x v p) (substVal x v q)
    | .iff s p q => .iff s (substVal x v p) (substVal x v q)
    | p => p
    termination_by structural p => p
  def substValList (x : Kore.EVar) (v : Kore.Pattern) : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => substVal x v p :: substValList x v ps
    termination_by structural ps => ps
end

mutual
  /-- The conjuncts of a conjunction, nested ones flattened. -/
  def andParts : Kore.Pattern → List Kore.Pattern
    | .and _ ps => andPartsList ps
    | p => [p]
    termination_by structural p => p
  def andPartsList : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => andParts p ++ andPartsList ps
    termination_by structural ps => ps
end

/-- A conjunction's conjuncts that are no predicates (`isPred`), and its predicate conjuncts,
`\top` dropped. The split is by `isPred`, before any conjunct is read: `hoist` lifts only
`{B #Equals true}`, and `term` reads `\and(p, X)` as `p #as X`. -/
def bodyParts (p : Kore.Pattern) : List Kore.Pattern × List Kore.Pattern :=
  let ps := andParts p
  (ps.filter (!isPred ·), ps.filter fun q => isPred q && (match q with | .top _ => false | _ => true))

/-- A term of a right side or of a predicate's operand, read where it holds no conjunction under
applications (`patternConnective` otherwise): `term` reads `\and(p, X)` as the left-side pattern
`p #as X`, which a right side does not have; there the conjunction is the elements both hold. -/
def termNoAnd (N : Names) (vs : List Var) (p : Kore.Pattern) : Rd (Term × List Var) :=
  if hasAnd p then fail .patternConnective "\\and" else term N vs p

/-- The disjunction of the conditions, `\bottom` for none. -/
def disjC : List Cond → Cond
  | [] => .bot
  | [p] => p
  | p :: ps => .or p (disjC ps)

mutual
  /-- A predicate pattern as a condition: `\equals`, `\in` and `\ceil` of terms, at the sort of
  their operands, `\top`, `\bottom` and their connectives `\not`, `\implies`, `\and`, `\or`. Any
  other pattern, a binder among them, is refused `patternConnective`, and so is an operand that
  holds a conjunction under applications (`termNoAnd`). -/
  def condOf (N : Names) (vs : List Var) : Kore.Pattern → Rd (Cond × List Var)
    | .top _ => pure (.top, vs)
    | .bottom _ => pure (.bot, vs)
    | .equals s _ p q => do
      let (t, vs) ← termNoAnd N vs p
      let (u, vs) ← termNoAnd N vs q
      pure (.equals (← N.sortE s) t u, vs)
    | .in s _ p q => do
      let (t, vs) ← termNoAnd N vs p
      let (u, vs) ← termNoAnd N vs q
      pure (.mem (← N.sortE s) t u, vs)
    | .ceil s _ p => do
      let (t, vs) ← termNoAnd N vs p
      pure (.ceil (← N.sortE s) t, vs)
    | .not _ p => do
      let (c, vs) ← condOf N vs p
      pure (.not c, vs)
    | .implies _ p q => do
      let (c, vs) ← condOf N vs p
      let (d, vs) ← condOf N vs q
      pure (.implies c d, vs)
    | .and _ ps => do
      let (cs, vs) ← condOfList N vs ps
      pure (conjC cs, vs)
    | .or _ ps => do
      let (cs, vs) ← condOfList N vs ps
      pure (disjC cs, vs)
    | p => fail .patternConnective (connective p)
    termination_by structural p => p
  def condOfList (N : Names) (vs : List Var) : List Kore.Pattern → Rd (List Cond × List Var)
    | [] => pure ([], vs)
    | p :: ps => do
      let (c, vs) ← condOf N vs p
      let (cs, vs) ← condOfList N vs ps
      pure (c :: cs, vs)
    termination_by structural ps => ps
end

/-- The conjunction of the predicate patterns, as one condition. -/
def condsOf (N : Names) (vs : List Var) (ps : List Kore.Pattern) : Rd (Cond × List Var) := do
  let (cs, vs) ← condOfList N vs ps
  pure (conjC cs, vs)

mutual
  /-- The pattern holds an `\exists`. -/
  def hasExists : Kore.Pattern → Bool
    | .exist .. => true
    | .app _ _ ps | .and _ ps | .or _ ps => hasExistsList ps
    | .not _ p | .ceil _ _ p | .floor _ _ p | .forall _ _ p => hasExists p
    | .equals _ _ p q | .in _ _ p q | .implies _ p q | .iff _ p q => hasExists p || hasExists q
    | _ => false
    termination_by structural p => p
  def hasExistsList : List Kore.Pattern → Bool
    | [] => false
    | p :: ps => hasExists p || hasExistsList ps
    termination_by structural ps => ps
end

/-! ## `\exists` over one Bool variable, by cases (`existsAsCases`)

The sentence is `premise → f(X̄) = ∃B:Bool. (t ∧ P)`. Where the elements of Bool are the two
literals the right side is `(t[true] ∧ P[true]) ∨ (t[false] ∧ P[false])`, an `\or` of two
alternatives, read as `frRead` reads one. -/

/-- The Bool literal `b`, as a pattern. -/
def boolDv (b : Bool) : Kore.Pattern := .dv (KoreAML.srt "Bool") (if b then "true" else "false")

/-- The right side is one `\exists` over a Bool variable whose body holds no further `\exists`
and has exactly one conjunct that is no predicate: the variable, that conjunct, the predicates. -/
def exShape? (e : RawEqn) : Option (Kore.EVar × Kore.Pattern × List Kore.Pattern) :=
  match e.rhs with
  | .exist _ B body =>
    if sortName? B.sort == some "Bool" && !hasExists body then
      match bodyParts body with
      | ([t], ps) => some (B, t, ps)
      | _ => none
    else none
  | _ => none

/-- The alternatives `(b, a)`, a an alternative of `t[b]`: a's term with the predicates `P[b]`. -/
def exAlts (N : Names) (B : Kore.EVar) (ps : List Kore.Pattern) :
    List Var → List (Bool × Kore.Pattern) → Rd (List (Term × List Cond) × List Var)
  | vs, [] => pure ([], vs)
  | vs, x :: rest => do
    if let some c := manyValued? x.2 then fail .manyValuedRightSide c
    let (a, vs) ← termNoAnd N vs x.2
    let (cs, vs) ← condOfList N vs (substValList B (boolDv x.1) ps)
    let (xs, vs) ← exAlts N B ps vs rest
    pure ((a, cs) :: xs, vs)
  termination_by structural _ rest => rest

/-- `existsAsCases`: an equation whose right side is `\exists B:Bool. (t ∧ P)` (`exShape?`), of a
function whose `functional` sentence the text holds: `frClauses` over the alternatives of
`t[true]` and of `t[false]` (`orAlts`), alternative k of `t[b]` with the predicates `P[b]` and the
equation's `ensures`.
`none` where the right side is not of that shape or the text does not hold the `functional`
sentence: the reading is not this function's.
Refused `manyValuedRightSide`: more than 8 alternatives; an alternative, a predicate or the
`ensures` holds a variable the arguments do not bind; an alternative holds `\top`, `\not` or
`\or` under no application. Refused `patternConnective`: a predicate `condOf` does not read; a
conjunction under applications of an alternative.
That the definition's Bool literals are its Bool values (`litSort Srt.bool`) is decided on the
built definition, not here. -/
def exRead (N : Names) (e : RawEqn) : Rd (Option (List Clause × List Var)) := do
  let some (B, t, ps) := exShape? e | pure none
  if !eqnFnl N e then pure none else
  let (pats, req, ens, vs, np) ← eqnHead N e
  let insts := [true, false].flatMap fun b => (orAlts (substVal B (boolDv b) t)).map (b, ·)
  if insts.length > 8 then fail .manyValuedRightSide s!"\\exists: {insts.length} alternatives, more than 8"
  let (alts, vs) ← exAlts N B ps vs insts
  boundByArgs vs np "\\exists"
    (alts.flatMap (fun a => varOccs a.1 ++ a.2.flatMap (varOccsCond vs.length)) ++ ens.toList.flatMap varOccs)
  let s ← resSort N e
  let alts := alts.map fun a => (a.1, a.2 ++ ens.toList.map isTrueC)
  pure (some (frClauses s (← varSorts N vs) pats req (eqnPrio e).2 (nonExec e) alts, vs))

/-! ## `\exists` on an equation's right side as the clause's existential variables

The sentence is `premise → f(X̄) = ∃x̄. (t ∧ P)`. The clause with `exs` the variables x̄, `rhs` t
and `post` P states that sentence: nothing is asked of the function or of the sorts of x̄ here.
Whether the definition admits the clause (each variable of x̄ of a confined sort or fixed by `post`)
is decided on the built definition. -/

/-- The indices of a right side's bound variables, in order, each a variable the first `n0` do
not name (`patternConnective` otherwise: the binder is not read renamed apart here). -/
def exBind (n0 : Nat) : List Var → List Kore.EVar → Rd (List Nat × List Var)
  | vs, [] => pure ([], vs)
  | vs, x :: xs => do
    let (i, vs) ← varIndex vs x
    if i < n0 then fail .patternConnective x.var.ident.name
    let (is, vs) ← exBind n0 vs xs
    pure (i :: is, vs)
  termination_by structural _ xs => xs

/-! ### `\and` of terms at a term position

`t₁ ∧ … ∧ tₙ` of terms is the elements every tⱼ holds. At a position `C[·]` under applications,
`C[t₁ ∧ … ∧ tₙ] = ∃Z. C[Z] ∧ Z ∈ t₁ ∧ … ∧ Z ∈ tₙ` for a fresh Z of the conjunction's sort: an
application holds the elements its arguments' elements give, and `Z ∈ tⱼ` holds exactly where the
element Z is one of tⱼ's. A predicate conjunct P of the conjunction is everything or nothing, so
`C[φ ∧ P] = C[φ] ∧ P`. Nothing is asked of the tⱼ (not that each has at most one element, not an
equality hook). Where a conjunct is an element variable V the conjunction is V where every other
conjunct holds it, `V ∧ t₂ ∧ … ∧ tₙ = V ∧ V ∈ t₂ ∧ … ∧ V ∈ tₙ`, so an `\exists` variable of the
equation that is a conjunct stands in the position itself and no variable is added. -/

/-- A cut: the variable that stands in the position, the conjunction's sort, its term conjuncts. -/
abbrev Cut := Kore.EVar × Kore.KSort × List Kore.Pattern

mutual
  /-- A pattern at a term position with each maximal conjunction of two or more terms under
  applications replaced by a variable: the first conjunct that is a variable named in `bound` (the
  equation's `\exists` variables), the cut's conjuncts then the others; where there is none, a
  fresh variable (`Var'Hash'Cut` and a number from `n`, primed until no name of `used` is it).
  The pattern, the next number, the cuts (one inside a conjunct before the conjunct's own), and
  the predicate conjuncts lifted out of the conjunctions. A conjunction with one term conjunct is
  that conjunct; one with none is `\top` of its sort. -/
  def cutAnd (used bound : List String) (n : Nat) : Kore.Pattern → Kore.Pattern × Nat × List Cut × List Kore.Pattern
    | .app h ss ps => let (ps', n, cs, qs) := cutAndList used bound n ps; (.app h ss ps', n, cs, qs)
    | .and s ps =>
      let (ts, n, cs, qs) := cutConjList used bound n ps
      match ts with
      | [] => (.top s, n, cs, qs)
      | [t] => (t, n, cs, qs)
      | _ =>
        match ts.findSome? (fun t => match t with
            | .var (.evar v) => if bound.contains v.var.ident.name then some v else none
            | _ => none) with
        | some v => (.var (.evar v), n, cs ++ [(v, s, ts.filter fun t => !decide (t = .var (.evar v)))], qs)
        | none =>
          let z := KoreAML.evar (freshIn used (used.length + 1) s!"Var'Hash'Cut{n}") s
          (.var (.evar z), n + 1, cs ++ [(z, s, ts)], qs)
    | p => (p, n, [], [])
    termination_by structural p => p
  def cutAndList (used bound : List String) (n : Nat) :
      List Kore.Pattern → List Kore.Pattern × Nat × List Cut × List Kore.Pattern
    | [] => ([], n, [], [])
    | p :: ps =>
      let (p', n, cs, qs) := cutAnd used bound n p
      let (ps', n, cs', qs') := cutAndList used bound n ps
      (p' :: ps', n, cs ++ cs', qs ++ qs')
    termination_by structural ps => ps
  /-- A conjunct of a conjunction at a term position: its term conjuncts (a nested conjunction's
  flattened, each cut inside), and its predicates (`isPred`, `\top` dropped). -/
  def cutConj (used bound : List String) (n : Nat) : Kore.Pattern → List Kore.Pattern × Nat × List Cut × List Kore.Pattern
    | .and _ ps => cutConjList used bound n ps
    | .app h ss ps => let (ps', n, cs, qs) := cutAndList used bound n ps; ([.app h ss ps'], n, cs, qs)
    | .top _ => ([], n, [], [])
    | p => if isPred p then ([], n, [], [p]) else ([p], n, [], [])
    termination_by structural p => p
  def cutConjList (used bound : List String) (n : Nat) :
      List Kore.Pattern → List Kore.Pattern × Nat × List Cut × List Kore.Pattern
    | [] => ([], n, [], [])
    | p :: ps =>
      let (ts, n, cs, qs) := cutConj used bound n p
      let (ts', n, cs', qs') := cutConjList used bound n ps
      (ts ++ ts', n, cs ++ cs', qs ++ qs')
    termination_by structural ps => ps
end

/-- The memberships of the cuts, `Z ∈ tⱼ` for each conjunct tⱼ of each cut, at the cut's sort. -/
def cutMems (N : Names) : List Var → List Cut → Rd (List Cond × List Var)
  | vs, [] => pure ([], vs)
  | vs, c :: cs => do
    let (z, vs) ← varIndex vs c.1
    let s ← N.sortE c.2.1
    let (ts, vs) ← terms N vs c.2.2
    let (ms, vs) ← cutMems N vs cs
    pure (ts.map (Cond.mem s (.var z) ·) ++ ms, vs)
  termination_by structural _ cs => cs

/-- An equation whose right side is `\exists x̄. body` (x̄ possibly empty), body under no further
binder: one clause. `exs` is the variables x̄ in the text's order of nesting, then the fresh
variables of `cutAnd`, which reads each conjunction of terms under applications of the body (a
conjunction with a variable of x̄ among its conjuncts as that variable); `rhs` is the body
so read; `post` is every predicate of the body (`condOf`), so that `Cond.fixes` reads them, then
the cuts' memberships; the equation's own `ensures` stays `ens`.
Refused `patternConnective`: a variable of x̄ that the arguments, the `requires` or the `ensures`
hold, or that is bound twice (these binders are not read here: a rule's are, renamed apart or
dropped, `rhsApart` and `exKept`).
Refused `unheldVariable`: a variable of x̄ that the body does not hold (the sentence then states
the term only where the variable's sort has an element, which the clause would not say: unlike a
rule's sentence, `f(x̄) = ∃Z:s. t` at an empty s is `f(x̄) = ⊥`, which does not entail `f(x̄) = t`).
Refused `manyValuedRightSide`: no term conjunct (`\top`: the body is a predicate, every element
or none); a further `\exists` in the body; `\or`, `\top` or `\not` under applications of the
term or of a cut's conjunct.
Refused `patternConnective`: a predicate `condOf` does not read. -/
def ceRead (N : Names) (e : RawEqn) : Rd (Clause × List Var) := do
  let (pats, req, ens, vs, _) ← eqnHead N e
  let n0 := vs.length
  let (xs, body) := peelExists e.rhs
  if hasExists body then fail .manyValuedRightSide "\\exists"
  if isPred body then fail .manyValuedRightSide "\\top"
  let bound := xs.map (·.var.ident.name)
  let (t, _, cuts, ps) := cutAnd (evarNamesList (e.rhs :: e.pats ++ e.req.toList ++ e.ens.toList)) bound 0 body
  if let some c := (t :: cuts.flatMap (·.2.2)).findSome? manyValued? then fail .manyValuedRightSide c
  if let some x := xs.find? (fun x => !(evarNames body).contains x.var.ident.name) then
    fail .unheldVariable s!"{x.var.ident.name}: bound by \\exists, not held by its body"
  let (exs, vs) ← exBind n0 vs xs
  unless nodup exs do fail .patternConnective s!"{(xs.headD default).var.ident.name}: bound twice"
  let (zs, vs) ← exBind n0 vs ((cuts.map (·.1)).filter (!bound.contains ·.var.ident.name))
  let (rhs, vs) ← term N vs t
  let (cs, vs) ← condOfList N vs ps
  let (ms, vs) ← cutMems N vs cuts
  pure ({ vars := ← varSorts N vs, pats, req, rhs, ens, prio := (eqnPrio e).2, aside := nonExec e,
          exs := exs ++ zs, post := conjC (cs ++ ms) }, vs)

end KCore.Parse
