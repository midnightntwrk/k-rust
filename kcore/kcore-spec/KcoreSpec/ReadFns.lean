/-
  Reading functions over `RawEqn` for an equation's right side that holds a matching-logic
  connective, beside the landed reader (Parse.lean). `clauseBody` calls none of them: a text is
  read as before, and no account changes. Each is structurally recursive and reduces in the kernel
  (test/RhsReader.lean and test/ExClauseReader.lean check an instance of each by `kernel_rfl`).

  - `dropEmptyAlts`: a right side with the alternatives of its `\or`s that are `\bottom` left out.
  - `frRead`: `\or` on the right side of an equation of a function whose `functional` sentence the
    text holds, as n+1 clauses with a premise predicate (`Clause.pre`).
  - `exRead` (`existsAsCases`): `\exists` over one Bool variable on the right side of an equation
    of such a function, as the clauses of its two instances; `condOf`, a predicate pattern as a
    `Cond`.
  - `ceRead`: `\exists` on an equation's right side as the clause's existential variables
    (`Clause.exs`), the body's predicates as its right-side predicate (`Clause.post`); `cutAnd`, a
    conjunction of terms at a term position as a fresh existential variable with its memberships;
    `orCut`, a disjunction of terms at a term position as a fresh existential variable with the
    disjunction of its memberships.
  - `hoistExists`: each `\exists` of an equation's right side under applications, `\and` conjuncts
    and `\or` alternatives moved to the top, renamed apart; the binder of an `\or` alternative only
    at a sort the caller's test of a value accepts (`valuedSort`: `Semantics.valued` on a built
    definition).
-/
import KcoreSpec.Parse

set_option autoImplicit false

namespace KCore.Parse

open KoreAML.Parse (sortName?)
open KoreAML (Var)

/-! ## Shared -/

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

/-! ## Alternatives that are `\bottom`

`⊥ ∨ φ = φ`, so an alternative that is `\bottom` (`vacuous`) adds no element to its `\or`: the
sentence is the one without it. With one alternative left no `\or` is written; with none the
`\or` is `\bottom`. -/

mutual
  /-- A right side with each `\or` under applications and conjunctions replaced by its
  alternatives that are not `vacuous` (each read so first): the one left where one is left,
  `\bottom` of the `\or`'s sort where none is. The result is `vacuous` exactly where the pattern
  is, and otherwise no alternative of an `\or` under its applications and conjunctions is. -/
  def dropEmptyAlts : Kore.Pattern → Kore.Pattern
    | .app h ss ps => .app h ss (dropEmptyAltsList ps)
    | .and s ps => .and s (dropEmptyAltsList ps)
    | .or s ps => match (dropEmptyAltsList ps).filter (!vacuous ·) with
      | [] => .bottom s
      | [p] => p
      | qs => .or s qs
    | p => p
    termination_by structural p => p
  def dropEmptyAltsList : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => dropEmptyAlts p :: dropEmptyAltsList ps
    termination_by structural ps => ps
end

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
  "\\or: the sentence gives the function every element of each side; the text holds no functional sentence of the function, so where the sides differ that is more than one element, which no clause states"

/-- An equation whose right side, after `dropEmptyAlts` and `hoist`, holds `\or` under
applications and conjunctions: the clauses of its alternatives (`orAlts`, the `\or` distributed
over applications), each read through `hoist`, the equation's `ensures` and the
`{B #Equals true}` conjuncts lifted at the top among the predicates of every alternative.
`none` where the right side is empty or holds no `\or` once its empty alternatives are left out
(fewer than two alternatives are not empty): the sentence is then a plain equation or
`f(X̄) = ⊥`, and the reading is not this function's, whether or not the text holds the function's
`functional` sentence.
Refused `rhsOperandSort` where the right side is not `rhsSorted`, whether or not it is this
function's. Refused `manyValuedRightSide`, the right side having two alternatives or more: the text does not
hold the function's `functional` sentence; more than 8 alternatives; an alternative, a lifted
conjunct or the `ensures` holds a variable the arguments do not bind; an alternative holds
`\top`, `\not` or `\exists`. -/
def frRead (N : Names) (e : RawEqn) : Rd (Option (List Clause × List Var)) := do
  rhsSortGuard e.rhs
  let (r, conds, empty) := hoist (dropEmptyAlts e.rhs)
  if empty || !hasOr r then pure none else
  let as := orAlts r
  if as.length < 2 then pure none else
  let (pats, req, ens, vs, np) ← eqnHead N e
  unless eqnFnl N e do fail .manyValuedRightSide orNotFunctional
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

/-- `frRead` reads only a right side that is `rhsSorted`. -/
theorem frRead_rhsSorted {N : Names} {e : RawEqn} {x : Option (List Clause × List Var)}
    (h : frRead N e = .ok x) : rhsSorted e.rhs = true := by
  obtain ⟨u, hu⟩ := rhsSortGuard_bind (p := e.rhs) h
  exact rhsSortGuard_ok hu

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

/-! ## `\and` of terms at a term position

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

/-! ## `\exists` over one Bool variable, by cases (`existsAsCases`)

The sentence is `premise → f(X̄) = ∃B:Bool. (t ∧ P)`. Where the elements of Bool are the two
literals the right side is `(t[true] ∧ P[true]) ∨ (t[false] ∧ P[false])`, an `\or` of two
alternatives, read as `frRead` reads one.
The body is taken after `cutAnd` with B the one bound variable: a predicate under applications
is among P, and a conjunction of terms with B among its conjuncts is B with `B ∈ u` among P for
each other conjunct u. A conjunction of terms without B has no such form over B alone (its form
is a further `\exists` variable), so the equation is then not of this shape. -/

/-- The Bool literal `b`, as a pattern. -/
def boolDv (b : Bool) : Kore.Pattern := .dv (KoreAML.srt "Bool") (if b then "true" else "false")

/-- The right side is one `\exists` over a Bool variable B whose body holds no further
`\exists`, is no predicate, and in which `cutAnd` with B bound adds no variable (every
conjunction of two terms or more under applications has B among its conjuncts): the variable,
the body with each such conjunction read as B, and the predicates: those `cutAnd` lifts, then
`\in(B, u)` for each other conjunct u of each conjunction. -/
def exShape? (e : RawEqn) : Option (Kore.EVar × Kore.Pattern × List Kore.Pattern) :=
  match e.rhs with
  | .exist rs B body =>
    if sortName? B.sort == some "Bool" && !hasExists body && !isPred body then
      let (t, n, cuts, qs) := cutAnd [] [B.var.ident.name] 0 body
      if n == 0 && cuts.all (fun c => decide (c.1 = B)) then
        some (B, t, qs ++ cuts.flatMap fun c => c.2.2.map (Kore.Pattern.in c.2.1 rs (.var (.evar B))))
      else none
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
`\or` under no application. Refused `patternConnective`: a predicate `condOf` does not read (a
conjunct of a conjunction with B that is no term among them); a conjunction under an `\or` of an
alternative.
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

/-- The predicates of a right side with the operand of each `\ceil` among them read by `cutAnd`
(numbers from `n`): the predicates (a `\ceil`'s followed by those lifted out of its operand), the
next number, the cuts. `⌈C[t ∧ u]⌉ = ∃Z. (⌈C[Z]⌉ ∧ Z ∈ t ∧ Z ∈ u)`: `\ceil` of a union is the
union of the `\ceil`s, and `⌈φ ∧ P⌉ = ⌈φ⌉ ∧ P` for a predicate P. The `\ceil` is a conjunct of
the right side and Z is fresh, so the binder stands around the whole right side, with the
equation's own. A `\ceil` under another connective is not reached. -/
def cutCeils (used bound : List String) : Nat → List Kore.Pattern → List Kore.Pattern × Nat × List Cut
  | n, [] => ([], n, [])
  | n, .ceil s r q :: ps =>
    let (q', n, cs, qs) := cutAnd used bound n q
    let (ps', n, cs') := cutCeils used bound n ps
    (.ceil s r q' :: qs ++ ps', n, cs ++ cs')
  | n, p :: ps =>
    let (ps', n, cs') := cutCeils used bound n ps
    (p :: ps', n, cs')
  termination_by structural _ ps => ps

/-- The first binder whose variable (name and sort) a binder under it binds again. -/
def dupBinder : List Kore.EVar → Option Kore.EVar
  | [] => none
  | x :: xs => if xs.any (decide <| · = x) then some x else dupBinder xs

/-! ### `\or` of terms at a term position

`t₁ ∨ … ∨ tₙ` of terms is the elements some tⱼ holds. At a position `C[·]` under applications,
`C[t₁ ∨ … ∨ tₙ] = ∃Z. C[Z] ∧ Z ∈ (t₁ ∨ … ∨ tₙ)` for a fresh Z of the disjunction's sort (the cut
identity, which asks nothing of the pattern cut out), and `Z ∈ (φ ∨ ψ) = (Z ∈ φ) ∨ (Z ∈ ψ)`, Z
being one element. So the disjunction becomes a variable with one predicate, the disjunction of
its memberships; nothing is distributed, and the number of alternatives is not bounded. A
disjunction that is a conjunct of a conjunction of terms needs no variable of its own: the
conjunction's variable is a member of it.

An alternative is not a position under applications of the right side: where an alternative is
empty the other alternatives' elements stay. So a connective inside an alternative is not cut to
a variable beside the disjunction: `C[g(a ∨ b) ∨ t]` is `C[t]` where a and b are empty, and
`∃Z Z'. C[Z] ∧ (Z' ∈ a ∨ Z' ∈ b) ∧ (Z ∈ g(Z') ∨ Z ∈ t)` is empty there. What is read in an
alternative is what membership of the one element Z reads without a further variable (`memOf`):
`Z ∈ (φ ∨ ψ) = (Z ∈ φ) ∨ (Z ∈ ψ)`, `Z ∈ (φ ∧ ψ) = (Z ∈ φ) ∧ (Z ∈ ψ)`, and `Z ∈ (φ ∧ P) =
(Z ∈ φ) ∧ P` for a predicate P. A connective under an application of an alternative is refused. -/

mutual
  /-- A pattern at a term position with each disjunction under applications that is no predicate
  replaced by a fresh variable (`Var'Hash'Or` and a number from `n`, primed until no name of
  `used` is it): the pattern, the next number, and for each variable the cut whose one conjunct
  is the disjunction, as the text writes it. Nothing inside a disjunction is replaced. -/
  def orCut (used : List String) (n : Nat) : Kore.Pattern → Kore.Pattern × Nat × List Cut
    | .app h ss ps => let (ps', n, cs) := orCutList used n ps; (.app h ss ps', n, cs)
    | .or s ps =>
      if isPredList ps then (.or s ps, n, []) else
      let z := KoreAML.evar (freshIn used (used.length + 1) s!"Var'Hash'Or{n}") s
      (.var (.evar z), n + 1, [(z, s, [.or s ps])])
    | p => (p, n, [])
    termination_by structural p => p
  def orCutList (used : List String) (n : Nat) : List Kore.Pattern → List Kore.Pattern × Nat × List Cut
    | [] => ([], n, [])
    | p :: ps =>
      let (p', n, cs) := orCut used n p
      let (ps', n, cs') := orCutList used n ps
      (p' :: ps', n, cs ++ cs')
    termination_by structural ps => ps
end

/-- The conjuncts of a cut with `orCut` applied under the applications of each; a conjunct that
is a disjunction stays (the cut's variable is a member of it). -/
def orCutConjs (used : List String) (n : Nat) : List Kore.Pattern → List Kore.Pattern × Nat × List Cut
  | [] => ([], n, [])
  | p :: ps =>
    let (p', n, cs) := match p with
      | .or .. => (p, n, [])
      | p => orCut used n p
    let (ps', n, cs') := orCutConjs used n ps
    (p' :: ps', n, cs ++ cs')
  termination_by structural ps => ps

/-- `orCutConjs` on the conjuncts of each cut: the cuts, the next number, the disjunctions' cuts. -/
def orCutCuts (used : List String) (n : Nat) : List Cut → List Cut × Nat × List Cut
  | [] => ([], n, [])
  | c :: cs =>
    let (ts, n, os) := orCutConjs used n c.2.2
    let (cs', n, os') := orCutCuts used n cs
    ((c.1, c.2.1, ts) :: cs', n, os ++ os')
  termination_by structural cs => cs

/-- `orCut` on a right side's term and on the conjuncts of its conjunctions' cuts (`cutAnd`): the
term, and the cuts, the disjunctions' after the conjunctions'. -/
def orCutAll (used : List String) (t : Kore.Pattern) (cuts : List Cut) : Kore.Pattern × List Cut :=
  let (t', n, os) := orCut used 0 t
  let (cuts', _, os') := orCutCuts used n cuts
  (t', cuts' ++ os ++ os')

/-- The first connective that has several elements or none at a point (`manyValued?`) in the
right side's term or in a cut's conjunct after `orCutAll`; none in a conjunct that is a
disjunction of terms, whose alternatives `memOf` reads. -/
def orManyValued? (p : Kore.Pattern) : Option String :=
  match p with
  | .or .. => if isPred p then manyValued? p else none
  | p => manyValued? p

mutual
  /-- `Z ∈ p` for the variable `z` of sort `s`, p a term or a disjunction or conjunction of
  such: the disjunction of the memberships in a disjunction's alternatives; the conjunction of
  the memberships in a conjunction's conjuncts that are no predicates and of its predicates
  (`condOf`); `Z ∈ t` for a term.
  Refused `manyValuedRightSide`: a predicate where a term is read, a conjunction of predicates
  among them (`\top`: Z is in it wherever it holds); `\or`, `\top`, `\not` or `\exists` under an
  application. Refused `patternConnective`: a conjunction under an application (`termNoAnd`). -/
  def memOf (N : Names) (s : Srt) (z : Nat) (vs : List Var) : Kore.Pattern → Rd (Cond × List Var)
    | .or _ [] => pure (.bot, vs)
    | .or _ ps =>
      if isPredList ps then fail .manyValuedRightSide "\\top" else do
        let (ms, vs) ← memOfAlts N s z vs ps
        pure (disjC ms, vs)
    | .and _ ps =>
      if isPredList ps then fail .manyValuedRightSide "\\top" else do
        let (ms, vs) ← memOfConjs N s z vs ps
        pure (conjC ms, vs)
    | p =>
      if isPred p then fail .manyValuedRightSide "\\top" else
      match manyValued? p with
      | some c => fail .manyValuedRightSide c
      | none => do
        let (t, vs) ← termNoAnd N vs p
        pure (.mem s (.var z) t, vs)
    termination_by structural p => p
  def memOfAlts (N : Names) (s : Srt) (z : Nat) (vs : List Var) : List Kore.Pattern → Rd (List Cond × List Var)
    | [] => pure ([], vs)
    | p :: ps => do
      let (m, vs) ← memOf N s z vs p
      let (ms, vs) ← memOfAlts N s z vs ps
      pure (m :: ms, vs)
    termination_by structural ps => ps
  def memOfConjs (N : Names) (s : Srt) (z : Nat) (vs : List Var) : List Kore.Pattern → Rd (List Cond × List Var)
    | [] => pure ([], vs)
    | p :: ps => do
      let (m, vs) ← if isPred p then condOf N vs p else memOf N s z vs p
      let (ms, vs) ← memOfConjs N s z vs ps
      pure (m :: ms, vs)
    termination_by structural ps => ps
end

/-- For each conjunct of a cut, `Z ∈ t`; for a conjunct that is a disjunction, `memOf`. -/
def cutDisjs (N : Names) (s : Srt) (z : Nat) : List Var → List Kore.Pattern → Rd (List Cond × List Var)
  | vs, [] => pure ([], vs)
  | vs, p :: ps => do
    let (m, vs) ← match p with
      | .or .. => memOf N s z vs p
      | p => do
        let (t, vs) ← term N vs p
        pure (Cond.mem s (.var z) t, vs)
    let (ds, vs) ← cutDisjs N s z vs ps
    pure (m :: ds, vs)
  termination_by structural _ ps => ps

/-- The memberships of the cuts where a conjunct may be a disjunction (`cutDisjs`); `cutMems`
where none is. -/
def cutMemsOr (N : Names) : List Var → List Cut → Rd (List Cond × List Var)
  | vs, [] => pure ([], vs)
  | vs, c :: cs => do
    let (z, vs) ← varIndex vs c.1
    let s ← N.sortE c.2.1
    let (ds, vs) ← cutDisjs N s z vs c.2.2
    let (ms, vs) ← cutMemsOr N vs cs
    pure (ds ++ ms, vs)
  termination_by structural _ cs => cs

/-- An equation whose right side is `\exists x̄. body` (x̄ possibly empty), body under no further
binder: one clause. `exs` is the variables x̄ in the text's order of nesting, then the fresh
variables of `cutAnd`, which reads each conjunction of terms under applications of the body (a
conjunction with a variable of x̄ among its conjuncts as that variable), then those of `orCut`,
which reads each disjunction of terms under applications of the body or of a conjunct; `rhs` is
the body so read; `post` is every predicate of the body (`condOf`), so that `Cond.fixes` reads
them, then the cuts' memberships, a disjunction's as the disjunction of the memberships in its
alternatives (`cutMemsOr`, `memOf`); the equation's own `ensures` stays `ens`. A `\ceil` among the
body's predicates has its operand read by `cutAnd` likewise (`cutCeils`): its fresh variables
follow the body's in `exs`, its memberships the body's in `post`, a disjunction that is a conjunct
of its conjunctions read by `memOf` as at a term position. `orCut` does not read the operand, and
the test of `manyValued?` does not range over it (a `\ceil` holds where its operand has some
element, so an operand with several is no right side with several values).
Refused `patternConnective`: a variable of x̄ (name and sort) that is bound twice, named in the
detail, or that the arguments, the `requires` or the `ensures` hold (these binders are not read here: a rule's are, renamed apart or
dropped, `rhsApart` and `exKept`).
Refused `unheldVariable`: a variable of x̄ that the body does not hold (the sentence then states
the term only where the variable's sort has an element, which the clause would not say: unlike a
rule's sentence, `f(x̄) = ∃Z:s. t` at an empty s is `f(x̄) = ⊥`, which does not entail `f(x̄) = t`).
Refused `manyValuedRightSide`: no term conjunct (`\top`: the body is a predicate, every element
or none); a further `\exists` in the body; `\top` or `\not` under applications of the term, of
a cut's conjunct or of an alternative; `\or` under an application of an alternative (not read:
the cut of a position inside an alternative is not the text where the alternative is empty); an
alternative that is a predicate.
Refused `patternConnective`: a predicate `condOf` does not read, among them a conjunction of terms
in an operand of `\equals` or `\in`, or of a `\ceil` under `\not`, `\or` or `\implies`; a
conjunction under an application of an alternative; a disjunction under an application in the
operand of a `\ceil`, outside an alternative. -/
def ceRead (N : Names) (e : RawEqn) : Rd (Clause × List Var) := do
  let (pats, req, ens, vs, _) ← eqnHead N e
  let n0 := vs.length
  let (xs, body) := peelExists e.rhs
  if hasExists body then fail .manyValuedRightSide "\\exists"
  if isPred body then fail .manyValuedRightSide "\\top"
  if let some x := dupBinder xs then fail .patternConnective s!"{x.var.ident.name}: bound twice"
  let bound := xs.map (·.var.ident.name)
  let used := evarNamesList (e.rhs :: e.pats ++ e.req.toList ++ e.ens.toList)
  let (t, n, cuts, ps) := cutAnd used bound 0 body
  let (t, cuts) := orCutAll used t cuts
  if let some c := (t :: cuts.flatMap (·.2.2)).findSome? orManyValued? then fail .manyValuedRightSide c
  if let some x := xs.find? (fun x => !(evarNames body).contains x.var.ident.name) then
    fail .unheldVariable s!"{x.var.ident.name}: bound by \\exists, not held by its body"
  let (ps, _, ccuts) := cutCeils used bound n ps
  let cuts := cuts ++ ccuts
  let (exs, vs) ← exBind n0 vs xs
  let (zs, vs) ← exBind n0 vs ((cuts.map (·.1)).filter (!bound.contains ·.var.ident.name))
  let (rhs, vs) ← term N vs t
  let (cs, vs) ← condOfList N vs ps
  let (ms, vs) ← cutMemsOr N vs cuts
  pure ({ vars := ← varSorts N vs, pats, req, rhs, ens, prio := (eqnPrio e).2, aside := nonExec e,
          exs := exs ++ zs, post := conjC (cs ++ ms) }, vs)

/-! ## `\exists` moved to the top of a right side (`hoistExists`)

Each step is an equality in every interpretation, the bound variable x not free outside its
binder:
- `C[∃x. φ] = ∃x. C[φ]` for a position `C[·]` under applications (an injection is one): an
  application holds the elements its arguments' elements give, and `\exists` is the union over the
  elements of the bound sort. Nothing is asked of the sort: where it has no element both sides are
  empty.
- `(∃x. φ) ∧ ψ = ∃x. (φ ∧ ψ)`, likewise with nothing asked of the sort.
- `(∃x:s. φ) ∨ ψ = ∃x:s. (φ ∨ ψ)` where s has an element: where it has none the left side is ψ
  and the right side is empty. A value of s is an element of it in every model, so the step is
  taken where `val` accepts s, a test of "the sort has a value" the caller passes.
The binder stays where it is under `\not`, `\implies`, `\iff`, `\forall`, `\mu` and `\nu`, and in a
predicate (`isPred`): none of the three equalities moves it out of those. -/

mutual
  /-- A pattern at a term position with each `\exists` under applications, `\and` conjuncts and
  `\or` alternatives taken out: the pattern, the binders (outermost first, then in the order of
  the text), the names `taken` and `used` with the binders' added.
  `taken` holds the names free in the equation and the binders' already taken out: a binder whose
  name is one of them is renamed, with the occurrences it binds, to its name primed until no name
  of `used` is it (`freshIn`; `used` holds every name of the equation), so that no binder taken
  out captures a variable of the position it leaves, and no two have one name. Under a binder its
  name is taken, so a binder of the same name inside it is the one renamed.
  Refused `existentialEquation`: a binder in an alternative of an `\or` at a sort `val` does not
  accept. Refused `patternConnective`: a binder to rename whose name stays free in its body
  (`renameEVar` reads name and sort, and no `\iff`, `\mu` or `\nu`). -/
  def hoistEx (val : Kore.KSort → Bool) (taken used : List String) :
      Kore.Pattern → Rd (Kore.Pattern × List Kore.EVar × List String × List String)
    | .exist _ x p => do
      let n := x.var.ident.name
      let (p', xs, taken', used') ← hoistEx val (n :: taken) used p
      if taken.contains n then
        let y := KoreAML.evar (freshIn used' (used'.length + 1) n) x.sort
        let p'' := renameEVar x y p'
        if (freeEVars [] p'').contains n then
          fail .patternConnective s!"{n}: bound by \\exists, not renamed apart"
        else pure (p'', y :: xs, y.var.ident.name :: taken', y.var.ident.name :: used')
      else pure (p', x :: xs, taken', used')
    | .app h ss ps => do
      let (ps', xs, taken, used) ← hoistExList val taken used ps
      pure (.app h ss ps', xs, taken, used)
    | .and s ps => do
      let (ps', xs, taken, used) ← hoistExList val taken used ps
      pure (.and s ps', xs, taken, used)
    | .or s ps => do
      let (ps', xs, taken, used) ← hoistExList val taken used ps
      match xs.find? (fun x => !val x.sort) with
      | some x =>
        let sn := (sortName? x.sort).getD "?"
        fail .existentialEquation
          s!"{x.var.ident.name}: bound in an alternative of \\or at the sort {sn}, which the test of a value does not accept"
      | none => pure (.or s ps', xs, taken, used)
    | p => pure (p, [], taken, used)
    termination_by structural p => p
  def hoistExList (val : Kore.KSort → Bool) (taken used : List String) :
      List Kore.Pattern → Rd (List Kore.Pattern × List Kore.EVar × List String × List String)
    | [] => pure ([], [], taken, used)
    | p :: ps => do
      let (p', xs, taken, used) ← if isPred p then pure (p, [], taken, used) else hoistEx val taken used p
      let (ps', xs', taken, used) ← hoistExList val taken used ps
      pure (p' :: ps', xs ++ xs', taken, used)
    termination_by structural ps => ps
end

/-- An equation with each `\exists` of its right side under applications, `\and` conjuncts and
`\or` alternatives moved to the top (`hoistEx`), renamed apart from the names free in the
equation and from each other: the right side is `\exists x̄. body` at the sort S, the right side's.
A right side that is a predicate is left as it is. -/
def hoistExists (val : Kore.KSort → Bool) (S : Kore.KSort) (e : RawEqn) : Rd RawEqn := do
  if isPred e.rhs then pure e else
  let all := e.rhs :: e.pats ++ e.req.toList ++ e.ens.toList ++ e.competitors.getD []
  let (body, xs, _, _) ← hoistEx val (freeEVarsList [] all) (evarNamesList all) e.rhs
  pure { e with rhs := xs.foldr (Kore.Pattern.exist S) body }

/-- `Semantics.valued` on a built definition, at a sort of the text: the test of a value
`hoistExists` takes. A sort the names do not hold is not accepted. -/
def valuedSort (N : Names) (c : Semantics) (s : Kore.KSort) : Bool :=
  match N.sortE s with
  | .ok a => c.valued a
  | .error _ => false

end KCore.Parse
