/-
  Reading functions over `RawEqn` for an equation's right side that holds a matching-logic
  connective, beside those the reader calls (Parse.lean: `dropEmptyAlts`, `frRead`, `exRead` with
  `condOf` and `cutAnd`, called by `clausesBody`). `clausesBody` calls none of the functions of
  this file: a text they would read is refused as before. Each is structurally recursive and
  reduces in the kernel (test/ExClauseReader.lean checks an instance of each by `kernel_rfl`).

  - `ceRead`: `\exists` on an equation's right side as the clause's existential variables
    (`Clause.exs`), the body's predicates as its right-side predicate (`Clause.post`); a
    conjunction of terms at a term position as a fresh existential variable with its memberships
    (`cutAnd`); `orCut`, a disjunction of terms at a term position as a fresh existential variable
    with the disjunction of its memberships; a conjunction of terms in the operand of a `\ceil`
    under `\not`, `\or` or `\implies` as a binder `Cond.ex` inside the predicate (`ceilExCond`).
  - `valuedSort`: `Semantics.valued` on a built definition, the test of a value `Parse.hoistExists`
    (Parse.lean) takes to move the binder of an `\or` alternative.
-/
import KcoreSpec.Parse

set_option autoImplicit false

namespace KCore.Parse

open KoreAML.Parse (sortName?)
open KoreAML (Var)

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
equation's own. A `\ceil` under another connective is not reached here: `ceilExCond` reads it, the
binder kept inside the predicate. -/
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

/-- The variables numbered in `vs` in order (`varIndex`). -/
def numberVarsCE : List Var → List Kore.EVar → Rd (List Var)
  | vs, [] => pure vs
  | vs, x :: xs => do
    let (_, vs) ← varIndex vs x
    numberVarsCE vs xs
  termination_by structural _ xs => xs
/-! ### A conjunction of terms in the operand of a `\ceil` under a connective of predicates

`⌈C[t₁ ∧ … ∧ tₙ]⌉ = ∃Z. (⌈C[Z]⌉ ∧ Z ∈ t₁ ∧ … ∧ Z ∈ tₙ)`, as in `cutCeils`. Under `\not`, `\or` or
`\implies` that `\exists` is no conjunct of the right side, so it does not join the equation's
binders: it stays inside the predicate, `Cond.ex` at the conjunction's sort, one binder for each
variable `cutAnd` cuts in the operand (one inside a conjunct before the conjunct's own), over
`⌈C[Z̄]⌉`, the predicates `cutAnd` lifts out of the operand and the memberships. A binder of a
condition binds the index past the variables in scope (`Holds`, `Cond.bound`), so every variable
of the clause is numbered before such a predicate is read (`ceilExConds`), and the binder's body
numbers no variable but the binders'. Whether the definition admits the binder (its sort confined,
or with a value and fixed by a membership in a term over the other variables) is `Cond.bound`'s
question on the built definition. -/

mutual
  /-- The pattern is a connective of predicates (`\not`, `\and`, `\or`, `\implies`) under which a
  `\ceil` is reached whose operand holds a conjunction under applications (`hasAnd`): the shape
  `condOf` refuses and `ceilExCond` reads. -/
  def ceilAndUnder : Kore.Pattern → Bool
    | .ceil _ _ q => hasAnd q
    | .not _ p => ceilAndUnder p
    | .implies _ p q => ceilAndUnder p || ceilAndUnder q
    | .and _ ps | .or _ ps => ceilAndUnderList ps
    | _ => false
    termination_by structural p => p
  def ceilAndUnderList : List Kore.Pattern → Bool
    | [] => false
    | p :: ps => ceilAndUnder p || ceilAndUnderList ps
    termination_by structural ps => ps
end

/-- The cuts' variables numbered after `vs`, each a name `vs` does not hold (`patternConnective`
otherwise). -/
def ceilExBind : List Var → List Cut → Rd (List Var)
  | vs, [] => pure vs
  | vs, c :: cs => do
    let (i, vs') ← varIndex vs c.1
    if i < vs.length then fail .patternConnective s!"{c.1.var.ident.name}: a cut's variable named as a variable of the clause"
    ceilExBind vs' cs
  termination_by structural _ cs => cs

mutual
  /-- `condOf`, with a `\ceil` whose operand holds a conjunction of terms under applications read
  as `∃Z̄. (⌈C[Z̄]⌉ ∧ P ∧ the memberships)`: `cutAnd` with no bound variable, its names apart from
  `used` and from `vs`; P the predicates it lifts (`condOf`) and the memberships those `cutMemsOr`
  reads; the binders `Cond.ex` at the indices `vs.length` and up. Every variable of the pattern but
  the binders' is in `vs`: refused `patternConnective` where the reading would number another. -/
  def ceilExCond (N : Names) (used : List String) (vs : List Var) : Kore.Pattern → Rd Cond
    | .ceil s r q => do
      let (q', _, cuts, qs) := cutAnd (used ++ vs.map ("Var" ++ ·.name)) [] 0 q
      let vsZ ← ceilExBind vs cuts
      let (c, vs1) ← condOf N vsZ (.ceil s r q')
      let (ps, vs1) ← condOfList N vs1 qs
      let (ms, vs1) ← cutMemsOr N vs1 cuts
      if vs1.length != vsZ.length then
        fail .patternConnective "\\ceil: a variable first held under its binder"
      let ss ← cuts.mapM (N.sortE ·.2.1)
      pure (ss.foldr Cond.ex (conjC (c :: ps ++ ms)))
    | .not _ p => do pure (.not (← ceilExCond N used vs p))
    | .implies _ p q => do pure (.implies (← ceilExCond N used vs p) (← ceilExCond N used vs q))
    | .and _ ps => do pure (conjC (← ceilExCondList N used vs ps))
    | .or _ ps => do pure (disjC (← ceilExCondList N used vs ps))
    | p => do
      let (c, vs1) ← condOf N vs p
      if vs1.length != vs.length then
        fail .patternConnective "\\ceil: a variable first held under its binder"
      pure c
    termination_by structural p => p
  def ceilExCondList (N : Names) (used : List String) (vs : List Var) : List Kore.Pattern → Rd (List Cond)
    | [] => pure []
    | p :: ps => do
      let c ← ceilExCond N used vs p
      let cs ← ceilExCondList N used vs ps
      pure (c :: cs)
    termination_by structural ps => ps
end

/-- The predicates `ps` (those `ceilAndUnder` holds of), after every other part of the clause is
read (`vs`): their free variables numbered first, then each read by `ceilExCond`, so that each
binder's index is past every variable of the clause. -/
def ceilExConds (N : Names) (used : List String) (vs : List Var) (ps : List Kore.Pattern) :
    Rd (List Cond × List Var) := do
  let vs ← numberVarsCE vs (freeEVarsSList [] ps)
  let cs ← ceilExCondList N used vs ps
  pure (cs, vs)

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
of its conjunctions read by `memOf` as at a term position. A predicate under which a `\ceil` with a
conjunction of terms in its operand is reached through `\not`, `\or`, `\and` or `\implies`
(`ceilAndUnder`) is read last (`ceilExConds`): the cut's `\exists` stays inside the predicate as
`Cond.ex`, past every variable of the clause, and the predicate follows the memberships in `post`.
`orCut` does not read the operand, and
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
in an operand of `\equals` or `\in`; a
conjunction under an application of an alternative; a disjunction under an application in the
operand of a `\ceil`, outside an alternative.
Refused `rhsOperandSort`, before any of these: the body (the right side under its `\exists`
binders) is not `rhsSorted`, or a binder is of another sort than the function's result
(`eqnBinderSortGuard`). -/
def ceRead (N : Names) (e : RawEqn) : Rd (Clause × List Var) := do
  rhsSortGuard (peelExists e.rhs).2
  eqnBinderSortGuard N e
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
  let (cs, vs) ← condOfList N vs (ps.filter (!ceilAndUnder ·))
  let (ms, vs) ← cutMemsOr N vs cuts
  let (bs, vs) ← ceilExConds N used vs (ps.filter ceilAndUnder)
  pure ({ vars := ← varSorts N vs, pats, req, rhs, ens, prio := (eqnPrio e).2, aside := nonExec e,
          exs := exs ++ zs, post := conjC (cs ++ ms ++ bs) }, vs)

/-- `ceRead` reads only a right side whose body under its `\exists` binders is `rhsSorted`. -/
theorem ceRead_rhsSorted {N : Names} {e : RawEqn} {x : Clause × List Var}
    (h : ceRead N e = .ok x) : rhsSorted (peelExists e.rhs).2 = true := by
  obtain ⟨u, hu⟩ := rhsSortGuard_bind (p := (peelExists e.rhs).2) h
  exact rhsSortGuard_ok hu

/-- `Semantics.valued` on a built definition, at a sort of the text: the test of a value
`hoistExists` takes. A sort the names do not hold is not accepted. -/
def valuedSort (N : Names) (c : Semantics) (s : Kore.KSort) : Bool :=
  match N.sortE s with
  | .ok a => c.valued a
  | .error _ => false

end KCore.Parse
