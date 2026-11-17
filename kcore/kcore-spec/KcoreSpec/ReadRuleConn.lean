/-
  Reading functions for a rewrite axiom that holds a matching-logic connective at a term position
  under applications, beside the landed reader (Parse.lean). `ruleBody` calls none of them: a text
  is read as before, and no account changes.

  A connective φ of sort S at a position `C[·]` under applications is the elements it holds, and an
  application holds the elements its arguments' elements give: `C[φ] = ∃Z:S. C[Z] ∧ Z ∈ φ` for a
  fresh Z (`KoreAML.cut_sorted`; `\or{S}`, `\not{S}` and `\top{S}` hold elements of S only). For one
  element Z of S, `Z ∈ φ` is the connective of the memberships in its operands
  (`KoreAML.mem_or`, `mem_not`, `mem_and`), every element of S for `\top{S}` and none for
  `\bottom{S}`.

  - `connCut`: a pattern with each maximal connective under applications replaced by a fresh
    variable; on a right side `\or`, `\top` and `\not`, on a left side `\not` (a left side's `\top`
    is a variable of the rule, `lhsBound`, and its `\or` is split, `orSplit`).
  - `memCond`: `Z ∈ φ` as a condition.
  - `connRuleBody`: a rewrite axiom the landed reader refuses, read with its connectives cut: a
    right side's cut variable is an existential variable of the rule (`exs`) and its membership a
    conjunct of `post`; a left side's is a variable of the rule and its membership a conjunct of
    `pre` (`L[¬φ] → •R` is `∀Z. L[Z] ∧ ¬(Z ∈ φ) → •R`, Z not in R). An axiom the landed reader
    reads is read by it, unchanged; a conjunction of terms at a term position is left to it.
  - `parseWith`: `parse` with the rules read by a given function; `parseWith ruleOf` is `parse`.

  A conjunction of terms `\and{S}(t₁, …, tₙ)` at a position under applications of a right side
  holds the elements all of the tᵢ hold. Where a conjunct is a variable V it is V where V is in
  each other conjunct, `C[V ∧ u] = C[V] ∧ V ∈ u`; otherwise it is cut as a connective is,
  `C[t₁ ∧ … ∧ tₙ] = ∃Z:S. C[Z] ∧ Z ∈ t₁ ∧ … ∧ Z ∈ tₙ`.
  - `andCut`: a right side with each maximal conjunction of terms under applications replaced by
    its first conjunct that is a variable, or by a fresh variable where none is.
  - `andRuleBody`: a rewrite axiom read with its right side's conjunctions of terms cut: the
    memberships are `post`, a fresh variable is added to `exs`, and the rule has no `ensures` from
    the conjunction. `ruleBody` reads the same axiom with the first conjunct at the position and
    the equality of the conjuncts as an `ensures`.
-/
import KcoreSpec.ReadFns

set_option autoImplicit false

namespace KCore.Parse

open KoreAML.Parse (sortName?)
open KoreAML (Var)

/-- A cut connective: the variable that stands in its place, its sort, the connective. -/
abbrev ConnCut := Kore.EVar × Kore.KSort × Kore.Pattern

/-- The variable of the n-th cut at the sort s: `Var'Hash'Cut<n>`, primed until no name of `used`
is it. -/
def connCutVar (used : List String) (n : Nat) (s : Kore.KSort) : Kore.EVar :=
  KoreAML.evar (freshIn used (used.length + 1) s!"Var'Hash'Cut{n}") s

mutual
  /-- A pattern at a term position with each maximal connective under applications replaced by a
  fresh variable of the connective's sort: `\not`, and on a right side (`left` false) `\or` and
  `\top` too. The pattern, the next number and the cuts, in the order met. -/
  def connCut (left : Bool) (used : List String) (n : Nat) : Kore.Pattern → Kore.Pattern × Nat × List ConnCut
    | .app h ss ps => let (ps', n, cs) := connCutList left used n ps; (.app h ss ps', n, cs)
    | .not s p => (.var (.evar (connCutVar used n s)), n + 1, [(connCutVar used n s, s, .not s p)])
    | .or s ps =>
      if left then (.or s ps, n, [])
      else (.var (.evar (connCutVar used n s)), n + 1, [(connCutVar used n s, s, .or s ps)])
    | .top s =>
      if left then (.top s, n, [])
      else (.var (.evar (connCutVar used n s)), n + 1, [(connCutVar used n s, s, .top s)])
    | p => (p, n, [])
    termination_by structural p => p
  def connCutList (left : Bool) (used : List String) (n : Nat) :
      List Kore.Pattern → List Kore.Pattern × Nat × List ConnCut
    | [] => ([], n, [])
    | p :: ps =>
      let (p', n, cs) := connCut left used n p
      let (ps', n, cs') := connCutList left used n ps
      (p' :: ps', n, cs ++ cs')
    termination_by structural ps => ps
end

mutual
  /-- `Z ∈ φ` for the variable z of the sort s (S in the text) and a pattern φ of that sort: the
  connective of the memberships in φ's operands, `\top` for `\top{S}` and `\bottom` for
  `\bottom{S}`, and `mem s Z t` for a term t (`termNoAnd`). A connective at another sort than S is
  refused `patternConnective`. -/
  def memCond (N : Names) (z : Nat) (s : Srt) (S : Kore.KSort) (vs : List Var) :
      Kore.Pattern → Rd (Cond × List Var)
    | .top S' => if decide (S' = S) then pure (.top, vs) else fail .patternConnective "\\top"
    | .bottom S' => if decide (S' = S) then pure (.bot, vs) else fail .patternConnective "\\bottom"
    | .not S' p => if decide (S' = S) then do
        let (c, vs) ← memCond N z s S vs p
        pure (.not c, vs)
      else fail .patternConnective "\\not"
    | .and S' ps => if decide (S' = S) then do
        let (cs, vs) ← memCondList N z s S vs ps
        pure (conjC cs, vs)
      else fail .patternConnective "\\and"
    | .or S' ps => if decide (S' = S) then do
        let (cs, vs) ← memCondList N z s S vs ps
        pure (disjC cs, vs)
      else fail .patternConnective "\\or"
    | p => do
      let (t, vs) ← termNoAnd N vs p
      pure (.mem s (.var z) t, vs)
    termination_by structural p => p
  def memCondList (N : Names) (z : Nat) (s : Srt) (S : Kore.KSort) (vs : List Var) :
      List Kore.Pattern → Rd (List Cond × List Var)
    | [] => pure ([], vs)
    | p :: ps => do
      let (c, vs) ← memCond N z s S vs p
      let (cs, vs) ← memCondList N z s S vs ps
      pure (c :: cs, vs)
    termination_by structural ps => ps
end

/-- The membership of each cut's variable in its connective, and the variables' indices. -/
def connCutConds (N : Names) : List Var → List ConnCut → Rd (List Cond × List Nat × List Var)
  | vs, [] => pure ([], [], vs)
  | vs, c :: cs => do
    let (i, vs) ← varIndex vs c.1
    let s ← N.sortE c.2.1
    let (p, vs) ← memCond N i s c.2.1 vs c.2.2
    let (ps, is, vs) ← connCutConds N vs cs
    pure (p :: ps, i :: is, vs)
  termination_by structural _ cs => cs

/-- The name of the sort numbered s (`Names.srt?`'s numbering). -/
def Names.sortNameOf (N : Names) (s : Srt) : String :=
  if s < nRegSorts then regSortNames.getD s "" else N.sorts.getD (s - nRegSorts) ""

/-- A rewrite axiom's rule, its connectives at term positions cut. An axiom the landed reader
reads (`ruleBody`) is read by it. Otherwise, for `\rewrites(\and(l, req), \and(r, ens))` with a
connective `connCut` cuts: the axiom with the cut variables in the connectives' places is read by
the landed reader; the memberships of the left side's cut variables are `pre`, those of the right
side's are `post`, and the right side's cut variables are added to `exs`. A variable only a
connective holds is a variable of the rule, read after the others. Where no connective is cut, or
the right side is under `\exists`, the landed reader's refusal stands. -/
def connRuleBody (N : Names) (msrc : String) (a : Kore.Axiom) : Rd (Rule × RulePres) :=
  match ruleBody N msrc a with
  | .ok x => .ok x
  | .error f =>
    match a.pattern with
    | .rewrites s (.and s' [l, r0]) (.and s'' [r, en]) =>
      let used := evarNames a.pattern
      let (l', n, cutsL) := connCut true used 0 l
      let (r', _, cutsR) := connCut false used n r
      if cutsL.isEmpty && cutsR.isEmpty then .error f else do
        let (rule, pres) ← ruleBody N msrc { a with pattern := .rewrites s (.and s' [l', r0]) (.and s'' [r', en]) }
        let vs : List Var := (pres.names.zip rule.vars).map fun (n, s) => ⟨n, N.sortNameOf s⟩
        let (pre, _, vs) ← connCutConds N vs cutsL
        let (post, zs, vs) ← connCutConds N vs cutsR
        pure ({ rule with vars := ← varSorts N vs, pre := conjC pre, post := conjC post, exs := rule.exs ++ zs },
              { pres with names := vs.map (·.name) })
    | _ => .error f

/-- The rule of a rewrite axiom, its connectives at term positions cut (`connRuleBody`). -/
def connRuleOf (N : Names) (msrc : String) (a : Kore.Axiom) : Rd (Rule × RulePres) :=
  Rd.within (.sentence (.axiom a)) (connRuleBody N msrc a)

/-- `finish` with the rules read by `rd`. -/
def finishWith (rd : Names → String → Kore.Axiom → Rd (Rule × RulePres)) (m : Kore.Module) (S : Scan) :
    Rd Definition := do
  let E ← envOf m S
  let symProds ← (prodSyms S E).mapM (symProd E S.eqs)
  let rules ← S.rewrites.mapM (rd E.N E.src)
  assemble m S E symProds rules

/-- `parse` with the rules read by `rd`. -/
def parseWith (rd : Names → String → Kore.Axiom → Rd (Rule × RulePres)) (k : Kore.Definition) :
    Except Refusal Definition :=
  match k.modules.getLast? with
  | none => .error ⟨none, "", .noModule, ""⟩
  | some m =>
    if k.modules.dropLast = preludeModules then
      let S := scan m.sentences
      match S.refused with
      | [] => (finishWith rd m S).mapError (Fault.toRefusal (preludeLength k) m)
      | _ :: _ => .error (classRefusal (preludeLength k) m)
    else .error (preludeRefusal k)

/-! ## A right side's conjunctions of terms -/

/-- A cut conjunction of terms: the variable that stands at its position, the conjunction's sort,
whether the variable is fresh (no conjunct is a variable), and the conjuncts the variable is in:
all of them for a fresh variable, the others for a conjunct. -/
structure AndCut where
  var : Kore.EVar
  sort : Kore.KSort
  fresh : Bool
  members : List Kore.Pattern
  deriving DecidableEq

/-- The conjuncts of a conjunction at the sort S, nested conjunctions at S flattened: its terms,
and its conjuncts `\equals(B, true)` (`isTrueOf?`, which `hoist` reads as conditions). -/
def andFlat (S : Kore.KSort) : Kore.Pattern → List Kore.Pattern × List Kore.Pattern
  | .and S' [t, u] =>
    if decide (S' = S) then
      match isTrueOf? u, isTrueOf? t with
      | some _, _ => let (ts, cs) := andFlat S t; (ts, cs ++ [u])
      | none, some _ => let (ts, cs) := andFlat S u; (ts, cs ++ [t])
      | none, none =>
        let (ts, cs) := andFlat S t
        let (us, ds) := andFlat S u
        (ts ++ us, cs ++ ds)
    else ([.and S' [t, u]], [])
  | p => ([p], [])
  termination_by structural p => p

/-- The first pattern of the list that is a variable, and the list without it. -/
def firstVar : List Kore.Pattern → Option (Kore.EVar × List Kore.Pattern)
  | [] => none
  | .var (.evar x) :: ps => some (x, ps)
  | p :: ps => (firstVar ps).map fun (x, qs) => (x, p :: qs)

mutual
  /-- A right side with each maximal conjunction of two terms or more under applications replaced
  by a variable: its first conjunct that is a variable, or the n-th fresh variable (`connCutVar`)
  where none is. A conjunct `\equals(B, true)` stays a conjunct of the variable. The pattern, the
  next number and the cuts, in the order met. -/
  def andCut (used : List String) (n : Nat) : Kore.Pattern → Kore.Pattern × Nat × List AndCut
    | .app h ss ps => let (ps', n, cs) := andCutList used n ps; (.app h ss ps', n, cs)
    | .and S [t, u] =>
      match isTrueOf? u, isTrueOf? t with
      | some _, _ => let (t', n, cs) := andCut used n t; (.and S [t', u], n, cs)
      | none, some _ => let (u', n, cs) := andCut used n u; (.and S [t, u'], n, cs)
      | none, none =>
        let (ts, conds) := andFlat S (.and S [t, u])
        if ts.length < 2 then (.and S [t, u], n, [])
        else match firstVar ts with
          | some (x, us) => (conds.foldl (fun acc b => .and S [acc, b]) (.var (.evar x)), n, [⟨x, S, false, us⟩])
          | none =>
            let z := connCutVar used n S
            (conds.foldl (fun acc b => .and S [acc, b]) (.var (.evar z)), n + 1, [⟨z, S, true, ts⟩])
    | p => (p, n, [])
    termination_by structural p => p
  def andCutList (used : List String) (n : Nat) :
      List Kore.Pattern → List Kore.Pattern × Nat × List AndCut
    | [] => ([], n, [])
    | p :: ps =>
      let (p', n, cs) := andCut used n p
      let (ps', n, cs') := andCutList used n ps
      (p' :: ps', n, cs ++ cs')
    termination_by structural ps => ps
end

/-- A rewrite axiom's right side `\exists(x̄, \and(r, en))` with `r`'s conjunctions of terms cut
(`andCut`); the `ensures` `en` is kept. -/
def andCutRhs (used : List String) : Kore.Pattern → Kore.Pattern × List AndCut
  | .exist S x p => let (p', cs) := andCutRhs used p; (.exist S x p', cs)
  | .and S [r, en] => let (r', _, cs) := andCut used 0 r; (.and S [r', en], cs)
  | p => (p, [])

/-- The memberships of each cut's variable in its conjuncts, the indices of the fresh variables,
and the variables. -/
def andCutConds (N : Names) : List Var → List AndCut → Rd (List Cond × List Nat × List Var)
  | vs, [] => pure ([], [], vs)
  | vs, c :: cs => do
    let (i, vs) ← varIndex vs c.var
    let s ← N.sortE c.sort
    let (ms, vs) ← memCondList N i s c.sort vs c.members
    let (ps, is, vs) ← andCutConds N vs cs
    pure (ms ++ ps, (if c.fresh then [i] else []) ++ is, vs)
  termination_by structural _ cs => cs

/-- A rewrite axiom's rule, its right side's conjunctions of terms cut. For
`\rewrites(\and(l, req), \exists(x̄, \and(r, en)))`, the binders renamed apart as the landed
reader renames them (`rhsApart`): the axiom with `andCut`'s variables at the conjunctions' places
is read by the landed reader, so the rule's `ensures` is `en`'s; `post` is the memberships of each
cut's variable in its conjuncts; the fresh variables are existential variables of the rule, after
the binders that bind something in the right side as written (`exKept`). An axiom with no such
conjunction, or of another shape, is read by the landed reader. -/
def andRuleBody (N : Names) (msrc : String) (a : Kore.Axiom) : Rd (Rule × RulePres) :=
  match a.pattern with
  | .rewrites s (.and s' [l, r0]) rx =>
    let rxA := rhsApart a.pattern l r0 rx
    let used := evarNames (.rewrites s (.and s' [l, r0]) rxA) ++ evarNames (lhsBound a.pattern l)
    let (rx', cuts) := andCutRhs used rxA
    if cuts.isEmpty then ruleBody N msrc a else do
      let (rule, pres) ← ruleBody N msrc { a with pattern := .rewrites s (.and s' [l, r0]) rx' }
      let vs : List Var := (pres.names.zip rule.vars).map fun (n, s) => ⟨n, N.sortNameOf s⟩
      let (post, zs, vs) ← andCutConds N vs cuts
      let kept := match peelExists rxA with
        | (xs, .and _ [r, en]) => exKept xs r en
        | _ => []
      pure ({ rule with vars := ← varSorts N vs, post := conjC post, exs := exIndices vs 0 kept ++ zs },
            { pres with names := vs.map (·.name) })
  | _ => ruleBody N msrc a

/-- The rule of a rewrite axiom, its right side's conjunctions of terms cut (`andRuleBody`). -/
def andRuleOf (N : Names) (msrc : String) (a : Kore.Axiom) : Rd (Rule × RulePres) :=
  Rd.within (.sentence (.axiom a)) (andRuleBody N msrc a)

/-- With the landed rule reader, `parseWith` is `parse`. -/
theorem parseWith_ruleOf (k : Kore.Definition) : parseWith ruleOf k = parse k := rfl

end KCore.Parse
