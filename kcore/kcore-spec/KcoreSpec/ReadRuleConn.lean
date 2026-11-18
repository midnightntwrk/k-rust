/-
  Reading functions for a rewrite axiom that holds a matching-logic connective at a term position
  under applications, beside the landed reader (Parse.lean). `ruleBody` calls `connRuleBody` nowhere;
  the cut of a conjunction of terms (`andCut`, `memCond`, `andRuleBody`) is the landed reader's
  (Parse.lean, where `ruleBody` takes it under the test at reading time `andCutOK`).

  A connective φ of sort S at a position `C[·]` under applications is the elements it holds, and an
  application holds the elements its arguments' elements give: `C[φ] = ∃Z:S. C[Z] ∧ Z ∈ φ` for a
  fresh Z (`KoreAML.cut_sorted`; `\or{S}`, `\not{S}` and `\top{S}` hold elements of S only). For one
  element Z of S, `Z ∈ φ` is the connective of the memberships in its operands
  (`KoreAML.mem_or`, `mem_not`, `mem_and`), every element of S for `\top{S}` and none for
  `\bottom{S}`.

  - `connCut`: a pattern with each maximal connective under applications replaced by a fresh
    variable; on a right side `\or`, `\top` and `\not`, on a left side `\not` (a left side's `\top`
    is a variable of the rule, `lhsBound`, and its `\or` is split, `orSplit`).
  - `memCond` (Parse.lean): `Z ∈ φ` as a condition.
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
  - `andCut` (Parse.lean): a right side with each maximal conjunction of terms under applications
    replaced by its first conjunct that is a variable, or by a fresh variable where none is.
  - `andRuleBody` (Parse.lean): a rewrite axiom read with its right side's conjunctions of terms
    cut: the memberships are `post`, a fresh variable is added to `exs`, and the rule has no
    `ensures` from the conjunction. `ruleBodyUncut` reads the same axiom with the first conjunct at
    the position and the equality of the conjuncts as an `ensures`; `ruleBody` takes the cut where
    `andCutOK` holds (`ReadingNote.andTermsCut`). `andRuleOf` takes it wherever it reads.
-/
import KcoreSpec.ReadFns

set_option autoImplicit false

namespace KCore.Parse

open KoreAML.Parse (sortName?)
open KoreAML (Var)

/-- A cut connective: the variable that stands in its place, its sort, the connective. -/
abbrev ConnCut := Kore.EVar × Kore.KSort × Kore.Pattern

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

/-- The rule of a rewrite axiom, its right side's conjunctions of terms cut (`andRuleBody`). -/
def andRuleOf (N : Names) (msrc : String) (a : Kore.Axiom) : Rd (Rule × RulePres) :=
  Rd.within (.sentence (.axiom a)) (andRuleBody N msrc a)

/-- The rule of a rewrite axiom read without the cut of its right side's conjunctions of terms
(`ruleBodyUncut`: a conjunction with the `ensures` of the conjuncts' equality, `andTermsWeaker`). -/
def ruleOfUncut (N : Names) (msrc : String) (a : Kore.Axiom) : Rd (Rule × RulePres) :=
  Rd.within (.sentence (.axiom a)) (ruleBodyUncut N msrc a)

/-- With the landed rule reader, `parseWith` is `parse`. -/
theorem parseWith_ruleOf (k : Kore.Definition) : parseWith ruleOf k = parse k := rfl

end KCore.Parse
