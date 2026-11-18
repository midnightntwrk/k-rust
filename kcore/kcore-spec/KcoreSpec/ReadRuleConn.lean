/-
  `parse` with the rules read by another function (`parseWith`; `parseWith ruleOf` is `parse`), and
  two such functions for the readings of a right side's conjunction of terms.

  The reader's rules are `ruleOf`'s (Parse.lean): `connRuleBody` reads a matching-logic connective
  at a term position under applications through the cut (`connCut`, `memCond`,
  `ReadingNote.connectiveCut`), and `ruleBody` a right side's conjunction of terms through the cut
  where the test at reading time `andCutOK` holds.

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
