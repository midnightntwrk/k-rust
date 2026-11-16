/-
  `#eval` of the total functions of `KoreParser/Stats.lean` on the milestone-1 subject.
  Run from the package root: `lake env lean test/Eval.lean`.
-/
import KoreParser

namespace Kore

mutual
  /-- Arities of the `\and` and `\or` nodes of a pattern (n-ary in the grammar). -/
  def Pattern.junctionArities : Pattern → List Nat
    | .and _ ps | .or _ ps => ps.length :: Pattern.junctionAritiesList ps
    | .app _ _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps => Pattern.junctionAritiesList ps
    | .not _ p | .exist _ _ p | .forall _ _ p | .mu _ p | .nu _ p
    | .ceil _ _ p | .floor _ _ p | .next _ p => p.junctionArities
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q =>
      p.junctionArities ++ q.junctionArities
    | .var _ | .string _ | .top _ | .bottom _ | .dv .. => []
    termination_by structural p => p
  def Pattern.junctionAritiesList : List Pattern → List Nat
    | [] => []
    | p :: ps => p.junctionArities ++ Pattern.junctionAritiesList ps
    termination_by structural ps => ps
end

end Kore

open Kore

#eval show IO Unit from do
  let .ok d ← parseFile "../milestone-1/kore/definition.kore" | throw (IO.userError "parse failed")
  IO.println s!"modules: {d.modules.map (·.name)}"
  IO.println s!"axioms: {d.axioms.length}, pattern nodes: {d.axiomNodes}"
  IO.println s!"axioms by top connective: {d.axiomsByTopConnective}"
  let arities := d.axioms.flatMap (·.pattern.junctionArities)
  IO.println s!"\\and/\\or arities: {tally (arities.map toString)}"
