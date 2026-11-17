/-
  The two equations of a clause without existential variables are the text with the right side
  `rhs` and the `ensures` part `ens`, at any premise predicate `pre` (`withPre`): `clauseRhs` adds a
  binder only where the clause has existential variables.
-/
import KcoreSpec.Faithful

set_option autoImplicit false

namespace KCore

namespace Faithful

/-- The equation of a clause without existential variables: `withPre`'s premise, `rhs` and `ens`. -/
theorem clauseEquation_noExs {c : Semantics} {f : Fn} {cl : Clause} (hex : cl.exs = []) :
    clauseEquation c f cl =
      eqnSentence c f
        (withPre c (canonVars c cl.vars) cl (premise (f.args.map c.sortName)
          (cl.req.map (Term.kore c (canonVars c cl.vars))) (Term.koreList c (canonVars c cl.vars) cl.pats)))
        (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c f.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))) := by
  unfold clauseEquation; simp only [clauseRhs_nil hex]

/-- The competing equation of a clause without existential variables: the negated competitors,
`withPre`'s premise, `rhs` and `ens`. -/
theorem competingEquation_noExs {c : Semantics} {f : Fn} {others : List Clause} {cl : Clause}
    (hex : cl.exs = []) :
    competingEquation c f others cl =
      eqnSentence c f
        (.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf (others.map fun cl' => exclusion c f cl' (canonClausePres cl'))),
          withPre c (canonVars c cl.vars) cl (premise (f.args.map c.sortName)
            (cl.req.map (Term.kore c (canonVars c cl.vars))) (Term.koreList c (canonVars c cl.vars) cl.pats))])
        (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c f.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))) := by
  unfold competingEquation; simp only [clauseRhs_nil hex]

end Faithful

end KCore
