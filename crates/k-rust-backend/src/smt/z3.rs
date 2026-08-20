//! In-process Z3 implementation of the backend SMT interface.

use z3::{Params, SatResult, Solver};

use super::{Satisfiability, SmtError, SmtPrelude, SmtSolver, TranslatedQuery, Validity};
use crate::{rule::Predicate, substitution::Substitution};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Z3Options {
    pub timeout_ms: u32,
    pub retry_limit: u32,
}

impl Default for Z3Options {
    fn default() -> Self {
        Self {
            timeout_ms: 125,
            retry_limit: 3,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Z3Solver {
    prelude: SmtPrelude,
    options: Z3Options,
}

impl Z3Solver {
    pub fn new(definition: &crate::definition::BackendDefinition) -> Result<Self, SmtError> {
        Self::with_options(definition, Z3Options::default())
    }

    pub fn with_options(
        definition: &crate::definition::BackendDefinition,
        options: Z3Options,
    ) -> Result<Self, SmtError> {
        let solver = Self {
            prelude: SmtPrelude::from_definition(definition)?,
            options,
        };
        match solver.solve(&solver.prelude.declarations().join("\n")) {
            Satisfiability::Sat => Ok(solver),
            Satisfiability::Unsat => Err(SmtError::InconsistentPrelude),
            Satisfiability::Unknown(reason) => Err(SmtError::UnknownPrelude(reason)),
        }
    }

    fn solve(&self, script: &str) -> Satisfiability {
        let mut timeout = self.options.timeout_ms;
        for attempt in 0..=self.options.retry_limit {
            let solver = Solver::new();
            let mut parameters = Params::new();
            parameters.set_u32("timeout", timeout);
            solver.set_params(&parameters);
            solver.from_string(script);
            match solver.check() {
                SatResult::Sat => return Satisfiability::Sat,
                SatResult::Unsat => return Satisfiability::Unsat,
                SatResult::Unknown if attempt < self.options.retry_limit => {
                    timeout = timeout.saturating_mul(2);
                }
                SatResult::Unknown => {
                    return Satisfiability::Unknown(
                        solver
                            .get_reason_unknown()
                            .unwrap_or_else(|| "Z3 returned unknown".into()),
                    );
                }
            }
        }
        unreachable!("the retry loop always returns")
    }

    fn solve_query(&self, query: &TranslatedQuery, assertion: Option<&str>) -> Satisfiability {
        let mut script = query.base.clone();
        if let Some(assertion) = assertion {
            script.push_str("\n(assert ");
            script.push_str(assertion);
            script.push(')');
        }
        self.solve(&script)
    }
}

impl SmtSolver for Z3Solver {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Result<Satisfiability, SmtError> {
        let query = self.prelude.query(predicates, substitution, &[], false)?;
        Ok(self.solve_query(&query, None))
    }

    fn check_predicates(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Result<Validity, SmtError> {
        if checked.is_empty() {
            return Ok(Validity::Valid);
        }
        let query = self.prelude.query(known, substitution, checked, true)?;
        match self.solve_query(&query, None) {
            Satisfiability::Unsat => return Ok(Validity::InconsistentGroundTruth),
            Satisfiability::Unknown(reason) => return Ok(Validity::Unknown(reason)),
            Satisfiability::Sat => {}
        }
        let checked = query.checked.to_string();
        let positive = self.solve_query(&query, Some(&checked));
        let negative = self.solve_query(&query, Some(&format!("(not {checked})")));
        let (positive, negative) = match (positive, negative) {
            (Satisfiability::Unsat, _) => (Satisfiability::Unsat, Satisfiability::Sat),
            (_, Satisfiability::Unsat) => (Satisfiability::Sat, Satisfiability::Unsat),
            results => results,
        };
        Ok(match (positive, negative) {
            (Satisfiability::Sat, Satisfiability::Unsat) => Validity::Valid,
            (Satisfiability::Unsat, Satisfiability::Sat) => Validity::Invalid,
            (Satisfiability::Sat, Satisfiability::Sat) => Validity::Indeterminate,
            (Satisfiability::Unsat, Satisfiability::Unsat) => Validity::InconsistentGroundTruth,
            (Satisfiability::Unknown(reason), _) | (_, Satisfiability::Unknown(reason)) => {
                Validity::Unknown(reason)
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::{definition::BackendDefinition, rule::Predicate, term::Variable};

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn term(definition: &BackendDefinition, source: &str) -> crate::term::Term {
        definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize")
    }

    fn x() -> Variable {
        Variable::new("X", crate::term::Sort::simple("SortInt"))
    }

    #[test]
    fn proves_and_refutes_predicates_under_a_substitution() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
        ))];

        assert_eq!(
            solver.check_predicates(
                &[],
                &Substitution::from([(x(), term(&definition, r#"\dv{SortInt{}}("5")"#))]),
                &checked,
            ),
            Ok(Validity::Valid)
        );
        assert_eq!(
            solver.check_predicates(
                &[],
                &Substitution::from([(x(), term(&definition, r#"\dv{SortInt{}}("15")"#))]),
                &checked,
            ),
            Ok(Validity::Invalid)
        );
        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), &checked),
            Ok(Validity::Indeterminate)
        );
    }

    #[test]
    fn distinguishes_unsatisfiable_and_inconsistent_constraints() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let x_term = term(&definition, "X:SortInt{}");
        let five = term(&definition, r#"\dv{SortInt{}}("5")"#);
        let six = term(&definition, r#"\dv{SortInt{}}("6")"#);
        let inconsistent = [
            Predicate::Equals(x_term.clone(), five),
            Predicate::Equals(x_term, six),
        ];

        assert_eq!(
            solver.is_sat(&inconsistent, &Substitution::new()),
            Ok(Satisfiability::Unsat)
        );
        assert_eq!(
            solver.check_predicates(
                &inconsistent,
                &Substitution::new(),
                &[Predicate::Term(term(
                    &definition,
                    r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
                ))],
            ),
            Ok(Validity::InconsistentGroundTruth)
        );
    }

    #[test]
    fn validity_filters_ground_truth_unrelated_to_the_checked_variables() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
        ))];
        let unrelated = term(&definition, "Z:SortInt{}");
        let contradictory = [
            Predicate::Equals(
                unrelated.clone(),
                term(&definition, r#"\dv{SortInt{}}("1")"#),
            ),
            Predicate::Equals(unrelated, term(&definition, r#"\dv{SortInt{}}("2")"#)),
        ];

        assert_eq!(
            solver.check_predicates(
                &contradictory,
                &Substitution::from([(x(), term(&definition, r#"\dv{SortInt{}}("5")"#))]),
                &checked,
            ),
            Ok(Validity::Valid)
        );
    }

    #[test]
    fn rejects_an_inconsistent_smt_lemma_prelude() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol f{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), smtlib{}("f")]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(
                            \dv{SortInt{}}("1"),
                            \top{SortInt{}}()
                        )
                    )
                ) [simplification{}(), smt-lemma{}(), label{}("f-is-one")]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(
                            \dv{SortInt{}}("2"),
                            \top{SortInt{}}()
                        )
                    )
                ) [simplification{}(), smt-lemma{}(), label{}("f-is-two")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        assert!(matches!(
            Z3Solver::new(&definition),
            Err(SmtError::InconsistentPrelude)
        ));
    }
}
