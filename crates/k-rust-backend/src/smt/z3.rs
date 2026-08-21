//! In-process Z3 implementation of the backend SMT interface.

use std::{
    collections::{BTreeMap, BTreeSet},
    str::FromStr,
};

use num_bigint::BigInt;
use z3::{
    Model, Params, SatResult, Solver,
    ast::{Bool, Int},
};

use super::{
    ModelResult, Satisfiability, SmtError, SmtPrelude, SmtSolver, TranslatedQuery, Validity,
};
use crate::{
    cancellation::cancellation_requested,
    rule::Predicate,
    substitution::Substitution,
    term::{Sort, Term, Variable},
};

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
        Self::with_options_and_prelude(definition, options, None)
    }

    pub fn with_prelude(
        definition: &crate::definition::BackendDefinition,
        prelude: &str,
    ) -> Result<Self, SmtError> {
        Self::with_options_and_prelude(definition, Z3Options::default(), Some(prelude))
    }

    pub fn with_options_and_prelude(
        definition: &crate::definition::BackendDefinition,
        options: Z3Options,
        prelude: Option<&str>,
    ) -> Result<Self, SmtError> {
        let solver = Self {
            prelude: match prelude {
                Some(prelude) => SmtPrelude::from_definition_with_prelude(definition, prelude)?,
                None => SmtPrelude::from_definition(definition)?,
            },
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
            if cancellation_requested() {
                return Satisfiability::Unknown("request cancelled".into());
            }
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

    fn solve_model(
        &self,
        query: &TranslatedQuery,
        variables: &BTreeSet<Variable>,
    ) -> Result<ModelResult, SmtError> {
        let mut timeout = self.options.timeout_ms;
        for attempt in 0..=self.options.retry_limit {
            if cancellation_requested() {
                return Ok(ModelResult::Unknown("request cancelled".into()));
            }
            let solver = Solver::new();
            let mut parameters = Params::new();
            parameters.set_u32("timeout", timeout);
            solver.set_params(&parameters);
            solver.from_string(query.base.as_str());
            match solver.check() {
                SatResult::Sat => {
                    let model = solver.get_model().ok_or(SmtError::MissingModel)?;
                    return self.extract_model(&model, &query.mappings, variables);
                }
                SatResult::Unsat => return Ok(ModelResult::Unsat),
                SatResult::Unknown if attempt < self.options.retry_limit => {
                    timeout = timeout.saturating_mul(2);
                }
                SatResult::Unknown => {
                    return Ok(ModelResult::Unknown(
                        solver
                            .get_reason_unknown()
                            .unwrap_or_else(|| "Z3 returned unknown".into()),
                    ));
                }
            }
        }
        unreachable!("the retry loop always returns")
    }

    fn extract_model(
        &self,
        model: &Model,
        mappings: &BTreeMap<Term, String>,
        variables: &BTreeSet<Variable>,
    ) -> Result<ModelResult, SmtError> {
        let mut substitution = Substitution::new();
        for variable in variables {
            let term = Term::variable(variable.clone());
            let value = match &variable.sort {
                sort if sort == &Sort::simple("SortInt") => {
                    let name = mappings
                        .get(&term)
                        .ok_or_else(|| SmtError::MissingModelValue(variable.clone()))?;
                    let value = model
                        .eval(&Int::new_const(name.clone()), true)
                        .ok_or_else(|| SmtError::MissingModelValue(variable.clone()))?;
                    let rendered = normalize_integer(&value.to_string()).ok_or_else(|| {
                        SmtError::InvalidModelValue {
                            variable: variable.clone(),
                            value: value.to_string(),
                        }
                    })?;
                    Term::domain_value(variable.sort.clone(), rendered)
                }
                sort if sort == &Sort::simple("SortBool") => {
                    let name = mappings
                        .get(&term)
                        .ok_or_else(|| SmtError::MissingModelValue(variable.clone()))?;
                    let value = model
                        .eval(&Bool::new_const(name.clone()), true)
                        .and_then(|value| value.as_bool())
                        .ok_or_else(|| SmtError::MissingModelValue(variable.clone()))?;
                    Term::domain_value(variable.sort.clone(), value.to_string())
                }
                _ => term,
            };
            substitution.insert(variable.clone(), value);
        }
        Ok(ModelResult::Sat(substitution))
    }
}

fn normalize_integer(rendered: &str) -> Option<String> {
    if let Ok(value) = BigInt::from_str(rendered) {
        return Some(value.to_string());
    }
    let magnitude = rendered.strip_prefix("(- ")?.strip_suffix(')')?;
    BigInt::from_str(magnitude)
        .ok()
        .map(|value| (-value).to_string())
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

    fn get_model(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Result<ModelResult, SmtError> {
        if predicates.is_empty() && substitution.is_empty() {
            return Ok(ModelResult::Sat(Substitution::new()));
        }
        let variables = substitution
            .keys()
            .cloned()
            .chain(predicates.iter().flat_map(Predicate::free_variables))
            .collect::<BTreeSet<_>>();
        let query = self.prelude.query(predicates, substitution, &[], false)?;
        self.solve_model(&query, &variables)
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
                sort SortS{} []
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
    fn proves_native_collection_sizes_are_nonnegative() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortList{} []
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                symbol abstractSize{}(SortList{}) : SortInt{}
                    [function{}(), total{}(), hook{}("LIST.size")]
                symbol translatedSize{}(SortList{}) : SortInt{}
                    [function{}(), total{}(), hook{}("LIST.size"), smtlib{}("list-size")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();

        for size in ["abstractSize", "translatedSize"] {
            let checked = [Predicate::Term(term(
                &definition,
                &format!(r#"lt{{}}(\dv{{SortInt{{}}}}("-1"), {size}{{}}(L:SortList{{}}))"#),
            ))];
            assert_eq!(
                solver.check_predicates(&[], &Substitution::new(), &checked),
                Ok(Validity::Valid),
                "{size} should be nonnegative"
            );
        }
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

    #[test]
    fn loads_external_smt_preludes_and_rejects_inconsistent_ones() {
        let definition = definition();
        let consistent = "(declare-const a Int)\n(assert (> a 0))";
        let inconsistent = "(declare-const a Int)\n(assert (> a 0))\n(assert (< a 0))";

        assert!(Z3Solver::with_prelude(&definition, consistent).is_ok());
        assert!(matches!(
            Z3Solver::with_prelude(&definition, inconsistent),
            Err(SmtError::InconsistentPrelude)
        ));
    }

    #[test]
    fn extracts_arbitrary_precision_integer_and_boolean_models() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let integer = Variable::new("X", Sort::simple("SortInt"));
        let boolean = Variable::new("B", Sort::simple("SortBool"));
        let expected_integer = "-99999999999999999999999999999999999999";
        let predicates = [
            Predicate::Equals(
                Term::variable(integer.clone()),
                Term::domain_value(Sort::simple("SortInt"), expected_integer),
            ),
            Predicate::Equals(
                Term::variable(boolean.clone()),
                Term::domain_value(Sort::simple("SortBool"), "true"),
            ),
        ];

        let ModelResult::Sat(model) = solver
            .get_model(&predicates, &Substitution::new())
            .expect("model should be extracted")
        else {
            panic!("constraints should be satisfiable")
        };

        assert_eq!(
            model.get(&integer),
            Some(&Term::domain_value(
                Sort::simple("SortInt"),
                expected_integer
            ))
        );
        assert_eq!(
            model.get(&boolean),
            Some(&Term::domain_value(Sort::simple("SortBool"), "true"))
        );
    }

    #[test]
    fn model_results_distinguish_empty_unsatisfiable_and_untranslated_inputs() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();

        assert_eq!(
            solver.get_model(&[], &Substitution::new()),
            Ok(ModelResult::Sat(Substitution::new()))
        );

        let integer = Variable::new("X", Sort::simple("SortInt"));
        let integer_term = Term::variable(integer);
        assert_eq!(
            solver.get_model(
                &[
                    Predicate::Equals(
                        integer_term.clone(),
                        Term::domain_value(Sort::simple("SortInt"), "1"),
                    ),
                    Predicate::Equals(
                        integer_term,
                        Term::domain_value(Sort::simple("SortInt"), "2"),
                    ),
                ],
                &Substitution::new(),
            ),
            Ok(ModelResult::Unsat)
        );

        let opaque = Variable::new("Y", Sort::simple("SortS"));
        let opaque_term = Term::variable(opaque.clone());
        let ModelResult::Sat(model) = solver
            .get_model(
                &[Predicate::Equals(opaque_term.clone(), opaque_term)],
                &Substitution::new(),
            )
            .unwrap()
        else {
            panic!("reflexive opaque equality should be satisfiable")
        };
        assert_eq!(model.get(&opaque), Some(&Term::variable(opaque.clone())));
    }
}
