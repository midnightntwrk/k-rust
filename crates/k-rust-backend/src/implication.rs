//! Subsumption checks between constrained backend patterns.

use std::{collections::BTreeSet, error::Error, fmt};

use crate::{
    definition::BackendDefinition,
    matching::{FailReason, MatchMode, MatchResult, SortError, match_terms},
    rewrite::{Pattern, Truth, predicates_truth},
    rule::Predicate,
    simplify::{
        SimplificationError, SimplificationOptions, simplify_predicates_with_solver,
        simplify_with_solver,
    },
    smt::{Satisfiability, SmtSolver, Validity},
    substitution::Substitution,
    term::Variable,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImplicationStatus {
    Valid,
    Invalid,
    Indeterminate,
}

/// The condition under which an implication was established.
///
/// An empty predicate list denotes `top`. A vacuous implication carries
/// `false`, mirroring the bottom predicate returned by the reference backend.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImplicationCondition {
    pub predicates: Vec<Predicate>,
    pub substitution: Substitution,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImplicationResult {
    pub status: ImplicationStatus,
    pub condition: Option<ImplicationCondition>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ImplicationError {
    ConsequentFreeVariables(BTreeSet<Variable>),
    Subsorting(SortError),
    Simplification(SimplificationError),
}

impl fmt::Display for ImplicationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl Error for ImplicationError {}

pub fn check_implication(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    consequent: &Pattern,
    solver: &dyn SmtSolver,
) -> Result<ImplicationResult, ImplicationError> {
    check_implication_with_existentials_and_options(
        definition,
        antecedent,
        &BTreeSet::new(),
        consequent,
        &BTreeSet::new(),
        SimplificationOptions::default(),
        solver,
    )
}

pub fn check_implication_with_options(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    consequent: &Pattern,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<ImplicationResult, ImplicationError> {
    check_implication_with_existentials_and_options(
        definition,
        antecedent,
        &BTreeSet::new(),
        consequent,
        &BTreeSet::new(),
        options,
        solver,
    )
}

pub fn check_implication_with_existentials(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    antecedent_existentials: &BTreeSet<Variable>,
    consequent: &Pattern,
    consequent_existentials: &BTreeSet<Variable>,
    solver: &dyn SmtSolver,
) -> Result<ImplicationResult, ImplicationError> {
    check_implication_with_existentials_and_options(
        definition,
        antecedent,
        antecedent_existentials,
        consequent,
        consequent_existentials,
        SimplificationOptions::default(),
        solver,
    )
}

pub fn check_implication_with_existentials_and_options(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    antecedent_existentials: &BTreeSet<Variable>,
    consequent: &Pattern,
    consequent_existentials: &BTreeSet<Variable>,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<ImplicationResult, ImplicationError> {
    let antecedent_variables = free_variables(antecedent)
        .difference(antecedent_existentials)
        .cloned()
        .collect::<BTreeSet<_>>();
    let consequent_variables = free_variables(consequent)
        .difference(consequent_existentials)
        .cloned()
        .collect::<BTreeSet<_>>();
    let extra_variables = consequent_variables
        .difference(&antecedent_variables)
        .cloned()
        .collect::<BTreeSet<_>>();
    if !extra_variables.is_empty() {
        return Err(ImplicationError::ConsequentFreeVariables(extra_variables));
    }

    if predicates_truth(&antecedent.constraints) == Truth::False
        || matches!(
            solver.is_sat(&antecedent.constraints, &Substitution::new()),
            Ok(Satisfiability::Unsat)
        )
    {
        return Ok(vacuously_valid());
    }

    let mut antecedent = antecedent.clone();
    loop {
        match match_terms(
            MatchMode::Implies,
            &definition.sort_graph,
            &consequent.term,
            &antecedent.term,
        ) {
            MatchResult::Failed(FailReason::Subsorting(error)) => {
                return Err(ImplicationError::Subsorting(error));
            }
            MatchResult::Failed(_) => return Ok(invalid()),
            MatchResult::Indeterminate { .. } => {
                let simplified = simplify_with_solver(
                    definition,
                    &antecedent.term,
                    &antecedent.constraints,
                    options,
                    solver,
                )
                .map_err(ImplicationError::Simplification)?;
                let simplified = Pattern {
                    term: simplified.term,
                    constraints: merge_predicates(
                        antecedent.constraints.clone(),
                        simplified.constraints,
                    ),
                };
                if simplified == antecedent {
                    // The reference backend deliberately treats a stable,
                    // unresolved term match as a decisive non-implication.
                    return Ok(invalid());
                }
                antecedent = simplified;
            }
            MatchResult::Success(substitution) => {
                return discharge_consequent(
                    definition,
                    &antecedent,
                    consequent,
                    substitution,
                    options,
                    solver,
                );
            }
        }
    }
}

fn discharge_consequent(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    consequent: &Pattern,
    substitution: Substitution,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<ImplicationResult, ImplicationError> {
    let obligations = consequent
        .constraints
        .iter()
        .filter(|predicate| !antecedent.constraints.contains(predicate))
        .cloned()
        .collect::<Vec<_>>();
    if obligations.is_empty() {
        return Ok(valid(substitution));
    }

    let obligations = match simplify_predicates_with_solver(
        definition,
        &obligations,
        &antecedent.constraints,
        options,
        solver,
    ) {
        Ok(obligations) => obligations,
        Err(_) => return Ok(indeterminate()),
    };
    match predicates_truth(&obligations) {
        Truth::True => return Ok(valid(substitution)),
        Truth::False => return Ok(invalid()),
        Truth::Unknown => {}
    }

    Ok(
        match solver.check_predicates(&antecedent.constraints, &Substitution::new(), &obligations) {
            Ok(Validity::Valid) => valid(substitution),
            Ok(Validity::Invalid) => invalid(),
            Ok(Validity::InconsistentGroundTruth) => vacuously_valid(),
            Ok(Validity::Indeterminate | Validity::Unknown(_)) | Err(_) => indeterminate(),
        },
    )
}

fn free_variables(pattern: &Pattern) -> BTreeSet<Variable> {
    pattern
        .term
        .attributes()
        .variables
        .iter()
        .cloned()
        .chain(
            pattern
                .constraints
                .iter()
                .flat_map(Predicate::free_variables),
        )
        .collect()
}

fn merge_predicates(mut left: Vec<Predicate>, right: Vec<Predicate>) -> Vec<Predicate> {
    for predicate in right {
        if !left.contains(&predicate) {
            left.push(predicate);
        }
    }
    left
}

fn valid(substitution: Substitution) -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Valid,
        condition: Some(ImplicationCondition {
            predicates: Vec::new(),
            substitution,
        }),
    }
}

fn vacuously_valid() -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Valid,
        condition: Some(ImplicationCondition {
            predicates: vec![Predicate::False],
            substitution: Substitution::new(),
        }),
    }
}

fn invalid() -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Invalid,
        condition: None,
    }
}

fn indeterminate() -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Indeterminate,
        condition: None,
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::{
        definition::BackendDefinition,
        smt::{NoSolver, SmtError},
        term::{Sort, Term},
    };

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortKItem{} []
                symbol pair{}(SortInt{}, SortInt{}) : SortKItem{} [constructor{}()]
                symbol f{}(SortInt{}) : SortInt{} [function{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(X:SortInt{}, \top{SortInt{}}())
                    )
                ) [label{}("identity-f"), simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize")
    }

    fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
        Pattern {
            term: term(definition, source),
            constraints: Vec::new(),
        }
    }

    fn int(definition: &BackendDefinition, value: &str) -> Term {
        term(definition, &format!(r#"\dv{{SortInt{{}}}}("{value}")"#))
    }

    #[derive(Clone, Debug)]
    struct FixedSolver {
        satisfiability: Result<Satisfiability, SmtError>,
        validity: Result<Validity, SmtError>,
    }

    impl SmtSolver for FixedSolver {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &Substitution,
        ) -> Result<Satisfiability, SmtError> {
            self.satisfiability.clone()
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Result<Validity, SmtError> {
            self.validity.clone()
        }
    }

    #[test]
    fn identical_patterns_imply_each_other() {
        let definition = definition();
        let pattern = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);

        assert_eq!(
            check_implication(&definition, &pattern, &pattern, &NoSolver),
            Ok(valid(Substitution::new()))
        );
    }

    #[test]
    fn returns_the_condition_found_by_implication_matching() {
        let definition = definition();
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let antecedent = Pattern {
            term: term(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#),
            constraints: vec![Predicate::Equals(
                Term::variable(x.clone()),
                Term::variable(x.clone()),
            )],
        };
        let consequent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &NoSolver),
            Ok(valid(Substitution::from([(x, int(&definition, "1"))])))
        );
    }

    #[test]
    fn rejects_free_variables_introduced_by_the_consequent() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        let consequent = pattern(&definition, r#"pair{}(X:SortInt{}, Y:SortInt{})"#);

        assert!(matches!(
            check_implication(&definition, &antecedent, &consequent, &NoSolver),
            Err(ImplicationError::ConsequentFreeVariables(variables))
                if variables.iter().any(|variable| variable.name.as_ref() == "Y")
        ));
    }

    #[test]
    fn consequent_existentials_are_not_treated_as_free_variables() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);
        let consequent = pattern(&definition, r#"pair{}(X:SortInt{}, Y:SortInt{})"#);
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));

        assert_eq!(
            check_implication_with_existentials(
                &definition,
                &antecedent,
                &BTreeSet::new(),
                &consequent,
                &BTreeSet::from([y]),
                &NoSolver,
            ),
            Ok(valid(Substitution::from([(
                crate::term::Variable::new("Y", Sort::simple("SortInt")),
                Term::variable(crate::term::Variable::new("X", Sort::simple("SortInt"))),
            )])))
        );
    }

    #[test]
    fn constructor_mismatch_is_invalid() {
        let definition = definition();
        let antecedent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("2"))"#,
        );
        let consequent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("3"))"#,
        );

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &NoSolver),
            Ok(invalid())
        );
    }

    #[test]
    fn retries_an_indeterminate_match_after_simplifying_the_antecedent() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"f{}(\dv{SortInt{}}("1"))"#);
        let consequent = pattern(&definition, r#"\dv{SortInt{}}("1")"#);

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &NoSolver),
            Ok(valid(Substitution::new()))
        );
    }

    #[test]
    fn unsatisfiable_antecedent_is_vacuously_valid() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"\dv{SortInt{}}("1")"#);
        let consequent = antecedent.clone();
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Unsat),
            validity: Ok(Validity::Invalid),
        };

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &solver),
            Ok(vacuously_valid())
        );
    }

    #[test]
    fn discharges_residual_consequent_constraints_with_smt() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"X:SortInt{}"#);
        let mut consequent = antecedent.clone();
        consequent.constraints.push(Predicate::Equals(
            Term::variable(crate::term::Variable::new("X", Sort::simple("SortInt"))),
            int(&definition, "1"),
        ));
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Valid),
        };

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &solver),
            Ok(valid(Substitution::new()))
        );
    }

    #[test]
    fn stable_unresolved_function_match_is_invalid() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"f{}(X:SortInt{})"#);
        let consequent = pattern(&definition, r#"f{}(X:SortInt{})"#);
        let other = pattern(&definition, r#"\dv{SortInt{}}("1")"#);

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &NoSolver),
            Ok(valid(Substitution::new()))
        );
        assert_eq!(
            check_implication(&definition, &antecedent, &other, &NoSolver),
            Ok(invalid())
        );
    }

    #[test]
    fn quantified_variables_do_not_hide_free_variables_in_sibling_predicates() {
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let x_term = Term::variable(x.clone());
        let predicate = Predicate::And(vec![
            Predicate::Equals(x_term.clone(), x_term.clone()),
            Predicate::Exists(
                x.clone(),
                Box::new(Predicate::Equals(x_term.clone(), x_term)),
            ),
        ]);

        assert_eq!(predicate.free_variables(), BTreeSet::from([x]));
    }
}
