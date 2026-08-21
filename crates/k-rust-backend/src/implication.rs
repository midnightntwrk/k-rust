//! Subsumption checks between constrained backend patterns.

use std::{collections::BTreeSet, error::Error, fmt};

use crate::{
    definition::BackendDefinition,
    matching::{
        FailReason, MatchMode, MatchResult, SortError, expand_closed_map_implication_remainders,
        match_terms_in_definition,
    },
    rewrite::{Pattern, Truth, predicates_truth, substitute_predicates},
    rule::Predicate,
    simplify::{
        SimplificationError, SimplificationOptions, simplify_predicates_with_solver,
        simplify_with_solver,
    },
    smt::{Satisfiability, SmtSolver, Validity},
    substitution::{Substitution, substitute},
    term::Variable,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImplicationStatus {
    Valid,
    Invalid,
    Indeterminate,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImplicationFailure {
    TermMismatch,
    ConsequentCondition,
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
    pub failure: Option<ImplicationFailure>,
}

#[derive(Clone, Copy)]
struct Destination<'a> {
    pattern: &'a Pattern,
    existentials: &'a BTreeSet<Variable>,
}

#[derive(Clone, Copy)]
struct Source<'a> {
    pattern: &'a Pattern,
    original_variable: Option<&'a Variable>,
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

/// Check whether an antecedent is covered by the union of several consequents.
///
/// A reachability destination is a disjunction, so proving each branch in
/// isolation is sufficient but not complete. This operation matches every
/// branch, combines the residual branch conditions with logical `or`, and
/// asks the solver to discharge that combined obligation.
pub fn check_disjunctive_implication_with_existentials(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    consequents: &[Pattern],
    consequent_existentials: &BTreeSet<Variable>,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<ImplicationResult, ImplicationError> {
    if let [consequent] = consequents {
        return check_implication_with_existentials_and_options(
            definition,
            antecedent,
            &BTreeSet::new(),
            consequent,
            consequent_existentials,
            options,
            solver,
        );
    }

    let consequents = consequents
        .iter()
        .map(|consequent| freshen_existentials(antecedent, consequent, consequent_existentials))
        .collect::<Vec<_>>();
    let antecedent_variables = free_variables(antecedent);
    for (consequent, existentials) in &consequents {
        let consequent_variables = free_variables(consequent)
            .difference(existentials)
            .cloned()
            .collect::<BTreeSet<_>>();
        let extra_variables = consequent_variables
            .difference(&antecedent_variables)
            .cloned()
            .collect::<BTreeSet<_>>();
        if !extra_variables.is_empty() {
            return Err(ImplicationError::ConsequentFreeVariables(extra_variables));
        }
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
        let mut branches = Vec::new();
        let mut matched = false;
        let mut incomplete = false;
        for (consequent, existentials) in &consequents {
            let (substitution, remainder) = match match_terms_in_definition(
                MatchMode::Implies,
                definition,
                &consequent.term,
                &antecedent.term,
            ) {
                MatchResult::Failed(FailReason::Subsorting(error)) => {
                    return Err(ImplicationError::Subsorting(error));
                }
                MatchResult::Failed(_) => continue,
                MatchResult::Indeterminate {
                    substitution,
                    remainder,
                } => (substitution, remainder),
                MatchResult::Success(substitution) => (substitution, Vec::new()),
            };
            matched = true;
            let obligations = implication_obligation_branches(
                consequent,
                &substitution,
                remainder,
                &antecedent.constraints,
            );
            let obligations = combine_obligation_branches(obligations, existentials);
            let obligations = match simplify_predicates_with_solver(
                definition,
                &obligations,
                &antecedent.constraints,
                options,
                solver,
            ) {
                Ok(obligations) => obligations,
                Err(_) => {
                    incomplete = true;
                    continue;
                }
            };
            match predicates_truth(&obligations) {
                Truth::True => return Ok(valid(Substitution::new())),
                Truth::False => continue,
                Truth::Unknown => branches.push(conjoin(obligations)),
            }
        }

        if !branches.is_empty() {
            let combined = vec![Predicate::Or(branches)];
            let combined = simplify_predicates_with_solver(
                definition,
                &combined,
                &antecedent.constraints,
                options,
                solver,
            )
            .unwrap_or(combined);
            match predicates_truth(&combined) {
                Truth::True => return Ok(valid(Substitution::new())),
                Truth::False => {}
                Truth::Unknown => match solver.check_predicates(
                    &antecedent.constraints,
                    &Substitution::new(),
                    &combined,
                ) {
                    Ok(Validity::Valid) => return Ok(valid(Substitution::new())),
                    Ok(Validity::InconsistentGroundTruth) => return Ok(vacuously_valid()),
                    Ok(Validity::Invalid) => {}
                    Ok(Validity::Indeterminate | Validity::Unknown(_)) | Err(_) => {
                        incomplete = true;
                    }
                },
            }
        }

        if incomplete {
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
            if simplified != antecedent {
                antecedent = simplified;
                continue;
            }
            return Ok(indeterminate());
        }
        return Ok(if matched {
            condition_invalid()
        } else {
            invalid()
        });
    }
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
    let (consequent, consequent_existentials) =
        freshen_existentials(antecedent, consequent, consequent_existentials);
    let antecedent_variables = free_variables(antecedent)
        .difference(antecedent_existentials)
        .cloned()
        .collect::<BTreeSet<_>>();
    let consequent_variables = free_variables(&consequent)
        .difference(&consequent_existentials)
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

    let original_antecedent_variable = match antecedent.term.kind() {
        crate::term::TermKind::Variable(variable) => Some(variable.clone()),
        _ => None,
    };
    let mut antecedent = antecedent.clone();
    loop {
        match match_terms_in_definition(
            MatchMode::Implies,
            definition,
            &consequent.term,
            &antecedent.term,
        ) {
            MatchResult::Failed(FailReason::Subsorting(error)) => {
                return Err(ImplicationError::Subsorting(error));
            }
            MatchResult::Failed(_) => return Ok(invalid()),
            MatchResult::Indeterminate {
                substitution,
                remainder,
            } => {
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
                    return discharge_consequent(
                        definition,
                        Source {
                            pattern: &antecedent,
                            original_variable: original_antecedent_variable.as_ref(),
                        },
                        Destination {
                            pattern: &consequent,
                            existentials: &consequent_existentials,
                        },
                        substitution,
                        remainder,
                        options,
                        solver,
                    );
                }
                antecedent = simplified;
            }
            MatchResult::Success(substitution) => {
                return discharge_consequent(
                    definition,
                    Source {
                        pattern: &antecedent,
                        original_variable: original_antecedent_variable.as_ref(),
                    },
                    Destination {
                        pattern: &consequent,
                        existentials: &consequent_existentials,
                    },
                    substitution,
                    Vec::new(),
                    options,
                    solver,
                );
            }
        }
    }
}

fn freshen_existentials(
    antecedent: &Pattern,
    consequent: &Pattern,
    existentials: &BTreeSet<Variable>,
) -> (Pattern, BTreeSet<Variable>) {
    let mut names = free_variables(antecedent)
        .into_iter()
        .chain(free_variables(consequent))
        .map(|variable| variable.name)
        .collect::<BTreeSet<_>>();
    let mut substitution = Substitution::new();
    let mut fresh = BTreeSet::new();
    for (counter, original) in existentials.iter().enumerate() {
        let mut suffix = counter;
        let name = loop {
            let candidate = format!("{}!exists{suffix}", original.name);
            if names.insert(candidate.as_str().into()) {
                break candidate;
            }
            suffix += 1;
        };
        let variable = original.with_name(name);
        substitution.insert(
            original.clone(),
            crate::term::Term::variable(variable.clone()),
        );
        fresh.insert(variable);
    }
    (
        Pattern {
            term: substitute(&consequent.term, &substitution),
            constraints: substitute_predicates(&consequent.constraints, &substitution),
        },
        fresh,
    )
}

fn discharge_consequent(
    definition: &BackendDefinition,
    antecedent: Source<'_>,
    consequent: Destination<'_>,
    substitution: Substitution,
    remainder: Vec<(crate::term::Term, crate::term::Term)>,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<ImplicationResult, ImplicationError> {
    let source = antecedent;
    let antecedent = source.pattern;
    let had_match_remainder = !remainder.is_empty();
    let obligations = implication_obligation_branches(
        consequent.pattern,
        &substitution,
        remainder,
        &antecedent.constraints,
    );
    let obligations = combine_obligation_branches(obligations, consequent.existentials);
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
        Truth::False => {
            return Ok(if had_match_remainder {
                invalid()
            } else {
                condition_invalid_with_substitution(substitution)
            });
        }
        Truth::Unknown => {}
    }

    Ok(
        match solver.check_predicates(&antecedent.constraints, &Substitution::new(), &obligations) {
            Ok(Validity::Valid) => valid(substitution),
            Ok(Validity::Invalid) if had_match_remainder => {
                partial(source.original_variable, substitution, obligations)
            }
            Ok(Validity::Invalid) => condition_invalid_with_substitution(substitution),
            Ok(Validity::InconsistentGroundTruth) => vacuously_valid(),
            Ok(Validity::Indeterminate | Validity::Unknown(_)) | Err(_) if had_match_remainder => {
                partial(source.original_variable, substitution, obligations)
            }
            Ok(Validity::Indeterminate | Validity::Unknown(_)) | Err(_) => indeterminate(),
        },
    )
}

fn quantify_obligations(
    obligations: Vec<Predicate>,
    existentials: &BTreeSet<Variable>,
) -> Vec<Predicate> {
    if obligations.is_empty() {
        return obligations;
    }
    let free = obligations
        .iter()
        .flat_map(Predicate::free_variables)
        .collect::<BTreeSet<_>>();
    let quantified = existentials
        .iter()
        .filter(|variable| free.contains(*variable))
        .cloned()
        .collect::<Vec<_>>();
    if quantified.is_empty() {
        return obligations;
    }
    let mut obligation = conjoin(obligations);
    for variable in quantified.into_iter().rev() {
        obligation = Predicate::Exists(variable, Box::new(obligation));
    }
    vec![obligation]
}

fn combine_obligation_branches(
    branches: Vec<Vec<Predicate>>,
    existentials: &BTreeSet<Variable>,
) -> Vec<Predicate> {
    let mut branches = branches
        .into_iter()
        .map(|branch| quantify_obligations(branch, existentials))
        .collect::<Vec<_>>();
    match branches.len() {
        0 => vec![Predicate::False],
        1 => branches.pop().expect("one implication branch is present"),
        _ => vec![Predicate::Or(
            branches.into_iter().map(conjoin).collect::<Vec<_>>(),
        )],
    }
}

fn implication_obligation_branches(
    consequent: &Pattern,
    substitution: &Substitution,
    remainder: Vec<(crate::term::Term, crate::term::Term)>,
    known: &[Predicate],
) -> Vec<Vec<Predicate>> {
    let branches = expand_closed_map_implication_remainders(substitution, &remainder)
        .unwrap_or_else(|| vec![remainder]);
    branches
        .into_iter()
        .map(|remainder| implication_obligations(consequent, substitution, remainder, known))
        .collect()
}

fn implication_obligations(
    consequent: &Pattern,
    substitution: &Substitution,
    remainder: Vec<(crate::term::Term, crate::term::Term)>,
    known: &[Predicate],
) -> Vec<Predicate> {
    let mut obligations = Vec::new();
    for (left, right) in remainder {
        let predicate = Predicate::Equals(
            substitute(&left, substitution),
            substitute(&right, substitution),
        );
        if !obligations.contains(&predicate) {
            obligations.push(predicate);
        }
    }
    for predicate in substitute_predicates(&consequent.constraints, substitution) {
        if !obligations.contains(&predicate) {
            obligations.push(predicate);
        }
    }
    obligations.retain(|predicate| !known.contains(predicate));
    obligations
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

fn conjoin(mut predicates: Vec<Predicate>) -> Predicate {
    match predicates.len() {
        0 => Predicate::True,
        1 => predicates.pop().expect("one predicate is present"),
        _ => Predicate::And(predicates),
    }
}

fn valid(substitution: Substitution) -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Valid,
        condition: Some(ImplicationCondition {
            predicates: Vec::new(),
            substitution,
        }),
        failure: None,
    }
}

fn vacuously_valid() -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Valid,
        condition: Some(ImplicationCondition {
            predicates: vec![Predicate::False],
            substitution: Substitution::new(),
        }),
        failure: None,
    }
}

fn invalid() -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Invalid,
        condition: None,
        failure: Some(ImplicationFailure::TermMismatch),
    }
}

fn condition_invalid() -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Invalid,
        condition: None,
        failure: Some(ImplicationFailure::ConsequentCondition),
    }
}

fn condition_invalid_with_substitution(substitution: Substitution) -> ImplicationResult {
    if substitution.is_empty() {
        return condition_invalid();
    }
    ImplicationResult {
        status: ImplicationStatus::Invalid,
        condition: Some(ImplicationCondition {
            predicates: Vec::new(),
            substitution,
        }),
        failure: Some(ImplicationFailure::ConsequentCondition),
    }
}

fn partial(
    antecedent_variable: Option<&Variable>,
    mut substitution: Substitution,
    predicates: Vec<Predicate>,
) -> ImplicationResult {
    let mut predicates = predicates;
    predicates.retain(|predicate| {
        let Predicate::Equals(left, right) = predicate else {
            return true;
        };
        let binding = implication_binding(left, right, antecedent_variable)
            .or_else(|| implication_binding(right, left, antecedent_variable));
        let Some((variable, value)) = binding else {
            return true;
        };
        if substitution.contains_key(variable) {
            return true;
        }
        substitution.insert(variable.clone(), value.clone());
        false
    });
    ImplicationResult {
        status: ImplicationStatus::Invalid,
        condition: Some(ImplicationCondition {
            predicates,
            substitution,
        }),
        failure: Some(ImplicationFailure::TermMismatch),
    }
}

fn implication_binding<'a>(
    variable: &'a crate::term::Term,
    value: &'a crate::term::Term,
    antecedent_variable: Option<&Variable>,
) -> Option<(&'a Variable, &'a crate::term::Term)> {
    let crate::term::TermKind::Variable(variable) = variable.kind() else {
        return None;
    };
    (antecedent_variable == Some(variable) && !value.attributes().variables.contains(variable))
        .then_some((variable, value))
}

fn indeterminate() -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Indeterminate,
        condition: None,
        failure: None,
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    #[cfg(feature = "z3")]
    use crate::smt::Z3Solver;
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
                symbol succ{}(SortInt{}) : SortInt{} [constructor{}()]
                symbol f{}(SortInt{}) : SortInt{} [function{}()]
                symbol opaque{}(SortInt{}) : SortInt{} [function{}()]
                symbol sub{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), smt-hook{}("-")]
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
    fn retains_a_simplifiable_occurs_check_as_a_partial_implication_condition() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"opaque{}(X:SortInt{})"#);
        let consequent = pattern(&definition, r#"X:SortInt{}"#);

        let result = check_implication(&definition, &antecedent, &consequent, &NoSolver)
            .expect("implication should be checked");

        assert_eq!(result.status, ImplicationStatus::Invalid);
        let condition = result
            .condition
            .expect("the recursively matched subset should be retained");
        assert!(matches!(
            condition.predicates.as_slice(),
            [Predicate::Equals(left, right)]
                if left == &term(&definition, "X:SortInt{}")
                    && right == &term(&definition, "opaque{}(X:SortInt{})")
        ));
    }

    #[test]
    fn promotes_a_partial_configuration_binding_into_the_implication_substitution() {
        let definition = definition();
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let antecedent = pattern(&definition, "X:SortInt{}");
        let value = int(&definition, "0");
        let consequent = Pattern {
            term: value.clone(),
            constraints: Vec::new(),
        };

        let result = check_implication(&definition, &antecedent, &consequent, &NoSolver)
            .expect("implication should be checked");
        let condition = result
            .condition
            .expect("the partial configuration binding should be retained");

        assert_eq!(result.status, ImplicationStatus::Invalid);
        assert_eq!(condition.substitution, Substitution::from([(x, value)]));
        assert!(condition.predicates.is_empty());
    }

    #[test]
    fn rejects_an_occurs_check_below_only_constructors() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"succ{}(X:SortInt{})"#);
        let consequent = pattern(&definition, r#"X:SortInt{}"#);

        let result = check_implication(&definition, &antecedent, &consequent, &NoSolver)
            .expect("implication should be checked");

        assert_eq!(result.status, ImplicationStatus::Invalid);
        assert_eq!(result.condition, None);
        assert_eq!(result.failure, Some(ImplicationFailure::TermMismatch));
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

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y]),
            &NoSolver,
        )
        .expect("implication should be checked");
        assert_eq!(result.status, ImplicationStatus::Valid);
        let condition = result.condition.expect("a valid result has a condition");
        assert!(condition.predicates.is_empty());
        assert_eq!(
            condition.substitution.values().collect::<Vec<_>>(),
            vec![&Term::variable(crate::term::Variable::new(
                "X",
                Sort::simple("SortInt"),
            ))]
        );
    }

    #[test]
    fn invalid_consequent_conditions_retain_the_match_substitution() {
        let definition = definition();
        let antecedent = pattern(&definition, "X:SortInt{}");
        let mut consequent = pattern(&definition, "Y:SortInt{}");
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        consequent
            .constraints
            .push(Predicate::Not(Box::new(Predicate::Equals(
                Term::variable(x.clone()),
                Term::variable(y.clone()),
            ))));

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y]),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result.status, ImplicationStatus::Invalid);
        let condition = result
            .condition
            .expect("the successful term match is retained");
        assert!(condition.predicates.is_empty());
        assert_eq!(
            condition.substitution.values().collect::<Vec<_>>(),
            [&Term::variable(x)]
        );
    }

    #[test]
    fn applies_the_match_substitution_to_consequent_constraints() {
        let definition = definition();
        let antecedent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("1"))"#,
        );
        let mut consequent = pattern(&definition, r#"pair{}(Y:SortInt{}, Y:SortInt{})"#);
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        consequent.constraints.push(Predicate::Equals(
            Term::variable(y.clone()),
            int(&definition, "1"),
        ));

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y]),
            &NoSolver,
        )
        .expect("implication should be checked");

        assert_eq!(result.status, ImplicationStatus::Valid);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn quantifies_existential_variables_nested_in_smt_terms() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);
        let consequent = pattern(
            &definition,
            r#"pair{}(X:SortInt{}, sub{}(Y:SortInt{}, \dv{SortInt{}}("1")))"#,
        );
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y]),
            &solver,
        )
        .expect("implication should be checked");

        assert_eq!(result.status, ImplicationStatus::Valid);
    }

    #[test]
    fn refreshes_existentials_away_from_antecedent_variables() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        let consequent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([x]),
            &NoSolver,
        )
        .expect("implication should be checked");
        assert_eq!(result.status, ImplicationStatus::Invalid);
        let condition = result
            .condition
            .expect("the matching subset should be retained");
        assert_eq!(condition.predicates.len(), 1);
        assert!(
            condition
                .substitution
                .keys()
                .all(|variable| variable.name.contains("!exists"))
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
    fn discharges_symbolic_term_match_equalities_with_smt() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);
        let consequent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("0"))"#,
        );
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
    fn discharges_the_union_of_complementary_consequent_conditions() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);
        let zero = int(&definition, "0");
        let x = Term::variable(crate::term::Variable::new("X", Sort::simple("SortInt")));
        let equality = Predicate::Equals(x, zero);
        let mut first = antecedent.clone();
        first.constraints.push(equality.clone());
        let mut second = antecedent.clone();
        second.constraints.push(Predicate::Not(Box::new(equality)));

        #[derive(Clone, Copy, Debug)]
        struct DisjunctionSolver;

        impl SmtSolver for DisjunctionSolver {
            fn is_sat(
                &self,
                _predicates: &[Predicate],
                _substitution: &Substitution,
            ) -> Result<Satisfiability, SmtError> {
                Ok(Satisfiability::Sat)
            }

            fn check_predicates(
                &self,
                _known: &[Predicate],
                _substitution: &Substitution,
                checked: &[Predicate],
            ) -> Result<Validity, SmtError> {
                if matches!(checked, [Predicate::Or(branches)] if branches.len() == 2) {
                    Ok(Validity::Valid)
                } else {
                    Ok(Validity::Invalid)
                }
            }
        }

        assert_eq!(
            check_implication(&definition, &antecedent, &first, &DisjunctionSolver),
            Ok(condition_invalid())
        );
        assert_eq!(
            check_implication(&definition, &antecedent, &second, &DisjunctionSolver),
            Ok(condition_invalid())
        );
        assert_eq!(
            check_disjunctive_implication_with_existentials(
                &definition,
                &antecedent,
                &[first, second],
                &BTreeSet::new(),
                SimplificationOptions::default(),
                &DisjunctionSolver,
            ),
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
        let result = check_implication(&definition, &antecedent, &other, &NoSolver)
            .expect("implication should be checked");
        assert_eq!(result.status, ImplicationStatus::Invalid);
        assert_eq!(
            result
                .condition
                .expect("the matching subset should be retained")
                .predicates
                .len(),
            1,
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
