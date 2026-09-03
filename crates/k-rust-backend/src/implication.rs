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
    substitution::{Substitution, compose, extract_substitution_for, substitute},
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
    PartialCoverage,
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
    /// Existential bindings recovered from residual implication obligations.
    ///
    /// These are kept separate from the term-match substitution because the KORE RPC wire only
    /// reports the latter.
    pub witnesses: Substitution,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImplicationResult {
    pub status: ImplicationStatus,
    pub condition: Option<ImplicationCondition>,
    pub failure: Option<ImplicationFailure>,
    /// Whether validity follows only because the antecedent simplifies to bottom.
    pub vacuous: bool,
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
struct Obligations {
    predicates: Vec<Predicate>,
    witnesses: Substitution,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CounterexamplePolicy {
    PreserveIndeterminate,
    RefuteImplication,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ImplicationCheckOptions {
    simplification: SimplificationOptions,
    counterexamples: CounterexamplePolicy,
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

/// Check an implication and use a concrete SMT counterexample as a decisive refutation.
///
/// Booster reports `indeterminate` when both the consequent obligation and its negation are
/// satisfiable under the antecedent. The public KORE service falls back to kore for that case,
/// which reports the counterexample as `invalid`. This entry point performs that final
/// classification in process while preserving genuine solver and matching uncertainty.
pub fn check_implication_with_existentials_complete(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    antecedent_existentials: &BTreeSet<Variable>,
    consequent: &Pattern,
    consequent_existentials: &BTreeSet<Variable>,
    solver: &dyn SmtSolver,
) -> Result<ImplicationResult, ImplicationError> {
    check_implication_with_existentials_and_options_and_policy(
        definition,
        antecedent,
        antecedent_existentials,
        consequent,
        consequent_existentials,
        ImplicationCheckOptions {
            simplification: SimplificationOptions::default(),
            counterexamples: CounterexamplePolicy::RefuteImplication,
        },
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
            let obligations = match eliminate_and_quantify_obligation_branches(
                definition,
                obligations,
                existentials,
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
            let predicates = match simplify_predicates_with_solver(
                definition,
                &obligations.predicates,
                &antecedent.constraints,
                options,
                solver,
            ) {
                Ok(predicates) => predicates,
                Err(_) => {
                    incomplete = true;
                    continue;
                }
            };
            let obligations = Obligations {
                predicates,
                witnesses: obligations.witnesses,
            };
            match predicates_truth(&obligations.predicates) {
                Truth::True => {
                    return Ok(valid_with_witnesses(
                        Substitution::new(),
                        obligations.witnesses,
                    ));
                }
                Truth::False => continue,
                Truth::Unknown => branches.push(obligations),
            }
        }

        if !branches.is_empty() {
            let witnesses = if let [branch] = branches.as_slice() {
                branch.witnesses.clone()
            } else {
                Substitution::new()
            };
            let combined = vec![Predicate::Or(
                branches
                    .into_iter()
                    .map(|branch| conjoin(branch.predicates))
                    .collect(),
            )];
            let combined = simplify_predicates_with_solver(
                definition,
                &combined,
                &antecedent.constraints,
                options,
                solver,
            )
            .unwrap_or(combined);
            match predicates_truth(&combined) {
                Truth::True => {
                    return Ok(valid_with_witnesses(Substitution::new(), witnesses));
                }
                Truth::False => {}
                Truth::Unknown => match solver.check_predicates(
                    &antecedent.constraints,
                    &Substitution::new(),
                    &combined,
                ) {
                    Ok(Validity::Valid) => {
                        return Ok(valid_with_witnesses(Substitution::new(), witnesses));
                    }
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
    check_implication_with_existentials_and_options_and_policy(
        definition,
        antecedent,
        antecedent_existentials,
        consequent,
        consequent_existentials,
        ImplicationCheckOptions {
            simplification: options,
            counterexamples: CounterexamplePolicy::PreserveIndeterminate,
        },
        solver,
    )
}

fn check_implication_with_existentials_and_options_and_policy(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    antecedent_existentials: &BTreeSet<Variable>,
    consequent: &Pattern,
    consequent_existentials: &BTreeSet<Variable>,
    options: ImplicationCheckOptions,
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
                    options.simplification,
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
    options: ImplicationCheckOptions,
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
    let obligations = match eliminate_and_quantify_obligation_branches(
        definition,
        obligations,
        consequent.existentials,
        &antecedent.constraints,
        options.simplification,
        solver,
    ) {
        Ok(obligations) => obligations,
        Err(_) => return Ok(indeterminate()),
    };
    if obligations.predicates.is_empty() {
        return Ok(valid_with_witnesses(substitution, obligations.witnesses));
    }

    let predicates = match simplify_predicates_with_solver(
        definition,
        &obligations.predicates,
        &antecedent.constraints,
        options.simplification,
        solver,
    ) {
        Ok(predicates) => predicates,
        Err(_) => return Ok(indeterminate()),
    };
    let obligations = Obligations {
        predicates,
        witnesses: obligations.witnesses,
    };
    match predicates_truth(&obligations.predicates) {
        Truth::True => {
            return Ok(valid_with_witnesses(substitution, obligations.witnesses));
        }
        Truth::False => {
            return Ok(if had_match_remainder {
                invalid()
            } else {
                condition_invalid_with_bindings(substitution, obligations.witnesses)
            });
        }
        Truth::Unknown => {}
    }

    let Obligations {
        predicates: obligations,
        witnesses,
    } = obligations;
    Ok(
        match solver.check_predicates(&antecedent.constraints, &Substitution::new(), &obligations) {
            Ok(Validity::Valid) => valid_with_witnesses(substitution, witnesses),
            Ok(Validity::Invalid) if had_match_remainder => partial(
                source.original_variable,
                substitution,
                witnesses,
                obligations,
            ),
            Ok(Validity::Invalid) => condition_invalid_with_bindings(substitution, witnesses),
            Ok(Validity::InconsistentGroundTruth) => vacuously_valid(),
            Ok(Validity::Indeterminate | Validity::Unknown(_)) | Err(_) if had_match_remainder => {
                partial(
                    source.original_variable,
                    substitution,
                    witnesses,
                    obligations,
                )
            }
            Ok(Validity::Indeterminate)
                if options.counterexamples == CounterexamplePolicy::RefuteImplication =>
            {
                counterexample_invalid_with_bindings(substitution, witnesses)
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

fn eliminate_and_quantify_obligation_branches(
    definition: &BackendDefinition,
    branches: Vec<Vec<Predicate>>,
    existentials: &BTreeSet<Variable>,
    known: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Obligations, SimplificationError> {
    let mut prepared = Vec::with_capacity(branches.len());
    for branch in branches {
        let mut obligations = eliminate_existential_witnesses(
            definition,
            branch,
            existentials,
            known,
            options,
            solver,
        )?;
        let remaining = existentials
            .iter()
            .filter(|variable| !obligations.witnesses.contains_key(*variable))
            .cloned()
            .collect::<BTreeSet<_>>();
        obligations.predicates = quantify_obligations(obligations.predicates, &remaining);
        prepared.push(obligations);
    }
    Ok(combine_obligation_branches(prepared))
}

fn eliminate_existential_witnesses(
    definition: &BackendDefinition,
    branch: Vec<Predicate>,
    existentials: &BTreeSet<Variable>,
    known: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Obligations, SimplificationError> {
    let mut branch = simplify_predicates_with_solver(definition, &branch, known, options, solver)?;
    branch.retain(|predicate| !matches!(predicate, Predicate::True));
    let mut witnesses = Substitution::new();
    if predicates_truth(&branch) == Truth::False {
        return Ok(Obligations {
            predicates: vec![Predicate::False],
            witnesses,
        });
    }

    let mut remaining = existentials.clone();
    loop {
        let (found, rest) = extract_substitution_for(&branch, &remaining, &definition.sort_graph);
        if found.is_empty() {
            break;
        }
        remaining.retain(|variable| !found.contains_key(variable));
        witnesses = compose(&found, &witnesses);
        branch = simplify_predicates_with_solver(
            definition,
            &substitute_predicates(&rest, &found),
            known,
            options,
            solver,
        )?;
        branch.retain(|predicate| !matches!(predicate, Predicate::True));
        if predicates_truth(&branch) == Truth::False {
            return Ok(Obligations {
                predicates: vec![Predicate::False],
                witnesses,
            });
        }
    }

    if let Some(found) = residual_existential_equality_match(definition, &branch, &remaining) {
        witnesses = compose(&found, &witnesses);
        branch.clear();
    }

    Ok(Obligations {
        predicates: substitute_predicates(&branch, &witnesses),
        witnesses,
    })
}

fn residual_existential_equality_match(
    definition: &BackendDefinition,
    branch: &[Predicate],
    remaining: &BTreeSet<Variable>,
) -> Option<Substitution> {
    let [Predicate::Equals(left, right)] = branch else {
        return None;
    };
    for (pattern, subject) in [(left, right), (right, left)] {
        if pattern.attributes().variables.is_disjoint(remaining) {
            continue;
        }
        if let MatchResult::Success(substitution) =
            match_terms_in_definition(MatchMode::Implies, definition, pattern, subject)
            && substitution
                .keys()
                .all(|variable| remaining.contains(variable))
        {
            return Some(substitution);
        }
    }
    None
}

fn combine_obligation_branches(mut branches: Vec<Obligations>) -> Obligations {
    match branches.len() {
        0 => Obligations {
            predicates: vec![Predicate::False],
            witnesses: Substitution::new(),
        },
        1 => branches.pop().expect("one implication branch is present"),
        _ => {
            if let Some(index) = branches
                .iter()
                .position(|branch| predicates_truth(&branch.predicates) == Truth::True)
            {
                return branches.swap_remove(index);
            }
            Obligations {
                predicates: vec![Predicate::Or(
                    branches
                        .into_iter()
                        .map(|branch| conjoin(branch.predicates))
                        .collect(),
                )],
                witnesses: Substitution::new(),
            }
        }
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

#[cfg(test)]
fn valid(substitution: Substitution) -> ImplicationResult {
    valid_with_witnesses(substitution, Substitution::new())
}

fn valid_with_witnesses(substitution: Substitution, witnesses: Substitution) -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Valid,
        condition: Some(ImplicationCondition {
            predicates: Vec::new(),
            substitution,
            witnesses,
        }),
        failure: None,
        vacuous: false,
    }
}

fn vacuously_valid() -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Valid,
        condition: Some(ImplicationCondition {
            predicates: vec![Predicate::False],
            substitution: Substitution::new(),
            witnesses: Substitution::new(),
        }),
        failure: None,
        vacuous: true,
    }
}

fn invalid() -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Invalid,
        condition: None,
        failure: Some(ImplicationFailure::TermMismatch),
        vacuous: false,
    }
}

fn condition_invalid() -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Invalid,
        condition: Some(ImplicationCondition {
            predicates: vec![Predicate::False],
            substitution: Substitution::new(),
            witnesses: Substitution::new(),
        }),
        failure: Some(ImplicationFailure::ConsequentCondition),
        vacuous: false,
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
            witnesses: Substitution::new(),
        }),
        failure: Some(ImplicationFailure::ConsequentCondition),
        vacuous: false,
    }
}

fn condition_invalid_with_bindings(
    substitution: Substitution,
    witnesses: Substitution,
) -> ImplicationResult {
    if witnesses.is_empty() {
        return condition_invalid_with_substitution(substitution);
    }
    ImplicationResult {
        status: ImplicationStatus::Invalid,
        condition: Some(ImplicationCondition {
            predicates: Vec::new(),
            substitution,
            witnesses,
        }),
        failure: Some(ImplicationFailure::ConsequentCondition),
        vacuous: false,
    }
}

fn counterexample_invalid(substitution: Substitution) -> ImplicationResult {
    ImplicationResult {
        status: ImplicationStatus::Invalid,
        condition: Some(ImplicationCondition {
            predicates: Vec::new(),
            substitution,
            witnesses: Substitution::new(),
        }),
        failure: Some(ImplicationFailure::ConsequentCondition),
        vacuous: false,
    }
}

fn counterexample_invalid_with_bindings(
    substitution: Substitution,
    witnesses: Substitution,
) -> ImplicationResult {
    if witnesses.is_empty() {
        return counterexample_invalid(substitution);
    }
    ImplicationResult {
        status: ImplicationStatus::Invalid,
        condition: Some(ImplicationCondition {
            predicates: Vec::new(),
            substitution,
            witnesses,
        }),
        failure: Some(ImplicationFailure::ConsequentCondition),
        vacuous: false,
    }
}

fn partial(
    antecedent_variable: Option<&Variable>,
    mut substitution: Substitution,
    witnesses: Substitution,
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
            witnesses,
        }),
        failure: Some(ImplicationFailure::PartialCoverage),
        vacuous: false,
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
        vacuous: false,
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
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortTree{} []
                sort SortKItem{} []
                symbol pair{}(SortInt{}, SortInt{}) : SortKItem{} [constructor{}()]
                symbol succ{}(SortTree{}) : SortTree{} [constructor{}()]
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

    fn assert_single_witness(result: &ImplicationResult, original_name: &str, expected: &Term) {
        let condition = result
            .condition
            .as_ref()
            .expect("a valid implication carries its condition");
        assert_eq!(condition.witnesses.len(), 1, "{condition:#?}");
        let (variable, value) = condition
            .witnesses
            .iter()
            .next()
            .expect("one witness was just required");
        assert!(
            variable.name.starts_with(original_name),
            "the refreshed witness should retain its source name: {variable:?}"
        );
        assert_eq!(value, expected);
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
        assert_eq!(result.failure, Some(ImplicationFailure::PartialCoverage));
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
    fn term_mismatch_results_carry_no_condition() {
        let definition = definition();
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let value = int(&definition, "0");
        let antecedent = Pattern {
            term: Term::variable(x.clone()),
            constraints: vec![Predicate::Not(Box::new(Predicate::Equals(
                Term::variable(x),
                value.clone(),
            )))],
        };
        let consequent = Pattern {
            term: value,
            constraints: vec![Predicate::False],
        };

        let result = check_implication(&definition, &antecedent, &consequent, &NoSolver)
            .expect("implication should be checked");

        assert_eq!(result.status, ImplicationStatus::Invalid);
        assert_eq!(result.condition, None);
        assert_eq!(result.failure, Some(ImplicationFailure::TermMismatch));
    }

    #[test]
    fn rejects_an_occurs_check_below_only_constructors() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"succ{}(X:SortTree{})"#);
        let consequent = pattern(&definition, r#"X:SortTree{}"#);

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
        assert!(condition.witnesses.is_empty());
        assert_eq!(
            condition.substitution.values().collect::<Vec<_>>(),
            vec![&Term::variable(crate::term::Variable::new(
                "X",
                Sort::simple("SortInt"),
            ))]
        );
    }

    #[test]
    fn eliminates_existential_witnesses_by_substitution() {
        let definition = definition();
        let value = int(&definition, "5");
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        let mut consequent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("5"), \dv{SortInt{}}("5"))"#,
        );
        consequent.constraints.push(Predicate::Equals(
            Term::injection(
                Sort::simple("SortInt"),
                Sort::simple("SortKItem"),
                Term::variable(y.clone()),
            ),
            Term::injection(Sort::simple("SortInt"), Sort::simple("SortKItem"), value),
        ));
        let antecedent = Pattern {
            term: consequent.term.clone(),
            constraints: Vec::new(),
        };

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y]),
            &NoSolver,
        )
        .expect("implication should be checked");

        assert_eq!(result.status, ImplicationStatus::Valid, "{result:#?}");
        assert_single_witness(&result, "Y", &int(&definition, "5"));
        assert!(
            result
                .condition
                .as_ref()
                .expect("a valid implication carries its condition")
                .substitution
                .is_empty(),
            "obligation witnesses must not leak into the term-match substitution"
        );
    }

    #[test]
    fn witness_elimination_is_iterated() {
        let definition = definition();
        let antecedent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("5"), \dv{SortInt{}}("5"))"#,
        );
        let mut consequent = antecedent.clone();
        let y1 = crate::term::Variable::new("Y1", Sort::simple("SortInt"));
        let y2 = crate::term::Variable::new("Y2", Sort::simple("SortInt"));
        consequent.constraints = vec![
            Predicate::Equals(
                term(&definition, "f{}(Y1:SortInt{})"),
                term(&definition, "f{}(Y2:SortInt{})"),
            ),
            Predicate::Equals(Term::variable(y2.clone()), int(&definition, "5")),
        ];

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y1, y2]),
            &NoSolver,
        )
        .expect("implication should be checked");

        assert_eq!(result.status, ImplicationStatus::Valid, "{result:#?}");
        let witnesses = &result
            .condition
            .as_ref()
            .expect("a valid implication carries its condition")
            .witnesses;
        assert_eq!(witnesses.len(), 2);
        assert!(
            witnesses
                .keys()
                .all(|variable| variable.name.starts_with('Y'))
        );
        assert!(
            witnesses
                .values()
                .all(|value| value == &int(&definition, "5"))
        );
    }

    #[test]
    fn residual_equality_with_an_existential_is_discharged_by_matching() {
        let definition = definition();
        let antecedent = pattern(&definition, "succ{}(X:SortTree{})");
        let mut consequent = antecedent.clone();
        let y = crate::term::Variable::new("Y", Sort::simple("SortTree"));
        consequent.constraints.push(Predicate::Equals(
            term(&definition, "succ{}(Y:SortTree{})"),
            term(&definition, "succ{}(X:SortTree{})"),
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

        assert_eq!(result.status, ImplicationStatus::Valid, "{result:#?}");
        assert_single_witness(&result, "Y", &term(&definition, "X:SortTree{}"));
    }

    #[test]
    fn universal_variables_are_never_bound_as_witnesses() {
        let definition = definition();
        let antecedent = pattern(&definition, "X:SortInt{}");
        let mut consequent = antecedent.clone();
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        consequent.constraints.push(Predicate::Equals(
            Term::variable(x),
            Term::variable(y.clone()),
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

        assert_eq!(result.status, ImplicationStatus::Valid, "{result:#?}");
        assert_single_witness(&result, "Y", &term(&definition, "X:SortInt{}"));
        assert!(
            result
                .condition
                .as_ref()
                .expect("a valid implication carries its condition")
                .substitution
                .is_empty(),
            "the universal must not be captured by either substitution"
        );
    }

    #[test]
    fn disjunctive_implication_eliminates_branch_witnesses() {
        let definition = definition();
        let antecedent = pattern(&definition, "X:SortInt{}");
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        let mut witnessed = antecedent.clone();
        witnessed.constraints.push(Predicate::Equals(
            Term::variable(y.clone()),
            Term::variable(x),
        ));
        let alternative = pattern(&definition, r#"\dv{SortInt{}}("0")"#);

        let result = check_disjunctive_implication_with_existentials(
            &definition,
            &antecedent,
            &[witnessed, alternative],
            &BTreeSet::from([y]),
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("disjunctive implication should be checked");

        assert_eq!(result.status, ImplicationStatus::Valid, "{result:#?}");
        assert_single_witness(&result, "Y", &term(&definition, "X:SortInt{}"));
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
    fn vacuously_valid_results_carry_the_vacuous_flag() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"\dv{SortInt{}}("1")"#);
        let consequent = antecedent.clone();
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Unsat),
            validity: Ok(Validity::Invalid),
        };

        let result = check_implication(&definition, &antecedent, &consequent, &solver).unwrap();
        assert_eq!(result, vacuously_valid());
        assert!(result.vacuous);

        let ordinary = check_implication(&definition, &antecedent, &consequent, &NoSolver).unwrap();
        assert!(!ordinary.vacuous);
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

        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Invalid),
        };
        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &solver),
            Ok(condition_invalid())
        );
        assert_eq!(
            condition_invalid()
                .condition
                .expect("a refuted condition should be retained")
                .predicates,
            vec![Predicate::False]
        );
    }

    #[test]
    fn complete_check_uses_smt_counterexamples_without_hiding_solver_uncertainty() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"X:SortInt{}"#);
        let mut consequent = antecedent.clone();
        consequent.constraints.push(Predicate::Equals(
            Term::variable(crate::term::Variable::new("X", Sort::simple("SortInt"))),
            int(&definition, "1"),
        ));
        let counterexample = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Indeterminate),
        };

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &counterexample),
            Ok(indeterminate())
        );
        assert_eq!(
            check_implication_with_existentials_complete(
                &definition,
                &antecedent,
                &BTreeSet::new(),
                &consequent,
                &BTreeSet::new(),
                &counterexample,
            ),
            Ok(counterexample_invalid(Substitution::new()))
        );

        let unavailable = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Err(SmtError::Unavailable),
        };
        assert_eq!(
            check_implication_with_existentials_complete(
                &definition,
                &antecedent,
                &BTreeSet::new(),
                &consequent,
                &BTreeSet::new(),
                &unavailable,
            ),
            Ok(indeterminate())
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
