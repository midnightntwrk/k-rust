//! Search-target compilation, generated-variable mapping, and hidden-binding filtering (S12 and S27).

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt, io,
};

use k_rust_backend::{
    definition::BackendDefinition,
    externalize,
    rewrite::Pattern,
    rule::Predicate,
    search::{PatternMatch, PatternSearchResult, match_disjunction},
    substitution::Substitution,
    term::{Sort as BackendSort, Variable, VariableKind as BackendVariableKind},
};

use crate::{
    kompile::{CompiledSearchPattern, KoreVariableIdentity},
    kore::ast::{Pattern as KorePattern, Sort as KoreSort, VariableKind as KoreVariableKind},
};

use super::{Backend, BackendError};

#[derive(Debug)]
pub struct BackendMatchTarget {
    pub pattern: Pattern,
    pub generated_anonymous_variables: BTreeSet<Variable>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GeneratedIdentityMappingError {
    Missing {
        identity: KoreVariableIdentity,
    },
    Ambiguous {
        identity: KoreVariableIdentity,
        candidates: BTreeSet<Variable>,
    },
}

impl fmt::Display for GeneratedIdentityMappingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Missing { identity } => write!(
                formatter,
                "generated {:?} KORE variable {:?} is missing from the internalized match target",
                identity.kind, identity.name
            ),
            Self::Ambiguous {
                identity,
                candidates,
            } => write!(
                formatter,
                "generated {:?} KORE variable {:?} has multiple internalized sorts: {}",
                identity.kind,
                identity.name,
                candidates
                    .iter()
                    .map(|candidate| format!("{:?}", candidate.sort))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl Error for GeneratedIdentityMappingError {}

impl Backend {
    pub fn match_patterns(
        &mut self,
        module: Option<&str>,
        target: &Pattern,
        alternatives: &[Pattern],
    ) -> Result<Vec<PatternMatch>, BackendError> {
        self.with_solver(module, |definition, _| {
            match_disjunction(definition, target, alternatives).map_err(|error| {
                BackendError(format!("KORE pattern match was indeterminate: {error:?}"))
            })
        })
    }
}

pub fn kore_variable_identity(variable: &crate::kore::ast::Variable) -> KoreVariableIdentity {
    KoreVariableIdentity {
        kind: variable.kind,
        name: variable.name.clone(),
    }
}

pub fn collect_predicate_variables(predicate: &Predicate, variables: &mut BTreeSet<Variable>) {
    match predicate {
        Predicate::True | Predicate::False => {}
        Predicate::Term(term) | Predicate::Ceil(term) | Predicate::Floor(term) => {
            variables.extend(term.attributes().variables.iter().cloned());
        }
        Predicate::Equals(left, right) | Predicate::In(left, right) => {
            variables.extend(left.attributes().variables.iter().cloned());
            variables.extend(right.attributes().variables.iter().cloned());
        }
        Predicate::Not(inner) => collect_predicate_variables(inner, variables),
        Predicate::And(inner) | Predicate::Or(inner) => {
            for predicate in inner {
                collect_predicate_variables(predicate, variables);
            }
        }
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            collect_predicate_variables(left, variables);
            collect_predicate_variables(right, variables);
        }
        Predicate::Exists(variable, inner) | Predicate::Forall(variable, inner) => {
            variables.insert(variable.clone());
            collect_predicate_variables(inner, variables);
        }
    }
}

pub fn map_generated_anonymous_variables(
    target: &Pattern,
    identities: &BTreeSet<KoreVariableIdentity>,
) -> Result<BTreeSet<Variable>, GeneratedIdentityMappingError> {
    let mut variables = target.term.attributes().variables.clone();
    for constraint in &target.constraints {
        collect_predicate_variables(constraint, &mut variables);
    }
    let mut mapped = BTreeSet::new();
    for identity in identities {
        let kind = match identity.kind {
            KoreVariableKind::Element => BackendVariableKind::Element,
            KoreVariableKind::Set => BackendVariableKind::Set,
        };
        let candidates = variables
            .iter()
            .filter(|variable| variable.kind == kind && variable.name.as_ref() == identity.name)
            .cloned()
            .collect::<BTreeSet<_>>();
        match candidates.len() {
            0 => {
                return Err(GeneratedIdentityMappingError::Missing {
                    identity: identity.clone(),
                });
            }
            1 => {
                mapped.extend(candidates);
            }
            _ => {
                return Err(GeneratedIdentityMappingError::Ambiguous {
                    identity: identity.clone(),
                    candidates,
                });
            }
        }
    }
    Ok(mapped)
}

pub fn prepare_backend_match_target(
    backend: &BackendDefinition,
    compiled: CompiledSearchPattern,
) -> Result<BackendMatchTarget, Box<dyn Error>> {
    backend.verify_standalone_pattern(&compiled.pattern)?;
    let occurring = compiled
        .pattern
        .variables()
        .iter()
        .map(kore_variable_identity)
        .collect::<BTreeSet<_>>();
    if let Some(identity) = compiled
        .generated_anonymous_variables
        .iter()
        .find(|identity| !occurring.contains(*identity))
    {
        return Err(io::Error::other(format!(
            "generated {:?} KORE variable {:?} does not occur in the compiled match target",
            identity.kind, identity.name
        ))
        .into());
    }
    let pattern = backend.internalize_pattern(&compiled.pattern, &[])?;
    let generated_anonymous_variables =
        map_generated_anonymous_variables(&pattern, &compiled.generated_anonymous_variables)?;
    Ok(BackendMatchTarget {
        pattern,
        generated_anonymous_variables,
    })
}

pub fn search_output(
    result: &PatternSearchResult,
    result_sort: &KoreSort,
    generated_anonymous_variables: &BTreeSet<Variable>,
    function_symbols: &BTreeSet<String>,
) -> KorePattern {
    let solutions = result
        .matches
        .iter()
        .map(|found| {
            raw_match_condition_output(
                &found.substitution,
                &found.constraints,
                result_sort,
                &found.state.pattern.term.sort(),
            )
        })
        .collect::<Vec<_>>();
    filter_match_condition(
        externalize::disjunction(
            result_sort,
            solutions,
            externalize::ConjunctionShape::LeftNested,
        )
        .unwrap_or_else(|| KorePattern::Bottom {
            sort: result_sort.clone(),
        }),
        result_sort,
        generated_anonymous_variables,
        function_symbols,
    )
}

pub fn pattern_matches_output(
    matches: &[PatternMatch],
    result_sort: &KoreSort,
    predicate_sort: &BackendSort,
    generated_anonymous_variables: &BTreeSet<Variable>,
    function_symbols: &BTreeSet<String>,
) -> KorePattern {
    let solutions = matches
        .iter()
        .map(|found| {
            raw_match_condition_output(
                &found.substitution,
                &found.constraints,
                result_sort,
                predicate_sort,
            )
        })
        .collect::<Vec<_>>();
    filter_match_condition(
        externalize::disjunction(
            result_sort,
            solutions,
            externalize::ConjunctionShape::LeftNested,
        )
        .unwrap_or_else(|| KorePattern::Bottom {
            sort: result_sort.clone(),
        }),
        result_sort,
        generated_anonymous_variables,
        function_symbols,
    )
}

pub fn raw_match_condition_output(
    substitution: &Substitution,
    constraints: &[Predicate],
    result_sort: &KoreSort,
    predicate_sort: &BackendSort,
) -> KorePattern {
    let predicate_sort_kore = externalize::sort(predicate_sort);
    let mut predicates = externalize::substitution_pattern(
        substitution,
        predicate_sort,
        externalize::BindingOrder::NameThenSort,
        externalize::ConjunctionShape::LeftNested,
    )
    .map(|pattern| {
        pattern
            .conjuncts_at(&predicate_sort_kore)
            .into_iter()
            .cloned()
            .collect::<Vec<_>>()
    })
    .unwrap_or_default();
    predicates.extend(
        constraints
            .iter()
            .map(|predicate| externalize::predicate_pattern(predicate, predicate_sort)),
    );
    externalize::conjunction(
        result_sort,
        predicates,
        externalize::ConjunctionShape::LeftNested,
    )
    .unwrap_or_else(|| KorePattern::Top {
        sort: result_sort.clone(),
    })
}

pub fn generated_kore_identities(variables: &BTreeSet<Variable>) -> BTreeSet<KoreVariableIdentity> {
    variables
        .iter()
        .map(|variable| KoreVariableIdentity {
            kind: match variable.kind {
                BackendVariableKind::Element => KoreVariableKind::Element,
                BackendVariableKind::Set => KoreVariableKind::Set,
            },
            name: externalize::external_variable_name(&variable.name),
        })
        .collect()
}

pub fn is_filterable_generated_equality(
    pattern: &KorePattern,
    generated_anonymous_variables: &BTreeSet<KoreVariableIdentity>,
    function_symbols: &BTreeSet<String>,
    occurrences: &BTreeMap<KoreVariableIdentity, usize>,
) -> bool {
    let KorePattern::Equals { left, .. } = pattern else {
        return false;
    };
    let eligible_left = match left.as_ref() {
        KorePattern::Variable(_) => true,
        KorePattern::Application { symbol, .. } => function_symbols.contains(&symbol.name),
        _ => false,
    };
    if !eligible_left {
        return false;
    }
    let left_variables = left
        .variables()
        .iter()
        .map(kore_variable_identity)
        .collect::<BTreeSet<_>>();
    left_variables.iter().all(|identity| {
        generated_anonymous_variables.contains(identity) && occurrences.get(identity) == Some(&1)
    })
}

pub fn filter_match_condition(
    condition: KorePattern,
    result_sort: &KoreSort,
    generated_anonymous_variables: &BTreeSet<Variable>,
    function_symbols: &BTreeSet<String>,
) -> KorePattern {
    let disjuncts = condition
        .disjuncts_at(result_sort)
        .into_iter()
        .cloned()
        .collect::<Vec<_>>();
    let disjuncts = disjuncts
        .into_iter()
        .map(|condition| {
            filter_match_conjunction(
                condition,
                result_sort,
                generated_anonymous_variables,
                function_symbols,
            )
        })
        .collect();
    externalize::disjunction(
        result_sort,
        order_distinct_match_outputs(disjuncts),
        externalize::ConjunctionShape::LeftNested,
    )
    .unwrap_or_else(|| KorePattern::Bottom {
        sort: result_sort.clone(),
    })
}

pub fn filter_match_conjunction(
    condition: KorePattern,
    result_sort: &KoreSort,
    generated_anonymous_variables: &BTreeSet<Variable>,
    function_symbols: &BTreeSet<String>,
) -> KorePattern {
    let occurrences = condition
        .variable_occurrences()
        .into_iter()
        .map(|((kind, name), count)| (KoreVariableIdentity { kind, name }, count))
        .collect::<BTreeMap<_, _>>();
    let generated_anonymous_variables = generated_kore_identities(generated_anonymous_variables);
    let conjuncts = condition
        .conjuncts_at(result_sort)
        .into_iter()
        .cloned()
        .collect::<Vec<_>>();
    let conjuncts = conjuncts
        .into_iter()
        .filter(|pattern| {
            !is_filterable_generated_equality(
                pattern,
                &generated_anonymous_variables,
                function_symbols,
                &occurrences,
            )
        })
        .collect();
    externalize::conjunction(
        result_sort,
        conjuncts,
        externalize::ConjunctionShape::LeftNested,
    )
    .unwrap_or_else(|| KorePattern::Top {
        sort: result_sort.clone(),
    })
}

pub fn order_distinct_match_outputs(mut solutions: Vec<KorePattern>) -> Vec<KorePattern> {
    solutions.sort();
    solutions.dedup();
    solutions
}

/// Print disjuncts in the structural order of their externalized KORE, never in
/// traversal order. Kore's internal term ordering is intentionally not reproduced; gates compare
/// result multisets (docs/compatibility.md#search-results).
pub fn order_disjuncts(mut solutions: Vec<KorePattern>) -> Vec<KorePattern> {
    solutions.sort();
    solutions
}
