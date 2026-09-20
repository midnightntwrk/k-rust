//! Shared implication validation, checking, and condition results (S8 and S9).

use std::{collections::BTreeSet, error::Error};

use k_rust_backend::{
    definition::DefinitionError,
    externalize,
    implication::{
        ImplicationCondition, ImplicationRequestError, ImplicationResult, ImplicationStatus, Side,
        check_implication_with_existentials_complete, special_case, validate_request,
    },
    substitution::Substitution,
    term::{Name, Sort, Term, TermKind},
};
use k_rust_kore::kore::{
    ast::{Pattern as KorePattern, Pattern},
    json as kore_json,
};

use super::{Backend, BackendError, error};

pub fn check(
    definition: &k_rust_backend::definition::BackendDefinition,
    antecedent: &k_rust_backend::rewrite::Pattern,
    antecedent_existentials: &BTreeSet<k_rust_backend::term::Variable>,
    consequent: &k_rust_backend::rewrite::Pattern,
    consequent_existentials: &BTreeSet<k_rust_backend::term::Variable>,
    solver: &dyn k_rust_backend::smt::SmtSolver,
) -> Result<ImplicationResult, k_rust_backend::implication::ImplicationError> {
    check_implication_with_existentials_complete(
        definition,
        antecedent,
        antecedent_existentials,
        consequent,
        consequent_existentials,
        solver,
    )
}

impl Backend {
    /// Validate, internalize, and check one implication through the selected module's cached solver.
    pub fn implies_kore(
        &mut self,
        module: Option<&str>,
        antecedent: &Pattern,
        consequent: &Pattern,
    ) -> Result<(ImplicationResult, Sort), BackendError> {
        self.with_solver(module, |definition, solver| {
            validate_request(definition, antecedent, consequent).map_err(|request_error| {
                BackendError(match request_error {
                    ImplicationRequestError::MacroOrAlias { side, name } => format!(
                        "invalid implication {}: {}",
                        match side {
                            Side::Antecedent => "antecedent",
                            Side::Consequent => "consequent",
                        },
                        DefinitionError::MacroOrAliasInImplication(name)
                    ),
                    ImplicationRequestError::NonFunctionLikeAntecedent => {
                        "implication antecedent must be function-like".into()
                    }
                    ImplicationRequestError::NonSingletonConsequent => {
                        "implication consequent must contain exactly one pattern".into()
                    }
                    ImplicationRequestError::ExistentialCapture { captured, .. } => format!(
                        "consequent existentials capture antecedent variables: {}",
                        captured.join(", ")
                    ),
                    ImplicationRequestError::SortMismatch {
                        antecedent,
                        consequent,
                    } => format!(
                        "antecedent and consequent sorts differ: {antecedent} and {consequent}"
                    ),
                })
            })?;
            let sort_variables = antecedent
                .sort_variables()
                .into_iter()
                .chain(consequent.sort_variables())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .map(Name::from)
                .collect::<Vec<_>>();
            let special_result = special_case(antecedent, consequent);
            let antecedent_pattern =
                if matches!(antecedent.strip_exists(), KorePattern::Bottom { .. }) {
                    None
                } else {
                    Some(
                        definition
                            .internalize_implication_pattern(antecedent, &sort_variables)
                            .map_err(error("could not internalize implication antecedent"))?,
                    )
                };
            let result_sort = match &antecedent_pattern {
                Some((pattern, _)) => pattern.term.sort(),
                None => {
                    definition
                        .internalize_predicate(antecedent, &sort_variables)
                        .map_err(error("could not internalize implication antecedent"))?
                        .1
                }
            };
            let result = if let Some(result) = special_result {
                result
            } else {
                let (antecedent_pattern, antecedent_existentials) =
                    antecedent_pattern.expect("only bottom bypasses implication internalization");
                let (consequent_pattern, consequent_existentials) = definition
                    .internalize_implication_pattern(consequent, &sort_variables)
                    .map_err(error("could not internalize implication consequent"))?;
                if antecedent_pattern.term.sort() != consequent_pattern.term.sort() {
                    return Err(BackendError(format!(
                        "antecedent and consequent sorts differ after internalization: {:?} and {:?}",
                        antecedent_pattern.term.sort(),
                        consequent_pattern.term.sort()
                    )));
                }
                check_implication_with_existentials_complete(
                    definition,
                    &antecedent_pattern,
                    &antecedent_existentials,
                    &consequent_pattern,
                    &consequent_existentials,
                    solver,
                )
                .map_err(error("could not check implication"))?
            };
            Ok((result, result_sort))
        })
    }
}

/// Render the CLI implication contract while the surface retains only file and stdout handling.
pub fn cli_output(
    antecedent: &KorePattern,
    consequent: &KorePattern,
    result_sort: &Sort,
    result: ImplicationResult,
) -> Result<String, Box<dyn Error>> {
    let status = match result.status {
        ImplicationStatus::Valid => "valid",
        ImplicationStatus::Invalid => "invalid",
        ImplicationStatus::Indeterminate => "unknown",
    };
    let implication = KorePattern::Implies {
        sort: externalize::sort(result_sort),
        left: Box::new(antecedent.clone()),
        right: Box::new(consequent.clone()),
    };
    let mut output = serde_json::json!({
        "status": status,
        "implication": kore_json::to_value(&implication)?,
    });
    if let Some(condition) = result.condition {
        let antecedent_variable = match antecedent.strip_exists() {
            KorePattern::Variable(variable) => Some(variable.name.as_str()),
            _ => None,
        };
        output["condition"] = cli_condition_output(&condition, result_sort, antecedent_variable)?;
    }
    Ok(serde_json::to_string_pretty(&output)?)
}

pub fn cli_condition_output(
    condition: &ImplicationCondition,
    result_sort: &Sort,
    antecedent_variable: Option<&str>,
) -> Result<serde_json::Value, Box<dyn Error>> {
    let substitution =
        condition_substitution(&condition.substitution, result_sort, antecedent_variable)
            .unwrap_or_else(|| KorePattern::Top {
                sort: externalize::sort(result_sort),
            });
    let predicate = externalize::predicates_pattern(
        &condition.predicates,
        result_sort,
        |predicate| externalize::predicate_pattern(predicate, result_sort),
        externalize::ConjunctionShape::Flat,
    )
    .unwrap_or_else(|| KorePattern::Top {
        sort: externalize::sort(result_sort),
    });
    let witnesses = condition_substitution(&condition.witnesses, result_sort, antecedent_variable)
        .unwrap_or_else(|| KorePattern::Top {
            sort: externalize::sort(result_sort),
        });
    Ok(serde_json::json!({
        "substitution": kore_json::to_value(&substitution)?,
        "predicate": kore_json::to_value(&predicate)?,
        "witnesses": kore_json::to_value(&witnesses)?,
    }))
}

pub fn condition_substitution(
    substitution: &Substitution,
    result_sort: &Sort,
    antecedent_variable: Option<&str>,
) -> Option<KorePattern> {
    let mut bindings = substitution.iter().collect::<Vec<_>>();
    bindings.sort_by_key(|(variable, _)| (variable.name.clone(), variable.sort.clone()));
    let bindings = bindings.into_iter().map(|(variable, value)| {
        let mut output_variable = variable.clone();
        let consequent_existential = variable
            .name
            .as_ref()
            .rsplit_once("!exists")
            .filter(|(_, suffix)| suffix.chars().all(|character| character.is_ascii_digit()));
        if let Some((name, _)) = consequent_existential {
            output_variable.name = Name::from(name);
        }
        let prefer_antecedent = consequent_existential.is_some()
            && matches!(
                value.kind(),
                TermKind::Variable(value) if antecedent_variable == Some(value.name.as_ref())
            );
        let (left, right) = if prefer_antecedent {
            (
                externalize::term(value),
                externalize::term(&Term::variable(output_variable)),
            )
        } else {
            (
                externalize::term(&Term::variable(output_variable)),
                externalize::term(value),
            )
        };
        KorePattern::Equals {
            operand_sort: externalize::sort(&variable.sort),
            result_sort: externalize::sort(result_sort),
            left: Box::new(left),
            right: Box::new(right),
        }
    });
    externalize::conjunction(
        &externalize::sort(result_sort),
        bindings.collect(),
        externalize::ConjunctionShape::LeftNested,
    )
}
