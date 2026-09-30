//! Shared implication validation, checking, and condition results.

#![deny(clippy::wildcard_enum_match_arm)]

use std::{collections::BTreeSet, error::Error};

use k_rust_backend::{
    definition::DefinitionError,
    externalize,
    implication::{
        Bindings, ImplicationCondition, ImplicationError, ImplicationRequestError,
        ImplicationStatus, ImplicationVerdict, Side, SpecialConsequent, bottom_antecedent,
        check_implication_with_existentials_complete, check_negated_consequent,
        grade_bottom_consequent, special_consequent, validate_request,
    },
    simplify::SimplificationError,
    stop::Stop,
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
) -> Result<ImplicationVerdict, k_rust_backend::implication::ImplicationError> {
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
    ) -> Result<(ImplicationVerdict, Sort), BackendError> {
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
            if let Some(verdict) = bottom_antecedent(antecedent) {
                let (_, result_sort) = definition
                    .internalize_predicate(antecedent, &sort_variables)
                    .map_err(error("could not internalize implication antecedent"))?;
                return Ok((verdict, result_sort));
            }
            let (antecedent_pattern, antecedent_existentials) = definition
                .internalize_implication_pattern(antecedent, &sort_variables)
                .map_err(error("could not internalize implication antecedent"))?;
            let result_sort = antecedent_pattern.term.sort();
            let verdict = match special_consequent(consequent) {
                Some(SpecialConsequent::Top) => ImplicationVerdict::Valid(Bindings::default()),
                Some(SpecialConsequent::Bottom) => {
                    grade_bottom_consequent(definition, &antecedent_pattern, solver)
                        .map_err(stopped_check)
                        .map_err(error("could not check implication"))?
                }
                Some(SpecialConsequent::Not) => check_negated_consequent(
                    definition,
                    &antecedent_pattern,
                    &antecedent_existentials,
                    consequent,
                    &sort_variables,
                    solver,
                )
                .map_err(stopped_check)
                .map_err(error("could not check implication"))?
                .map_err(error("could not internalize implication consequent"))?,
                None => {
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
                }
            };
            Ok((verdict, result_sort))
        })
    }
}

/// A stop of a check of a special consequent, spelled as the complete check spells a stop in its
/// error, so that every check reports a stop with one text (until CBC-04-T9 types it).
fn stopped_check(stop: Stop) -> ImplicationError {
    ImplicationError::Simplification(SimplificationError::Stopped(stop.into_cause()))
}

/// Render the CLI implication contract while the surface retains only file and stdout handling.
pub fn cli_output(
    antecedent: &KorePattern,
    consequent: &KorePattern,
    result_sort: &Sort,
    verdict: ImplicationVerdict,
) -> Result<String, Box<dyn Error>> {
    let status = match verdict.status() {
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
    if let Some(condition) = verdict.into_condition() {
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "KorePattern is syntax; only the listed variants are special here"
        )]
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
            operand_sort: Box::new(externalize::sort(&variable.sort)),
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
