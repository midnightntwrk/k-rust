//! Shared implication validation, checking, and condition results.

#![deny(clippy::wildcard_enum_match_arm)]

use std::{collections::BTreeSet, error::Error};

use k_rust_backend::{
    definition::{Admission, DefinitionError},
    externalize,
    implication::{
        Bindings, ImplicationCondition, ImplicationError, ImplicationRequestError,
        ImplicationStatus, ImplicationVerdict, Side, SpecialConsequent, bottom_antecedent,
        check_implication_with_existentials_complete, check_negated_consequent,
        grade_bottom_consequent, special_consequent, validate_request,
    },
    stop::Stoppable,
    substitution::Substitution,
    term::{Name, Sort, Term, TermKind},
};
use k_rust_kore::kore::{
    ast::{Pattern as KorePattern, Pattern},
    json as kore_json,
};

use super::{Backend, BackendError, admit, error, simplification::stopped_operation};

pub fn check(
    definition: &k_rust_backend::definition::BackendDefinition,
    antecedent: &k_rust_backend::rewrite::Pattern,
    antecedent_existentials: &BTreeSet<k_rust_backend::term::Variable>,
    consequent: &k_rust_backend::rewrite::Pattern,
    consequent_existentials: &BTreeSet<k_rust_backend::term::Variable>,
    solver: &dyn k_rust_backend::smt::SmtSolver,
) -> Stoppable<Result<ImplicationVerdict, ImplicationError>> {
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
    ///
    /// The sort variables of the two patterns are parameters of the implication, so each side is
    /// admitted, as `admission` decides, under the sort variables of both: the context it is
    /// internalized with.
    pub fn implies_kore(
        &mut self,
        module: Option<&str>,
        antecedent: &Pattern,
        consequent: &Pattern,
        admission: Admission,
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
            let antecedent_admitted = admit(
                definition,
                antecedent,
                &sort_variables,
                admission,
                "implication antecedent",
            )?;
            let consequent_admitted = admit(
                definition,
                consequent,
                &sort_variables,
                admission,
                "implication consequent",
            )?;
            if let Some(verdict) = bottom_antecedent(antecedent) {
                let (_, result_sort) = antecedent_admitted
                    .internalize_predicate()
                    .map_err(error("could not internalize implication antecedent"))?;
                return Ok((verdict, result_sort));
            }
            let (antecedent_pattern, antecedent_existentials) = antecedent_admitted
                .internalize_implication_pattern()
                .map_err(error("could not internalize implication antecedent"))?;
            let result_sort = antecedent_pattern.term.sort();
            let verdict = match special_consequent(consequent) {
                Some(SpecialConsequent::Top) => ImplicationVerdict::Valid(Bindings::default()),
                Some(SpecialConsequent::Bottom) => {
                    grade_bottom_consequent(definition, &antecedent_pattern, solver)
                        .map_err(stopped_operation)?
                }
                Some(SpecialConsequent::Not) => check_negated_consequent(
                    definition,
                    &antecedent_pattern,
                    &antecedent_existentials,
                    consequent_admitted,
                    solver,
                )
                .map_err(stopped_operation)?
                .map_err(error("could not internalize implication consequent"))?,
                None => {
                    let (consequent_pattern, consequent_existentials) = consequent_admitted
                        .internalize_implication_pattern()
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
                    .map_err(stopped_operation)?
                    .map_err(error("could not check implication"))?
                }
            };
            Ok((verdict, result_sort))
        })
    }
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

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::parse_pattern;

    use super::*;
    use crate::backend::BackendOptions;

    const DEFINITION: &str = r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
        endmodule []"#;

    fn implies(
        antecedent: &str,
        consequent: &str,
        admission: Admission,
    ) -> Result<(ImplicationVerdict, Sort), BackendError> {
        let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::default())
            .expect("implication definition should internalize");
        backend.implies_kore(
            None,
            &parse_pattern(antecedent).expect("antecedent should parse"),
            &parse_pattern(consequent).expect("consequent should parse"),
            admission,
        )
    }

    #[test]
    fn a_verified_schematic_implication_reads_its_sort_variables_as_parameters() {
        let (verdict, _) = implies(r"\bottom{S}()", r"\top{S}()", Admission::Verified)
            .expect("a schematic implication is well formed under its own sort variables");
        assert_eq!(verdict.status(), ImplicationStatus::Valid);
    }

    #[test]
    fn a_verified_consequent_has_one_sort_per_variable() {
        let consequent = r#"\and{S}(
            \equals{SortInt{}, S}(X:SortInt{}, \dv{SortInt{}}("1")),
            \equals{SortBool{}, S}(X:SortBool{}, \dv{SortBool{}}("true")))"#;
        let error = implies(r"\bottom{S}()", consequent, Admission::Verified)
            .expect_err("one variable name at two sorts is not a well-formed consequent");
        assert!(
            error.0.starts_with("invalid implication consequent: ")
                && error.0.contains("Inconsistent free variable usage"),
            "{error}"
        );
        assert!(implies(r"\bottom{S}()", consequent, Admission::Unverified).is_ok());
    }
}
