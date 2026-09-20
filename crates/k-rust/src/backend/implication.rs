//! Shared implication validation, checking, and condition results (S8 and S9).

use std::collections::BTreeSet;

use k_rust_backend::{
    definition::DefinitionError,
    implication::{
        ImplicationRequestError, ImplicationResult, Side,
        check_implication_with_existentials_complete, special_case, validate_request,
    },
    term::{Name, Sort},
};
use k_rust_kore::kore::ast::{Pattern as KorePattern, Pattern};

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
