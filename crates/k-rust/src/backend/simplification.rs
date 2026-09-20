//! Shared standalone simplification and model-generation orchestration (S4 and S5).

#[cfg(feature = "z3-inference")]
use k_rust_backend::smt::ModelResult;
use k_rust_backend::{
    definition::BackendDefinition,
    definition::PatternOrPredicate,
    externalize,
    simplify::{
        SimplificationError, SimplificationOptions, simplify_and_decide_predicate_with_solver,
        simplify_pattern_with_solver,
    },
    smt::SmtSolver,
    substitution::Substitution,
    term::Sort,
};
use k_rust_backend::{rewrite::Pattern, rule::Predicate};
use k_rust_kore::kore::ast::Pattern as KorePattern;

use super::{Backend, BackendError, error};

pub fn simplify_pattern(
    definition: &BackendDefinition,
    pattern: &Pattern,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Pattern, SimplificationError> {
    simplify_pattern_with_solver(definition, pattern, options, solver)
}

pub fn simplify_predicate(
    definition: &BackendDefinition,
    predicate: &Predicate,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Predicate, SimplificationError> {
    simplify_and_decide_predicate_with_solver(definition, predicate, &[], options, solver)
}

/// Externalize model bindings in the natural variable order shared by CLI and RPC surfaces.
pub fn model_substitution(substitution: &Substitution, result_sort: &Sort) -> Option<KorePattern> {
    externalize::substitution_pattern(
        substitution,
        result_sort,
        externalize::BindingOrder::Natural,
        externalize::ConjunctionShape::Flat,
    )
}

impl Backend {
    pub fn simplify_kore(
        &mut self,
        module: Option<&str>,
        syntax: &KorePattern,
    ) -> Result<KorePattern, BackendError> {
        self.with_solver(module, |definition, solver| {
            match definition
                .internalize_pattern_or_predicate(syntax, &[])
                .map_err(error("could not internalize KORE pattern"))?
            {
                PatternOrPredicate::Term(pattern) => {
                    let simplified = simplify_pattern_with_solver(
                        definition,
                        &pattern,
                        SimplificationOptions::unbounded(),
                        solver,
                    )
                    .map_err(error("could not simplify KORE pattern"))?;
                    Ok(externalize::constrained_pattern(&simplified))
                }
                PatternOrPredicate::Predicate(predicate, result_sort) => {
                    let simplified = simplify_and_decide_predicate_with_solver(
                        definition,
                        &predicate,
                        &[],
                        SimplificationOptions::unbounded(),
                        solver,
                    )
                    .map_err(error("could not simplify KORE predicate"))?;
                    Ok(externalize::ml_pattern(&simplified, &result_sort))
                }
            }
        })
    }

    #[cfg(feature = "z3-inference")]
    pub fn model_for(
        &mut self,
        module: Option<&str>,
        syntax: &KorePattern,
    ) -> Result<(ModelResult, Option<Sort>), BackendError> {
        self.with_solver(module, |definition, solver| {
            let Some((predicate, result_sort)) = definition
                .internalize_model_predicate(syntax, &[])
                .map_err(error("could not internalize model predicate"))?
            else {
                return Ok((ModelResult::Unknown("no predicate".into()), None));
            };
            let result = solver
                .get_model(&[predicate], &Substitution::new())
                .map_err(error("could not obtain model"))?;
            Ok((result, Some(result_sort)))
        })
    }
}
