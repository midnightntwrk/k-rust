//! Shared standalone simplification and model-generation orchestration (S4 and S5).

use k_rust_backend::{
    definition::PatternOrPredicate,
    externalize,
    simplify::{
        SimplificationOptions, simplify_and_decide_predicate_with_solver,
        simplify_pattern_with_solver,
    },
    smt::ModelResult,
    substitution::Substitution,
    term::Sort,
};
use k_rust_kore::kore::ast::Pattern as KorePattern;

use super::{Backend, BackendError, error};

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
