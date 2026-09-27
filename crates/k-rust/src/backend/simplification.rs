//! Shared standalone simplification and model-generation orchestration.

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

/// Decide a model predicate before asking SMT for a valuation of its residual.
/// A predicate simplified to truth needs no bindings: every valuation satisfies it. Keep the complete residual,
/// including any open `\ceil` obligations introduced by simplification, in the SMT query.
#[cfg(feature = "z3-inference")]
pub fn model_predicate_with_solver(
    definition: &BackendDefinition,
    predicate: &Predicate,
    solver: &dyn SmtSolver,
) -> Result<ModelResult, BackendError> {
    let simplified = simplify_and_decide_predicate_with_solver(
        definition,
        predicate,
        &[],
        SimplificationOptions::unbounded(),
        solver,
    )
    .map_err(error("could not simplify model predicate"))?;
    match simplified {
        Predicate::False => Ok(ModelResult::Unsat),
        Predicate::True => Ok(ModelResult::Sat(Substitution::new())),
        residual => solver
            .get_model(&[residual], &Substitution::new())
            .map_err(error("could not obtain model")),
    }
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
            let result = model_predicate_with_solver(definition, &predicate, solver)?;
            Ok((result, Some(result_sort)))
        })
    }
}

#[cfg(all(test, feature = "z3-inference"))]
mod tests {
    use k_rust_kore::kore::parser::parse_pattern;

    use super::*;
    use crate::backend::BackendOptions;

    const MODEL_DEFINITION: &str = r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            sort SortState{} []
            symbol start{}() : SortState{} [constructor{}()]
            symbol done{}() : SortState{} [constructor{}()]
            symbol bitwise{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), smtlib{}("bitwise")]
            symbol partial{}(SortInt{}) : SortInt{} [function{}()]
        endmodule []"#;

    fn model(source: &str) -> ModelResult {
        let mut backend = Backend::new(MODEL_DEFINITION, "MAIN", BackendOptions::default())
            .expect("model definition should internalize");
        backend
            .model_for(
                None,
                &parse_pattern(source).expect("model predicate should parse"),
            )
            .expect("model query should succeed")
            .0
    }

    #[test]
    fn reflexive_configuration_has_an_empty_sat_model() {
        assert_eq!(
            model(r"\equals{SortState{}, SortBool{}}(start{}(), start{}())"),
            ModelResult::Sat(Substitution::new())
        );
    }

    #[test]
    fn distinct_constructor_configurations_have_no_model() {
        assert_eq!(
            model(r"\equals{SortState{}, SortBool{}}(start{}(), done{}())"),
            ModelResult::Unsat
        );
    }

    #[test]
    fn uninterpreted_residual_has_no_certified_model() {
        assert!(matches!(
            model(
                r#"\equals{SortInt{}, SortBool{}}(
                    bitwise{}(X:SortInt{}, \dv{SortInt{}}("1")),
                    \dv{SortInt{}}("2"))"#
            ),
            ModelResult::Unknown(_)
        ));
    }

    #[test]
    fn an_open_definedness_obligation_remains_in_the_model_query() {
        assert!(matches!(
            model(
                r"\and{SortBool{}}(
                    \equals{SortState{}, SortBool{}}(start{}(), start{}()),
                    \ceil{SortInt{}, SortBool{}}(partial{}(X:SortInt{})))"
            ),
            ModelResult::Unknown(_)
        ));
    }
}
