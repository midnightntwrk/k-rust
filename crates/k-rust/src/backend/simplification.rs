//! Shared standalone simplification and model-generation orchestration.

#[cfg(feature = "z3-inference")]
use k_rust_backend::smt::ModelResult;
use k_rust_backend::{
    definition::BackendDefinition,
    definition::{Admission, PatternOrPredicate},
    externalize,
    simplify::{
        SimplificationError, SimplificationOptions, simplify_and_decide_predicate_with_solver,
        simplify_pattern_with_solver,
    },
    smt::SmtSolver,
    stop::{Stop, Stoppable},
    substitution::Substitution,
    term::Sort,
};
use k_rust_backend::{rewrite::Pattern, rule::Predicate};
use k_rust_kore::kore::ast::Pattern as KorePattern;

use super::{Backend, BackendError, admit, error};

/// The error of an operation whose work stopped: the error `BackendError` gives the stop's
/// cause, the one the operation boundary gives it too (`Backend::with_solver`), so an operation
/// reports a stop the same way wherever it was observed.
pub(crate) fn stopped_operation(stop: Stop) -> BackendError {
    BackendError::from(stop.into_cause())
}

/// Simplify `pattern`. As the simplifier's, the result has two layers: the outer `Err` is a
/// [`Stop`], for which no simplified form exists; the inner result is the simplified pattern or
/// the simplification's failure.
pub fn simplify_pattern(
    definition: &BackendDefinition,
    pattern: &Pattern,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Pattern, SimplificationError>> {
    simplify_pattern_with_solver(definition, pattern, options, solver)
}

/// Simplify and decide `predicate`, with the two layers of [`simplify_pattern`].
pub fn simplify_predicate(
    definition: &BackendDefinition,
    predicate: &Predicate,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Predicate, SimplificationError>> {
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
    .map_err(stopped_operation)?
    .map_err(error("could not simplify model predicate"))?;
    match simplified {
        Predicate::False => Ok(ModelResult::Unsat),
        Predicate::True => Ok(ModelResult::Sat(Substitution::new())),
        // A stopped query has no model.
        residual => solver
            .get_model(&[residual], &Substitution::new())
            .map_err(stopped_operation)?
            .map_err(error("could not obtain model")),
    }
}

impl Backend {
    /// Simplify `syntax`, a pattern without sort variables, admitted as `admission` decides.
    pub fn simplify_kore(
        &mut self,
        module: Option<&str>,
        syntax: &KorePattern,
        admission: Admission,
    ) -> Result<KorePattern, BackendError> {
        self.with_solver(module, |definition, solver| {
            match admit(definition, syntax, &[], admission, "KORE pattern")?
                .internalize_pattern_or_predicate()
                .map_err(error("could not internalize KORE pattern"))?
            {
                PatternOrPredicate::Term(pattern) => {
                    let simplified = simplify_pattern_with_solver(
                        definition,
                        &pattern,
                        SimplificationOptions::unbounded(),
                        solver,
                    )
                    .map_err(stopped_operation)?
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
                    .map_err(stopped_operation)?
                    .map_err(error("could not simplify KORE predicate"))?;
                    Ok(externalize::ml_pattern(&simplified, &result_sort))
                }
            }
        })
    }

    /// Ask for a model of `syntax`, a predicate without sort variables, admitted as `admission`
    /// decides.
    #[cfg(feature = "z3-inference")]
    pub fn model_for(
        &mut self,
        module: Option<&str>,
        syntax: &KorePattern,
        admission: Admission,
    ) -> Result<(ModelResult, Option<Sort>), BackendError> {
        self.with_solver(module, |definition, solver| {
            let Some((predicate, result_sort)) =
                admit(definition, syntax, &[], admission, "model predicate")?
                    .internalize_model_predicate()
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
                Admission::Verified,
            )
            .expect("model query should succeed")
            .0
    }

    /// One variable name at two sorts: two occurrences of one ill-formed variable, which an
    /// internalizer keying variables by name and sort would read as two variables.
    const ONE_NAME_TWO_SORTS: &str = r#"\and{SortBool{}}(
        \equals{SortInt{}, SortBool{}}(X:SortInt{}, \dv{SortInt{}}("1")),
        \equals{SortBool{}, SortBool{}}(X:SortBool{}, \dv{SortBool{}}("true")))"#;

    #[test]
    fn a_verified_admission_rejects_a_variable_at_two_sorts() {
        let mut backend = Backend::new(MODEL_DEFINITION, "MAIN", BackendOptions::default())
            .expect("model definition should internalize");
        let syntax = parse_pattern(ONE_NAME_TWO_SORTS).expect("predicate should parse");
        let model = backend
            .model_for(None, &syntax, Admission::Verified)
            .expect_err("a verified model predicate has one sort per variable");
        assert!(
            model.0.starts_with("invalid model predicate: ")
                && model.0.contains("Inconsistent free variable usage"),
            "{model}"
        );
        let simplified = backend
            .simplify_kore(None, &syntax, Admission::Verified)
            .expect_err("a verified pattern has one sort per variable");
        assert!(
            simplified.0.starts_with("invalid KORE pattern: ")
                && simplified.0.contains("Inconsistent free variable usage"),
            "{simplified}"
        );
        assert!(
            backend
                .model_for(None, &syntax, Admission::Unverified)
                .is_ok()
        );
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
