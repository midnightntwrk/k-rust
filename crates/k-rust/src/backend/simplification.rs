//! Shared standalone simplification and model-generation orchestration.

use k_rust_backend::evaluation::{EvaluationMode, EvaluationScope, with_evaluation};
use k_rust_backend::{
    definition::BackendDefinition,
    definition::{Admission, PatternOrPredicate},
    externalize,
    model::ModelError,
    simplify::{
        SimplificationError, SimplificationOptions, simplify_and_decide_predicate_with_solver,
        simplify_pattern_with_solver,
    },
    smt::SmtSolver,
    stop::{Stop, Stoppable},
    substitution::Substitution,
    term::Sort,
};
#[cfg(feature = "z3-inference")]
use k_rust_backend::{model::model_of, smt::ModelResult};
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
    // A proof route: it evaluates only consequences of the definition, whatever scope the
    // caller runs it in (`k_rust_backend::evaluation`).
    with_evaluation(EvaluationMode::Proof, || {
        simplify_pattern_with_solver(definition, pattern, options, solver)
    })
}

/// Simplify and decide `predicate`, with the two layers of [`simplify_pattern`].
pub fn simplify_predicate(
    definition: &BackendDefinition,
    predicate: &Predicate,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Predicate, SimplificationError>> {
    // A proof route: it evaluates only consequences of the definition, whatever scope the
    // caller runs it in (`k_rust_backend::evaluation`).
    with_evaluation(EvaluationMode::Proof, || {
        simplify_and_decide_predicate_with_solver(definition, predicate, &[], options, solver)
    })
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

/// A model query's failure as the `BackendError` CLI and host surfaces report: the simplifier's
/// and the solver's failures each under their own context.
impl From<ModelError> for BackendError {
    #[deny(clippy::wildcard_enum_match_arm)]
    fn from(failure: ModelError) -> Self {
        match failure {
            ModelError::Simplification(cause) => error("could not simplify model predicate")(cause),
            ModelError::Solver(cause) => error("could not obtain model")(cause),
        }
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
        self.simplify_kore_with(module, syntax, admission, Ok)
    }

    /// [`Self::simplify_kore`], with `finish` turning the simplified pattern into the
    /// operation's result inside the operation, on the stack that the backend provides for
    /// `syntax` (`Backend::with_solver_over`).
    pub fn simplify_kore_with<T>(
        &mut self,
        module: Option<&str>,
        syntax: &KorePattern,
        admission: Admission,
        finish: impl FnOnce(KorePattern) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        // A proof route (`k_rust_backend::evaluation`).
        let _proof = EvaluationScope::enter(EvaluationMode::Proof);
        self.with_solver_over(module, &[syntax], |definition, solver| {
            let simplified = match admit(definition, syntax, &[], admission, "KORE pattern")?
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
                    externalize::constrained_pattern(&simplified)
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
                    externalize::ml_pattern(&simplified, &result_sort)
                }
            };
            // A cancellation a refinement observed and set aside is still the operation's
            // answer: poll once after the work returns.
            k_rust_backend::stop::check().map_err(stopped_operation)?;
            finish(simplified)
        })
    }

    /// Ask for a model of `syntax`, a predicate without sort variables, admitted as `admission`
    /// decides.
    ///
    /// The model and the sort hold internal terms and sorts built from `syntax`, which the
    /// caller drops on its own stack; [`Self::model_for_with`] reads them inside the operation.
    #[cfg(feature = "z3-inference")]
    pub fn model_for(
        &mut self,
        module: Option<&str>,
        syntax: &KorePattern,
        admission: Admission,
    ) -> Result<(ModelResult, Option<Sort>), BackendError> {
        self.model_for_with(module, syntax, admission, |model, sort| Ok((model, sort)))
    }

    /// [`Self::model_for`], with `finish` turning the model and the predicate's sort into the
    /// operation's result inside the operation, on the stack that the backend provides for
    /// `syntax` (`Backend::with_solver_over`), where they are also dropped.
    #[cfg(feature = "z3-inference")]
    pub fn model_for_with<T>(
        &mut self,
        module: Option<&str>,
        syntax: &KorePattern,
        admission: Admission,
        finish: impl FnOnce(ModelResult, Option<Sort>) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        // A proof route (`k_rust_backend::evaluation`).
        let _proof = EvaluationScope::enter(EvaluationMode::Proof);
        self.with_solver_over(module, &[syntax], |definition, solver| {
            let Some((predicate, result_sort)) =
                admit(definition, syntax, &[], admission, "model predicate")?
                    .internalize_model_predicate()
                    .map_err(error("could not internalize model predicate"))?
            else {
                return finish(ModelResult::Unknown("no predicate".into()), None);
            };
            let result = model_of(definition, &predicate, solver)
                .map_err(stopped_operation)?
                .map_err(BackendError::from)?;
            // As in `simplify_kore_with`: a cancellation set aside during the work is the answer.
            k_rust_backend::stop::check().map_err(stopped_operation)?;
            finish(result, Some(result_sort))
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
            model.message().starts_with("invalid model predicate: ")
                && model.message().contains("Inconsistent free variable usage"),
            "{model}"
        );
        let simplified = backend
            .simplify_kore(None, &syntax, Admission::Verified)
            .expect_err("a verified pattern has one sort per variable");
        assert!(
            simplified.message().starts_with("invalid KORE pattern: ")
                && simplified
                    .message()
                    .contains("Inconsistent free variable usage"),
            "{simplified}"
        );
        assert!(
            backend
                .model_for(None, &syntax, Admission::Unverified)
                .is_ok()
        );
    }

    #[test]
    fn a_model_failure_reports_the_failing_stage_and_its_cause() {
        assert_eq!(
            BackendError::from(ModelError::Simplification(
                SimplificationError::DisjunctiveResult {
                    rule_id: "rule".into(),
                    alternatives: 2,
                }
            ))
            .message(),
            "could not simplify model predicate: equation rule gives 2 alternative results where \
             simplification needs one"
        );
        assert_eq!(
            BackendError::from(ModelError::Solver(
                k_rust_backend::smt::SmtError::Unavailable
            ))
            .message(),
            "could not obtain model: no solver is available"
        );
    }
}
