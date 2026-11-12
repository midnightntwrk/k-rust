//! Shared standalone simplification and model-generation orchestration.

use std::sync::Arc;

use k_rust_backend::evaluation::{EvaluationMode, EvaluationScope, with_evaluation};
use k_rust_backend::{
    definition::BackendDefinition,
    definition::{Admission, PatternOrPredicate},
    externalize::{self, HeldState},
    model::ModelError,
    simplify::{
        SimplificationError, SimplificationOptions, simplify_and_decide_predicate_with_solver,
        simplify_pattern_with_solver,
    },
    smt::SmtSolver,
    stop::{Stop, Stoppable},
    substitution::Substitution,
    term::{Sort, Symbol, SymbolType},
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

/// The symbol `symbol` of `definition`, where it is a function [`Backend::apply_to_held`]
/// applies to `state`: declared, a function, without sort variables, of one argument whose sort
/// is the state's.
fn function_of_state(
    definition: &BackendDefinition,
    symbol: &str,
    state: &HeldState,
) -> Result<Arc<Symbol>, BackendError> {
    let refused =
        |why: String| BackendError::new(format!("could not apply {symbol} to a held state: {why}"));
    let Some(function) = definition.symbols().get(symbol) else {
        return Err(refused("the symbol is not declared".to_owned()));
    };
    if !matches!(function.attributes.symbol_type, SymbolType::Function(_)) {
        return Err(refused("the symbol is not a function".to_owned()));
    }
    if !function.sort_variables.is_empty() {
        return Err(refused(format!(
            "the symbol has {} sort variables, and a state gives it no sort argument",
            function.sort_variables.len()
        )));
    }
    let [argument] = function.argument_sorts.as_slice() else {
        return Err(refused(format!(
            "the symbol takes {} arguments, not one",
            function.argument_sorts.len()
        )));
    };
    let sort = state.sort();
    if *argument != sort {
        return Err(refused(format!(
            "the symbol's argument is of sort {}, and the state of sort {}",
            externalize::sort(argument),
            externalize::sort(&sort)
        )));
    }
    Ok(Arc::clone(function))
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
    /// `syntax` with its builtin collections associated (`Backend::with_solver_over`,
    /// `BackendDefinition::associated_collections`), which is the form the operation reads;
    /// `syntax` itself is not changed.
    pub fn simplify_kore_with<T>(
        &mut self,
        module: Option<&str>,
        syntax: &KorePattern,
        admission: Admission,
        finish: impl FnOnce(KorePattern) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        // A proof route (`k_rust_backend::evaluation`), the definition's first load included.
        let _proof = EvaluationScope::enter(EvaluationMode::Proof);
        let definition = self.definition_of(module)?;
        let associated = definition.associated_collections(syntax);
        self.simplify_associated(definition, &associated, admission, finish)
    }

    /// [`Self::simplify_kore_with`] in `definition`, of `syntax` with its builtin collections
    /// associated, inside the caller's proof scope.
    pub(crate) fn simplify_associated<T>(
        &mut self,
        definition: Arc<BackendDefinition>,
        syntax: &KorePattern,
        admission: Admission,
        finish: impl FnOnce(KorePattern) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        self.with_solver_on(definition, &[syntax], |definition, solver| {
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
                    // Each Boolean term is printed as the predicate it stands for, `true = t`,
                    // so the response states its meaning and reads back as the same predicate.
                    externalize::predicate_pattern(&simplified, &result_sort)
                }
            };
            // A cancellation a refinement observed and set aside is still the operation's
            // answer: poll once after the work returns.
            k_rust_backend::stop::check().map_err(stopped_operation)?;
            finish(simplified)
        })
    }

    /// Apply the function `symbol` to `state`, a state an execution of `module` held, and
    /// simplify the application: the result is the one [`Self::simplify_kore`] gives for the
    /// pattern `symbol{}(state.kore())`, where it admits that pattern.
    ///
    /// For a state that is a value ([`HeldState::is_value`]) the state's pattern is not built:
    /// the application is built over the state's own term, which it shares, and only the
    /// simplified result is written as a pattern. That is the same result because the term
    /// [`Self::simplify_kore`] simplifies is this one, node for node:
    ///
    /// - it internalizes the application's argument, the state's pattern, to a term equal to
    ///   the state's (the pattern of a term reads back as an equal term,
    ///   `k_rust_backend::externalize::term`), and builds the application from it by the call
    ///   [`HeldState::under`] makes;
    /// - a term equal to a value has the value's attributes at every node
    ///   ([`HeldState::is_value`]), the simplifier's marks among them, so the simplifier, which
    ///   reads a term's kinds and attributes, takes the same steps on both;
    /// - both run as a proof route, with the same options, and on a stack sized for the same
    ///   depth: the state's height is measured on its term
    ///   (`BackendDefinition::operation_depth_under`) and is the height of its pattern with
    ///   its collections associated, so a collection's length adds no level to it.
    ///
    /// A state that is not a value is built and simplified as [`Self::simplify_kore`] does it.
    /// Its term may hold a function application the execution marked as one no equation
    /// matches, and an execution decides some matches a proof route leaves undecided (a
    /// pattern over `LIST.update`, an equation holding a literal whose element the definition
    /// leaves open), so the mark is not one the simplification of the pattern would set, and a
    /// simplification that read it could differ from it. Nor is a variable's pattern read
    /// back unconditionally (a set variable is refused).
    ///
    /// `admission` decides how the pattern of a state that is not a value is admitted. A value
    /// is the backend's own term of a state it reached, and is not verified again: the entry
    /// checks the application itself, which is all of the pattern the caller wrote.
    ///
    /// # Errors
    ///
    /// Fails, before anything is built or simplified, unless `symbol` is declared in `module`
    /// as a function without sort variables of one argument whose sort is the state's; and
    /// as [`Self::simplify_kore`] fails.
    pub fn apply_to_held(
        &mut self,
        module: Option<&str>,
        symbol: &str,
        state: &HeldState,
        admission: Admission,
    ) -> Result<KorePattern, BackendError> {
        // A proof route (`k_rust_backend::evaluation`), the definition's first load included.
        let _proof = EvaluationScope::enter(EvaluationMode::Proof);
        let definition = self.definition_of(module)?;
        let function = function_of_state(&definition, symbol, state)?;
        if !state.is_value() {
            let application = KorePattern::Application {
                symbol: k_rust_kore::kore::ast::Symbol {
                    name: symbol.to_owned(),
                    sort_parameters: Vec::new(),
                },
                arguments: vec![state.kore()],
            };
            let associated = definition.associated_collections(&application);
            return self.simplify_associated(definition, &associated, admission, Ok);
        }
        let depth = definition.operation_depth_under(state);
        self.with_solver_at(definition, depth, |definition, solver| {
            let simplified = simplify_pattern_with_solver(
                definition,
                &state.under(function),
                SimplificationOptions::unbounded(),
                solver,
            )
            .map_err(stopped_operation)?
            .map_err(error("could not simplify KORE pattern"))?;
            let simplified = externalize::constrained_pattern(&simplified);
            // As in `simplify_associated`: a cancellation set aside during the work is the
            // answer.
            k_rust_backend::stop::check().map_err(stopped_operation)?;
            Ok(simplified)
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
    /// `syntax` with its builtin collections associated (`Backend::with_solver_over`,
    /// `BackendDefinition::associated_collections`), where they are also dropped; the
    /// operation reads the associated form, and `syntax` itself is not changed.
    #[cfg(feature = "z3-inference")]
    pub fn model_for_with<T>(
        &mut self,
        module: Option<&str>,
        syntax: &KorePattern,
        admission: Admission,
        finish: impl FnOnce(ModelResult, Option<Sort>) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        // A proof route (`k_rust_backend::evaluation`), the definition's first load included.
        let _proof = EvaluationScope::enter(EvaluationMode::Proof);
        let definition = self.definition_of(module)?;
        let associated = definition.associated_collections(syntax);
        self.model_for_associated(definition, &associated, admission, finish)
    }

    /// [`Self::model_for_with`] in `definition`, of `syntax` with its builtin collections
    /// associated, inside the caller's proof scope.
    #[cfg(feature = "z3-inference")]
    pub(crate) fn model_for_associated<T>(
        &mut self,
        definition: Arc<BackendDefinition>,
        syntax: &KorePattern,
        admission: Admission,
        finish: impl FnOnce(ModelResult, Option<Sort>) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        self.with_solver_on(definition, &[syntax], |definition, solver| {
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
        let mut backend = Backend::new(MODEL_DEFINITION, "MAIN", BackendOptions::DEFAULT)
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

    /// get-model drops a term conjunct below `\exists`, a positive position: `∃Y.(X ∧ Y = 1)` is
    /// nonempty, and `∃Y.(X ∧ Y = 1 ∧ Y = 2)` is empty, so their predicate parts answer `Sat`
    /// and `Unsat`.
    #[test]
    fn a_term_conjunct_below_an_existential_is_dropped_for_a_model() {
        let mut backend = Backend::new(MODEL_DEFINITION, "MAIN", BackendOptions::DEFAULT)
            .expect("model definition should internalize");
        let equals = |value: i64| {
            format!(
                r#"\equals{{SortInt{{}}, SortBool{{}}}}(VarY:SortInt{{}}, \dv{{SortInt{{}}}}("{value}"))"#
            )
        };
        for (conjuncts, satisfiable) in [
            (equals(1), true),
            (format!("{}, {}", equals(1), equals(2)), false),
        ] {
            let source = format!(
                r#"\exists{{SortBool{{}}}}(VarY:SortInt{{}}, \and{{SortBool{{}}}}(VarX:SortBool{{}}, {conjuncts}))"#
            );
            let syntax = parse_pattern(&source).expect("predicate should parse");
            let (model, _) = backend
                .model_for(None, &syntax, Admission::Verified)
                .expect("the model query succeeds");
            assert!(
                if satisfiable {
                    matches!(model, ModelResult::Sat(_))
                } else {
                    matches!(model, ModelResult::Unsat)
                },
                "{source}: {model:?}"
            );
        }
    }

    /// A configuration of a computation, a log and an exit value, and functions of it: an
    /// exit code, a Bool over the whole configuration, one over the log's length, one partial
    /// hook away from a value (`ratio` at exit value 0), and ones no equation gives a value at
    /// some configuration (`isDone` and `reason`, `opaque` anywhere). The rule appends the
    /// count to the log.
    const HELD_DEFINITION: &str = r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            hooked-sort SortList{}
                [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
            sort SortK{} []
            sort SortCfg{} []
            hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
            hooked-symbol listItem{}(SortInt{}) : SortList{} [function{}(), total{}(), hook{}("LIST.element")]
            hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
                [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
            hooked-symbol listSize{}(SortList{}) : SortInt{} [function{}(), total{}(), hook{}("LIST.size")]
            hooked-symbol intAdd{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}(), hook{}("INT.add")]
            hooked-symbol intDiv{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), hook{}("INT.tdiv")]
            hooked-symbol intLt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.lt")]
            symbol count{}(SortInt{}) : SortK{} [constructor{}(), functional{}()]
            symbol done{}() : SortK{} [constructor{}(), functional{}()]
            symbol opaque{}(SortInt{}) : SortK{} [function{}()]
            symbol cfg{}(SortK{}, SortList{}, SortInt{}) : SortCfg{} [constructor{}(), functional{}()]
            symbol LblgetExitCode{}(SortCfg{}) : SortInt{} [function{}()]
            symbol isDone{}(SortCfg{}) : SortBool{} [function{}()]
            symbol short{}(SortCfg{}) : SortBool{} [function{}(), total{}()]
            symbol ratio{}(SortCfg{}) : SortInt{} [function{}()]
            symbol reason{}(SortCfg{}) : SortInt{} [function{}()]
            symbol ofK{}(SortK{}) : SortInt{} [function{}()]
            symbol ofTwo{}(SortCfg{}, SortCfg{}) : SortInt{} [function{}()]
            symbol ofAny{S}(S) : SortInt{} [function{}()]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortCfg{}, R}(X0:SortCfg{}, cfg{}(K:SortK{}, L:SortList{}, E:SortInt{})), \top{R}())),
                \equals{SortInt{}, R}(LblgetExitCode{}(X0:SortCfg{}), \and{SortInt{}}(E:SortInt{}, \top{SortInt{}}()))
            ) [label{}("exit")]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortCfg{}, R}(X0:SortCfg{}, cfg{}(done{}(), L:SortList{}, E:SortInt{})), \top{R}())),
                \equals{SortBool{}, R}(isDone{}(X0:SortCfg{}), \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}()))
            ) [label{}("done")]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortCfg{}, R}(X0:SortCfg{}, cfg{}(count{}(N:SortInt{}), L:SortList{}, E:SortInt{})), \top{R}())),
                \equals{SortBool{}, R}(isDone{}(X0:SortCfg{}), \and{SortBool{}}(\dv{SortBool{}}("false"), \top{SortBool{}}()))
            ) [label{}("not-done")]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortCfg{}, R}(X0:SortCfg{}, cfg{}(K:SortK{}, L:SortList{}, E:SortInt{})), \top{R}())),
                \equals{SortBool{}, R}(short{}(X0:SortCfg{}), \and{SortBool{}}(intLt{}(listSize{}(L:SortList{}), \dv{SortInt{}}("100")), \top{SortBool{}}()))
            ) [label{}("short")]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortCfg{}, R}(X0:SortCfg{}, cfg{}(K:SortK{}, L:SortList{}, E:SortInt{})), \top{R}())),
                \equals{SortInt{}, R}(ratio{}(X0:SortCfg{}), \and{SortInt{}}(intDiv{}(\dv{SortInt{}}("6"), E:SortInt{}), \top{SortInt{}}()))
            ) [label{}("ratio")]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortCfg{}, R}(X0:SortCfg{}, cfg{}(done{}(), L:SortList{}, E:SortInt{})), \top{R}())),
                \equals{SortInt{}, R}(reason{}(X0:SortCfg{}), \and{SortInt{}}(listSize{}(L:SortList{}), \top{SortInt{}}()))
            ) [label{}("reason")]
            axiom{} \rewrites{SortCfg{}}(
                \and{SortCfg{}}(cfg{}(count{}(N:SortInt{}), L:SortList{}, E:SortInt{}), \top{SortCfg{}}()),
                \and{SortCfg{}}(
                    cfg{}(
                        count{}(intAdd{}(N:SortInt{}, \dv{SortInt{}}("1"))),
                        listConcat{}(L:SortList{}, listItem{}(N:SortInt{})),
                        E:SortInt{}
                    ),
                    \top{SortCfg{}}()
                )
            ) [label{}("step")]
        endmodule []"#;

    /// The functions of a configuration of [`HELD_DEFINITION`].
    const HELD_FUNCTIONS: [&str; 5] = ["LblgetExitCode", "isDone", "short", "ratio", "reason"];

    /// The configuration of `computation`, a log of the integers below `entries`, and the exit
    /// value `exit`, its log one associative application.
    fn configuration(computation: &str, entries: usize, exit: i64) -> KorePattern {
        let value = |value: String| KorePattern::DomainValue {
            sort: k_rust_kore::kore::ast::Sort::Application {
                name: "SortInt".to_owned(),
                arguments: Vec::new(),
            },
            value: value.into(),
        };
        let apply = |name: &str, arguments| KorePattern::Application {
            symbol: k_rust_kore::kore::ast::Symbol {
                name: name.to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments,
        };
        let mut items = (0..entries)
            .map(|entry| apply("listItem", vec![value(entry.to_string())]))
            .collect::<Vec<_>>();
        let log = match items.len() {
            0 => apply("listUnit", Vec::new()),
            1 => items.pop().expect("one item"),
            _ => KorePattern::AssociativeApplication {
                associativity: k_rust_kore::kore::ast::Associativity::Right,
                symbol: k_rust_kore::kore::ast::Symbol {
                    name: "listConcat".to_owned(),
                    sort_parameters: Vec::new(),
                },
                arguments: items,
            },
        };
        apply(
            "cfg",
            vec![
                parse_pattern(computation).expect("the computation should parse"),
                log,
                value(exit.to_string()),
            ],
        )
    }

    /// The one leaf's state of a run of `depth` steps from `state`, as the backend holds it.
    fn held_after(backend: &mut Backend, state: KorePattern, depth: u64) -> HeldState {
        let mut request = crate::backend::ExecuteRequest::new(state);
        request.max_depth = Some(depth);
        let mut result = backend
            .execute_kore_held(
                request,
                crate::backend::ProbeRules::default(),
                crate::backend::InProcess::default(),
            )
            .expect("the run should end");
        assert_eq!(result.leaves.len(), 1);
        match result.leaves.pop().expect("one leaf").state {
            crate::backend::LeafState::Held(held) => held,
            crate::backend::LeafState::Kore(kore) => panic!("a state with constraints: {kore}"),
        }
    }

    /// The application of `symbol` to the pattern of `state`, built.
    fn built_application(symbol: &str, state: &HeldState) -> KorePattern {
        KorePattern::Application {
            symbol: k_rust_kore::kore::ast::Symbol {
                name: symbol.to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments: vec![state.kore()],
        }
    }

    /// [`Backend::apply_to_held`] gives what [`Backend::simplify_kore`] gives for the built
    /// application, under both admissions, for every function of the configuration at states a
    /// run reached and at states as given; with what each is expected to be, so that the
    /// comparison is of values, of a function left as its application, and of a function with
    /// no value. For a state that is a value the term simplified is the one the built
    /// application internalizes to, attributes included, and the operation's depth is the
    /// built application's.
    #[test]
    fn a_function_of_a_held_state_is_the_function_of_its_built_pattern() {
        let mut backend = Backend::new(HELD_DEFINITION, "MAIN", BackendOptions::DEFAULT)
            .expect("the definition should internalize");
        let definition = backend.definition_of(None).expect("the main module");
        let integer = |value: i64| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
        let boolean = |value: bool| format!(r#"\dv{{SortBool{{}}}}("{value}")"#);
        // A value at the state whose computation is `opaque(1)`, which no equation defines:
        // the value where that application is defined.
        let where_defined = |sort: &str, value: &str| {
            format!(
                r#"\and{{{sort}{{}}}}({value}, \ceil{{SortK{{}}, {sort}{{}}}}(opaque{{}}(\dv{{SortInt{{}}}}("1"))))"#
            )
        };
        // Each state: whether it is a value, and what the functions give at it, in the order
        // of `HELD_FUNCTIONS`; `None` where the function stays applied to the state.
        let reached = held_after(
            &mut backend,
            configuration(r#"count{}(\dv{SortInt{}}("0"))"#, 0, 3),
            150,
        );
        let finished = held_after(&mut backend, configuration("done{}()", 7, 2), 5);
        let zero = held_after(&mut backend, configuration("done{}()", 2, 0), 0);
        let stuck = held_after(
            &mut backend,
            configuration(r#"opaque{}(\dv{SortInt{}}("1"))"#, 3, 4),
            1,
        );
        let cases = [
            (
                "a run of 150 steps",
                &reached,
                true,
                [
                    Some(integer(3)),
                    Some(boolean(false)),
                    Some(boolean(false)),
                    Some(integer(2)),
                    None,
                ],
            ),
            (
                "a finished computation",
                &finished,
                true,
                [
                    Some(integer(2)),
                    Some(boolean(true)),
                    Some(boolean(true)),
                    Some(integer(3)),
                    Some(integer(7)),
                ],
            ),
            (
                "an exit value of 0",
                &zero,
                true,
                [
                    Some(integer(0)),
                    Some(boolean(true)),
                    Some(boolean(true)),
                    Some(r"\bottom{SortInt{}}()".to_owned()),
                    Some(integer(2)),
                ],
            ),
            (
                "a computation no equation evaluates",
                &stuck,
                false,
                [
                    Some(where_defined("SortInt", &integer(4))),
                    None,
                    Some(where_defined("SortBool", &boolean(true))),
                    Some(where_defined("SortInt", &integer(1))),
                    None,
                ],
            ),
        ];
        for (name, state, value, expected) in cases {
            assert_eq!(state.is_value(), value, "{name}");
            for (symbol, expected) in HELD_FUNCTIONS.into_iter().zip(expected) {
                let application = built_application(symbol, state);
                for admission in [Admission::Unverified, Admission::Verified] {
                    let built = backend.simplify_kore(None, &application, admission);
                    let held = backend.apply_to_held(None, symbol, state, admission);
                    match (&built, &held) {
                        (Ok(built), Ok(held)) => assert_eq!(held, built, "{name}: {symbol}"),
                        (Err(built), Err(held)) => {
                            assert_eq!(held.message(), built.message(), "{name}: {symbol}");
                        }
                        _ => panic!("{name}: {symbol}: {held:?} for {built:?}"),
                    }
                    let expected = match &expected {
                        Some(expected) => parse_pattern(expected).expect("the expectation"),
                        None => application.clone(),
                    };
                    assert_eq!(
                        held.as_ref().expect("the function simplifies"),
                        &expected,
                        "{name}: {symbol}"
                    );
                }
                if !value {
                    continue;
                }
                let function = function_of_state(&definition, symbol, state)
                    .expect("a function of the configuration");
                let associated = definition.associated_collections(&application);
                let internalized = definition
                    .admit_unverified(&associated, &[])
                    .internalize_pattern()
                    .expect("the built application internalizes");
                let under = state.under(function);
                assert_eq!(under.term, internalized.term, "{name}: {symbol}");
                assert_eq!(
                    under.term.attributes(),
                    internalized.term.attributes(),
                    "{name}: {symbol}"
                );
                assert!(internalized.constraints.is_empty(), "{name}: {symbol}");
                assert_eq!(
                    definition.operation_depth_under(state),
                    definition.operation_depth(&[&associated]),
                    "{name}: {symbol}"
                );
            }
        }
    }

    /// A log of 200,000 entries adds no level to the operation: the functions of the
    /// configuration are simplified at the depth of a configuration with a log of three, on
    /// the stack sized for it alone (no simplification stack budget), and give what the built
    /// application gives.
    #[test]
    fn a_function_of_a_state_with_a_long_log_runs_at_the_depth_of_a_short_one() {
        let mut backend = Backend::new(HELD_DEFINITION, "MAIN", BackendOptions::DEFAULT)
            .expect("the definition should internalize");
        backend.set_simplification_stack_budget(0);
        let definition = backend.definition_of(None).expect("the main module");
        let short = held_after(&mut backend, configuration("done{}()", 3, 9), 0);
        let long = held_after(&mut backend, configuration("done{}()", 200_000, 9), 0);
        assert!(long.is_value());
        assert_eq!(
            definition.operation_depth_under(&long),
            definition.operation_depth_under(&short)
        );
        let integer = |value: i64| {
            parse_pattern(&format!(r#"\dv{{SortInt{{}}}}("{value}")"#)).expect("an integer")
        };
        let boolean = |value: bool| {
            parse_pattern(&format!(r#"\dv{{SortBool{{}}}}("{value}")"#)).expect("a Boolean")
        };
        for (symbol, expected) in HELD_FUNCTIONS.into_iter().zip([
            integer(9),
            boolean(true),
            boolean(false),
            integer(0),
            integer(200_000),
        ]) {
            let held = backend
                .apply_to_held(None, symbol, &long, Admission::Unverified)
                .unwrap_or_else(|error| panic!("{symbol}: {error}"));
            assert_eq!(held, expected, "{symbol}");
            let built = backend
                .simplify_kore(
                    None,
                    &built_application(symbol, &long),
                    Admission::Unverified,
                )
                .unwrap_or_else(|error| panic!("{symbol}: {error}"));
            assert_eq!(held, built, "{symbol}");
        }
    }

    /// Only a declared function without sort variables, of one argument of the state's sort, is
    /// applied to a held state, whether or not the state is a value.
    #[test]
    fn a_held_state_is_refused_a_symbol_that_is_no_function_of_it() {
        let mut backend = Backend::new(HELD_DEFINITION, "MAIN", BackendOptions::DEFAULT)
            .expect("the definition should internalize");
        let value = held_after(&mut backend, configuration("done{}()", 2, 0), 0);
        let stuck = held_after(
            &mut backend,
            configuration(r#"opaque{}(\dv{SortInt{}}("1"))"#, 0, 0),
            0,
        );
        for state in [&value, &stuck] {
            for (symbol, why) in [
                ("missing", "the symbol is not declared"),
                ("cfg", "the symbol is not a function"),
                (
                    "ofK",
                    "the symbol's argument is of sort SortK{}, and the state of sort SortCfg{}",
                ),
                ("ofTwo", "the symbol takes 2 arguments, not one"),
                (
                    "ofAny",
                    "the symbol has 1 sort variables, and a state gives it no sort argument",
                ),
                ("listUnit", "the symbol takes 0 arguments, not one"),
            ] {
                let refused = backend
                    .apply_to_held(None, symbol, state, Admission::Unverified)
                    .expect_err(symbol);
                assert_eq!(
                    refused.message(),
                    format!("could not apply {symbol} to a held state: {why}")
                );
            }
        }
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
