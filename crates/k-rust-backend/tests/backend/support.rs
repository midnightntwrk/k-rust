//! Fixture helpers shared by more than one module of the `backend` target.

use std::{cell::RefCell, collections::VecDeque};

use k_rust_backend::{
    definition::BackendDefinition,
    rule::{Predicate, RuleOrigin},
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    stop::{self, CancellationToken, Stoppable},
    substitution::Substitution,
    term::Term,
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

/// The first written sentence of the one axiom of `definition` whose id is `unique_id`, as a
/// diagnostic about that axiom names it.
pub fn first_origin(definition: &BackendDefinition, unique_id: &str) -> Option<RuleOrigin> {
    let mut axioms = definition
        .classified_axioms()
        .iter()
        .filter(|axiom| axiom.attributes().unique_id == unique_id);
    let axiom = axioms.next().expect("the axiom is in the definition");
    assert!(axioms.next().is_none(), "one axiom has the id {unique_id}");
    axiom.attributes().origins.first().cloned()
}

/// One ordered query made to [`ScriptedSolver`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ScriptedQuery {
    IsSat {
        predicates: Vec<Predicate>,
        substitution: Substitution,
    },
    CheckPredicates {
        known: Vec<Predicate>,
        substitution: Substitution,
        checked: Vec<Predicate>,
    },
}

/// An ordered SMT test double whose answers and complete query transcript are explicit fixtures.
#[derive(Debug)]
pub struct ScriptedSolver {
    pub answers: RefCell<VecDeque<Result<Satisfiability, SmtError>>>,
    pub validity: RefCell<VecDeque<Result<Validity, SmtError>>>,
    pub transcript: RefCell<Vec<ScriptedQuery>>,
    /// Zero-based query index and token to cancel after recording that query.
    pub cancel_at: Option<(usize, CancellationToken)>,
    /// Whether each query polls for a stop after it is recorded, as a solver polls before each
    /// attempt: a cancellation raised by this query or an earlier one is then its answer.
    pub polls: bool,
}

impl ScriptedSolver {
    pub fn new(
        answers: impl IntoIterator<Item = Result<Satisfiability, SmtError>>,
        validity: impl IntoIterator<Item = Result<Validity, SmtError>>,
    ) -> Self {
        Self {
            answers: RefCell::new(answers.into_iter().collect()),
            validity: RefCell::new(validity.into_iter().collect()),
            transcript: RefCell::default(),
            cancel_at: None,
            polls: false,
        }
    }

    pub fn cancelling_at(mut self, query_index: usize, token: CancellationToken) -> Self {
        self.cancel_at = Some((query_index, token));
        self
    }

    /// Poll for a stop after recording each query, so that a cancellation the query raises is
    /// observed by the solver itself rather than by a later poll.
    pub fn polling(mut self) -> Self {
        self.polls = true;
        self
    }

    fn poll(&self) -> Stoppable<()> {
        if self.polls { stop::check() } else { Ok(()) }
    }

    fn record(&self, query: ScriptedQuery) {
        let mut transcript = self.transcript.borrow_mut();
        let query_index = transcript.len();
        transcript.push(query);
        if let Some((cancel_at, token)) = &self.cancel_at
            && query_index == *cancel_at
        {
            token.cancel();
        }
    }
}

impl SmtSolver for ScriptedSolver {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        self.record(ScriptedQuery::IsSat {
            predicates: predicates.to_vec(),
            substitution: substitution.clone(),
        });
        self.poll()?;
        Ok(self.answers.borrow_mut().pop_front().unwrap_or_else(|| {
            panic!(
                "ScriptedSolver exhausted satisfiability answers after transcript {:#?}",
                self.transcript.borrow()
            )
        }))
    }

    fn check_predicates(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        self.record(ScriptedQuery::CheckPredicates {
            known: known.to_vec(),
            substitution: substitution.clone(),
            checked: checked.to_vec(),
        });
        self.poll()?;
        Ok(self.validity.borrow_mut().pop_front().unwrap_or_else(|| {
            panic!(
                "ScriptedSolver exhausted validity answers after transcript {:#?}",
                self.transcript.borrow()
            )
        }))
    }
}

/// A single-constructor cell sort collected in a hooked set, with rewrite rules that add either
/// a distinct, unresolved cell value or an exact duplicate.
pub fn ground_cell_set_definition() -> BackendDefinition {
    let syntax = parse_definition(include_str!("../fixtures/ground-cell-set.kore"))
        .expect("ground cell set fixture should parse");
    BackendDefinition::internalize(&syntax, "GROUND-CELL-SET")
        .expect("ground cell set fixture should internalize")
}

/// A strict-list overload and `isKResult` equation pair used to distinguish concrete lowering
/// from symbolic sort membership.
pub fn ground_overload_definition() -> BackendDefinition {
    let syntax = parse_definition(include_str!("../fixtures/ground-overload.kore"))
        .expect("ground overload fixture should parse");
    BackendDefinition::internalize(&syntax, "GROUND-OVERLOAD")
        .expect("ground overload fixture should internalize")
}

/// A constructor `pair(SortInt, SortInt) : SortState`, the partial hooked `divInt` (`INT.tdiv`,
/// not `total`), the total `neInt`, and the simplification axiom
/// `⌈divInt(I1, I2)⌉ = (neInt(I2, 0) = true)`, with no rewrite rule. Under it
/// `pair(X, divInt(X, 0))` has no instance, while `pair(X, divInt(10, X))` is defined exactly
/// where `X =/=Int 0`.
pub fn ceil_div_definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortState{} []
                symbol pair{}(SortInt{}, SortInt{}) : SortState{} [constructor{}()]
                hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
                hooked-symbol neInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.ne"), smt-hook{}("distinct")]
                axiom{R} \implies{R}(\top{R}(), \equals{R, R}(
                    \ceil{SortInt{}, R}(divInt{}(I1:SortInt{}, I2:SortInt{})),
                    \and{R}(
                        \equals{SortBool{}, R}(
                            neInt{}(I2:SortInt{}, \dv{SortInt{}}("0")),
                            \dv{SortBool{}}("true")),
                        \top{R}())))
                    [label{}("ceil-div"), simplification{}()]
            endmodule []"#,
    )
    .expect("ceil-div definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("ceil-div definition should internalize")
}

/// Parse a KORE pattern and internalize it as a term of `definition`.
pub fn internal_term(definition: &BackendDefinition, source: &str) -> Term {
    let syntax = parse_pattern(source).expect("term should parse");
    definition
        .admit_unverified(&syntax, &[])
        .internalize_term()
        .expect("term should internalize")
}

/// The simplifier's entry points on their failure layer, for the tests that arm no stop.
///
/// Each entry point returns a layered result: a stop outside, the simplification or its failure
/// inside. A test that arms no stop asserts on the inner layer; a stop there is a test failure,
/// reported with its cause. A test that expects a stop calls `k_rust_backend::simplify` itself.
pub mod unstopped {
    use k_rust_backend::{
        definition::BackendDefinition,
        rewrite::{self, Pattern, RewriteResult},
        rule::Predicate,
        simplify::{self, Simplification, SimplificationError, SimplificationOptions},
        smt::SmtSolver,
        stop::Stoppable,
        term::Term,
    };

    /// A rewrite step's result where no stop is armed: a stop panics with its cause.
    fn unstopped_step(result: Stoppable<RewriteResult>) -> RewriteResult {
        result.unwrap_or_else(|stop| {
            panic!(
                "the rewrite step stopped although no stop was armed: {}",
                stop.into_cause()
            )
        })
    }

    pub fn rewrite_step(
        definition: &BackendDefinition,
        pattern: &Pattern,
        fresh_counter: &mut k_rust_backend::fresh::FreshCounter,
    ) -> RewriteResult {
        unstopped_step(rewrite::rewrite_step(definition, pattern, fresh_counter))
    }

    pub fn rewrite_step_with_solver(
        definition: &BackendDefinition,
        pattern: &Pattern,
        fresh_counter: &mut k_rust_backend::fresh::FreshCounter,
        solver: &dyn SmtSolver,
    ) -> RewriteResult {
        unstopped_step(rewrite::rewrite_step_with_solver(
            definition,
            pattern,
            fresh_counter,
            solver,
        ))
    }

    pub fn rewrite_step_sequential_with_solver(
        definition: &BackendDefinition,
        pattern: &Pattern,
        fresh_counter: &mut k_rust_backend::fresh::FreshCounter,
        solver: &dyn SmtSolver,
    ) -> RewriteResult {
        unstopped_step(rewrite::rewrite_step_sequential_with_solver(
            definition,
            pattern,
            fresh_counter,
            solver,
        ))
    }

    fn unstopped<T>(
        result: Stoppable<Result<T, SimplificationError>>,
    ) -> Result<T, SimplificationError> {
        result.unwrap_or_else(|stop| {
            panic!(
                "the simplification stopped although no stop was armed: {}",
                stop.into_cause()
            )
        })
    }

    pub fn simplify(
        definition: &BackendDefinition,
        term: &Term,
        options: SimplificationOptions,
    ) -> Result<Simplification, SimplificationError> {
        unstopped(simplify::simplify(definition, term, options))
    }

    pub fn simplify_with_solver(
        definition: &BackendDefinition,
        term: &Term,
        known_predicates: &[Predicate],
        options: SimplificationOptions,
        solver: &dyn SmtSolver,
    ) -> Result<Simplification, SimplificationError> {
        unstopped(simplify::simplify_with_solver(
            definition,
            term,
            known_predicates,
            options,
            solver,
        ))
    }

    pub fn simplify_pattern_with_solver(
        definition: &BackendDefinition,
        pattern: &Pattern,
        options: SimplificationOptions,
        solver: &dyn SmtSolver,
    ) -> Result<Pattern, SimplificationError> {
        unstopped(simplify::simplify_pattern_with_solver(
            definition, pattern, options, solver,
        ))
    }

    pub fn simplify_predicates_with_solver(
        definition: &BackendDefinition,
        predicates: &[Predicate],
        known_predicates: &[Predicate],
        options: SimplificationOptions,
        solver: &dyn SmtSolver,
    ) -> Result<Vec<Predicate>, SimplificationError> {
        unstopped(simplify::simplify_predicates_with_solver(
            definition,
            predicates,
            known_predicates,
            options,
            solver,
        ))
    }

    pub fn simplify_predicate_with_solver(
        definition: &BackendDefinition,
        predicate: &Predicate,
        known_predicates: &[Predicate],
        options: SimplificationOptions,
        solver: &dyn SmtSolver,
    ) -> Result<Predicate, SimplificationError> {
        unstopped(simplify::simplify_predicate_with_solver(
            definition,
            predicate,
            known_predicates,
            options,
            solver,
        ))
    }

    pub fn simplify_and_decide_predicate_with_solver(
        definition: &BackendDefinition,
        predicate: &Predicate,
        known_predicates: &[Predicate],
        options: SimplificationOptions,
        solver: &dyn SmtSolver,
    ) -> Result<Predicate, SimplificationError> {
        unstopped(simplify::simplify_and_decide_predicate_with_solver(
            definition,
            predicate,
            known_predicates,
            options,
            solver,
        ))
    }
}
