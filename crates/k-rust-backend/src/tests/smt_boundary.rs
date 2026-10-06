//! Boundary contracts of the in-process Z3 solver (`crate::smt::Z3Solver`): what an undecided
//! answer and an undecided prelude mean.
//!
//! The undecided query is a nonlinear one with no solution that Z3 cannot refute: positive
//! integers `X`, `Y`, `Z` with `X³ + Y³ = Z³`. It has no solution, so no attempt can answer
//! `Sat`, and refuting it is out of reach of Z3's integer arithmetic, so every attempt, at any of
//! the millisecond timeouts used here, ends `Unknown`.

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::BackendDefinition,
    model::ModelQuery,
    rule::Predicate,
    smt::{ModelResult, Satisfiability, SmtSolver, Z3Options, Z3Solver},
    stop::{PreludeFailure, Stop, StopCause, Stoppable},
    substitution::Substitution,
    term::{Sort, Term},
};

fn definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
            hooked-symbol mulInt{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.mul"), smt-hook{}("*")]
            hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
        endmodule []"#,
    )
    .expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
        .expect("term should internalize")
}

fn int(value: &str) -> Term {
    Term::domain_value(Sort::simple("SortInt"), value)
}

/// `X > 0 ∧ Y > 0 ∧ Z > 0 ∧ X·X·X + Y·Y·Y = Z·Z·Z`: unsatisfiable, and undecided by Z3.
fn undecided(definition: &BackendDefinition) -> Vec<Predicate> {
    let positive = |name: &str| {
        Predicate::Term(term(
            definition,
            &format!(r#"gtInt{{}}({name}:SortInt{{}}, \dv{{SortInt{{}}}}("0"))"#),
        ))
    };
    let cube = |name: &str| {
        format!(
            "mulInt{{}}({name}:SortInt{{}}, mulInt{{}}({name}:SortInt{{}}, {name}:SortInt{{}}))"
        )
    };
    vec![
        positive("X"),
        positive("Y"),
        positive("Z"),
        Predicate::Equals(
            term(
                definition,
                &format!("addInt{{}}({}, {})", cube("X"), cube("Y")),
            ),
            term(definition, &cube("Z")),
        ),
    ]
}

/// `X = 1 ∧ X = 2`: refuted at once, whatever else the script asserts.
fn refuted(definition: &BackendDefinition) -> Vec<Predicate> {
    let x = term(definition, "X:SortInt{}");
    vec![
        Predicate::Equals(x.clone(), int("1")),
        Predicate::Equals(x, int("2")),
    ]
}

/// The same three positive cubes as a user prelude.
const UNDECIDED_PRELUDE: &str = "(declare-const a Int)\n(declare-const b Int)\n\
(declare-const c Int)\n(assert (> a 0))\n(assert (> b 0))\n(assert (> c 0))\n\
(assert (= (+ (* a a a) (* b b b)) (* c c c)))";

/// The timeouts of the `retry_limit + 1` attempts of one query: each retry doubles the last.
fn doubling(timeout_ms: u32, retry_limit: u32) -> Vec<u32> {
    (0..=retry_limit)
        .map(|attempt| timeout_ms << attempt)
        .collect()
}

/// The cause of a stopped answer, published so that no stop is dropped armed.
fn cause<T>(answer: Stoppable<T>) -> Result<T, StopCause> {
    answer.map_err(Stop::into_cause)
}

/// An `Unknown` answer is a fact about the attempts, not about the query: each of the
/// `retry_limit + 1` attempts runs with twice the previous timeout, and only the last one's
/// `Unknown` is the answer. Since a later attempt could still decide the query, the answer is not
/// cached, and since it refutes nothing, it does not make the solver check its prelude (only an
/// `Unsat` answer needs a consistent prelude to mean anything).
#[test]
fn an_undecided_query_is_retried_with_doubled_timeouts_and_answers_unknown_uncached() {
    let definition = definition();
    let predicates = undecided(&definition);
    for retry_limit in [0, 1, 2] {
        let options = Z3Options {
            timeout_ms: 1,
            retry_limit,
        };
        let solver = Z3Solver::with_options(&definition, options).unwrap();
        for asked in 1..=2 {
            let answer = solver.is_sat(&predicates, &Substitution::new());
            assert!(
                matches!(&answer, Ok(Ok(Satisfiability::Unknown(reason))) if !reason.is_empty()),
                "retry limit {retry_limit}: {answer:?}"
            );
            assert_eq!(
                solver.attempt_timeouts(),
                doubling(1, retry_limit).repeat(asked),
                "retry limit {retry_limit}, asked {asked} times"
            );
        }
        assert_eq!(solver.prelude_failure(), None);
    }
}

/// A model query undecided by every attempt is retried like a satisfiability query and answers
/// `ModelResult::Unknown`, not a model and not a failure.
#[test]
fn an_undecided_model_query_is_retried_and_answers_unknown() {
    let definition = definition();
    let predicates = undecided(&definition);
    let solver = Z3Solver::with_options(
        &definition,
        Z3Options {
            timeout_ms: 1,
            retry_limit: 2,
        },
    )
    .unwrap();
    let answer = solver.get_model(&ModelQuery::for_solver_tests(
        &predicates,
        &Substitution::new(),
    ));
    assert!(
        matches!(&answer, Ok(Ok(ModelResult::Unknown(reason))) if !reason.is_empty()),
        "{answer:?}"
    );
    assert_eq!(solver.attempt_timeouts(), doubling(1, 2));
    assert_eq!(solver.prelude_failure(), None);
}

/// A prelude the solver cannot decide may be inconsistent, so no `Unsat` answer under it means
/// anything: the prelude check reports it as a failed prelude (`Unknown`, with Z3's reason),
/// after the same retries as a query, and from then on every query of every kind stops with that
/// cause without running Z3.
#[test]
fn an_undecided_prelude_is_a_failed_prelude_that_stops_every_later_query() {
    let definition = definition();
    let options = Z3Options {
        timeout_ms: 1,
        retry_limit: 3,
    };
    let solver =
        Z3Solver::with_options_and_prelude(&definition, options, Some(UNDECIDED_PRELUDE)).unwrap();
    let failure = match cause(solver.check_prelude()) {
        Err(StopCause::SolverPrelude(failure @ PreludeFailure::Unknown(_))) => failure,
        other => panic!("expected an undecided prelude, found {other:?}"),
    };
    assert_eq!(solver.attempt_timeouts(), doubling(1, 3));
    assert_eq!(solver.prelude_failure(), Some(failure.clone()));

    let stopped = Err(StopCause::SolverPrelude(failure));
    let predicates = refuted(&definition);
    assert_eq!(
        cause(solver.is_sat(&predicates, &Substitution::new())).map(|_| ()),
        stopped
    );
    assert_eq!(
        cause(solver.check_predicates(&[], &Substitution::new(), &predicates)).map(|_| ()),
        stopped
    );
    assert_eq!(
        cause(solver.get_model(&ModelQuery::for_solver_tests(
            &predicates,
            &Substitution::new()
        )))
        .map(|_| ()),
        stopped
    );
    assert_eq!(cause(solver.check_prelude()), stopped);
    assert_eq!(
        solver.attempt_timeouts(),
        doubling(1, 3),
        "no later query runs Z3"
    );
}

/// The first `Unsat` answer under an unchecked prelude is confirmed by checking the prelude; when
/// that check cannot decide it, the query stops with the failed prelude instead of answering
/// `Unsat`, which an inconsistent prelude would also have produced.
#[test]
fn an_unsat_answer_under_an_undecided_prelude_stops_instead_of_answering() {
    let definition = definition();
    // Long enough for Z3 to refute `X = 1 ∧ X = 2` on a loaded machine; the prelude check still
    // ends `Unknown` at any timeout.
    let options = Z3Options {
        timeout_ms: 25,
        retry_limit: 1,
    };
    let solver =
        Z3Solver::with_options_and_prelude(&definition, options, Some(UNDECIDED_PRELUDE)).unwrap();
    let answer = cause(solver.is_sat(&refuted(&definition), &Substitution::new()));
    assert!(
        matches!(
            &answer,
            Err(StopCause::SolverPrelude(PreludeFailure::Unknown(_)))
        ),
        "{answer:?}"
    );
    let timeouts = solver.attempt_timeouts();
    assert!(
        timeouts.ends_with(&doubling(25, 1)) && timeouts.len() > doubling(25, 1).len(),
        "the query's own attempts, then the prelude check's: {timeouts:?}"
    );
}
