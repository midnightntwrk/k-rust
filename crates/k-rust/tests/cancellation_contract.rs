//! The cancellation contract of `k_rust::backend` ("Bounding an operation"), in both builds:
//! a request cancelled before its operation starts does not run and answers
//! `Err(e)` with `e.stop_cause() == Some(&StopCause::Cancelled)`; a cancellation observed during
//! an `execute` or `search` run is reported in-band, and during a proof as the same error.

use std::{sync::mpsc, thread, time::Duration};

use k_rust::backend::{
    Backend, BackendError, BackendOptions, CancellationToken, CancelledResultOutput,
    ExecuteRequest, HaltReasonOutput, IncompleteSearchOutput, PatternRequest, ProveRequest,
    ResultModalityOutput, SearchRequest, StopCause,
};
use k_rust::kore::{ast::Pattern, parser::parse_pattern};

/// A counter that never stops: `count(I) => count(I +Int 1)`, and a claim that it reaches
/// `done()`, which no path does.
const LOOP: &str = r#"[]
module LOOP
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  sort SortS{} []
  symbol count{}(SortInt{}) : SortS{} [constructor{}(), functional{}()]
  symbol done{}() : SortS{} [constructor{}(), functional{}()]
  hooked-symbol add{}(SortInt{}, SortInt{}) : SortInt{}
    [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
  alias weakExistsFinally{S}(S) : S where weakExistsFinally{S}(@X:S) := @X:S []
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(count{}(I:SortInt{}), \top{SortS{}}()),
    \and{SortS{}}(count{}(add{}(I:SortInt{}, \dv{SortInt{}}("1"))), \top{SortS{}}())
  ) [label{}("count")]
  claim{} \implies{SortS{}}(
    \and{SortS{}}(\top{SortS{}}(), count{}(\dv{SortInt{}}("0"))),
    weakExistsFinally{SortS{}}(\and{SortS{}}(done{}(), \top{SortS{}}()))
  ) [label{}("never-done")]
endmodule []"#;

fn backend() -> Backend {
    Backend::new(LOOP, "LOOP", BackendOptions::default()).unwrap()
}

fn start() -> Pattern {
    parse_pattern(r#"count{}(\dv{SortInt{}}("0"))"#).unwrap()
}

fn assert_cancelled(error: &BackendError) {
    assert_eq!(error.stop_cause(), Some(&StopCause::Cancelled), "{error}");
    assert_eq!(error.to_string(), "Request cancelled");
}

/// Run `operation` inside a token's scope and cancel the token from another thread after
/// 100 ms, unless `operation` has returned by then.
fn with_watchdog<T>(operation: impl FnOnce() -> T) -> T {
    with_watchdog_after(Duration::from_millis(100), operation)
}

/// [`with_watchdog`] with the cancellation after `delay`.
fn with_watchdog_after<T>(delay: Duration, operation: impl FnOnce() -> T) -> T {
    let token = CancellationToken::new();
    let (finished, done) = mpsc::channel::<()>();
    let watchdog = {
        let token = token.clone();
        thread::spawn(move || {
            if done.recv_timeout(delay).is_err() {
                token.cancel();
            }
        })
    };
    let outcome = token.scope(operation);
    drop(finished);
    watchdog.join().unwrap();
    outcome
}

#[test]
fn an_operation_cancelled_before_it_starts_does_not_run() {
    let mut backend = backend();
    let token = CancellationToken::new();
    token.cancel();
    let execute = token
        .scope(|| backend.execute(ExecuteRequest::new(start())))
        .unwrap_err();
    assert_cancelled(&execute);
    let search = token
        .scope(|| backend.search(SearchRequest::new(start())))
        .unwrap_err();
    assert_cancelled(&search);
    let simplify = token
        .scope(|| backend.simplify(PatternRequest::new(start())))
        .unwrap_err();
    assert_cancelled(&simplify);
}

#[test]
fn a_backend_constructed_in_a_cancelled_scope_reports_the_cancellation() {
    let token = CancellationToken::new();
    token.cancel();
    let Err(error) = token.scope(|| Backend::new(LOOP, "LOOP", BackendOptions::default())) else {
        panic!("a backend constructed under a cancelled token was returned");
    };
    assert_cancelled(&error);
}

#[test]
fn a_cancelled_execution_reports_the_stopped_state_as_its_one_cancelled_leaf() {
    for modality in [
        ResultModalityOutput::PathSet,
        ResultModalityOutput::StateSet,
    ] {
        let mut backend = backend();
        let outcome = with_watchdog(|| {
            backend.execute(ExecuteRequest {
                result_modality: modality,
                ..ExecuteRequest::new(start())
            })
        });
        // A cancellation that lands before the boundary's entry poll is the entry error
        // instead (contract point 4).
        let result = match outcome {
            Ok(result) => result,
            Err(error) => {
                assert_cancelled(&error);
                continue;
            }
        };
        assert_eq!(result.leaves.len(), 1, "{modality:?}");
        assert!(
            matches!(result.leaves[0].reason, HaltReasonOutput::Cancelled),
            "{modality:?}: {:?}",
            result.leaves[0].reason
        );
    }
}

#[test]
fn a_cancelled_search_reports_the_stopped_state_as_a_cancelled_entry() {
    let mut backend = backend();
    // As for execution, a cancellation before the entry poll is the entry error.
    let response = match with_watchdog(|| backend.search(SearchRequest::new(start()))) {
        Ok(response) => response,
        Err(error) => return assert_cancelled(&error),
    };
    assert_eq!(response.incomplete.len(), 1, "{:?}", response.incomplete);
    assert!(
        matches!(
            response.incomplete[0],
            IncompleteSearchOutput::Cancelled { .. }
        ),
        "{:?}",
        response.incomplete
    );
}

#[test]
fn a_proof_cancelled_while_it_runs_answers_the_cancellation() {
    let mut backend = backend();
    let error = with_watchdog(|| backend.prove(ProveRequest::default())).unwrap_err();
    assert_cancelled(&error);
}

/// An all-path claim `start => done` whose `start` steps either to a stuck state, which certifies
/// a refutation, or into a counter that never ends.
const REFUTED: &str = r#"[]
module REFUTED
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  sort SortS{} []
  symbol start{}() : SortS{} [constructor{}(), functional{}()]
  symbol stuck{}() : SortS{} [constructor{}(), functional{}()]
  symbol done{}() : SortS{} [constructor{}(), functional{}()]
  symbol count{}(SortInt{}) : SortS{} [constructor{}(), functional{}()]
  hooked-symbol add{}(SortInt{}, SortInt{}) : SortInt{}
    [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
  alias weakAlwaysFinally{S}(S) : S where weakAlwaysFinally{S}(@X:S) := @X:S []
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(start{}(), \top{SortS{}}()), \and{SortS{}}(stuck{}(), \top{SortS{}}())
  ) [label{}("to-stuck")]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(start{}(), \top{SortS{}}()),
    \and{SortS{}}(count{}(\dv{SortInt{}}("0")), \top{SortS{}}())
  ) [label{}("to-count")]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(count{}(I:SortInt{}), \top{SortS{}}()),
    \and{SortS{}}(count{}(add{}(I:SortInt{}, \dv{SortInt{}}("1"))), \top{SortS{}}())
  ) [label{}("count")]
  claim{} \implies{SortS{}}(
    \and{SortS{}}(\top{SortS{}}(), start{}()),
    weakAlwaysFinally{SortS{}}(\and{SortS{}}(done{}(), \top{SortS{}}()))
  ) [label{}("all-done")]
endmodule []"#;

/// A certified refutation found before the cancellation stands: the proof asked for two
/// counterexamples, found the stuck one at once, and was cancelled while it counted, with
/// states left unexplored.
#[test]
fn a_proof_cancelled_after_a_certified_refutation_keeps_its_verdict() {
    let mut backend = Backend::new(REFUTED, "REFUTED", BackendOptions::default()).unwrap();
    let request = ProveRequest {
        max_counterexamples: 2,
        ..ProveRequest::default()
    };
    // The facade has no hook to cancel once the stuck leaf is recorded, so the watchdog waits.
    // The stuck leaf is two steps from the start and is found within microseconds; a host so
    // slow that the cancellation lands first gets `Err(Cancelled)`, which the contract also
    // allows (the proof had decided nothing yet), and the test retries with a longer delay.
    for delay in [300, 1_200, 4_800] {
        match with_watchdog_after(Duration::from_millis(delay), || {
            backend.prove(request.clone())
        }) {
            Ok(result) => {
                assert_eq!(result.status, "disproved");
                assert!(result.unexplored_states > 0, "{result:?}");
                return;
            }
            Err(error) => assert_cancelled(&error),
        }
    }
    panic!("the proof never recorded its stuck leaf before the cancellation");
}

/// With the default limit of one counterexample, the stuck leaf ends the proof; a watchdog that
/// fires later, or a cancellation the last leaf's refinement observed, leaves that verdict.
#[test]
fn a_proof_that_reached_its_counterexample_limit_keeps_its_verdict() {
    let mut backend = Backend::new(REFUTED, "REFUTED", BackendOptions::default()).unwrap();
    let result = with_watchdog(|| backend.prove(ProveRequest::default())).unwrap();
    assert_eq!(result.status, "disproved");
}

/// Under `cancelledResult: error` a cancellation that ends an `execute` answers `Err` with the
/// `Cancelled` cause, whichever phase observed it, and builds no leaf; under `partial` the same
/// request answers `Ok` with the stopped state as its one `cancelled` leaf, or the entry error when
/// the cancellation lands before the boundary's entry poll (point 4).
#[test]
fn an_error_shaped_cancellation_builds_no_leaves() {
    for modality in [
        ResultModalityOutput::PathSet,
        ResultModalityOutput::StateSet,
    ] {
        let mut executor = backend();
        let error = with_watchdog(|| {
            executor.execute(ExecuteRequest {
                result_modality: modality,
                cancelled_result: CancelledResultOutput::Error,
                ..ExecuteRequest::new(start())
            })
        })
        .expect_err("an error-shaped cancellation answers Err");
        assert_cancelled(&error);

        let mut executor = backend();
        let outcome = with_watchdog(|| {
            executor.execute(ExecuteRequest {
                result_modality: modality,
                cancelled_result: CancelledResultOutput::Partial,
                ..ExecuteRequest::new(start())
            })
        });
        match outcome {
            Ok(result) => {
                assert_eq!(result.leaves.len(), 1, "{modality:?}");
                assert_eq!(result.leaves[0].reason, HaltReasonOutput::Cancelled);
            }
            Err(error) => assert_cancelled(&error),
        }
    }
}
