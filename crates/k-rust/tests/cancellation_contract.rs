//! The cancellation contract of `k_rust::backend` ("Bounding an operation"), in both builds:
//! a request cancelled before its operation starts does not run and answers
//! `Err(e)` with `e.stop_cause() == Some(&StopCause::Cancelled)`; a cancellation observed during
//! an `execute` or `search` run is reported in-band, and during a proof as the same error.

use std::{sync::mpsc, thread, time::Duration};

use k_rust::backend::{
    Backend, BackendError, BackendOptions, CancellationToken, ExecuteRequest, HaltReasonOutput,
    IncompleteSearchOutput, PatternRequest, ProveRequest, ResultModalityOutput, SearchRequest,
    StopCause,
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
    let token = CancellationToken::new();
    let (finished, done) = mpsc::channel::<()>();
    let watchdog = {
        let token = token.clone();
        thread::spawn(move || {
            if done.recv_timeout(Duration::from_millis(100)).is_err() {
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
        let result = with_watchdog(|| {
            backend.execute(ExecuteRequest {
                result_modality: modality,
                ..ExecuteRequest::new(start())
            })
        })
        .unwrap();
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
    let response = with_watchdog(|| backend.search(SearchRequest::new(start()))).unwrap();
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
