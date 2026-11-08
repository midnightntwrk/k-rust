//! A result run that matches its states (`ExecutionAdapter::execute_result_probed` with a match
//! request) matches the states of the system its stop rules and count truncate, and nothing past
//! them (`testdata/k/clock.k`, a free-running clock whose `frame` step comes every fourth step,
//! so no run of `clock(0, 0)` ends on its own).
//!
//! - After the `N`th frame (a terminal rule), the frame's successor is the path's last state:
//!   it is matched, and no later state is.
//! - Before the `N`th frame (a cut-point rule), the state before the step is the path's last
//!   state: it is matched, and the step's proposed successor is not.
//! - Asking for matches changes nothing else of the run, and a condition that always holds
//!   matches what the run without it matches.
//! - The summary records whether the request asked for proof agreement; on a target that
//!   evaluates nothing, agreement changes no verdict.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::num::NonZeroU64;
use std::path::Path;
use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kompile::CompileOptions;
use k_rust::kore::ast::Pattern;
use kink_native::NativeValidator;
use kink_native::execution::{
    AdaptedExecution, DefinitionTables, ExecutionAdapter, ExecutionBudget, HaltClass, ResultRun,
    SolverProfile, StateMatchRequest, StopArrival, StopCondition, StopDecision, StopRules,
};

fn backend() -> Backend {
    let side = NativeValidator::bind(
        support::load_path(&Path::new(support::DIR).join("clock.k"), "CLOCK"),
        CompileOptions::default(),
    )
    .compile_baseline()
    .expect("the clock compiles");
    Backend::new(
        &side.artifacts().definition_kore,
        "CLOCK",
        BackendOptions::default(),
    )
    .expect("the clock loads")
}

/// The configuration `<k> clock(n, phase) </k>`.
fn clock(n: i64, phase: i64) -> Pattern {
    support::initial_state(
        support::app("Lblclock", vec![support::int(n), support::int(phase)]),
        "SortClock",
    )
}

/// A depth bound no passing run reaches (a stop ends each of them first), and a clock that fires
/// only on a test that fails anyway.
const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(600),
    max_simplification_iterations: 10_000,
    max_depth: Some(64),
    max_breadth: None,
};

fn stop(before: &[&str], after: &[&str]) -> StopRules {
    StopRules {
        before: before.iter().map(|rule| (*rule).to_owned()).collect(),
        after: after.iter().map(|rule| (*rule).to_owned()).collect(),
    }
}

/// The run of `clock(0, 0)` to its `count`th arrival at `stop`, with `condition` asked at each,
/// matching its states against `target` when given.
fn run(
    backend: &mut Backend,
    stop: &StopRules,
    count: u64,
    condition: Option<&mut dyn StopCondition>,
    target: Option<&Pattern>,
) -> AdaptedExecution {
    run_agreed(backend, stop, count, condition, target, false)
}

/// [`run`] whose match request asks for proof agreement when `proof_agreement`.
fn run_agreed(
    backend: &mut Backend,
    stop: &StopRules,
    count: u64,
    condition: Option<&mut dyn StopCondition>,
    target: Option<&Pattern>,
    proof_agreement: bool,
) -> AdaptedExecution {
    let target = target.map(|target| StateMatchRequest {
        pattern: target.clone(),
        proof_agreement,
    });
    ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute_result_probed(
            backend,
            &mut DefinitionTables::new(),
            &clock(0, 0),
            BUDGET,
            ResultRun::default(),
            stop,
            NonZeroU64::new(count).unwrap(),
            condition,
            None,
            target.as_ref(),
        )
        .expect("the run is adapted")
}

/// The depth of the first clean reach of `target` by the run, or `None` when the matcher refuted
/// every state the run reached.
fn reach(backend: &mut Backend, stop: &StopRules, count: u64, target: &Pattern) -> Option<u64> {
    let execution = run(backend, stop, count, None, Some(target));
    let matches = execution
        .state_matches()
        .expect("the run matched its states");
    assert!(matches.undecided.is_empty(), "{target:?}: {matches:?}");
    assert_eq!(matches.smt_unknowns, 0);
    assert_eq!(matches.stack_stops, 0);
    match &matches.first_clean_reach {
        Some(reach) => {
            assert_eq!(reach.state, *target);
            assert!(reach.diagnostics.is_empty());
            assert!(!reach.term_conjunction);
            Some(reach.depth)
        }
        None => {
            assert!(matches.all_refuted(), "{target:?}: {matches:?}");
            assert!(matches.matched > 0);
            None
        }
    }
}

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// The `N`th frame after it is at `clock(4N, 0)`, depth `4N`; before it at `clock(4N - 1, 3)`,
/// depth `4N - 1`. A state on the way to the path's last stop is reached, the last stop's state
/// is, and a state past it is not: with count 2 the state past the first frame is reached.
#[test]
fn a_stopped_run_matches_only_the_states_of_its_truncated_system() {
    on_a_big_stack(|| {
        let mut backend = backend();
        let after = stop(&[], &["CLOCK.frame"]);
        let before = stop(&["CLOCK.frame"], &[]);
        for (stop, count, target, depth) in [
            (&after, 1, clock(0, 0), Some(0)),
            (&after, 1, clock(2, 2), Some(2)),
            (&after, 1, clock(4, 0), Some(4)),
            (&after, 1, clock(5, 1), None),
            (&after, 2, clock(5, 1), Some(5)),
            (&after, 2, clock(8, 0), Some(8)),
            (&after, 2, clock(9, 1), None),
            (&before, 1, clock(3, 3), Some(3)),
            // The cut-point step's proposed successor is no state of the truncated system.
            (&before, 1, clock(4, 0), None),
            (&before, 2, clock(4, 0), Some(4)),
            (&before, 2, clock(7, 3), Some(7)),
            (&before, 2, clock(8, 0), None),
        ] {
            assert_eq!(
                reach(&mut backend, stop, count, &target),
                depth,
                "{stop:?} {count} {target:?}"
            );
        }
    });
}

/// Asking for matches leaves the leaves, facts, coverage and work of the run as they are without
/// it, its leaves those of the truncated system; a stop condition that holds at every arrival
/// matches what the run without a condition matches.
#[test]
fn matching_changes_nothing_else_and_composes_with_a_condition() {
    on_a_big_stack(|| {
        let mut backend = backend();
        let after = stop(&[], &["CLOCK.frame"]);
        for count in [1, 2] {
            for target in [clock(2, 2), clock(5, 1)] {
                let plain = run(&mut backend, &after, count, None, None);
                assert!(plain.state_matches().is_none());
                let matched = run(&mut backend, &after, count, None, Some(&target));
                assert_eq!(matched.leaves(), plain.leaves());
                assert_eq!(matched.facts(), plain.facts());
                assert_eq!(matched.coverage(), plain.coverage());
                assert_eq!(matched.work(), plain.work());
                assert_eq!(
                    matched
                        .leaves()
                        .iter()
                        .map(|leaf| (leaf.halt, leaf.branch.state.clone()))
                        .collect::<Vec<_>>(),
                    [(
                        HaltClass::TerminalRule,
                        clock(4 * i64::try_from(count).unwrap(), 0)
                    )]
                );
                let mut holds = |_: &StopArrival<'_>| StopDecision::Holds;
                let conditioned = run(&mut backend, &after, count, Some(&mut holds), Some(&target));
                assert_eq!(conditioned.state_matches(), matched.state_matches());
                assert_eq!(conditioned.undecided_answers(), matched.undecided_answers());
            }
        }
    });
}

/// A request with proof agreement is recorded as one, and on the clock's targets, which have no
/// constraint and only free constructors and integers, its summary is the one without agreement
/// in every other field.
#[test]
fn proof_agreement_is_recorded_and_changes_no_verdict_of_a_target_that_evaluates_nothing() {
    on_a_big_stack(|| {
        let mut backend = backend();
        let after = stop(&[], &["CLOCK.frame"]);
        for target in [clock(2, 2), clock(5, 1)] {
            let plain = run(&mut backend, &after, 1, None, Some(&target));
            let agreed = run_agreed(&mut backend, &after, 1, None, Some(&target), true);
            let plain = plain.state_matches().expect("matched").clone();
            let agreed = agreed.state_matches().expect("matched").clone();
            assert!(!plain.proof_agreement);
            assert!(agreed.proof_agreement);
            assert_eq!(
                kink_native::execution::StateMatches {
                    proof_agreement: false,
                    ..agreed
                },
                plain,
                "{target:?}"
            );
        }
    });
}
