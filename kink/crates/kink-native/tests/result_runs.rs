//! Re-pin lane 1 (L1-1): result runs are state sets without a trace, with run coverage, answering
//! a cancellation with an error, and optionally under a work budget.
//!
//! - A state set whose leaves hold an undefined step (`Trivial`), a vacuous leaf or a
//!   contradicted claim is replaced by the path set of the same request, so kink's exclusions read
//!   each such leaf's own rule (k-rust reports it under a state set only as witness metadata).
//! - A work budget at least the unbounded run's work changes nothing; below it the run ends in
//!   one `work-bound` leaf, which the adapter admits only under `max_work` and the bridge reads as
//!   an incomplete path without a real prefix or a term, so the run is never complete.
//! - Every run collects k-rust's run coverage and carries no trace; a result run carries no
//!   branch identity, a stepped run does.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::path::Path;
use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kompile::CompileOptions;
use k_rust::kore::{ast::Pattern, parser::parse_definition};
use kink_native::bridge::{BridgeContext, paths_from_execution_values};
use kink_native::coverage::{RuleAuthors, TestCoverage};
use kink_native::execution::{
    AdaptedExecution, ExecutionAdapter, ExecutionBudget, HaltClass, ResultModality, ResultRun,
    SolverProfile,
};
use kink_native::feasibility::TestInitialState;
use kink_native::step_events::ObservationDecider;
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_pattern::{CollectionStop, ExecutionTerminalKind, PathStop, SymbolSorts};

/// The fixture `testdata/k/<dir>/<name>.k`, compiled, and its encoded main module.
fn fixture(dir: &str, name: &str) -> (ValidatedDefinition, String) {
    let module = name.to_ascii_uppercase();
    let loaded = support::load_path(
        &Path::new(support::DIR).join(format!("{dir}/{name}.k")),
        &module,
    );
    let side = NativeValidator::bind(loaded, CompileOptions::default())
        .compile_baseline()
        .unwrap_or_else(|e| panic!("{name}: {e}"));
    (side, k_rust::kast::identifier::encode(&module))
}

fn backend(side: &ValidatedDefinition, module: &str) -> Backend {
    Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .unwrap()
}

fn budget() -> ExecutionBudget {
    ExecutionBudget {
        time: Duration::from_secs(60),
        max_simplification_iterations: 10_000,
        max_depth: Some(1000),
        max_breadth: None,
    }
}

fn adapter() -> ExecutionAdapter {
    ExecutionAdapter::with_profile(SolverProfile::BUILD)
}

fn state(symbol: &str, argument: i64) -> Pattern {
    support::initial_state(
        support::app(symbol, vec![support::int(argument)]),
        "SortProg",
    )
}

fn halts(execution: &AdaptedExecution) -> Vec<(HaltClass, serde_json::Value)> {
    execution
        .leaves()
        .iter()
        .map(|leaf| (leaf.halt, leaf.branch.state.clone()))
        .collect()
}

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// A state set with an undefined step, plain (`half(0)`) or contradicting `td`'s `total` claim
/// (`tdiv(-1)`), is replaced by its path set, whose leaf names its own rule; a run without one
/// (`half(2)`) stays a state set. k-rust's own state set of the same request is a state set
/// (`execute_once`).
#[test]
fn a_state_set_with_an_undefined_step_is_replaced_by_its_path_set() {
    on_a_big_stack(|| {
        let (side, module) = fixture("r0b", "tdiv");
        let mut backend = backend(&side, &module);
        let adapter = adapter();
        for (symbol, argument) in [("Lblhalf", 0), ("Lbltdiv", -1)] {
            let initial = state(symbol, argument);
            let run = adapter.execute(&mut backend, &initial, budget()).unwrap();
            assert_eq!(run.modality(), ResultModality::PathSet, "{symbol}");
            let [leaf] = run.leaves() else {
                panic!("{symbol}: {run:?}")
            };
            assert_eq!(leaf.halt, HaltClass::Trivial);
            assert!(leaf.undefined_rule.is_some(), "{symbol}: names its rule");
            let raw = adapter
                .execute_once(&mut backend, &initial, budget(), ResultRun::default())
                .unwrap();
            assert_eq!(raw.modality(), ResultModality::StateSet);
            assert!(
                raw.leaves()
                    .iter()
                    .any(|leaf| leaf.halt == HaltClass::Trivial)
            );
        }
        let defined = adapter
            .execute(&mut backend, &state("Lblhalf", 2), budget())
            .unwrap();
        assert_eq!(defined.modality(), ResultModality::StateSet);
        assert_eq!(
            defined
                .leaves()
                .iter()
                .map(|leaf| leaf.halt)
                .collect::<Vec<_>>(),
            [HaltClass::Stuck]
        );
    });
}

/// Every run collects k-rust's run coverage and carries no trace. A result run is unobserved
/// (no branch identity), and its rule coverage names the rules it reached and applied; a stepped
/// run keeps its branch identities, which name the same rewrite rules as k-rust's
/// `applied_rewrites` (the reading before L1-1, kept here as an independent check of k-rust's
/// coverage since re-pin L2-1 retired `TestCoverage::of_branches`).
#[test]
fn every_run_collects_coverage_and_carries_no_trace() {
    on_a_big_stack(|| {
        let (side, module) = fixture("l1", "workloop");
        let mut backend = backend(&side, &module);
        let authors = RuleAuthors::of(&side);
        let adapter = adapter();
        let initial = state("Lblcount", 2);
        let run = adapter.execute(&mut backend, &initial, budget()).unwrap();
        let coverage = run.coverage().expect("collected");
        assert_eq!(coverage.applied_rewrites.len(), 2, "{coverage:?}");
        assert!(coverage.applied_rewrites.is_subset(&coverage.applied));
        assert!(coverage.applied.is_subset(&coverage.matched));
        for leaf in run.leaves() {
            assert!(leaf.branch.trace.is_empty());
            assert!(leaf.branch.identity.is_empty());
        }
        let rules = TestCoverage::of_execution("count", &run, &authors);
        assert!(rules.complete);
        let baseline =
            support::load_path(&Path::new(support::DIR).join("l1/workloop.k"), "WORKLOOP");
        assert_eq!(
            rules.sentences,
            ["WORKLOOP.step", "WORKLOOP.stop"]
                .map(|label| support::rule(&baseline, label))
                .into_iter()
                .collect()
        );
        let stepped = adapter
            .execute_steps(&mut backend, &initial, budget())
            .unwrap()
            .unwrap();
        assert!(stepped.adapted.coverage().is_some());
        for leaf in stepped.adapted.leaves() {
            assert!(leaf.branch.trace.is_empty());
            assert!(!leaf.branch.identity.is_empty());
        }
        let named = stepped
            .adapted
            .leaves()
            .iter()
            .flat_map(|leaf| {
                leaf.branch
                    .identity
                    .iter()
                    .map(|transition| transition.rule.as_str())
                    .chain(leaf.undefined_rule.iter().map(|rule| rule.id.as_str()))
            })
            .flat_map(|ids| ids.split(','))
            .filter(|id| !id.is_empty())
            .map(str::to_owned)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(named, coverage.applied_rewrites);
        assert_eq!(
            stepped.adapted.coverage().map(|c| &c.applied_rewrites),
            Some(&named)
        );
        assert!(coverage.applied_rewrites.is_subset(&rules.applied_ids));
        assert_eq!(
            TestCoverage::of_execution("count", &stepped.adapted, &authors),
            rules
        );
    });
}

mod kink_tier {
    use super::*;

    /// Every request answers a cancellation with an error: a run whose time bound expires publishes
    /// no leaf and no coverage, and is a timeout (k-rust 501f18b9 `cancelled_result: error`).
    #[test]
    #[ignore = "kink"]
    fn a_timed_out_run_publishes_no_leaf() {
        on_a_big_stack(|| {
            let (side, module) = fixture("l1", "workloop");
            let mut backend = backend(&side, &module);
            let adapter = adapter();
            let short = ExecutionBudget {
                time: Duration::from_millis(200),
                max_depth: None,
                ..budget()
            };
            // count(N) for a large N runs far past 200 ms.
            let run = adapter
                .execute(&mut backend, &state("Lblcount", 100_000_000), short)
                .unwrap();
            assert!(run.timed_out());
            assert!(run.leaves().is_empty());
            assert!(run.coverage().is_none());
            assert_eq!(run.work(), 0);
        });
    }

    /// k-rust KINK-16 criterion 2, as kink requests it: a budget at least the unbounded run's work
    /// gives the unbounded run, under either modality; one state less ends the run in one
    /// `work-bound` leaf, the last, which the bridge reads as an incomplete path without a real
    /// prefix or a term, so the collection stops at `BackendLimit` and no terminal is complete. A
    /// request without `max_work` never admits such a leaf.
    #[test]
    #[ignore = "kink"]
    fn a_work_budget_stops_a_run_and_never_completes_it() {
        on_a_big_stack(|| {
            let (side, module) = fixture("l1", "workloop");
            let mut backend = backend(&side, &module);
            let sorts = SymbolSorts::from_definition(
                &parse_definition(&side.artifacts().definition_kore).unwrap(),
            );
            let adapter = adapter();
            let initial = state("Lblcount", 5);
            for modality in [ResultModality::StateSet, ResultModality::PathSet] {
                let run = |backend: &mut Backend, max_work| {
                    adapter
                        .execute_result(
                            backend,
                            &initial,
                            budget(),
                            ResultRun { modality, max_work },
                        )
                        .unwrap()
                };
                let unbounded = run(&mut backend, None);
                let work = unbounded.work();
                assert!(work >= 6, "{modality:?}: {work}");
                assert_eq!(halts(&unbounded).len(), 1);
                assert_eq!(halts(&unbounded)[0].0, HaltClass::Stuck);
                for budget_work in [work, work + 1] {
                    let bounded = run(&mut backend, Some(budget_work));
                    assert_eq!(halts(&bounded), halts(&unbounded), "{modality:?}");
                    assert_eq!(bounded.work(), work);
                }
                let stopped = run(&mut backend, Some(work - 1));
                assert_eq!(
                    stopped.leaves().last().map(|leaf| leaf.halt),
                    Some(HaltClass::WorkBound),
                    "{modality:?}"
                );
                assert!(!stopped.timed_out());
                let bridged = backend
                    .with_solver(None, |definition, solver| {
                        let decider = ObservationDecider::new(
                            definition,
                            solver,
                            TestInitialState::of_test(&initial),
                        );
                        Ok::<_, k_rust::backend::BackendError>(paths_from_execution_values(
                            &stopped,
                            &BridgeContext {
                                test_id: "count",
                                classify: &|_| ExecutionTerminalKind::Normal,
                                sorts: &sorts,
                            },
                            &|term| decider.terminal_value(term),
                        ))
                    })
                    .unwrap()
                    .unwrap();
                assert_eq!(bridged.collection.stop, CollectionStop::BackendLimit);
                let last = bridged.paths.last().unwrap();
                assert!(!last.complete);
                assert_eq!(last.stop, PathStop::BackendLimit);
                assert!(!last.stop.has_real_prefix());
                assert!(last.execution_terminal.is_none());
            }
            // A stepped run (never under a work budget) and a result run without one admit no
            // work-bound leaf.
            assert!(!HaltClass::WorkBound.adapter_admits(&budget()));
            assert!(HaltClass::WorkBound.admitted_by(&budget(), Some(1)));
        });
    }
}
