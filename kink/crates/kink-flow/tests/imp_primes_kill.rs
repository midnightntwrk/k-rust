//! Re-pin L1-1-fix-1 (L1-1 STOP item 1, confirmed by L1-1 review 1): the IMP mutation
//! `and-false-returns-rhs` (`false && _ => false` becomes `false && B => B`) is killed by `primes`
//! only because its mutant run of `primes` finishes as a state set (about 20 ms) where the path set
//! of the same request did not finish within 120 s. The kill rests on re-pin decision 3 (k-rust's
//! state-set merge is correct; decisions log 2026-10-17, "L1-1 StateSet moves on IMP").
//!
//! This test pins today's verdict and the confirmation that does not need the merge premise:
//! - the baseline's `primes` path set is complete and clean, with exactly one distinct final
//!   configuration (`s = 2`), which is also its state set;
//! - one concrete path of the mutant (k-rust strategy `any`: one successor per step; a path set,
//!   no merge, no work budget) ends Stuck and clean outside that set (`s = 0`), and is the
//!   mutant's state set;
//! - so every path of the mutant ends outside the baseline's complete final set (IMP's only
//!   nondeterminism is the evaluation order of side-effect-free strict arguments), and the
//!   whole-term slot's Distinguish holds without the merge premise;
//! - the campaign runner over `primes` alone kills the mutant under `StateSet` and times out
//!   under `PathSet` (the manifest's 10 s bound).
//!
//! About 20 s (the path sets and the 10 s timeout): run on demand
//! (`cargo test -p kink-flow --test imp_primes_kill -- --ignored`).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::Duration;

use k_rust::backend::{
    BACKEND_SCHEMA_VERSION, Backend, CancelledResultOutput, ExecuteRequest, ExecutionStrategy,
    HaltReasonOutput, ResultModalityOutput,
};
use k_rust::kore::{ast::Pattern, codec};
use kink_campaign::{
    Campaign, CampaignOptions, MutantStatus, RunOptions, ScheduleMode, TestCase, run_campaign_with,
};
use kink_corpus::{admission::input_backend, runner::all_normal};
use kink_flow::{
    admit::admit,
    manifest::FlowManifest,
    mutation::{MutationList, resolve},
    results::{execution_budget, fixed_oracles},
};
use kink_native::execution::{
    AdaptedExecution, ExecutionAdapter, ExecutionBudget, HaltClass, ResultModality, ResultRun,
    SolverProfile,
};
use kink_patch::ClaimSupport;

fn imp() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/imp")
}

fn text(value: &serde_json::Value) -> String {
    codec::from_value(value)
        .map(|state: Pattern| state.to_string())
        .unwrap_or_else(|_| value.to_string())
}

/// The `s` binding of an IMP final configuration's text.
fn s_value(config: &str) -> String {
    let marker = "\\dv{SortId{}}(\"s\")), inj{SortInt{}, SortKItem{}}(\\dv{SortInt{}}(\"";
    let at = config.find(marker).expect("an s binding") + marker.len();
    config[at..at + config[at..].find('"').unwrap()].to_owned()
}

/// The final configurations of a complete, clean run.
fn complete_finals(label: &str, execution: &AdaptedExecution) -> BTreeSet<String> {
    assert!(!execution.timed_out(), "{label}: timed out");
    assert_eq!(execution.stack_stops(), 0, "{label}: stack stops");
    for leaf in execution.leaves() {
        assert_eq!(leaf.halt, HaltClass::Stuck, "{label}: halt");
        assert!(leaf.diagnostics.is_empty(), "{label}: diagnostics");
        assert!(leaf.contradicted_total.is_none(), "{label}: contradicted");
    }
    execution
        .leaves()
        .iter()
        .map(|leaf| text(&leaf.branch.state))
        .collect()
}

/// One concrete path of `state`: strategy `any`, a path set, no merge, no work budget.
fn single_path(backend: &mut Backend, state: &Pattern, budget: ExecutionBudget) -> String {
    let result = backend
        .execute(ExecuteRequest {
            state: state.clone(),
            module_name: None,
            max_depth: Some(100_000),
            max_breadth: None,
            max_simplification_iterations: budget.max_simplification_iterations,
            strategy: ExecutionStrategy::Any,
            stop_at_branch: false,
            cut_point_rules: Vec::new(),
            terminal_rules: Vec::new(),
            step_timeout_ms: None,
            moving_average_timeout: false,
            assume_state_defined: false,
            result_modality: ResultModalityOutput::PathSet,
            collect_coverage: false,
            collect_offered: false,
            collect_counts: false,
            collect_conditions: None,
            max_work: None,
            trace: false,
            cancelled_result: CancelledResultOutput::Error,
            match_states: None,
            collect_committed: false,
            schema_version: BACKEND_SCHEMA_VERSION,
        })
        .unwrap();
    assert_eq!(result.stack_stops, 0);
    let [leaf] = result.leaves.as_slice() else {
        panic!("one path: {} leaves", result.leaves.len());
    };
    assert_eq!(leaf.reason, HaltReasonOutput::Stuck);
    assert!(leaf.diagnostics.is_empty());
    assert!(leaf.contradicted_total.is_none());
    text(&leaf.state)
}

mod heavy {
    use super::*;

    #[test]
    // Formerly ignored as "about 20 s: run on demand, recorded in the L1-1-fix-1 handoff".
    #[ignore = "heavy"]
    fn and_false_returns_rhs_is_killed_by_primes_and_a_single_path_confirms_it() {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(confirm)
            .unwrap()
            .join()
            .unwrap();
    }
}

fn confirm() {
    let manifest = FlowManifest::read(&imp().join("FLOW.toml")).unwrap();
    let admission = admit(&manifest);
    let spec = admission.spec.as_ref().expect("IMP admitted");
    let primes = admission
        .programs
        .iter()
        .find(|program| program.id == "primes")
        .and_then(|program| program.outcome.as_ref().ok())
        .expect("primes admitted")
        .initial_state
        .clone();
    let mutation = MutationList::read(&imp().join("MUTATIONS.toml"))
        .unwrap()
        .mutations
        .into_iter()
        .find(|mutation| mutation.id == "and-false-returns-rhs")
        .unwrap();
    let mutation = resolve(&manifest, &spec.loaded, &mutation).unwrap();
    let baseline = spec.validator.baseline();
    // IMP declares no claim, so the claim-free mutant is the mutant as written.
    let withdrawal = ClaimSupport::new(baseline)
        .withdraw(baseline, &mutation.patch)
        .unwrap();
    assert!(withdrawal.trusted() && withdrawal.patch().is_none());
    let mutant = spec.validator.validate(&mutation.patch).unwrap();

    let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
    let budget = execution_budget(manifest.budget);
    let long = ExecutionBudget {
        time: Duration::from_secs(300),
        ..budget
    };
    let run = |backend: &mut Backend, modality| {
        adapter
            .execute_once(
                backend,
                &primes,
                long,
                ResultRun {
                    modality,
                    max_work: None,
                },
            )
            .unwrap()
    };
    let mut b_backend = input_backend(&spec.compiled, &manifest.spec.main_module).unwrap();
    let b_path_set = run(&mut b_backend, ResultModality::PathSet);
    let b_finals = complete_finals("baseline path set", &b_path_set);
    assert!(b_path_set.leaves().len() > 1, "the baseline's paths");
    assert_eq!(
        b_finals.iter().map(|c| s_value(c)).collect::<Vec<_>>(),
        ["2"],
        "one distinct baseline final"
    );
    let b_state_set = run(&mut b_backend, ResultModality::StateSet);
    assert_eq!(
        complete_finals("baseline state set", &b_state_set),
        b_finals
    );
    let b_path = single_path(&mut b_backend, &primes, budget);
    assert!(
        b_finals.contains(&b_path),
        "a baseline path ends in its set"
    );

    let mut m_backend = input_backend(&mutant, &manifest.spec.main_module).unwrap();
    let m_state_set = run(&mut m_backend, ResultModality::StateSet);
    let m_finals = complete_finals("mutant state set", &m_state_set);
    assert_eq!(
        m_finals.iter().map(|c| s_value(c)).collect::<Vec<_>>(),
        ["0"]
    );
    let m_path = single_path(&mut m_backend, &primes, budget);
    assert!(
        !b_finals.contains(&m_path),
        "the mutant's path ends outside the baseline's complete final set"
    );
    assert!(m_finals.contains(&m_path), "and in the mutant's state set");

    // The campaign runner over primes alone, under the manifest's budget.
    let tests = [TestCase {
        id: "primes".into(),
        initial_state: primes.clone(),
        oracles: fixed_oracles(),
    }];
    let module = k_rust::kast::identifier::encode(&manifest.spec.main_module);
    let campaign = Campaign {
        validator: &spec.validator,
        module: &module,
        observation: &[],
        classify: &all_normal,
        tests: &tests,
        budget,
    };
    let generation = mutation.generation(baseline).unwrap();
    let report = |result_modality| {
        let run = run_campaign_with(
            &campaign,
            &generation,
            &CampaignOptions {
                schedule: ScheduleMode::Full,
                selection: kink_campaign::SelectionPolicy::None,
                share_evidence: true,
                run: RunOptions {
                    result_modality,
                    ..RunOptions::default()
                },
                compile_workers: 1,
            },
        )
        .unwrap();
        let [mutant] = run.mutants.as_slice() else {
            panic!("one mutant");
        };
        (mutant.report.status, mutant.report.killing_test_ids.clone())
    };
    assert_eq!(
        report(ResultModality::StateSet),
        (MutantStatus::Killed, vec!["primes".to_owned()])
    );
    assert_eq!(
        report(ResultModality::PathSet),
        (MutantStatus::Timeout, Vec::new())
    );
}
