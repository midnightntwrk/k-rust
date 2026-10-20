//! The representative campaign set of flow F-01 (`representative/mod.rs`) in one pass, one test
//! per case (test-gate TG-C). Each case runs once in the reference configuration (evidence
//! sharing on, selection none, one compile worker) in Full and FirstKill, keeps what its original
//! test pins, and is compared with the variants of the three optimisations whose differential
//! tests walked the set separately until TG-C:
//!
//! - evidence sharing off (CS-10, formerly `dedup.rs`): equal complete runs and report bytes;
//! - 2 and 5 compile workers (re-pin L1-3 deliverable 3, formerly `compile_workers.rs`): equal
//!   complete runs, manifest bytes and report bytes; with 2 workers a chunk holds 8 candidates,
//!   so the larger cases span several chunks;
//! - Prioritize under both coupled rules (CS-07 Theorem 2, formerly `selection.rs`): every
//!   `none` status and score kept, the Full killing set equal and the FirstKill one non-empty
//!   iff it is under `none` and a subset of the Full one. A case that fires a wall-clock bound
//!   by design is run but not compared, as CS-07 excluded it.
//!
//! The kink tier runs every case against one variant ([`ROTATION`], every variant on some case
//! that runs in this profile), the timeout case's variant in Full only; the heavy tier runs every
//! case against every variant in both schedules.
//! `kink_tier::the_set_is_complete_and_the_rotation_covers_every_variant` checks the set's
//! [`representative::Coverage`] over the contributions the cases declare, and each case's test
//! checks that its Full run contributes exactly what it declares.
#[path = "../../../testdata/k/step_support.rs"]
mod step_support;
#[path = "../../../testdata/k/support.rs"]
mod support;

mod representative;

use std::collections::BTreeSet;

use kink_campaign::selection::{CompiledEdit, coverage_selected};
use kink_campaign::{
    Campaign, CampaignFailure, CampaignManifest, CampaignOptions, CampaignRun, Coupled,
    ManifestOperator, MultiManifestInput, OperatorId, RunOptions, ScheduleMode, Sel,
    SelectionPolicy, campaign_manifest_multi, campaign_report_multi, run_campaign_multi,
};
use kink_patch::CandidateGeneration;
use representative::{CASES, Case, Contribution, Expected};

/// A configuration compared with the reference one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Variant {
    SharingOff,
    Workers(usize),
    Prioritize(Coupled),
}

use Variant::{Prioritize, SharingOff, Workers};

const EVERY_VARIANT: [Variant; 5] = [
    SharingOff,
    Workers(2),
    Workers(5),
    Prioritize(Coupled::Union),
    Prioritize(Coupled::AllSites),
];

const SCHEDULES: [ScheduleMode; 2] = [ScheduleMode::Full, ScheduleMode::FirstKill];

fn with_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap();
}

fn options(
    schedule: ScheduleMode,
    selection: SelectionPolicy,
    share_evidence: bool,
    compile_workers: usize,
) -> CampaignOptions {
    CampaignOptions {
        schedule,
        selection,
        share_evidence,
        run: RunOptions::default(),
        compile_workers,
    }
}

/// The reference runs, Full first: sharing on, selection none, one compile worker.
fn reference(case: &Case<'_>) -> [Result<CampaignRun, CampaignFailure>; 2] {
    SCHEDULES.map(|schedule| {
        run_campaign_multi(
            &case.campaign,
            &case.generations,
            &options(schedule, SelectionPolicy::None, true, 1),
        )
    })
}

/// The case's manifest, with code operator declarations: candidate identities are unchanged,
/// and the report bytes check serialization as well as the complete typed evidence.
fn manifest(case: &Case<'_>, schedule: ScheduleMode) -> CampaignManifest {
    let operators = case
        .generations
        .iter()
        .map(|generation| {
            ManifestOperator::Code(OperatorId {
                id: generation
                    .candidates()
                    .first()
                    .map_or("empty", |c| &c.operator),
                version: 1,
                policy: kink_patch::SelectionPolicy::Each,
            })
        })
        .collect::<Vec<_>>();
    campaign_manifest_multi(&MultiManifestInput {
        campaign: &case.campaign,
        generations: &case.generations,
        schedule,
        selection: SelectionPolicy::None,
        operators: &operators,
        classifier: "representative-fixture",
        universe: None,
    })
    .expect("fixture manifest")
}

fn report(manifest: &CampaignManifest, case: &Case<'_>, run: &CampaignRun) -> String {
    campaign_report_multi(manifest, &case.campaign, &case.generations, run)
        .expect("report")
        .text()
}

/// Compares `variant` with the reference runs of `case`, in Full and FirstKill, or in Full only
/// when `once` and the case fires a wall-clock bound by design: it has one test case, so
/// FirstKill runs it as Full does and waits for the same bound again.
fn compare(
    case: &Case<'_>,
    reference: &[Result<CampaignRun, CampaignFailure>; 2],
    variant: Variant,
    once: bool,
) {
    let name = &case.name;
    let workers = match variant {
        SharingOff => 1,
        Workers(workers) => workers,
        Prioritize(coupled) => {
            if let [Ok(full), Ok(first)] = reference
                && !case.wall_clock_bound
            {
                cs07_check_theorem(
                    name,
                    &case.campaign,
                    &case.generations,
                    full,
                    first,
                    coupled,
                );
            }
            return;
        }
    };
    if workers > 1 && case.campaign.validator.compile_workers(2) < 2 {
        // Review L1-3-1 D3: one CPU, or a memory allowance too small for two workers.
        eprintln!(
            "this host allows one compile worker: every worker count runs the sequential path, \
             so the comparison is vacuous here"
        );
    }
    let schedules = if once && case.wall_clock_bound { 1 } else { 2 };
    for (schedule, reference) in SCHEDULES.iter().zip(reference).take(schedules) {
        let run = run_campaign_multi(
            &case.campaign,
            &case.generations,
            &options(
                *schedule,
                SelectionPolicy::None,
                variant != SharingOff,
                workers,
            ),
        );
        assert_eq!(
            &run, reference,
            "STOP: {name}: {variant:?} changed the complete run ({schedule:?})"
        );
        let Ok(reference) = reference else {
            continue;
        };
        let run = run.as_ref().expect("an admitted run");
        let mut used = manifest(case, *schedule);
        let expected = report(&used, case, reference);
        if variant != SharingOff {
            let again = manifest(case, *schedule);
            assert_eq!(
                again.text(),
                used.text(),
                "STOP: {name}: manifest bytes ({workers} workers, {schedule:?})"
            );
            used = again;
        }
        assert_eq!(
            report(&used, case, run),
            expected,
            "STOP: {name}: {variant:?} changed the report bytes ({schedule:?})"
        );
    }
}

/// Runs case `name` in the reference configuration, checks what its original pins and what it
/// contributes to the set's coverage, and compares it with every variant of `variants` (see
/// [`compare`] for `once`).
fn check(name: &'static str, variants: &'static [Variant], once: bool) {
    with_stack(move || {
        representative::representative_case(name, &mut |case| {
            eprintln!("TG_C_REPRESENTATIVE_CASE {name} {variants:?}");
            let reference = reference(case);
            representative::check_expected(case, &reference[0], &reference[1]);
            assert_eq!(
                Contribution::observed(case, &reference[0]),
                Contribution::declared(case),
                "{name}: the Full run contributes what the case declares"
            );
            for variant in variants {
                compare(case, &reference, *variant, once);
            }
        });
    });
}

// ---------------------------------------------------------------- CS-07 Theorem 2

/// Fails if a fixture fired a wall-clock bound: Theorem 2 assumes none fires.
fn cs07_no_time_bound(run: &CampaignRun) {
    use kink_campaign::{
        ExecutionFailureKind, MutantScopeFailure, OracleOutcome, OracleSide, SideRun, TestRun,
    };
    let evidence = run
        .baseline
        .iter()
        .chain(run.mutants.iter().flat_map(|mutant| mutant.evidence.iter()));
    for test in evidence {
        match &test.run {
            SideRun::Failed(ExecutionFailureKind::TimeLimit) => {
                panic!("CS07 STOP: fixture fired a wall-clock bound")
            }
            SideRun::Sides { sides } => assert!(
                !sides.contains(&OracleSide::Timeout),
                "CS07 STOP: fixture fired a wall-clock bound"
            ),
            SideRun::Failed(_) => {}
        }
    }
    for mutant in &run.mutants {
        assert_ne!(
            mutant.plan.mutant_failure,
            Some(MutantScopeFailure::LoweringTimeLimit),
            "CS07 STOP: lowering wall-clock bound"
        );
        for test in &mutant.plan.tests {
            match &test.run {
                TestRun::Failed(ExecutionFailureKind::TimeLimit) => {
                    panic!("CS07 STOP: fixture fired a wall-clock bound")
                }
                TestRun::Compared(outcomes) => assert!(
                    !outcomes.contains(&OracleOutcome::Timeout),
                    "CS07 STOP: fixture fired a wall-clock bound"
                ),
                _ => {}
            }
        }
    }
}

/// CS-07 Theorem 2 (README 5.4 as corrected) under one coupled rule: under Prioritize every
/// mutant keeps its `none` status and the score is unchanged; in Full its killing set is equal,
/// in FirstKill it is non-empty iff it is under `none` and a subset of the Full killing set.
fn cs07_check_theorem(
    name: &str,
    campaign: &Campaign<'_>,
    generations: &[CandidateGeneration<'_>],
    none_full: &CampaignRun,
    none_first: &CampaignRun,
    coupled: Coupled,
) {
    cs07_no_time_bound(none_full);
    cs07_no_time_bound(none_first);
    let policy = SelectionPolicy::Prioritize(Sel { coupled });
    for (schedule, none) in [
        (ScheduleMode::Full, none_full),
        (ScheduleMode::FirstKill, none_first),
    ] {
        let prioritized =
            run_campaign_multi(campaign, generations, &options(schedule, policy, true, 1))
                .expect("CS07 Theorem 2: an admitted none fixture stays admitted");
        cs07_no_time_bound(&prioritized);
        assert_eq!(
            none.mutants.len(),
            prioritized.mutants.len(),
            "{name}: candidate count"
        );
        assert_eq!(none.score, prioritized.score, "{name}: score");
        for ((original, mutant), full) in none
            .mutants
            .iter()
            .zip(&prioritized.mutants)
            .zip(&none_full.mutants)
        {
            if coupled == Coupled::Union && schedule == ScheduleMode::Full {
                let (selected, order) = if let Some(selection) = &mutant.plan.selection {
                    (
                        cs07_selected_count(campaign, generations, &prioritized, mutant, coupled),
                        selection.order.as_slice(),
                    )
                } else {
                    (0, &[][..])
                };
                eprintln!(
                    "CS07_FIXTURE {name} {} {:?} {coupled:?} {schedule:?} selected={}/{} order={:?} failure={:?}",
                    campaign.module,
                    mutant.report.mutant_id,
                    selected,
                    campaign.tests.len(),
                    order,
                    mutant.plan.mutant_failure
                );
            }
            assert_eq!(
                original.report.mutant_id, mutant.report.mutant_id,
                "{name}: candidate pairing"
            );
            assert_eq!(
                original.report.status, mutant.report.status,
                "{name}/{coupled:?}/{schedule:?}: Theorem 2 status"
            );
            let kills = mutant
                .report
                .killing_test_ids
                .iter()
                .collect::<BTreeSet<_>>();
            let original_kills = original
                .report
                .killing_test_ids
                .iter()
                .collect::<BTreeSet<_>>();
            let full_kills = full.report.killing_test_ids.iter().collect::<BTreeSet<_>>();
            if schedule == ScheduleMode::Full {
                assert_eq!(
                    original_kills, kills,
                    "{name}/{coupled:?}: Full killing set"
                );
            } else {
                assert_eq!(
                    original_kills.is_empty(),
                    kills.is_empty(),
                    "{name}/{coupled:?}: FirstKill existence"
                );
                assert!(
                    kills.is_subset(&full_kills),
                    "{name}/{coupled:?}: FirstKill killing subset"
                );
            }
        }
    }
}

/// How many tests coverage selects for `mutant` (all of them for a global edit or an
/// empty selection), recomputed from its compiled sides: the CS07_FIXTURE record.
fn cs07_selected_count(
    campaign: &Campaign<'_>,
    generations: &[CandidateGeneration<'_>],
    run: &CampaignRun,
    mutant: &kink_campaign::MutantRun,
    coupled: Coupled,
) -> usize {
    let selection = mutant.plan.selection.as_ref().expect("selection");
    if selection.global {
        return campaign.tests.len();
    }
    let baseline = campaign.validator.compile_baseline().expect("baseline");
    let authors = kink_native::coverage::RuleAuthors::of(&baseline);
    let patch = &generations
        .iter()
        .flat_map(CandidateGeneration::candidates)
        .nth(mutant.report.mutant_id.0)
        .expect("candidate")
        .patch;
    let patched = campaign.validator.validate(patch).expect("patched");
    let withdrawn = mutant
        .plan
        .claims
        .patch()
        .map(|patch| campaign.validator.validate(patch).expect("withdrawn"));
    let mut selected = 0;
    for test in campaign.tests {
        let side = if test.initial_state.variable_occurrences().is_empty() {
            &patched
        } else {
            withdrawn.as_ref().unwrap_or(&patched)
        };
        let edit = CompiledEdit::between(&baseline, side);
        let groups = patch
            .written_sentences()
            .iter()
            .map(|at| {
                authors
                    .ids_of(at)
                    .filter(|id| edit.removed_rule_ids.contains(*id))
                    .map(str::to_owned)
                    .collect::<BTreeSet<_>>()
            })
            .collect::<Vec<_>>();
        let coverage = run
            .baseline_coverage
            .iter()
            .find(|coverage| coverage.test_id == test.id)
            .expect("coverage");
        selected += usize::from(coverage_selected(coverage, &edit, coupled, &groups));
    }
    if selected == 0 {
        campaign.tests.len()
    } else {
        selected
    }
}

// ---------------------------------------------------------------- the tests

/// One test per case in the kink tier (the case against its variant of the rotation) and one
/// per case in the heavy tier (against every variant), and the rotation itself.
macro_rules! cases {
    ($($test:ident: $name:literal, $variant:expr;)*) => {
        /// Each case of the set and its kink-tier variant, in set order.
        const ROTATION: &[(&str, Variant)] = &[$(($name, $variant)),*];

        mod kink_tier {
            use super::*;

            $(
                #[test]
                #[ignore = "kink"]
                fn $test() {
                    check($name, &[$variant], true);
                }
            )*

            /// The set holds what F-01 deliverable 3 lists, over the contributions its cases
            /// declare (each case's test checks its Full run against its declaration), and the
            /// compile-worker comparison's minimum (two cases with several candidates, one
            /// candidate refused before any test); the rotation names every case once, in set
            /// order, gives every variant to a case that runs in this profile, sharing off and
            /// 2 workers to a case with several candidates, and never Prioritize to a case that
            /// fires a wall-clock bound by design.
            #[test]
            #[ignore = "kink"]
            fn the_set_is_complete_and_the_rotation_covers_every_variant() {
                with_stack(|| {
                    let mut coverage = representative::Coverage::default();
                    let mut order = Vec::new();
                    let mut compared = BTreeSet::new();
                    let mut workers_several = false;
                    let mut sharing_several = false;
                    representative::representative_set(&mut |case| {
                        order.push(case.name.clone());
                        let declared = Contribution::declared(case);
                        let (_, variant) = ROTATION
                            .iter()
                            .find(|(name, _)| *name == case.name)
                            .unwrap_or_else(|| panic!("{} has no variant", case.name));
                        if !matches!(case.expected, Expected::Refused(_))
                            && !(case.wall_clock_bound && matches!(variant, Prioritize(_)))
                        {
                            compared.insert(format!("{variant:?}"));
                        }
                        assert!(
                            !(case.wall_clock_bound && matches!(variant, Prioritize(_))),
                            "{}: CS-07 does not compare a wall-clock fixture",
                            case.name
                        );
                        workers_several |= *variant == Workers(2) && declared.several;
                        sharing_several |= *variant == SharingOff && declared.several;
                        coverage.record(case, declared);
                    });
                    coverage.assert_complete();
                    assert!(coverage.several >= 2, "two campaigns with several candidates");
                    assert!(coverage.refused, "a candidate refused before any test");
                    assert_eq!(order, CASES);
                    assert_eq!(
                        ROTATION.iter().map(|(name, _)| *name).collect::<Vec<_>>(),
                        CASES
                    );
                    assert_eq!(
                        compared,
                        EVERY_VARIANT
                            .iter()
                            .map(|variant| format!("{variant:?}"))
                            .collect::<BTreeSet<_>>(),
                        "every variant compared on a case that runs in this profile"
                    );
                    assert!(workers_several, "2 workers over several candidates");
                    assert!(
                        sharing_several,
                        "sharing off where later candidates could reuse evidence"
                    );
                });
            }
        }

        mod heavy {
            use super::*;

            $(
                #[test]
                #[ignore = "heavy"]
                fn $test() {
                    check($name, &EVERY_VARIANT, false);
                }
            )*
        }
    };
}

cases! {
    s1_whole: "S1 whole=true", SharingOff;
    k_whole: "K whole=true", Workers(5);
    s1_steps: "S1 whole=false", Workers(2);
    k_steps: "K whole=false", Prioritize(Coupled::Union);
    unknown_coherent_value: "Unknown: coherent value representation", Prioritize(Coupled::AllSites);
    unknown_coherent_value_ground: "Unknown: coherent value representation, ground test", SharingOff;
    c_row_1b_valued: "C row 1b: valued", Workers(2);
    c_row_1b_zero_valued: "C row 1b: zero valued", Workers(5);
    c_row_1b_guarded_name_swap: "C row 1b: guarded name swap", Prioritize(Coupled::Union);
    as7a_load_as_write: "AS7(a): load as write", Prioritize(Coupled::AllSites);
    g: "G", SharingOff;
    g_ground: "G: ground test", Workers(5);
    digit_audit: "digit audit", Workers(2);
    ei_d2_b: "EI-D2=b", Prioritize(Coupled::Union);
    invalid_killed_survived: "Invalid, Killed, Survived: counter final result", SharingOff;
    equivalent_clone: "Equivalent: anonymous clone", Prioritize(Coupled::AllSites);
    error_crash: "Error: crash against a normal result", Workers(5);
    multi_generation: "multi-generation: counter catalogue and code", Workers(2);
    timeout: "Timeout: nonterminating mutant", SharingOff;
}
