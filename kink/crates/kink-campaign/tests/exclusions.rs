//! Re-pin R0b (`draft/tasks/repin-501f18b9`): campaigns over runs that are no evidence
//! (kink-native `exclusion`). A mutant whose run is excluded is `Unknown`, never killed, in both
//! schedules; a baseline whose run is excluded is refused before any mutant runs, except one
//! that contradicts a claim, which makes only its own test unknown (re-pin R0c-fix-1). Re-pin
//! adoption A-1 (`draft/tasks/repin-58720d2e/ADOPTION.md`): k-rust's run-level lists exclude a run
//! whose leaves are clean, and a baseline excluded by a record on its list alone is refused.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::path::Path;
use std::time::Duration;

use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kore::{ast::Pattern, parser::parse_pattern};
use kink_campaign::{
    Campaign, CampaignFailureKind, CrashPolicy, ExecutionFailureKind, MutantStatus,
    OracleDeclaration, Projection, ScheduleMode, StateProjection, TestCase, TestRun, run_campaign,
};
use kink_native::{NativeValidator, execution::ExecutionBudget};
use kink_patch::{
    Baseline, CandidateGeneration, Discovery, Edit, Patch, SelectionPolicy, SiteSelector, TermRef,
    derive_sites, select,
};
use kink_pattern::ExecutionTerminalKind;

fn oracles() -> Vec<OracleDeclaration> {
    [
        StateProjection::ExitStop {
            exit_code_cell: None,
        },
        StateProjection::WholeTerm,
    ]
    .into_iter()
    .map(|p| OracleDeclaration::new(CrashPolicy::Reject, Projection::State(p)).unwrap())
    .collect()
}

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

fn validator(name: &str) -> NativeValidator {
    NativeValidator::bind(
        support::load_path(
            &Path::new(support::DIR).join(format!("r0b/{name}.k")),
            &name.to_ascii_uppercase(),
        ),
        CompileOptions::default(),
    )
}

/// The validator of the R0c fixture `testdata/k/r0c/<name>.k` (its main module the upper-cased
/// name).
fn r0c_validator(name: &str) -> NativeValidator {
    NativeValidator::bind(
        support::load_path(
            &Path::new(support::DIR).join(format!("r0c/{name}.k")),
            &name.to_ascii_uppercase(),
        ),
        CompileOptions::default(),
    )
}

fn test(id: &str, program: Pattern) -> TestCase {
    TestCase {
        id: id.into(),
        initial_state: support::initial_state(program, "SortProg"),
        oracles: oracles(),
    }
}

fn campaign<'a>(
    validator: &'a NativeValidator,
    module: &'a str,
    tests: &'a [TestCase],
) -> Campaign<'a> {
    Campaign {
        validator,
        module,
        observation: &[],
        classify: &normal,
        tests,
        budget: ExecutionBudget {
            time: Duration::from_secs(60),
            max_simplification_iterations: 10_000,
            max_depth: Some(100),
            max_breadth: None,
        },
    }
}

/// The paths of every `Int` token `token` in the rule labelled `rule`.
fn tokens(baseline: &Baseline, rule: &str, token: &str) -> Vec<TermRef> {
    fn walk(
        b: &Baseline,
        at: kink_patch::SentenceRef,
        path: &mut Vec<u32>,
        token: &str,
        out: &mut Vec<TermRef>,
    ) {
        let here = TermRef::new(at.clone(), path.as_slice());
        let Some(term) = b.term(&here) else { return };
        if matches!(term.unannotated(), Term::Token { token: t, .. } if t == token) {
            out.push(here);
        }
        for index in 0.. {
            path.push(index);
            if b.term(&TermRef::new(at.clone(), path.as_slice())).is_none() {
                path.pop();
                break;
            }
            walk(b, at.clone(), path, token, out);
            path.pop();
        }
    }
    let mut out = Vec::new();
    walk(
        baseline,
        support::rule(baseline, rule),
        &mut vec![0],
        token,
        &mut out,
    );
    out
}

/// The one-candidate generation whose patch replaces the only `1` of `rule` by `0`.
fn one_to_zero<'b>(baseline: &'b Baseline, rule: &str) -> CandidateGeneration<'b> {
    let [at] = tokens(baseline, rule, "1")
        .try_into()
        .expect("one literal 1");
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).unwrap().clone(),
        at,
        replacement: Term::Token {
            token: "0".into(),
            sort: Sort::new("Int"),
        },
    }])
    .unwrap();
    let discovery = derive_sites(
        baseline,
        rule,
        &[
            SiteSelector::RuleLabel(rule.into()),
            SiteSelector::Path(vec![0]),
        ],
    )
    .unwrap();
    let generation = select(&discovery, SelectionPolicy::Each, 1)
        .unwrap()
        .fold(rule, |_| patch.clone())
        .unwrap();
    assert_eq!(generation.candidates().len(), 1);
    generation
}

fn no_mutant(baseline: &Baseline) -> CandidateGeneration<'_> {
    let generation = select(
        &Discovery::empty(baseline, false, false),
        SelectionPolicy::Each,
        1,
    )
    .unwrap()
    .fold("none", |_| -> Patch { unreachable!("no fold call") })
    .unwrap();
    assert!(generation.candidates().is_empty());
    generation
}

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// The killing test `id`'s baseline and mutant runs both gave sides: neither is excluded, so
/// neither has a leaf that contradicts a claim.
fn assert_clean(run: &kink_campaign::CampaignRun, mutant: &kink_campaign::MutantRun, id: &str) {
    let sides = |evidence: &[kink_campaign::TestEvidence]| {
        evidence
            .iter()
            .find(|evidence| evidence.test_id == id)
            .map(|evidence| matches!(evidence.run, kink_campaign::SideRun::Sides { .. }))
    };
    assert_eq!(sides(&run.baseline), Some(true), "{id}: baseline");
    assert_eq!(sides(&mutant.evidence), Some(true), "{id}: mutant");
}

/// Re-pin R0c-fix-1 deliverable 1 (R0c review 1 major 1, the reviewer's `tdivloop` probe): a
/// contradiction inside a run that is also timed out is never a kill. On `both(0)` the mutant
/// `tdeq` with `I +Int 0` takes an undefined step that contradicts `td`'s `total` claim and spins
/// until the time bound: its run is timed out and one of its leaves names the contradicted claim
/// (read from the mutant's text, `r0c/tdivloopm.k`). The test is `Failed(TimeLimit)`, never
/// compared; with `tdiv(1)` beside it the mutant is killed by `tdiv(1)` alone, whose runs are
/// clean, in both schedules; alone it is `Timeout`.
///
/// Each run waits for the 3 s bound, and the schedule does not change what the bound checks: the
/// kink tier runs the mutant's own run, the campaign in Full and the campaign alone
/// (`own_run_and_alone`), the heavy tier the campaign in FirstKill.
fn timed_out_contradiction(schedules: &'static [ScheduleMode], own_run_and_alone: bool) {
    use kink_native::execution::{ExecutionAdapter, SolverProfile};
    on_a_big_stack(move || {
        let both = || support::app("Lblboth", vec![support::int(0)]);
        let budget = ExecutionBudget {
            time: Duration::from_secs(3),
            max_simplification_iterations: 10_000,
            max_depth: None,
            max_breadth: None,
        };
        if own_run_and_alone {
            // The mutant's own run: timed out, with a contradicted leaf.
            let mutant = r0c_validator("tdivloopm").compile_baseline().unwrap();
            let mut backend = k_rust::backend::Backend::new(
                &mutant.artifacts().definition_kore,
                k_rust::kast::identifier::encode("TDIVLOOPM"),
                k_rust::backend::BackendOptions::default(),
            )
            .unwrap();
            let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
                .execute(
                    &mut backend,
                    &support::initial_state(both(), "SortProg"),
                    budget,
                )
                .unwrap();
            assert!(execution.timed_out());
            // Re-pin L1-1 (finding A-03): every request answers a cancellation with an error, so
            // the timed-out run publishes no leaf at all, the contradicted one included. Before,
            // under `cancelled_result: partial`, it returned the leaves finished before the
            // cancel, one of them naming the contradicted `total` claim; either way the run is
            // never compared.
            assert!(execution.leaves().is_empty(), "{execution:?}");
        }

        let validator = r0c_validator("tdivloop");
        let generation = one_to_zero(validator.baseline(), "TDIVLOOP.tdeq");
        let tests = [
            test("masked", both()),
            test("kill", support::app("Lbltdiv", vec![support::int(1)])),
        ];
        let mut both_tests = campaign(&validator, "TDIVLOOP", &tests);
        both_tests.budget = budget;
        for &schedule in schedules {
            let run = run_campaign(&both_tests, &generation, schedule).unwrap();
            let [mutant] = run.mutants.as_slice() else {
                panic!("one mutant")
            };
            assert_eq!(
                mutant.plan.tests[0].run,
                TestRun::Failed(ExecutionFailureKind::TimeLimit),
                "{schedule:?}"
            );
            assert!(
                matches!(&mutant.plan.tests[1].run, TestRun::Compared(outcomes)
                    if outcomes.contains(&kink_campaign::OracleOutcome::Distinguish)),
                "{schedule:?}"
            );
            assert_eq!(mutant.report.status, MutantStatus::Killed, "{schedule:?}");
            assert_eq!(mutant.report.killing_test_ids, vec!["kill".to_owned()]);
            assert_clean(&run, mutant, "kill");
        }
        if !own_run_and_alone {
            return;
        }
        let alone = [test("masked", both())];
        let mut masked = campaign(&validator, "TDIVLOOP", &alone);
        masked.budget = budget;
        let run = run_campaign(&masked, &generation, ScheduleMode::Full).unwrap();
        assert_eq!(run.mutants[0].report.status, MutantStatus::Timeout);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());
    });
}

/// The validator of the A-1 fixture `testdata/k/a1/<name>.k` (its main module the upper-cased
/// name; re-pin adoption A-1).
fn a1_validator(name: &str) -> NativeValidator {
    NativeValidator::bind(
        support::load_path(
            &Path::new(support::DIR).join(format!("a1/{name}.k")),
            &name.to_ascii_uppercase(),
        ),
        CompileOptions::default(),
    )
}

mod kink_tier {
    use super::*;

    #[test]
    #[ignore = "kink"]
    fn a_timed_out_run_with_a_contradiction_never_distinguishes() {
        timed_out_contradiction(&[ScheduleMode::Full], true);
    }

    /// Decision 2 (finding A-13): a mutant that contradicts a trusted claim at the test's input (k-rust
    /// names the contradicted `total`, or the undefined step's rule carries `preserves-definedness`)
    /// ends in an undefined step where the baseline computes a value. Before R0b that undefined step
    /// was a complete terminal and killed the mutant; now the mutant's run is excluded and the mutant
    /// is `Unknown`, in both schedules.
    ///
    /// Re-pin R0c-fix-2: a mutant now keeps only the claims its edit does not reach (kink-patch
    /// `ClaimSupport::withdraw`), so the guard fires for a baseline claim the mutant still carries.
    /// `r0c/tdivshift.k`'s mutants of the rewrite rules `tdiv` and `go` drop a shift and reach -1,
    /// where `td`'s `total` and `pd`'s `preserves-definedness` are false. The TDIV mutants this test
    /// used before (edits of `td`'s equation and of `pd`'s own rule) now run without the claim their
    /// edit falsified and are killed (`a_mutant_whose_edit_falsified_a_claim_runs_claim_free`).
    #[test]
    #[ignore = "kink"]
    fn a_mutant_that_contradicts_a_claim_is_unknown() {
        on_a_big_stack(|| {
            let validator = r0c_validator("tdivshift");
            let baseline = validator.baseline();
            for (rule, symbol) in [("TDIVSHIFT.tdiv", "Lbltdiv"), ("TDIVSHIFT.go", "Lblgo")] {
                let generation = one_to_zero(baseline, rule);
                let tests = [test("t", support::app(symbol, vec![support::int(-1)]))];
                let campaign = campaign(&validator, "TDIVSHIFT", &tests);
                for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                    let run = run_campaign(&campaign, &generation, schedule).unwrap();
                    let [mutant] = run.mutants.as_slice() else {
                        panic!("one mutant")
                    };
                    assert!(mutant.report.claims.withdrawn.is_empty(), "{rule}");
                    assert_eq!(
                        mutant.plan.tests[0].run,
                        TestRun::Failed(ExecutionFailureKind::ContradictedClaim),
                        "{rule} {schedule:?}"
                    );
                    assert_eq!(
                        mutant.report.status,
                        MutantStatus::Unknown,
                        "{rule} {schedule:?}"
                    );
                    assert!(mutant.report.killing_test_ids.is_empty());
                }
            }
        });
    }

    /// Re-pin R0c-fix-2 (a mutant drops the claims its edit leaves unbacked): the TDIV mutant of
    /// `td`'s equation (`I +Int 0`) runs without `td`'s `total`, and the mutant of `pd`'s own rule
    /// without its `preserves-definedness`. On 0 each takes an undefined step of the claim-free
    /// mutant (`10 /Int 0` is undefined in every model of it), where the baseline computes `val(10)`:
    /// a kill on a consistent theory, in both schedules. Before R0c-fix-2 each mutant carried the
    /// claim its edit falsified, contradicted it, and was `Unknown` (`contradicted-claim`).
    #[test]
    #[ignore = "kink"]
    fn a_mutant_whose_edit_falsified_a_claim_runs_claim_free() {
        on_a_big_stack(|| {
            let validator = validator("tdiv");
            let baseline = validator.baseline();
            for (rule, symbol, removed) in [
                ("TDIV.tdeq", "Lbltdiv", "total"),
                ("TDIV.pd", "Lblpd", "preserves-definedness"),
            ] {
                let generation = one_to_zero(baseline, rule);
                let tests = [test("t", support::app(symbol, vec![support::int(0)]))];
                let campaign = campaign(&validator, "TDIV", &tests);
                for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                    let run = run_campaign(&campaign, &generation, schedule).unwrap();
                    let [mutant] = run.mutants.as_slice() else {
                        panic!("one mutant")
                    };
                    assert_eq!(
                        mutant
                            .report
                            .claims
                            .withdrawn
                            .iter()
                            .map(|claim| claim.key.as_str())
                            .collect::<Vec<_>>(),
                        [removed],
                        "{rule}"
                    );
                    assert_eq!(
                        mutant.plan.tests[0].run,
                        TestRun::Compared(vec![
                            kink_campaign::OracleOutcome::Distinguish,
                            kink_campaign::OracleOutcome::Distinguish,
                        ]),
                        "{rule} {schedule:?}"
                    );
                    assert_eq!(
                        mutant.report.status,
                        MutantStatus::Killed,
                        "{rule} {schedule:?}"
                    );
                    assert_clean(&run, mutant, "t");
                }
            }
        });
    }

    /// The baseline side of each exclusion that a definition or a test's initial state carries:
    /// decision 1's census (a rule listing a map's keys; an initial state applying `keys_list` over a
    /// definition with no such rule) and finding C-10 (an equation or a simplification rooted at a
    /// collection role symbol makes the List or Set terminal no value). Each baseline is refused as
    /// `BaselineOracleFailed` before any mutant runs; before R0b each was admitted.
    #[test]
    #[ignore = "kink"]
    fn an_excluded_baseline_is_refused() {
        on_a_big_stack(|| {
            let keys = parse_pattern(
                r#"Lblkeys{}(Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")))))"#,
            )
            .unwrap();
            for (name, program, reason) in [
                (
                    "implchosen",
                    support::app("Lblstart", vec![support::int(1)]),
                    Some("implementation-chosen-hook"),
                ),
                ("keysfree", keys, Some("implementation-chosen-hook")),
                (
                    "rolerooted",
                    support::app("Lblstart", vec![support::int(5)]),
                    None,
                ),
                (
                    "rolesimp",
                    support::app("Lblstart", vec![support::int(5)]),
                    None,
                ),
            ] {
                let validator = validator(name);
                let module = name.to_ascii_uppercase();
                let tests = [test("t", program)];
                let campaign = campaign(&validator, &module, &tests);
                let generation = no_mutant(validator.baseline());
                let failure =
                    run_campaign(&campaign, &generation, ScheduleMode::Full).expect_err(name);
                assert_eq!(
                    failure.kind(),
                    CampaignFailureKind::BaselineOracleFailed,
                    "{name}"
                );
                if let Some(reason) = reason {
                    assert!(failure.to_string().contains(reason), "{name}: {failure}");
                }
            }
            // Control: the same initial-state shape without `keys_list` is admitted.
            let validator = validator("keysfree");
            let tests = [test("t", support::app("Lblstart", vec![support::int(1)]))];
            let campaign = campaign(&validator, "KEYSFREE", &tests);
            run_campaign(
                &campaign,
                &no_mutant(validator.baseline()),
                ScheduleMode::Full,
            )
            .expect("a definition that only imports MAP is admitted");
        });
    }

    /// Re-pin R0c-fix-1 deliverable 1 (decision 2 per test, Sebastien 2026-10-17: "killing test
    /// only"): the mutant distinguishes on `tdiv(1)` and contradicts `td`'s `total` claim on
    /// another input (since re-pin R0c-fix-2 `r0c/tdivshift.k`'s `tdiv` with `I +Int 0`, which keeps
    /// the claim: `val(5)` against the baseline's `val(3)` on 1, `td(-1)` on -1). The contradicting test
    /// is unknown and the kill by `tdiv(1)` stands, in both orders and both schedules, so `Full` and
    /// `FirstKill` agree (under R0c's mutant-wide rule `Full`, and `FirstKill` with the contradicting
    /// test first, gave `Unknown`). The killing test is free of contradictions: both of its runs gave
    /// sides, which an excluded run never does.
    #[test]
    #[ignore = "kink"]
    fn a_contradicted_claim_leaves_the_kill_of_another_test_standing() {
        on_a_big_stack(|| {
            // Re-pin R0c-fix-2: `r0c/tdivshift.k`'s mutant of the rewrite rule `tdiv` keeps `td`'s
            // `total` (its edit does not reach `td`) and contradicts it on tdiv(-1). Before, the TDIV
            // mutant of `td`'s equation contradicted it on tdiv(0); it now runs without the claim.
            let validator = r0c_validator("tdivshift");
            let baseline = validator.baseline();
            let generation = one_to_zero(baseline, "TDIVSHIFT.tdiv");
            let kill = || test("kill", support::app("Lbltdiv", vec![support::int(1)]));
            let contra = || test("contra", support::app("Lbltdiv", vec![support::int(-1)]));
            let distinguish = TestRun::Compared(vec![
                kink_campaign::OracleOutcome::Agree,
                kink_campaign::OracleOutcome::Distinguish,
            ]);
            let contradicted = TestRun::Failed(ExecutionFailureKind::ContradictedClaim);
            for (tests, schedule, runs) in [
                (
                    [kill(), contra()],
                    ScheduleMode::Full,
                    vec![distinguish.clone(), contradicted.clone()],
                ),
                (
                    [contra(), kill()],
                    ScheduleMode::Full,
                    vec![contradicted.clone(), distinguish.clone()],
                ),
                (
                    [contra(), kill()],
                    ScheduleMode::FirstKill,
                    vec![contradicted.clone(), distinguish.clone()],
                ),
                (
                    [kill(), contra()],
                    ScheduleMode::FirstKill,
                    vec![distinguish.clone(), TestRun::SkippedAfterKill],
                ),
            ] {
                let campaign = campaign(&validator, "TDIVSHIFT", &tests);
                let run = run_campaign(&campaign, &generation, schedule).unwrap();
                let [mutant] = run.mutants.as_slice() else {
                    panic!("one mutant")
                };
                let ids = tests.iter().map(|t| t.id.as_str()).collect::<Vec<_>>();
                assert_eq!(
                    mutant
                        .plan
                        .tests
                        .iter()
                        .map(|t| t.run.clone())
                        .collect::<Vec<_>>(),
                    runs,
                    "{ids:?} {schedule:?}"
                );
                assert_eq!(
                    mutant.report.status,
                    MutantStatus::Killed,
                    "{ids:?} {schedule:?}"
                );
                assert_eq!(
                    mutant.report.killing_test_ids,
                    vec!["kill".to_owned()],
                    "{ids:?} {schedule:?}"
                );
                assert_clean(&run, mutant, "kill");
            }
        });
    }

    /// Re-pin R0c-fix-1 deliverable 1: a baseline run that contradicts a claim no longer refuses the
    /// campaign; it makes its own test unknown for every mutant. The baseline `TDIV` contradicts
    /// `td`'s `total` claim on `tdiv(-1)`. Under R0b and R0c the campaign was refused
    /// (`BaselineOracleFailed`, `contradicted-claim`); now the mutant `tdeq` with `I +Int 0`, which is
    /// defined on -1, is killed by `tdiv(1)`, whose runs are clean, and the contradicting test is
    /// `Failed(ContradictedClaim)`, in both schedules.
    #[test]
    #[ignore = "kink"]
    fn a_contradicted_baseline_run_makes_only_its_test_unknown() {
        on_a_big_stack(|| {
            let validator = validator("tdiv");
            let baseline = validator.baseline();
            let generation = one_to_zero(baseline, "TDIV.tdeq");
            let tests = [
                test("base", support::app("Lbltdiv", vec![support::int(-1)])),
                test("kill", support::app("Lbltdiv", vec![support::int(1)])),
            ];
            let campaign_of_both = campaign(&validator, "TDIV", &tests);
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let run = run_campaign(&campaign_of_both, &generation, schedule).unwrap();
                assert_eq!(
                    run.baseline[0].run,
                    kink_campaign::SideRun::Failed(ExecutionFailureKind::ContradictedClaim)
                );
                let [mutant] = run.mutants.as_slice() else {
                    panic!("one mutant")
                };
                assert_eq!(
                    mutant.plan.tests[0].run,
                    TestRun::Failed(ExecutionFailureKind::ContradictedClaim),
                    "{schedule:?}"
                );
                assert_eq!(mutant.report.status, MutantStatus::Killed, "{schedule:?}");
                assert_eq!(mutant.report.killing_test_ids, vec!["kill".to_owned()]);
                assert_clean(&run, mutant, "kill");
            }
            // A campaign of the contradicting test alone is admitted, and its mutant is unknown.
            let alone = [test(
                "base",
                support::app("Lbltdiv", vec![support::int(-1)]),
            )];
            let run = run_campaign(
                &campaign(&validator, "TDIV", &alone),
                &generation,
                ScheduleMode::Full,
            )
            .unwrap();
            assert_eq!(run.mutants[0].report.status, MutantStatus::Unknown);
        });
    }

    /// Re-pin adoption A-1 (ADOPTION.md section 2.2, the README's former residual): the mutant
    /// `sobtd` with `X +Int 0` keeps `td`'s `total` (its edit does not reach `td`) and on `sob(0)`
    /// its candidate `val(td(0))` is undefined beside the defined sibling `sobok`, so its one leaf
    /// `done` is clean while the baseline gives `val(10)` and `done`. Only k-rust's list holds the
    /// record. Before A-1 kink read only the leaves, so the two sets differed and `sob(0)` killed the
    /// mutant on a claim that is false in the baseline too; now the test is
    /// `Failed(ContradictedClaim)` and the mutant `Unknown`, in both schedules. A kill by a test whose
    /// runs list no record (`sob(1)`: `val(10)` against the baseline's `val(5)`) stands.
    #[test]
    #[ignore = "kink"]
    fn a_record_on_the_mutant_run_list_alone_makes_its_test_unknown() {
        on_a_big_stack(|| {
            let validator = a1_validator("a1claims");
            let generation = one_to_zero(validator.baseline(), "A1CLAIMS.sobtd");
            let contradicted = TestRun::Failed(ExecutionFailureKind::ContradictedClaim);
            let alone = [test(
                "contra",
                support::app("Lblsob", vec![support::int(0)]),
            )];
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let run = run_campaign(
                    &campaign(&validator, "A1CLAIMS", &alone),
                    &generation,
                    schedule,
                )
                .unwrap();
                let [mutant] = run.mutants.as_slice() else {
                    panic!("one mutant")
                };
                assert!(mutant.report.claims.withdrawn.is_empty());
                assert_eq!(mutant.plan.tests[0].run, contradicted, "{schedule:?}");
                assert_eq!(mutant.report.status, MutantStatus::Unknown, "{schedule:?}");
                assert!(mutant.report.killing_test_ids.is_empty());
                // The record is carried as a note of the mutant's evidence; its baseline run is clean.
                assert_eq!(mutant.evidence[0].notes.contradicted_claims.len(), 1);
                assert!(!mutant.evidence[0].notes.leaf_contradiction);
                assert!(run.baseline[0].notes.contradicted_claims.is_empty());
            }
            let kill = || test("kill", support::app("Lblsob", vec![support::int(1)]));
            let contra = || test("contra", support::app("Lblsob", vec![support::int(0)]));
            for (tests, schedule) in [
                ([contra(), kill()], ScheduleMode::Full),
                ([contra(), kill()], ScheduleMode::FirstKill),
            ] {
                let run = run_campaign(
                    &campaign(&validator, "A1CLAIMS", &tests),
                    &generation,
                    schedule,
                )
                .unwrap();
                let [mutant] = run.mutants.as_slice() else {
                    panic!("one mutant")
                };
                assert_eq!(mutant.plan.tests[0].run, contradicted, "{schedule:?}");
                assert_eq!(mutant.report.status, MutantStatus::Killed, "{schedule:?}");
                assert_eq!(mutant.report.killing_test_ids, vec!["kill".to_owned()]);
                assert_clean(&run, mutant, "kill");
            }
        });
    }

    /// Re-pin adoption A-1: the mutant `rr` with `rq(I +Int 0)` keeps `td`'s `total`; on `rr(0)` it
    /// reaches `rq(0)`, whose condition `td(0) >Int 0` is undefined, read as false, and its stuck leaf
    /// carries the record (ADOPTION.md's `r(0)`, the README's former residual); the baseline reaches
    /// `rq(1)` and `done`. Before A-1 the leaf's diagnostic made the
    /// mutant's side unknown; now the test is `Failed(ContradictedClaim)`. The mutant is `Unknown`
    /// either way, in both schedules.
    #[test]
    #[ignore = "kink"]
    fn a_mutant_whose_condition_rests_on_a_record_is_unknown() {
        on_a_big_stack(|| {
            let validator = a1_validator("a1claims");
            let generation = one_to_zero(validator.baseline(), "A1CLAIMS.rr");
            let tests = [test("t", support::app("Lblrr", vec![support::int(0)]))];
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let run = run_campaign(
                    &campaign(&validator, "A1CLAIMS", &tests),
                    &generation,
                    schedule,
                )
                .unwrap();
                let [mutant] = run.mutants.as_slice() else {
                    panic!("one mutant")
                };
                assert_eq!(
                    mutant.plan.tests[0].run,
                    TestRun::Failed(ExecutionFailureKind::ContradictedClaim),
                    "{schedule:?}"
                );
                assert_eq!(mutant.report.status, MutantStatus::Unknown, "{schedule:?}");
            }
        });
    }

    /// Re-pin adoption A-1: a baseline run that one of k-rust's run-level lists excludes is refused
    /// before any mutant runs (`BaselineOracleFailed`, naming the exclusion), as every other excluded
    /// baseline is. A record on the list alone is not decision 2's leaf rule, so admission does not
    /// keep the baseline per test: before A-1 such a run was either compared (`sib(0)`, `m(0)`,
    /// `go(1)`, `run(2^40)`, `runh(1)`: their leaves are clean, so each was admitted) or, when its
    /// leaf carried the record, unknown and refused (`r(0)`, refused then for its unknown side, now
    /// for `contradicted-claim`); keeping it per test would relax the second refusal. The load record
    /// of `loadrec.k` is on every run's list (decision D-6), so no campaign over that definition is
    /// admitted. The controls `sib(1)` and `run(1)` are admitted, and so is `tv(0)`, whose undefined
    /// step names the contradicted claim on its leaf: that test alone is unknown (decision 2 per test).
    #[test]
    #[ignore = "kink"]
    fn a_baseline_whose_run_list_holds_an_entry_is_refused() {
        on_a_big_stack(|| {
            for (name, program, reason) in [
                (
                    "a1claims",
                    support::app("Lblsib", vec![support::int(0)]),
                    "contradicted-claim",
                ),
                (
                    "a1claims",
                    support::app("Lblm", vec![support::int(0)]),
                    "contradicted-claim",
                ),
                (
                    "a1claims",
                    support::app("Lblr", vec![support::int(0)]),
                    "contradicted-claim",
                ),
                (
                    "loadrec",
                    support::app("Lblgo", vec![support::int(1)]),
                    "contradicted-claim",
                ),
                (
                    "refusals",
                    support::app("Lblrun", vec![support::int(1 << 40)]),
                    "allowance-refusal",
                ),
                (
                    "refusals",
                    support::app("Lblrunh", vec![support::int(1)]),
                    "unsupported-hook",
                ),
            ] {
                let validator = a1_validator(name);
                let module = name.to_ascii_uppercase();
                let tests = [test("t", program)];
                let failure = run_campaign(
                    &campaign(&validator, &module, &tests),
                    &no_mutant(validator.baseline()),
                    ScheduleMode::Full,
                )
                .expect_err(name);
                assert_eq!(
                    failure.kind(),
                    CampaignFailureKind::BaselineOracleFailed,
                    "{name}"
                );
                assert!(
                    failure.to_string().contains(reason),
                    "{name} {reason}: {failure}"
                );
            }
            // The load record refuses a campaign whose mutant would otherwise be killed: `go` with
            // `I +Int 0` gives `val(1)` where the baseline gives `val(2)`.
            let validator = a1_validator("loadrec");
            let generation = one_to_zero(validator.baseline(), "LOADREC.go");
            let tests = [test("t", support::app("Lblgo", vec![support::int(1)]))];
            let failure = run_campaign(
                &campaign(&validator, "LOADREC", &tests),
                &generation,
                ScheduleMode::Full,
            )
            .expect_err("a load record refuses the baseline");
            assert_eq!(failure.kind(), CampaignFailureKind::BaselineOracleFailed);
            // Controls.
            for (name, program) in [
                ("a1claims", support::app("Lblsib", vec![support::int(1)])),
                ("refusals", support::app("Lblrun", vec![support::int(1)])),
            ] {
                let validator = a1_validator(name);
                let module = name.to_ascii_uppercase();
                let tests = [test("t", program)];
                run_campaign(
                    &campaign(&validator, &module, &tests),
                    &no_mutant(validator.baseline()),
                    ScheduleMode::Full,
                )
                .unwrap_or_else(|failure| panic!("{name}: {failure}"));
            }
            let validator = a1_validator("a1claims");
            let tests = [
                test("leaf", support::app("Lbltv", vec![support::int(0)])),
                test("clean", support::app("Lblsib", vec![support::int(1)])),
            ];
            let run = run_campaign(
                &campaign(&validator, "A1CLAIMS", &tests),
                &no_mutant(validator.baseline()),
                ScheduleMode::Full,
            )
            .expect("a leaf's contradiction makes only its test unknown");
            assert_eq!(
                run.baseline[0].run,
                kink_campaign::SideRun::Failed(ExecutionFailureKind::ContradictedClaim)
            );
            assert!(run.baseline[0].notes.leaf_contradiction);
            assert!(matches!(
                run.baseline[1].run,
                kink_campaign::SideRun::Sides { .. }
            ));
        });
    }

    /// A campaign over k-rust's fixtures `crates/k-rust-fuzz/tests/data/fresh/`: the baseline
    /// `<baseline>.k` (module `FRESH`), the one mutant that replaces its rule `FRESH.mk` by
    /// `<mutant>.k`'s, and the test `mk(3)`, whose configuration holds the `Int` cells `cells`
    /// after `<k>` and the counter 0. `check` gets the run of each schedule.
    fn fresh_campaign(
        baseline: &'static str,
        mutant: &'static str,
        cells: &'static [(&'static str, i64)],
        check: impl Fn(ScheduleMode, Result<kink_campaign::CampaignRun, kink_campaign::CampaignFailure>)
        + Send
        + 'static,
    ) {
        use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
        on_a_big_stack(move || {
            let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../../crates/k-rust-fuzz/tests/data/fresh");
            let validator = NativeValidator::bind(
                support::load_path(&fixture.join(format!("{baseline}.k")), "FRESH"),
                CompileOptions::default(),
            );
            let baseline = validator.baseline();
            let replacing = support::load_path(&fixture.join(format!("{mutant}.k")), "FRESH");
            let at = support::rule(baseline, "FRESH.mk");
            let mut replacement = replacing
                .sentence(&support::rule(&replacing, "FRESH.mk"))
                .expect("the replacing rule")
                .clone();
            *replacement.attributes_mut() = baseline.sentence(&at).unwrap().attributes().clone();
            let discovery = derive_sites(
                baseline,
                "FRESH.mk",
                &[
                    SiteSelector::RuleLabel("FRESH.mk".into()),
                    SiteSelector::Path(vec![0]),
                ],
            )
            .unwrap();
            let generation = select(&discovery, SelectionPolicy::Each, 1)
                .unwrap()
                .fold("replace", |_| {
                    Patch::new(vec![Edit::ReplaceSentence {
                        at: at.clone(),
                        replacement: replacement.clone(),
                    }])
                    .unwrap()
                })
                .unwrap();
            assert_eq!(generation.candidates().len(), 1);
            let cell = |name: &str, child: Pattern| {
                support::app(&format!("Lbl'-LT-'{name}'-GT-'"), vec![child])
            };
            let program = support::app(
                "Lblmk'LParUndsRParUnds'FRESH-SYNTAX'Unds'Pgm'Unds'Int",
                vec![support::int(3)],
            );
            let k = support::app(
                "kseq",
                vec![
                    kore_application(
                        "inj",
                        vec![kore_sort("SortPgm"), kore_sort("SortKItem")],
                        vec![program],
                    ),
                    support::app("dotk", Vec::new()),
                ],
            );
            let top = std::iter::once(cell("k", k))
                .chain(
                    cells
                        .iter()
                        .map(|&(name, value)| cell(name, support::int(value))),
                )
                .collect();
            let tests = [TestCase {
                id: "mk(3)".into(),
                initial_state: support::app(
                    "Lbl'-LT-'generatedTop'-GT-'",
                    vec![
                        support::app("Lbl'-LT-'T'-GT-'", top),
                        cell("generatedCounter", support::int(0)),
                    ],
                ),
                oracles: oracles(),
            }];
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                check(
                    schedule,
                    run_campaign(
                        &campaign(&validator, "FRESH", &tests),
                        &generation,
                        schedule,
                    ),
                );
            }
        });
    }

    /// The baseline run is no evidence: the campaign is refused before the mutant runs
    /// (`BaselineOracleFailed`, `implementation-chosen-value`).
    fn assert_baseline_refused(
        schedule: ScheduleMode,
        run: Result<kink_campaign::CampaignRun, kink_campaign::CampaignFailure>,
    ) {
        let failure = run.expect_err("the baseline run is no evidence");
        assert_eq!(
            failure.kind(),
            CampaignFailureKind::BaselineOracleFailed,
            "{schedule:?}"
        );
        assert!(
            failure.to_string().contains("implementation-chosen-value"),
            "{schedule:?}: {failure}"
        );
    }

    /// fz26 FZ-FRESH, K-REORDER: k-rust's fixture pair `crates/k-rust-fuzz/tests/data/fresh/`
    /// `base.k` and `mut.k` is one K rule, `<a> _ => !_A </a> <b> _ => !_B </b>`, written with its
    /// cells in the two orders. k-rust numbers the `!` names by first occurrence, so its baseline
    /// ends in `<a> 0 <b> 1` and the mutant in `<a> 1 <b> 0`; the definition leaves the association
    /// open, so no kill can rest on it. k-rust notes the step on the run's list (class
    /// `fresh-association`), which excludes the baseline run, so the campaign is refused before
    /// the mutant runs (`BaselineOracleFailed`, `implementation-chosen-value`), with no kink code.
    /// Before the mark the whole-term slot distinguished and the mutant was killed.
    #[test]
    #[ignore = "kink"]
    fn a_rule_reordered_with_two_fresh_names_is_never_killed() {
        fresh_campaign(
            "base",
            "mut",
            &[("a", 7), ("b", 7)],
            assert_baseline_refused,
        );
    }

    /// fz26 FZ-FRESH fix round (review B1): as K-REORDER, with a cell `<c> 2 </c>` that the rule
    /// matches as the literal 2 (`lit.k`, `litm.k`). Compilation then advances the counter by a
    /// variable bound to that 2 on the left-hand side, which k-rust reads through the binding: the
    /// step is marked all the same and the campaign is refused. Before the fix round the baseline
    /// was unmarked and the mutant killed.
    #[test]
    #[ignore = "kink"]
    fn a_reordered_rule_whose_left_hand_side_holds_its_advance_is_never_killed() {
        fresh_campaign(
            "lit",
            "litm",
            &[("c", 2), ("a", 7), ("b", 7)],
            assert_baseline_refused,
        );
    }

    /// fz26 FZ-FRESH fix round (review S1): the baseline `swap.k` writes the constants `<a> 1 <b> 0`
    /// and is unmarked; the mutant is `base.k`'s two-name rule, which k-rust's numbering ends in
    /// `<a> 0 <b> 1` and the other numbering in the baseline's end. The mutant's run is marked, so
    /// it is excluded: the test fails with `implementation-chosen-value` and the mutant is
    /// `Unknown`, never killed, in both schedules.
    #[test]
    #[ignore = "kink"]
    fn a_mutant_through_a_rule_with_two_fresh_names_is_never_killed() {
        fresh_campaign("swap", "base", &[("a", 7), ("b", 7)], |schedule, run| {
            let run = run.expect("the baseline is evidence");
            let [mutant] = run.mutants.as_slice() else {
                panic!("one mutant")
            };
            assert_eq!(
                mutant.plan.tests[0].run,
                TestRun::Failed(ExecutionFailureKind::ImplementationChosenValue),
                "{schedule:?}"
            );
            assert_eq!(mutant.report.status, MutantStatus::Unknown, "{schedule:?}");
            assert!(mutant.report.killing_test_ids.is_empty(), "{schedule:?}");
        });
    }

    /// fz26 FZ-FRESH, K-COUNTER: `fresh/counter.k`'s `go(N)` mints one value and discards it, and
    /// its mutant `mint(0)` mints none, so the ends differ only in the content of
    /// `<generatedCounter>` (1 against 0). Neither run uses a rule with two `!` names, so both are
    /// evidence. A whole-term slot compares terminals without the counter's content
    /// (`StateProjection::WholeTerm`): the mutant survives. A term-path slot that names the counter
    /// cell (`<generatedTop>`'s child 1) still reads it and kills, as documented. Before the
    /// erasure the whole-term slot killed.
    #[test]
    #[ignore = "kink"]
    fn a_difference_only_in_the_generated_counter_is_no_kill() {
        on_a_big_stack(|| {
            let validator = NativeValidator::bind(
                support::load_path(&Path::new(support::DIR).join("fresh/counter.k"), "COUNTER"),
                CompileOptions::default(),
            );
            let generation = one_to_zero(validator.baseline(), "COUNTER.go");
            let tests = [test("go(5)", support::app("Lblgo", vec![support::int(5)]))];
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let run = run_campaign(
                    &campaign(&validator, "COUNTER", &tests),
                    &generation,
                    schedule,
                )
                .unwrap();
                let [mutant] = run.mutants.as_slice() else {
                    panic!("one mutant")
                };
                assert_clean(&run, mutant, "go(5)");
                assert_eq!(
                    mutant.plan.tests[0].run,
                    TestRun::Compared(vec![
                        kink_campaign::OracleOutcome::Agree,
                        kink_campaign::OracleOutcome::Agree
                    ]),
                    "{schedule:?}"
                );
                assert_eq!(mutant.report.status, MutantStatus::Survived, "{schedule:?}");
            }
            let counter = [TestCase {
                oracles: vec![
                    OracleDeclaration::new(
                        CrashPolicy::Reject,
                        Projection::State(StateProjection::TermPaths(vec![vec![1]])),
                    )
                    .unwrap(),
                ],
                ..test("go(5)", support::app("Lblgo", vec![support::int(5)]))
            }];
            let run = run_campaign(
                &campaign(&validator, "COUNTER", &counter),
                &generation,
                ScheduleMode::Full,
            )
            .unwrap();
            assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
        });
    }
}

mod heavy {
    use super::*;

    /// `kink_tier::a_timed_out_run_with_a_contradiction_never_distinguishes` in FirstKill.
    #[test]
    #[ignore = "heavy"]
    fn a_timed_out_run_with_a_contradiction_never_distinguishes() {
        timed_out_contradiction(&[ScheduleMode::FirstKill], false);
    }
}
