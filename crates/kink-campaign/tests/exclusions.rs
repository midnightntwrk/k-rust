//! Re-pin R0b (`draft/tasks/repin-501f18b9`): campaigns over runs that are no evidence
//! (kink-native `exclusion`). A mutant whose run is excluded is `Unknown`, never killed, in both
//! schedules; a baseline whose run is excluded is refused before any mutant runs, except one
//! that contradicts a claim, which makes only its own test unknown (re-pin R0c-fix-1).

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

/// Decision 2 (finding A-13): a mutant that makes `td`'s `total` claim false at the test's input
/// (k-rust names the contradicted claim), or `pd`'s `preserves-definedness` claim false, ends in
/// an undefined step where the baseline computes `val(10)`. Before R0b that undefined step was a
/// complete terminal and killed the mutant (`Distinguish` on both slots); now the mutant's run is
/// excluded and the mutant is `Unknown`, in both schedules.
#[test]
fn a_mutant_that_contradicts_a_claim_is_unknown() {
    on_a_big_stack(|| {
        let validator = validator("tdiv");
        let baseline = validator.baseline();
        for (rule, symbol) in [("TDIV.tdeq", "Lbltdiv"), ("TDIV.pd", "Lblpd")] {
            let generation = one_to_zero(baseline, rule);
            let tests = [test("t", support::app(symbol, vec![support::int(0)]))];
            let campaign = campaign(&validator, "TDIV", &tests);
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let run = run_campaign(&campaign, &generation, schedule).unwrap();
                let [mutant] = run.mutants.as_slice() else {
                    panic!("one mutant")
                };
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

/// The baseline side of each exclusion that a definition or a test's initial state carries:
/// decision 1's census (a rule listing a map's keys; an initial state applying `keys_list` over a
/// definition with no such rule) and finding C-10 (an equation or a simplification rooted at a
/// collection role symbol makes the List or Set terminal no value). Each baseline is refused as
/// `BaselineOracleFailed` before any mutant runs; before R0b each was admitted.
#[test]
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
            let failure = run_campaign(&campaign, &generation, ScheduleMode::Full).expect_err(name);
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
/// only"): `TDIV.tdeq` with `I +Int 0` distinguishes on `tdiv(1)` (`val(10)` against the
/// baseline's `val(5)`) and contradicts `td`'s `total` claim on `tdiv(0)`. The contradicting test
/// is unknown and the kill by `tdiv(1)` stands, in both orders and both schedules, so `Full` and
/// `FirstKill` agree (under R0c's mutant-wide rule `Full`, and `FirstKill` with the contradicting
/// test first, gave `Unknown`). The killing test is free of contradictions: both of its runs gave
/// sides, which an excluded run never does.
#[test]
fn a_contradicted_claim_leaves_the_kill_of_another_test_standing() {
    on_a_big_stack(|| {
        let validator = validator("tdiv");
        let baseline = validator.baseline();
        let generation = one_to_zero(baseline, "TDIV.tdeq");
        let kill = || test("kill", support::app("Lbltdiv", vec![support::int(1)]));
        let contra = || test("contra", support::app("Lbltdiv", vec![support::int(0)]));
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
            let campaign = campaign(&validator, "TDIV", &tests);
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

/// Re-pin R0c-fix-1 deliverable 1: a baseline run that contradicts a claim no longer refuses the
/// campaign; it makes its own test unknown for every mutant. The baseline `TDIV` contradicts
/// `td`'s `total` claim on `tdiv(-1)`. Under R0b and R0c the campaign was refused
/// (`BaselineOracleFailed`, `contradicted-claim`); now the mutant `tdeq` with `I +Int 0`, which is
/// defined on -1, is killed by `tdiv(1)`, whose runs are clean, and the contradicting test is
/// `Failed(ContradictedClaim)`, in both schedules.
#[test]
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

/// Re-pin R0c-fix-1 deliverable 1 (R0c review 1 major 1, the reviewer's `tdivloop` probe): a
/// contradiction inside a run that is also timed out is never a kill. On `both(0)` the mutant
/// `tdeq` with `I +Int 0` takes an undefined step that contradicts `td`'s `total` claim and spins
/// until the time bound: its run is timed out and one of its leaves names the contradicted claim
/// (read from the mutant's text, `r0c/tdivloopm.k`). The test is `Failed(TimeLimit)`, never
/// compared; with `tdiv(1)` beside it the mutant is killed by `tdiv(1)` alone, whose runs are
/// clean, in both schedules; alone it is `Timeout`.
#[test]
fn a_timed_out_run_with_a_contradiction_never_distinguishes() {
    use kink_native::execution::{ExecutionAdapter, SolverProfile};
    on_a_big_stack(|| {
        let both = || support::app("Lblboth", vec![support::int(0)]);
        let budget = ExecutionBudget {
            time: Duration::from_secs(3),
            max_simplification_iterations: 10_000,
            max_depth: None,
            max_breadth: None,
        };
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
        assert!(
            execution
                .leaves()
                .iter()
                .any(|leaf| leaf.contradicted_total.is_some()),
            "{execution:?}"
        );

        let validator = r0c_validator("tdivloop");
        let generation = one_to_zero(validator.baseline(), "TDIVLOOP.tdeq");
        let tests = [
            test("masked", both()),
            test("kill", support::app("Lbltdiv", vec![support::int(1)])),
        ];
        let mut both_tests = campaign(&validator, "TDIVLOOP", &tests);
        both_tests.budget = budget;
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
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
        let alone = [test("masked", both())];
        let mut masked = campaign(&validator, "TDIVLOOP", &alone);
        masked.budget = budget;
        let run = run_campaign(&masked, &generation, ScheduleMode::Full).unwrap();
        assert_eq!(run.mutants[0].report.status, MutantStatus::Timeout);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());
    });
}
