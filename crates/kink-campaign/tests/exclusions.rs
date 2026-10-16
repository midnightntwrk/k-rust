//! Re-pin R0b (`draft/tasks/repin-501f18b9`): campaigns over runs that are no evidence
//! (kink-native `exclusion`). A mutant whose run is excluded is `Unknown`, never killed, in both
//! schedules; a baseline whose run is excluded is refused before any mutant runs.

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

/// Re-pin R0c deliverable 3 (decision 2, mutant-wide): a theory whose claim is false on one input
/// has no model, so a kill by another test of the same mutant is vacuous. `TDIV.tdeq` with
/// `I +Int 0` distinguishes on `tdiv(1)` (`val(10)` against the baseline's `val(5)`) and
/// contradicts `td`'s `total` claim on `tdiv(0)`. Under `Full`, and under `FirstKill` when the
/// contradicting test runs first, the mutant is `Unknown`, never `Killed` (before R0c it was
/// killed by `tdiv(1)`). Under `FirstKill` with the killing test first the contradicting test
/// never runs and the kill stands: the documented early-stop residual
/// (`kink_campaign::contradicts_a_claim`).
#[test]
fn a_contradicted_claim_leaves_no_kill_standing() {
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
        for (tests, schedule, runs, status) in [
            (
                [kill(), contra()],
                ScheduleMode::Full,
                vec![distinguish.clone(), contradicted.clone()],
                MutantStatus::Unknown,
            ),
            (
                [contra(), kill()],
                ScheduleMode::FirstKill,
                vec![contradicted.clone(), distinguish.clone()],
                MutantStatus::Unknown,
            ),
            (
                [kill(), contra()],
                ScheduleMode::FirstKill,
                vec![distinguish.clone(), TestRun::SkippedAfterKill],
                MutantStatus::Killed,
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
            assert_eq!(mutant.report.status, status, "{ids:?} {schedule:?}");
            assert_eq!(
                mutant.report.killing_test_ids,
                if status == MutantStatus::Killed {
                    vec!["kill".to_owned()]
                } else {
                    Vec::new()
                },
                "{ids:?} {schedule:?}"
            );
        }
    });
}
