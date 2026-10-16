//! Re-pin R0c-fix-2 (`draft/tasks/repin-501f18b9`; Sebastien 2026-10-17, decisions log "false
//! claims in mutants: remove unbacked claims"): kink builds every mutant without the trusted
//! claims its edit leaves unbacked (kink-patch `ClaimSupport::withdraw`), so the mutant is a
//! consistent theory k-rust executes without trusting them, and every test runs on it. The
//! baseline keeps its claims, a trusted premise, and the per-test contradicted-claim guard stays
//! the guard for them.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::path::Path;
use std::time::Duration;

use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kore::ast::Pattern;
use kink_campaign::{
    Campaign, CampaignFailureKind, CampaignRun, CrashPolicy, ExecutionFailureKind, MutantRun,
    MutantScopeFailure, MutantStatus, OracleDeclaration, OracleOutcome, Projection, ScheduleMode,
    SideRun, StateProjection, TestCase, TestEvidence, TestRun, run_campaign,
};
use kink_native::{NativeValidator, execution::ExecutionBudget};
use kink_patch::{
    Baseline, CandidateGeneration, Claim, Edit, Patch, SelectionPolicy, SentenceOrigin,
    SiteSelector, TermRef, derive_sites, select,
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

/// The validator of `testdata/k/r0c/<name>.k`, its main module the upper-cased name.
fn validator(name: &str) -> NativeValidator {
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

/// The paths of every `Int` token `token` in the body or condition of the rule labelled `rule`.
fn tokens(baseline: &Baseline, rule: &str, token: &str) -> Vec<TermRef> {
    fn walk(
        b: &Baseline,
        at: &kink_patch::SentenceRef,
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
            walk(b, at, path, token, out);
            path.pop();
        }
    }
    let mut out = Vec::new();
    // The body, then the condition.
    for root in [0, 1] {
        walk(
            baseline,
            &support::rule(baseline, rule),
            &mut vec![root],
            token,
            &mut out,
        );
    }
    out
}

/// The one-candidate generation whose patch replaces the only `Int` token `from` of the rule
/// labelled `rule` by `to`.
fn literal<'b>(
    baseline: &'b Baseline,
    rule: &str,
    from: &str,
    to: &str,
) -> CandidateGeneration<'b> {
    let [at] = tokens(baseline, rule, from)
        .try_into()
        .unwrap_or_else(|found: Vec<_>| panic!("one literal {from} in {rule}: {found:?}"));
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("a baseline term").clone(),
        at,
        replacement: Term::Token {
            token: to.into(),
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

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// Each claim by (production symbol or rule label without its module, key), for the main
/// module's sentences.
fn named(baseline: &Baseline, module: &str, claims: &[Claim]) -> Vec<(String, String)> {
    let mut names = claims
        .iter()
        .filter_map(|claim| match &claim.origin {
            SentenceOrigin::Baseline(at) if at.module.starts_with(module) => {
                let sentence = baseline.sentence(at).expect("a baseline sentence");
                let name = match sentence {
                    k_rust::definition::Sentence::Production {
                        label: Some(label), ..
                    } => label.name.clone(),
                    sentence => sentence
                        .attributes()
                        .string(k_rust::definition::AttributeKey::Label)
                        .map(|label| label.trim_start_matches(&format!("{module}.")).to_owned())
                        .expect("a labelled rule"),
                };
                Some((name, claim.key.clone()))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    names.sort();
    names
}

/// The test `id`'s baseline and mutant runs both gave sides: neither is excluded, so neither has
/// a leaf that contradicts a claim.
fn assert_clean(run: &CampaignRun, mutant: &MutantRun, id: &str) {
    let sides = |evidence: &[TestEvidence]| {
        evidence
            .iter()
            .find(|evidence| evidence.test_id == id)
            .map(|evidence| matches!(evidence.run, SideRun::Sides { .. }))
    };
    assert_eq!(sides(&run.baseline), Some(true), "{id}: baseline");
    assert_eq!(sides(&mutant.evidence), Some(true), "{id}: mutant");
}

fn pair(name: &str, key: &str) -> (String, String) {
    (name.to_owned(), key.to_owned())
}

/// Deliverable 5, the R0c-fix-1 review's critical probe (`r0c/tdcondb.k`, mutant `TDCONDB.tdeq`
/// with `I +Int 0`): the edit of `td`'s equation leaves `td`'s `total` unbacked, so the mutant
/// runs without it. On 0 the mutant's `td(0)` is `10 /Int 0`, undefined in every model of the
/// claim-free mutant, so `chk`'s condition is undefined and the rule does not apply (`chk(0)`
/// stuck), `cho` takes its `owise` rule (`no()`) and `k` its `owise` equation (`val(2)`), where
/// the baseline gives `yes()`, `yes()` and `val(1)`: each is killed by its own test, in both
/// schedules, on a consistent theory. Before R0c-fix-2 the same kills stood on the mutant that
/// still claimed `td` total, an inconsistent theory at 0 (the review's critical defect). `pr(0)`
/// (`td` in the right-hand side of the higher-priority rule) and `sb(0)` (beside a same-priority
/// sibling) are killed too: the claim-free mutant's step to `val(td(0))` is undefined, an
/// undefined step (`pr`) or a candidate k-rust drops beside its sibling's successor (`sb`), where
/// the baseline gives `val(10)`. Before, `pr(0)` was `Failed(ContradictedClaim)` (the mutant's
/// contradicted `total`) and `sb(0)` was killed on the inconsistent mutant.
#[test]
fn a_condition_through_a_claim_the_edit_falsified_kills_on_the_claim_free_mutant() {
    on_a_big_stack(|| {
        let validator = validator("tdcondb");
        let baseline = validator.baseline();
        let generation = literal(baseline, "TDCONDB.tdeq", "1", "0");
        for (id, symbol) in [
            ("chk0", "Lblchk"),
            ("cho0", "Lblcho"),
            ("kv0", "Lblkv"),
            ("pr0", "Lblpr"),
            ("sb0", "Lblsb"),
        ] {
            let tests = [test(id, support::app(symbol, vec![support::int(0)]))];
            let campaign = campaign(&validator, "TDCONDB", &tests);
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let run = run_campaign(&campaign, &generation, schedule).unwrap();
                let [mutant] = run.mutants.as_slice() else {
                    panic!("one mutant")
                };
                assert_eq!(
                    named(baseline, "TDCONDB", &mutant.report.claims.withdrawn),
                    [pair("td", "total")],
                    "{id} {schedule:?}"
                );
                assert!(mutant.report.claims.unsupported.is_empty());
                assert_eq!(mutant.plan.mutant_failure, None);
                assert!(
                    matches!(&mutant.plan.tests[0].run, TestRun::Compared(outcomes)
                        if outcomes.contains(&OracleOutcome::Distinguish)),
                    "{id} {schedule:?}: {:?}",
                    mutant.plan.tests
                );
                assert_eq!(
                    mutant.report.status,
                    MutantStatus::Killed,
                    "{id} {schedule:?}"
                );
                assert_eq!(mutant.report.killing_test_ids, vec![id.to_owned()]);
                assert_clean(&run, mutant, id);
            }
        }
    });
}

/// Deliverable 5 (transitive reach, `r0c/claimreach.k`): the mutant makes `f` partial at 0
/// (`10 /Int (I +Int 0)`); `g`'s equation applies `f` and `h`'s condition applies `g`, so the
/// claims of all three are removed, with `f`'s `smtlib`, the lemma about `f` (deleted) and the
/// `preserves-definedness` of `use`, whose condition applies `g`. `use(0)`'s condition is then
/// undefined and the rule does not apply, where the baseline halts: killed on the claim-free
/// mutant. `other(0)`, which rests on `k`, agrees.
#[test]
fn a_claim_that_reaches_the_edit_is_removed_transitively() {
    on_a_big_stack(|| {
        let validator = validator("claimreach");
        let baseline = validator.baseline();
        let generation = literal(baseline, "CLAIMREACH.f", "1", "0");
        let tests = [
            test("use0", support::app("Lbluse", vec![support::int(0)])),
            test("other0", support::app("Lblother", vec![support::int(1)])),
        ];
        let campaign = campaign(&validator, "CLAIMREACH", &tests);
        let run = run_campaign(&campaign, &generation, ScheduleMode::Full).unwrap();
        let [mutant] = run.mutants.as_slice() else {
            panic!("one mutant")
        };
        assert_eq!(
            named(baseline, "CLAIMREACH", &mutant.report.claims.withdrawn),
            [
                pair("f", "smtlib"),
                pair("f", "total"),
                pair("flemma", "simplification"),
                pair("g", "total"),
                pair("h", "total"),
                pair("use", "preserves-definedness"),
            ]
        );
        assert_eq!(mutant.report.status, MutantStatus::Killed);
        assert_eq!(mutant.report.killing_test_ids, vec!["use0".to_owned()]);
        assert_eq!(
            mutant.plan.tests[1].run,
            TestRun::Compared(vec![OracleOutcome::Agree, OracleOutcome::Agree])
        );
        assert_clean(&run, mutant, "use0");
    });
}

/// Deliverable 5: the per-test contradicted-claim guard stays the guard for the baseline's own
/// claims. The baseline `r0c/tdcond.k` claims `td` total although `td(0)` is `10 /Int 0`; the
/// mutant edits the rewrite rule `chk` (`>Int 0` to `>Int 1`), which redefines no symbol, so
/// `td`'s claim is not the edit's to remove and the mutant keeps it (nothing is withdrawn). On
/// `pr(0)` (`td` in a right-hand side) both runs contradict it: the baseline run is
/// `Failed(ContradictedClaim)` and the test is unknown for the mutant, in both schedules; `iv(1)`
/// agrees.
#[test]
fn the_contradicted_claim_guard_still_fires_for_a_baseline_claim() {
    on_a_big_stack(|| {
        let validator = validator("tdcond");
        let baseline = validator.baseline();
        let generation = literal(baseline, "TDCOND.chk", "0", "1");
        let tests = [
            test("pr0", support::app("Lblpr", vec![support::int(0)])),
            test("iv1", support::app("Lbliv", vec![support::int(1)])),
        ];
        let campaign = campaign(&validator, "TDCOND", &tests);
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let run = run_campaign(&campaign, &generation, schedule).unwrap();
            assert_eq!(
                run.baseline[0].run,
                SideRun::Failed(ExecutionFailureKind::ContradictedClaim)
            );
            let [mutant] = run.mutants.as_slice() else {
                panic!("one mutant")
            };
            assert_eq!(mutant.report.claims, kink_patch::Withdrawal::default());
            assert_eq!(
                mutant.plan.tests[0].run,
                TestRun::Failed(ExecutionFailureKind::ContradictedClaim),
                "{schedule:?}"
            );
            assert_eq!(mutant.report.status, MutantStatus::Unknown, "{schedule:?}");
        }
    });
}

/// Deliverable 6 (R0c-fix-1 review major, `r0c/scsib.k`): `siba`'s right-hand side applies
/// `andBool` over `10 /Int (I -Int 1) >Int 0`, which may be undefined, beside the same-priority
/// sibling `sibb`. On `sib(1)` k-rust drops `siba`'s undefined candidate and keeps `other()`,
/// where a short-circuiting backend also gives `res(false)`, so the static exclusion excludes the
/// definition and the baseline is refused (`short-circuit-reading`). Before R0c-fix-2 the mutant
/// `siba` with `I -Int 0` was killed by `sib(1)` in both schedules (baseline `{other()}`, mutant
/// `{res(false), other()}`).
#[test]
fn a_short_circuit_beside_a_same_priority_sibling_is_excluded() {
    on_a_big_stack(|| {
        let validator = validator("scsib");
        let baseline = validator.baseline();
        let generation = literal(baseline, "SCSIB.siba", "1", "0");
        let tests = [test("sib1", support::app("Lblsib", vec![support::int(1)]))];
        let campaign = campaign(&validator, "SCSIB", &tests);
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let failure = run_campaign(&campaign, &generation, schedule).expect_err("refused");
            assert_eq!(failure.kind(), CampaignFailureKind::BaselineOracleFailed);
            assert!(
                failure.to_string().contains("short-circuit-reading"),
                "{failure}"
            );
        }
    });
}

/// Deliverable 3: a mutant with no claim-free definition is unknown, never killed.
#[test]
fn a_refused_claim_free_mutant_is_unknown() {
    for failure in [
        MutantScopeFailure::UnsupportedClaims,
        MutantScopeFailure::StrippedClaimCompileFailure,
    ] {
        assert_eq!(failure.status(), MutantStatus::Unknown);
    }
}
