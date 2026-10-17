//! Re-pin R0c-fix-4 (`draft/tasks/repin-501f18b9`, R0c-fix-3 review 1): what an edit changes is
//! read from the compiled definitions, which k-rust executes, and kink-patch's source reading is
//! a fail-closed cross-check (kink-native `consistency::admit_mutant`). The fixtures are the
//! review's probes: a generated `#fun` lambda (`r0c/lamrule.k`, `r0c/lamfun.k`, control
//! `r0c/mapfun.k`) and a function rule written with configuration context (`r0c/cfgf.k`).

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::path::Path;
use std::time::Duration;

use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kore::ast::Pattern;
use kink_campaign::{
    Campaign, CrashPolicy, MutantRun, MutantScopeFailure, MutantStatus, OracleDeclaration,
    Projection, ScheduleMode, SideRun, StateProjection, TestCase, run_campaign,
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

/// The mutant is refused as inconsistent before any test runs, in both schedules alike, and its
/// report names exactly the pair `first`/`second` (either order).
fn assert_inconsistent(mutant: &MutantRun, first: &str, second: &str) {
    assert_eq!(mutant.report.status, MutantStatus::Invalid);
    assert_eq!(
        mutant.plan.mutant_failure,
        Some(MutantScopeFailure::InconsistentMutant)
    );
    assert!(mutant.plan.tests.is_empty() && mutant.evidence.is_empty());
    assert!(mutant.report.killing_test_ids.is_empty());
    let pairs = mutant
        .report
        .inconsistent_pairs
        .iter()
        .map(|pair| {
            let mut names = [pair.first.clone(), pair.second.clone()];
            names.sort();
            names
        })
        .collect::<Vec<_>>();
    let mut expected = [first.to_owned(), second.to_owned()];
    expected.sort();
    assert_eq!(pairs, [expected], "{:?}", mutant.report.inconsistent_pairs);
}

fn start() -> TestCase {
    test("start", support::app("Lblstart", vec![]))
}

/// The review's critical 1 (`r0c/lamrule.k`): the rewrite rule `go` holds
/// `#fun((_K |-> V) _R => V *Int 0)`, whose map pattern matches `(1 |-> 10) (2 |-> 20)` in two
/// ways. In the baseline both matchings give 0; the int-literal mutant 0 -> 1 makes the lambda
/// give 10 and 20 on one map, so it has no model. The source reading redefines nothing (a
/// rewrite rule), but the compiled lambda's equation differs, so its self pair is checked and the
/// mutant is refused. At 25e229e it was killed by `start` (mutant `val(10)`, baseline `val(0)`).
#[test]
fn a_lambda_in_a_rewrite_rule_is_read_from_the_compiled_definition() {
    on_a_big_stack(|| {
        let validator = validator("lamrule");
        let baseline = validator.baseline();
        let generation = literal(baseline, "LAMRULE.go", "0", "1");
        let tests = [start()];
        let campaign = campaign(&validator, "LAMRULE", &tests);
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let run = run_campaign(&campaign, &generation, schedule).unwrap();
            assert!(matches!(run.baseline[0].run, SideRun::Sides { .. }));
            assert_self_pair(&run.mutants[0], None);
        }
    });
}

/// The review's critical 1 (`r0c/lamfun.k`): the same lambda in the equation of `f`. The source
/// reading redefines `f`; the lambda is a generated symbol outside it, read from the compiled
/// diff. At 25e229e the mutant was killed by `start`.
#[test]
fn a_lambda_in_a_function_equation_is_read_from_the_compiled_definition() {
    on_a_big_stack(|| {
        let validator = validator("lamfun");
        let baseline = validator.baseline();
        let generation = literal(baseline, "LAMFUN.f", "0", "1");
        let tests = [start()];
        let campaign = campaign(&validator, "LAMFUN", &tests);
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let run = run_campaign(&campaign, &generation, schedule).unwrap();
            assert_self_pair(&run.mutants[0], None);
        }
    });
}

/// The control (`r0c/mapfun.k`): the map pattern as `f`'s own equation stays refused.
#[test]
fn a_map_pattern_equation_stays_refused() {
    on_a_big_stack(|| {
        let validator = validator("mapfun");
        let baseline = validator.baseline();
        let generation = literal(baseline, "MAPFUN.f", "0", "1");
        let tests = [start()];
        let campaign = campaign(&validator, "MAPFUN", &tests);
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let run = run_campaign(&campaign, &generation, schedule).unwrap();
            assert_self_pair(&run.mutants[0], Some("MAPFUN.f"));
        }
    });
}

/// An edit that changes no equation still runs: `start`'s map literal 10 -> 11 leaves every
/// compiled equation as it is (the lambda's included), so nothing is checked, and the mutant
/// survives (every matching still gives 0).
#[test]
fn an_edit_that_changes_no_equation_runs() {
    on_a_big_stack(|| {
        let validator = validator("lamrule");
        let baseline = validator.baseline();
        let generation = literal(baseline, "LAMRULE.start", "10", "11");
        let tests = [start()];
        let campaign = campaign(&validator, "LAMRULE", &tests);
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let run = run_campaign(&campaign, &generation, schedule).unwrap();
            let mutant = &run.mutants[0];
            assert_eq!(mutant.plan.mutant_failure, None, "{schedule:?}");
            assert!(mutant.report.inconsistent_pairs.is_empty());
            assert_eq!(mutant.report.status, MutantStatus::Survived, "{schedule:?}");
        }
    });
}

/// The review's critical 2 (`r0c/cfgf.k`): `rule [[ f(I) => 1 ]] <k> _ </k> requires I >=Int 0`
/// is an equation of `f`, which k-rust loads as `#withConfig(F, C)`; kink-patch now reads its head
/// through `#withConfig`. The guard mutants that make `fpos` and `fneg` overlap are refused, as on
/// `r0c/nomatch.k` (at 25e229e `fpos` 0 -> -5 was killed by `go(-1)` and `fneg` 0 -> 5 survived),
/// and the narrowing `fpos` 0 -> 5 withdraws `f`'s `total` (at 25e229e it was kept). The
/// narrowed pair `I >=Int 5` / `I <Int 0` is not refuted without a solver, so that mutant is
/// refused too, as `nomatch.k`'s.
#[test]
fn a_function_rule_with_configuration_context_is_an_equation_of_its_head() {
    on_a_big_stack(|| {
        let validator = validator("cfgf");
        let baseline = validator.baseline();
        let go = |i| support::app("Lblgo", vec![support::int(i)]);
        let chk = |i| support::app("Lblchk", vec![support::int(i)]);
        for (rule, from, to, tests) in [
            (
                "CFGF.fpos",
                "0",
                "-5",
                vec![test("gom1", go(-1)), test("chkm1", chk(-1))],
            ),
            (
                "CFGF.fneg",
                "0",
                "5",
                vec![test("go1", go(1)), test("go7", go(7))],
            ),
            (
                "CFGF.fpos",
                "0",
                "5",
                vec![test("go1", go(1)), test("chk1", chk(1))],
            ),
        ] {
            let generation = literal(baseline, rule, from, to);
            let campaign = campaign(&validator, "CFGF", &tests);
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let run = run_campaign(&campaign, &generation, schedule).unwrap();
                let mutant = &run.mutants[0];
                assert_eq!(
                    named(baseline, "CFGF", &mutant.report.claims.withdrawn),
                    [("f".to_owned(), "total".to_owned())],
                    "{rule} {to} {schedule:?}"
                );
                assert_inconsistent(mutant, "CFGF.fpos", "CFGF.fneg");
            }
        }
    });
}

/// `mutant` is refused as inconsistent for the self pair of one equation (a map pattern that
/// matches one subject in several ways, with a result that reads the choice): `equation`, or a
/// generated lambda's (`None`; it has no label or position, so it is named by its unique id).
fn assert_self_pair(mutant: &MutantRun, equation: Option<&str>) {
    assert_eq!(mutant.report.status, MutantStatus::Invalid);
    assert_eq!(
        mutant.plan.mutant_failure,
        Some(MutantScopeFailure::InconsistentMutant)
    );
    assert!(mutant.plan.tests.is_empty() && mutant.evidence.is_empty());
    assert!(mutant.report.killing_test_ids.is_empty());
    assert!(
        !mutant.report.inconsistent_pairs.is_empty()
            && mutant.report.inconsistent_pairs.iter().all(|pair| {
                equation.is_none_or(|equation| pair.first == equation)
                    && pair.second == pair.first
                    && pair.reason.contains("several ways")
            }),
        "{:?}",
        mutant.report.inconsistent_pairs
    );
}
