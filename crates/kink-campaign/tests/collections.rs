//! CS-16 C1-C4: natural ground collection terminals in both campaign schedules.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::{
    kast::{Sort, Term},
    kompile::{
        CompileOptions,
        initial_configuration::{ConfigurationAssembler, ConfigurationError, ProgramGrammar},
    },
    kore::ast::Pattern,
};
use kink_campaign::{
    Campaign, CampaignFailureKind, CrashPolicy, MutantStatus, OracleDeclaration, OracleOutcome,
    Projection, ScheduleMode, StateProjection, TestCase, TestRun, run_campaign,
};
use kink_native::{NativeValidator, execution::ExecutionBudget};
use kink_patch::{
    Baseline, Edit, Patch, SelectionPolicy, SiteSelector, TermRef, derive_sites, select,
};
use kink_pattern::ExecutionTerminalKind;
use std::{path::Path, time::Duration};

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

/// The same concrete-program assembly as kink-corpus's input.rs, without a dependency on it.
fn program(validator: &NativeValidator, syntax: &str, sort: &str, text: &str) -> Pattern {
    let compiled = validator.compile_baseline().unwrap();
    let definition = validator.baseline().definition();
    let grammar = ProgramGrammar::new(definition).unwrap();
    let mut assembler = ConfigurationAssembler::new(
        &grammar,
        &definition.main_module,
        syntax,
        &compiled.artifacts().configuration_variables,
    );
    assembler.program(&Sort::new(sort), text).unwrap();
    assembler
        .bind_stream_defaults::<ConfigurationError>(false, false, || Ok(Vec::new()))
        .unwrap();
    assembler.finish().unwrap()
}

/// Locate variables on rewrite right sides only: program pattern bindings remain unchanged.
fn rhs_variables(baseline: &Baseline, rule: &str, name: &str) -> Vec<TermRef> {
    fn walk(
        b: &Baseline,
        rule: &str,
        name: &str,
        path: &mut Vec<u32>,
        rhs: bool,
        out: &mut Vec<TermRef>,
    ) {
        let at = TermRef::new(support::rule(b, rule), path.as_slice());
        let Some(term) = b.term(&at) else { return };
        if rhs && matches!(term.unannotated(), Term::Variable { name: n, .. } if n == name) {
            out.push(at);
        }
        let rewrite = matches!(term.unannotated(), Term::Rewrite { .. });
        for index in 0.. {
            path.push(index);
            if b.term(&TermRef::new(support::rule(b, rule), path.as_slice()))
                .is_none()
            {
                path.pop();
                break;
            }
            walk(b, rule, name, path, rhs || (rewrite && index == 1), out);
            path.pop();
        }
    }
    let mut out = vec![];
    walk(baseline, rule, name, &mut vec![0], false, &mut out);
    out
}
fn int(n: i64) -> Term {
    Term::Token {
        token: n.to_string(),
        sort: Sort::new("Int"),
    }
}
fn replace(b: &Baseline, at: TermRef, replacement: Term) -> Edit {
    Edit::ReplaceTerm {
        expected: b.term(&at).unwrap().clone(),
        at,
        replacement,
    }
}

fn row(
    id: &str,
    file: &Path,
    main: &str,
    syntax_and_sort: (&str, &str),
    rule: &str,
    text: &str,
    expected: Option<(MutantStatus, Vec<OracleOutcome>)>,
) {
    let validator =
        NativeValidator::bind(support::load_path(file, main), CompileOptions::default());
    let baseline = validator.baseline();
    let edits = match id {
        "C1" | "C4" => {
            let name = if id == "C1" { "V" } else { "I" };
            let positions = rhs_variables(baseline, rule, name);
            let [at] = positions.as_slice() else {
                panic!("one RHS variable")
            };
            vec![replace(
                baseline,
                at.clone(),
                int(if id == "C1" { 7 } else { 2 }),
            )]
        }
        "C2" => [("K1", "K2"), ("K2", "K1"), ("V1", "V2"), ("V2", "V1")]
            .into_iter()
            .map(|(from, to)| {
                let positions = rhs_variables(baseline, rule, from);
                let [at] = positions.as_slice() else {
                    panic!("one RHS {from}")
                };
                let mut replacement = baseline.term(at).unwrap().unannotated().clone();
                let Term::Variable { name, .. } = &mut replacement else {
                    panic!("variable")
                };
                *name = to.into();
                replace(baseline, at.clone(), replacement)
            })
            .collect(),
        "C3" => vec![replace(
            baseline,
            TermRef::new(support::rule(baseline, rule), [1]),
            Term::Token {
                token: "false".into(),
                sort: Sort::new("Bool"),
            },
        )],
        _ => unreachable!(),
    };
    let patch = Patch::new(edits).unwrap();
    let discovery = derive_sites(
        baseline,
        id,
        &[
            SiteSelector::RuleLabel(rule.into()),
            SiteSelector::Path(vec![0]),
        ],
    )
    .unwrap();
    let generation = select(&discovery, SelectionPolicy::Each, 1)
        .unwrap()
        .fold(id, |_| patch.clone())
        .unwrap();
    assert_eq!(generation.candidates().len(), 1);
    // C4's baseline does not compile at 501f18b9 (E-06), so its program cannot be parsed through
    // the compiled grammar; its initial state is written as KORE instead.
    let initial_state = if expected.is_some() {
        program(&validator, syntax_and_sort.0, syntax_and_sort.1, text)
    } else {
        support::initial_state(support::app("Lblstart", vec![support::int(1)]), "SortProg")
    };
    let tests = [TestCase {
        id: id.into(),
        initial_state,
        oracles: oracles(),
    }];
    let module = k_rust::kast::identifier::encode(main);
    let campaign = Campaign {
        validator: &validator,
        module: &module,
        observation: &[],
        classify: &normal,
        tests: &tests,
        budget: ExecutionBudget {
            time: Duration::from_secs(60),
            max_simplification_iterations: 10_000,
            max_depth: Some(100),
            max_breadth: None,
        },
    };
    for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
        let result = run_campaign(&campaign, &generation, schedule);
        // Re-pin R0c (deliverable 8, decision 1 "keep, rewrite fixtures"): R0b refused C2 and
        // C3 (BaselineOracleFailed, implementation-chosen-hook) because collstore.k's `bytesKey`
        // rule built its key with `String2Bytes`, whose value domains.md leaves open. The rule
        // now uses `encodeBytes("UTF-8", S)` (domains.md:2012 names the encoding; k-rust
        // bytes.rs:116-130), so the census flags nothing and the rows are back to their R0a
        // values: C2 Survived [A, A], C3 Unknown [U, U]. Neither program reaches `bytesKey`.
        let Some((status, outcomes)) = &expected else {
            // Re-pin R0a (finding E-06; k-rust f07565265, 55a57846b, bc90d4226): at 927b9ce6 the
            // B1 baseline compiled and was refused by the baseline oracle (BaselineOracleFailed).
            // At 501f18b9 k-rust refuses the misfit list role at compilation, so the baseline is
            // invalid before any run: the refusal moved earlier (fail-closed).
            assert_eq!(
                result.expect_err("C4 B1 baseline refused").kind(),
                CampaignFailureKind::BaselineInvalid
            );
            let (stage, detail) = support::expected_compile_failure("b1coll.k").expect("listed");
            match validator.compile_baseline() {
                Err(kink_native::NativeFailure::Compilation {
                    stage: actual,
                    detail: text,
                }) => {
                    assert_eq!(actual, stage, "{text}");
                    assert!(
                        detail.iter().all(|fragment| text.contains(fragment)),
                        "{text}"
                    );
                }
                Ok(_) => panic!("C4 B1 baseline compiled"),
            }
            continue;
        };
        let run = result.unwrap();
        let [mutant] = run.mutants.as_slice() else {
            panic!("one mutant")
        };
        assert_eq!(mutant.report.status, *status, "{id} {schedule:?}");
        assert_eq!(
            mutant.plan.tests[0].run,
            TestRun::Compared(outcomes.clone()),
            "{id} {schedule:?}"
        );
        if *status == MutantStatus::Killed {
            assert_eq!(mutant.report.killing_test_ids, [id]);
        } else {
            assert!(mutant.report.killing_test_ids.is_empty());
        }
    }
}
#[test]
fn c1_c4_collection_campaign_rows() {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(|| {
            let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
            use OracleOutcome::{Agree as A, Distinguish as D, Unknown as U};
            row(
                "C1",
                &root.join("testdata/flow/map-store/map-store.k"),
                "MAP-STORE",
                ("MAP-STORE-SYNTAX", "Stmt"),
                "MAP-STORE.store",
                "store(1, 2)",
                Some((MutantStatus::Killed, vec![A, D])),
            );
            row(
                "C2",
                &root.join("testdata/k/collstore.k"),
                "COLLSTORE",
                ("COLLSTORE-SYNTAX", "Prog"),
                "COLLSTORE.putTwo",
                "putTwo(1, 10, 2, 20)",
                Some((MutantStatus::Survived, vec![A, A])),
            );
            row(
                "C3",
                &root.join("testdata/k/collstore.k"),
                "COLLSTORE",
                ("COLLSTORE-SYNTAX", "Prog"),
                "COLLSTORE.f0",
                "fKey(0)",
                Some((MutantStatus::Unknown, vec![U, U])),
            );
            row(
                "C4",
                &root.join("testdata/k/b1coll.k"),
                "B1COLL",
                ("B1COLL-SYNTAX", "Prog"),
                "B1COLL.start",
                "start(1)",
                None,
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
