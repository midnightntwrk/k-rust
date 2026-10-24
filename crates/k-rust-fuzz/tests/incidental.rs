//! Incidental findings (FZ-INCIDENTAL): the report keeps the first `stuck` and the first
//! `undefined` case of any campaign, and leaves a report without such a case as it was.
//!
//! The tests read the report's canonical JSON, the form every client reads.

mod support;

use std::{collections::BTreeMap, sync::Arc};

use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl,
    HoleLocation, OutcomeClass, ProgramInput, ProposerConfig, SpanAddress, Target, TargetKind,
    Value,
    report::FuzzReport,
    spec::{DEFAULT_REJECTION_CAP, PathMode},
    target::{DifferentialTarget, PatternAt, PatternTarget},
    values::{Constraints, GenerationBounds, IntRange},
};
use num_bigint::BigInt;
use serde_json::Value as Json;
use support::{Fixture, IMP, IMP_ADD_COMMUTED, IMP_DIFF, IMP_DIV_GUARD_DROPPED};

const DIV: &str = "imp-diff/div.imp";

/// An `Int` hole on `literal` inside `find` of `program`, in `[0, 1000]` (DOGFOOD campaign 1).
fn int_hole(name: &str, program: &str, find: &str, literal: &str) -> HoleDecl {
    HoleDecl {
        name: name.into(),
        sort: "Int".into(),
        location: HoleLocation::Span(SpanAddress {
            program: program.into(),
            line: None,
            find: find.into(),
            literal: literal.into(),
        }),
        constraints: Constraints {
            range: Some(IntRange {
                min: Some(BigInt::from(0)),
                max: Some(BigInt::from(1000)),
            }),
            ..Constraints::default()
        },
        allow_refused_sort: false,
    }
}

/// DOGFOOD campaign 1 on `div.imp`: the pattern `q |-> Q requires Q >Int 50` on a natural end,
/// holes B (the 7) and C (the 3), blind after the anchors and `explicit`, max-work 10000.
fn c1(
    baseline: &'static Fixture,
    mutant: Option<&'static Fixture>,
    explicit: &[(i64, i64)],
) -> CampaignSpec {
    let definition = |fixture: &'static Fixture| Arc::new(fixture.compiled().definition());
    let target = match mutant {
        Some(_) => TargetKind::Differential(DifferentialTarget::default()),
        None => TargetKind::Pattern(PatternTarget {
            pattern:
                r#"<k> .K </k> <state> #token("q", "Id") |-> Q _M </state> requires Q >Int 50"#
                    .into(),
            at: PatternAt::Final,
        }),
    };
    CampaignSpec {
        definitions: Definitions {
            baseline: definition(baseline),
            mutant: mutant.map(definition),
        },
        program: ProgramInput::Source(baseline.compiled().program_source(DIV)),
        holes: vec![
            int_hole("B", DIV, "b = 7;", "7"),
            int_hole("C", DIV, "- 3;", "3"),
        ],
        target: Target {
            kind: target,
            run_to_completion: false,
            negated_property: false,
            data_end: true,
        },
        options: CaseOptions {
            max_work: Some(10_000),
            ..CaseOptions::default()
        },
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: explicit
                .iter()
                .map(|(b, c)| {
                    BTreeMap::from([
                        ("B".to_owned(), Value::Int(BigInt::from(*b))),
                        ("C".to_owned(), Value::Int(BigInt::from(*c))),
                    ])
                })
                .collect(),
            weights: ProposerConfig::default().weights,
        },
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 0x5eed,
        identity: CallerIdentity {
            k_rust_revision: "fz26-test".into(),
            thread_stack_size: None,
        },
    }
}

fn run(spec: CampaignSpec, cases: u64) -> (FuzzReport, Json) {
    let report = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(cases), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    let json = serde_json::from_str(&report.to_canonical_json()).expect("the report is JSON");
    (report, json)
}

/// The value of hole `name` in a finding, as its decimal text.
fn hole(finding: &Json, name: &str) -> String {
    finding["holes"]
        .as_array()
        .expect("holes")
        .iter()
        .find(|hole| hole["name"] == name)
        .unwrap_or_else(|| panic!("no hole {name} in {finding}"))["value"]["int"]
        .as_str()
        .expect("an Int value")
        .to_owned()
}

#[test]
fn the_imp_division_campaign_reports_its_undefined_case() {
    // DOGFOOD campaign 1 counted `undefined 1` for B = C and showed no values. On the tutorial
    // IMP without the division guard, `100 / 0` is an undefined step: the division rule applies
    // and `100 /Int 0` is undefined. The anchors (7, 3) miss, the explicit (5, 5) is case 1.
    let (report, json) = run(c1(&IMP_DIV_GUARD_DROPPED, None, &[(5, 5)]), 40);
    assert!(
        report.totals.classes.contains_key(&OutcomeClass::Undefined),
        "{:?}",
        report.totals.classes
    );
    let undefined = &json["incidental"]["undefined"];
    assert_eq!(undefined["case"], 1, "{json}");
    assert_eq!(
        (hole(undefined, "B"), hole(undefined, "C")),
        ("5".into(), "5".into())
    );
    assert_eq!(undefined["role"], "baseline");
    assert_eq!(undefined["k-head"], "100 / 0", "{undefined}");
    let krun = undefined["krun-command"].as_str().expect("a krun line");
    assert!(
        krun.contains("--strategy any") && krun.contains("b = 5;"),
        "{krun}"
    );
    assert_eq!(json["incidental"].get("stuck"), None);
    // The witness search is unchanged: B = 2, C = 1 style cases still hit.
    assert!(report.witness().is_some(), "{:?}", report.outcome);
}

#[test]
fn a_stuck_division_is_reported_with_its_k_head() {
    // On the tutorial IMP with the guard, `100 / 0` is an abnormal stop: no rule applies.
    let (report, json) = run(c1(&IMP_DIFF, None, &[(5, 5)]), 40);
    assert!(report.totals.classes.contains_key(&OutcomeClass::Stuck));
    let stuck = &json["incidental"]["stuck"];
    assert_eq!(stuck["case"], 1, "{json}");
    assert_eq!(stuck["k-head"], "100 / 0", "{stuck}");
    assert!(
        stuck["configuration"]
            .as_str()
            .is_some_and(|kore| kore.contains("Lbl'-LT-'k'-GT-'")),
        "{stuck}"
    );
    assert_eq!(json["incidental"].get("undefined"), None);
}

#[test]
fn a_campaign_without_such_cases_reports_no_finding() {
    // FZ-06's `le.imp` campaign: every case ends naturally, with `r` 0 or 1.
    let compiled = IMP.compiled();
    let program = "imp/le.imp";
    let spec = CampaignSpec {
        program: ProgramInput::Source(compiled.program_source(program)),
        definitions: Definitions {
            baseline: Arc::new(compiled.definition()),
            mutant: None,
        },
        holes: vec![
            int_hole("X", program, "x = 3;", "3"),
            int_hole("Y", program, "y = 5;", "5"),
        ],
        target: Target {
            kind: TargetKind::Pattern(PatternTarget {
                pattern:
                    r#"<k> .K </k> <state> #token("r", "Id") |-> R _M </state> requires R >Int 5"#
                        .into(),
                at: PatternAt::Final,
            }),
            run_to_completion: false,
            negated_property: false,
            data_end: true,
        },
        ..c1(&IMP_DIFF, None, &[])
    };
    let (report, json) = run(spec, 20);
    assert_eq!(
        report.totals.classes.keys().copied().collect::<Vec<_>>(),
        vec![OutcomeClass::Miss]
    );
    assert_eq!(json.get("incidental"), None, "{json}");
}

#[test]
fn a_differential_case_where_both_sides_stop_names_the_baseline() {
    // `add-commuted` agrees with the baseline everywhere: on B = C both stop at `100 / 0`, so
    // the case is `stuck`, not a kill, and the finding names the baseline's stop, with a krun
    // line on all paths (the baseline's mode).
    for paths in [PathMode::OnePath, PathMode::AllPaths] {
        let mut spec = c1(&IMP_DIFF, Some(&IMP_ADD_COMMUTED), &[(5, 5)]);
        spec.options.paths = paths;
        let (report, json) = run(spec, 4);
        assert_eq!(report.totals.classes.get(&OutcomeClass::Hit), None);
        let stuck = &json["incidental"]["stuck"];
        assert_eq!(stuck["case"], 1, "{paths:?}: {json}");
        assert_eq!(stuck["role"], "baseline");
        assert_eq!(stuck["k-head"], "100 / 0");
        let krun = stuck["krun-command"].as_str().expect("a krun line");
        assert!(krun.contains("--strategy all"), "{krun}");
    }
}
