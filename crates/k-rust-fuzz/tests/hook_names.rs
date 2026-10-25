//! Reasons that name their hook (UNNAMED-HOOK, TRIAL3): an `unsupported` case whose reason rests
//! on a hook (a value the definition leaves open, an application k-rust does not evaluate) names
//! that hook where a reader sees the reason: `totals.unsupported-hooks`, the no-witness
//! statement, and a witness's `comparable.hooks`. And the pattern-body warning ("a misspelled
//! key?") counts only cases whose ends were judged against the pattern. Every campaign fixes its
//! seed.

mod support;

use std::sync::Arc;

use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl,
    HoleLocation, ProgramInput, ProposerConfig, SpanAddress, Target, TargetKind,
    report::FuzzReport,
    spec::{DEFAULT_REJECTION_CAP, PathMode},
    target::{PatternAt, PatternTarget, RuleMode, RuleRef, RuleTarget},
    values::{Constraints, GenerationBounds, IntRange},
};
use num_bigint::BigInt;
use serde_json::{Value as Json, json};
use support::{CHOSEN, Fixture, HOOKNAME};

/// An `Int` hole `N` at `literal` in `find` of `program`, over `min..=max`.
fn hole(program: &str, find: &str, literal: &str, (min, max): (i64, i64)) -> HoleDecl {
    HoleDecl {
        name: "N".into(),
        sort: "Int".into(),
        location: HoleLocation::Span(SpanAddress {
            program: program.into(),
            line: None,
            column: None,
            find: find.into(),
            literal: literal.into(),
        }),
        constraints: Constraints {
            range: Some(IntRange {
                min: Some(BigInt::from(min)),
                max: Some(BigInt::from(max)),
            }),
            ..Constraints::default()
        },
        allow_refused_sort: false,
    }
}

fn target(kind: TargetKind, comparable: bool) -> Target {
    Target {
        kind,
        run_to_completion: false,
        negated_property: false,
        data_end: true,
        comparable,
        query_confirmable: false,
    }
}

fn fired(label: &str) -> TargetKind {
    TargetKind::Rule(RuleTarget {
        rule: RuleRef::Label(label.into()),
        mode: RuleMode::Fired,
    })
}

fn final_pattern(pattern: &str) -> TargetKind {
    TargetKind::Pattern(PatternTarget {
        pattern: pattern.into(),
        at: PatternAt::Final,
    })
}

fn spec(
    fixture: &'static Fixture,
    program: &str,
    hole: HoleDecl,
    target: Target,
    paths: PathMode,
) -> CampaignSpec {
    let compiled = fixture.compiled();
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(compiled.definition()),
            mutant: None,
        },
        program: ProgramInput::Source(compiled.program_source(program)),
        holes: vec![hole],
        target,
        options: CaseOptions {
            paths,
            ..CaseOptions::default()
        },
        proposers: ProposerConfig::default(),
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 7,
        identity: CallerIdentity {
            k_rust_revision: "fz26-test".into(),
            thread_stack_size: None,
        },
    }
}

fn run(spec: CampaignSpec, cases: u64) -> FuzzReport {
    let report = Campaign::new(spec)
        .expect("the campaign is valid")
        .run(Budget::Cases(cases), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    report
}

/// The report as JSON, as it is written.
fn json(report: &FuzzReport) -> Json {
    serde_json::from_str(&report.to_canonical_json()).expect("a report is JSON")
}

fn statement(report: &FuzzReport) -> String {
    report
        .no_witness()
        .unwrap_or_else(|| panic!("no witness: {}", json(report)))
        .statement
        .clone()
}

/// The report's `unsupported` cases per reason, as JSON.
fn reasons(report: &FuzzReport) -> Json {
    json(report)["totals"]["unsupported-reasons"].clone()
}

/// CHOSEN's `listKeys(1, N)` lists the keys of a map of two keys for every N other than 1:
/// `MAP.keys_list` chooses their order (class `order`), so every end carries the mark and the
/// case is `unsupported` with `implementation-chosen-value` (KEVM's `store4` in TRIAL3). The
/// reason names the hook that read the value, in the totals and in the statement.
#[test]
fn an_implementation_chosen_value_names_the_hook_that_read_it() {
    let report = run(
        spec(
            &CHOSEN,
            "chosen/keys.pgm",
            hole("chosen/keys.pgm", "listKeys(1, 2)", "2", (2, 5)),
            target(final_pattern("<out> .List </out>"), false),
            PathMode::OnePath,
        ),
        4,
    );
    assert_eq!(
        reasons(&report),
        json!({"implementation-chosen-value": 4}),
        "{}",
        json(&report)
    );
    assert_eq!(
        json(&report)["totals"]["unsupported-hooks"],
        json!({"implementation-chosen-value": {"hooks": [{"hook": "MAP.keys_list", "class": "order"}]}})
    );
    let statement = statement(&report);
    assert!(
        statement.contains("4 implementation-chosen-value (hook MAP.keys_list [order])"),
        "{statement}"
    );
}

/// HOOKNAME's `pick(N)` for N of 33554432 or more: the `steer` path leaves `1 <<Int N`
/// unevaluated (`INT.shl`). Run on every path, the `plain` leaf that fires the target rests on a
/// run whose unsupported hook may have steered an equation (D21), so the case is `unsupported`
/// with `unsupported-hook` (WASM's trap cases in TRIAL3), and the reason names the hook.
#[test]
fn an_unsupported_hook_in_the_run_names_the_hook() {
    let report = run(
        spec(
            &HOOKNAME,
            "hookname/pick.pgm",
            hole(
                "hookname/pick.pgm",
                "pick(33554432)",
                "33554432",
                (33_554_432, 33_554_440),
            ),
            target(fired("plain"), false),
            PathMode::AllPaths,
        ),
        4,
    );
    assert_eq!(
        reasons(&report),
        json!({"unsupported-hook": 4}),
        "{}",
        json(&report)
    );
    assert_eq!(
        json(&report)["totals"]["unsupported-hooks"],
        json!({"unsupported-hook": {"hooks": [{"hook": "INT.shl"}]}})
    );
    let statement = statement(&report);
    assert!(
        statement.contains("4 unsupported-hook (hook INT.shl)"),
        "{statement}"
    );
}

/// On one path HOOKNAME's `pick(N)` follows `plain` and fires it cleanly; the program's run of
/// every path holds the unsupported `INT.shl`. Without `comparable-end` the witness's comparable
/// judgement names the hook beside the condition; with it, the refused hit's reason
/// `end-not-comparable:unsupported-hook` names it in the totals and the statement.
#[test]
fn a_hit_not_comparable_for_an_unsupported_hook_names_the_hook() {
    let campaign = |comparable| {
        spec(
            &HOOKNAME,
            "hookname/pick.pgm",
            hole(
                "hookname/pick.pgm",
                "pick(33554432)",
                "33554432",
                (33_554_432, 33_554_440),
            ),
            target(fired("plain"), comparable),
            PathMode::OnePath,
        )
    };
    let off = run(campaign(false), 4);
    assert_eq!(
        json(&off)["outcome"]["witness"]["first"]["comparable"],
        json!({
            "holds": false,
            "reasons": ["unsupported-hook"],
            "hooks": {"unsupported-hook": {"hooks": [{"hook": "INT.shl"}]}}
        }),
        "{}",
        json(&off)
    );
    let on = run(campaign(true), 4);
    assert_eq!(
        reasons(&on),
        json!({"end-not-comparable:unsupported-hook": 4}),
        "{}",
        json(&on)
    );
    assert_eq!(
        json(&on)["totals"]["unsupported-hooks"],
        json!({"end-not-comparable:unsupported-hook": {"hooks": [{"hook": "INT.shl"}]}})
    );
    let statement = statement(&on);
    assert!(
        statement.contains("4 end-not-comparable:unsupported-hook (hook INT.shl)"),
        "{statement}"
    );
}

/// The report's warnings about the pattern's body.
fn body_warnings(report: &FuzzReport) -> Vec<&String> {
    report
        .warnings
        .iter()
        .filter(|warning| warning.starts_with("pattern body:"))
        .collect()
}

/// When every case is `unsupported` (each end carries a chosen value, TRIAL3's `store4`), no
/// end was judged against the pattern, so nothing says the pattern names a configuration no end
/// holds: no "misspelled key?" warning. With one judged case beside two unjudged ones, the
/// warning counts the judged case only, and says why the others are not counted.
#[test]
fn the_pattern_body_warning_counts_only_cases_whose_ends_were_judged() {
    let campaign = |range| {
        spec(
            &CHOSEN,
            "chosen/keys.pgm",
            hole("chosen/keys.pgm", "listKeys(1, 2)", "2", range),
            target(final_pattern("<out> .List </out>"), false),
            PathMode::OnePath,
        )
    };
    let unjudged = run(campaign((2, 5)), 4);
    assert_eq!(
        reasons(&unjudged),
        json!({"implementation-chosen-value": 4})
    );
    assert_eq!(json(&unjudged)["totals"]["pattern-body-matches"], json!(0));
    assert!(
        body_warnings(&unjudged).is_empty(),
        "{:?}",
        unjudged.warnings
    );
    // N = 1 lists one key, with no mark: a clean end, judged (and not matched). The domain of
    // three values is exhausted after three cases.
    let mixed = run(campaign((1, 3)), 10);
    assert_eq!(reasons(&mixed), json!({"implementation-chosen-value": 2}));
    let warnings = body_warnings(&mixed);
    assert_eq!(warnings.len(), 1, "{:?}", mixed.warnings);
    assert!(
        warnings[0].contains("no end of the 1 executed case whose ends were judged matched")
            && warnings[0].contains("2 other executed cases had no end clean enough to judge"),
        "{}",
        warnings[0]
    );
}
