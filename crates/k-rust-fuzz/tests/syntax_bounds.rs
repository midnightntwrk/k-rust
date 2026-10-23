//! Integer holes draw only values the program's syntax can hold at the hole (FZ-INTGEN).
//!
//! UNSIGNED's literals are unsigned, so `-5` written at a literal reads as the negation
//! `neg(5)`, not the value -5, and every case with a negative value at a span hole is
//! `rejected`. The campaign probes each such hole once and generates from 0; IMP's literals
//! are signed, so its holes keep negative values.

mod support;

use std::{collections::BTreeMap, sync::Arc};

use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignError, CampaignSpec, CaseOptions, Definitions,
    HoleDecl, HoleLocation, OutcomeClass, ProgramInput, ProposerConfig, SpanAddress, Target,
    TargetKind, Value,
    report::FuzzReport,
    spec::DEFAULT_REJECTION_CAP,
    target::{PatternAt, PatternTarget},
    values::{Constraints, GenerationBounds, IntRange},
};
use num_bigint::BigInt;
use support::{Fixture, IMP, UNSIGNED};

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
        constraints: Constraints::default(),
        allow_refused_sort: false,
    }
}

fn spec(
    fixture: &'static Fixture,
    program: &str,
    holes: Vec<HoleDecl>,
    pattern: &str,
    proposers: ProposerConfig,
) -> CampaignSpec {
    let compiled = fixture.compiled();
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(compiled.definition()),
            mutant: None,
        },
        program: ProgramInput::Source(compiled.program_source(program)),
        holes,
        target: Target {
            kind: TargetKind::Pattern(PatternTarget {
                pattern: pattern.into(),
                at: PatternAt::Final,
            }),
            run_to_completion: false,
            negated_property: false,
        },
        options: CaseOptions::default(),
        proposers,
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 0x1a7e,
        identity: CallerIdentity {
            k_rust_revision: "fz26-intgen".into(),
            thread_stack_size: None,
        },
    }
}

/// UNSIGNED's `print 7 + B ;` with an unconstrained `Int` hole `B`, and a target no value
/// within the default bounds reaches, so the campaign spends its whole budget.
fn unsigned_campaign() -> CampaignSpec {
    spec(
        &UNSIGNED,
        "unsigned/sum.pgm",
        vec![int_hole("B", "unsigned/sum.pgm", "+ 5", "5")],
        "<out> ListItem(N:Int) </out> requires N ==Int 0 -Int 7",
        ProposerConfig::default(),
    )
}

fn run(spec: CampaignSpec, cases: u64) -> FuzzReport {
    Campaign::new(spec)
        .expect("the campaign is valid")
        .run(Budget::Cases(cases), None)
}

#[test]
fn an_unconstrained_int_hole_at_an_unsigned_literal_rejects_no_case() {
    let report = run(unsigned_campaign(), 200);
    assert_eq!(report.totals.cases, 200);
    // Before narrowing about half the blind draws were negative, each one `rejected` by the
    // round-trip check.
    assert_eq!(
        report.totals.classes.get(&OutcomeClass::Rejected),
        None,
        "{:?}",
        report.totals.rejections
    );
    assert!(report.totals.rejections.is_empty());
}

#[test]
fn the_report_records_the_effective_constraints_and_warns() {
    let report = run(unsigned_campaign(), 20);
    let [narrowed] = report.identity.effective_constraints.as_slice() else {
        panic!(
            "one narrowed hole: {:?}",
            report.identity.effective_constraints
        );
    };
    assert_eq!(narrowed.hole, "B");
    assert_eq!(narrowed.declared, Constraints::default());
    assert_eq!(
        narrowed.effective.range,
        Some(IntRange {
            min: Some(BigInt::from(0)),
            max: None,
        })
    );
    assert!(narrowed.reason.contains("`-1`"), "{}", narrowed.reason);
    assert!(
        report
            .warnings
            .iter()
            .any(|warning| warning.starts_with("hole `B`: values are generated from 0")),
        "{:?}",
        report.warnings
    );
    // The field reads back.
    let json = report.to_canonical_json();
    assert!(
        json.contains(r#""effective-constraints":[{"hole":"B""#),
        "{json}"
    );
    assert_eq!(FuzzReport::from_json(&json).expect("reads back"), report);
}

#[test]
fn signed_literals_keep_negative_values() {
    // IMP's `x = 3;`: a final state with a negative `x` needs a negative value at the hole.
    let report = run(
        spec(
            &IMP,
            "imp/le.imp",
            vec![int_hole("X", "imp/le.imp", "x = 3;", "3")],
            r#"<k> .K </k> <state> (#token("x", "Id") |-> X:Int) _:Map </state> requires X <Int 0"#,
            ProposerConfig::default(),
        ),
        200,
    );
    assert!(report.identity.effective_constraints.is_empty());
    assert!(report.witness().is_some(), "{:?}", report.outcome);
}

#[test]
fn an_explicit_negative_value_is_still_judged_by_the_round_trip() {
    // The declared constraints admit -3, so the explicit assignment is accepted; the case is
    // rejected by the round-trip check, not by the narrowed bounds.
    let proposers = ProposerConfig {
        anchors_first: false,
        explicit: vec![BTreeMap::from([(
            "B".to_owned(),
            Value::Int(BigInt::from(-3)),
        )])],
        weights: BTreeMap::new(),
    };
    let mut spec = unsigned_campaign();
    spec.proposers = proposers;
    let report = run(spec, 1);
    assert_eq!(report.totals.cases, 1);
    assert_eq!(
        report
            .totals
            .rejections
            .get(&k_rust_fuzz::report::RejectionReason::RoundTrip),
        Some(&1),
        "{:?}",
        report.totals.rejections
    );
}

#[test]
fn a_range_of_negative_values_only_is_refused_where_none_can_be_written() {
    let mut spec = unsigned_campaign();
    spec.holes[0].constraints.range = Some(IntRange {
        min: Some(BigInt::from(-40)),
        max: Some(BigInt::from(-2)),
    });
    let Err(error) = Campaign::new(spec) else {
        panic!("the campaign is refused");
    };
    assert!(
        matches!(&error, CampaignError::InvalidConstraints { hole, message }
            if hole == "B" && message.contains("`-2`")),
        "{error}"
    );
}
