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
    report::{DefinitionRole, FuzzReport, NarrowingProbe, NarrowingReason, ProbeOutcome},
    spec::DEFAULT_REJECTION_CAP,
    target::{DifferentialTarget, PatternAt, PatternTarget},
    values::{Constraints, GenerationBounds, IntRange},
};
use num_bigint::BigInt;
use support::{Fixture, IMP, MINUSONE, SIGNED, UNSIGNED};

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
            data_end: true,
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
    assert_eq!(narrowed.reason, NarrowingReason::NegativeNotReadBack);
    assert_eq!(narrowed.side, DefinitionRole::Baseline);
    let probe = |value: &str, reads_as: &str| NarrowingProbe {
        value: value.into(),
        outcome: ProbeOutcome::ReadsAs,
        reads_as: Some(reads_as.into()),
        head: Some("neg".into()),
    };
    assert_eq!(
        narrowed.probes,
        vec![probe("-1", "- 1"), probe("-999", "- 999")]
    );
    assert!(
        report.warnings.iter().any(|warning| warning.starts_with(
            "hole `B`: values are generated from 0 (declared: no minimum), since no negative \
             integer probed at the hole reads back as itself (on the baseline, `-1` reads as \
             `- 1`, an application of `neg`; `-999` reads as `- 999`, an application of \
             `neg`). To fuzz negative values, write the program \
             with a unary minus before the literal (`- 5`)"
        ) && warning
            .ends_with("declare `range = { min = 0 }`.")),
        "{:?}",
        report.warnings
    );
    // The field reads back.
    let json = report.to_canonical_json();
    assert!(
        json.contains(concat!(
            r#""effective-constraints":[{"hole":"B","declared":"#,
            r#"{"range":null,"length":null,"elements":null,"choices":null},"#,
            r#""effective":{"range":{"min":"0","max":null},"length":null,"elements":null,"#,
            r#""choices":null},"reason":"negative-not-read-back","side":"baseline","#,
            r#""probes":[{"value":"-1","outcome":"reads-as","reads-as":"- 1","head":"neg"},"#,
            r#"{"value":"-999","outcome":"reads-as","reads-as":"- 999","head":"neg"}]}]"#
        )),
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
            if hole == "B" && message.contains("`-2` reads as `- 2`, an application of `neg`; `-40`")),
        "{error}"
    );
}

/// MINUSONE reads `-1` as a production of its own but every other negative literal as an `Int`
/// (review S1): the `-1` probe is refused, the `-999` probe reads back, so nothing is narrowed
/// and negative witnesses are still drawn.
fn minusone_campaign(range: Option<IntRange>) -> CampaignSpec {
    let mut hole = int_hole("B", "intgen/sum.pgm", "+ 5", "5");
    hole.constraints.range = range;
    spec(
        &MINUSONE,
        "intgen/sum.pgm",
        vec![hole],
        "<out> ListItem(N:Int) </out> requires N <Int 0",
        ProposerConfig::default(),
    )
}

#[test]
fn a_terminal_that_spells_one_negative_literal_narrows_nothing() {
    let report = run(minusone_campaign(None), 300);
    assert!(
        report.identity.effective_constraints.is_empty(),
        "{:?}",
        report.identity.effective_constraints
    );
    assert!(report.witness().is_some(), "{:?}", report.outcome);

    // A range of negative values only, -1 among them, is a campaign with witnesses.
    let report = run(
        minusone_campaign(Some(IntRange {
            min: Some(BigInt::from(-40)),
            max: Some(BigInt::from(-1)),
        })),
        300,
    );
    assert!(report.identity.effective_constraints.is_empty());
    assert!(report.witness().is_some(), "{:?}", report.outcome);
}

#[test]
fn either_side_of_a_differential_narrows_by_its_own_grammar() {
    for (baseline, program, mutant, side) in [
        (&SIGNED, "intgen/sum.pgm", &UNSIGNED, DefinitionRole::Mutant),
        (
            &UNSIGNED,
            "unsigned/sum.pgm",
            &SIGNED,
            DefinitionRole::Baseline,
        ),
    ] {
        let mut spec = spec(
            baseline,
            program,
            vec![int_hole("B", program, "+ 5", "5")],
            "<k> .K </k>",
            ProposerConfig::default(),
        );
        spec.definitions.mutant = Some(Arc::new(mutant.compiled().definition()));
        spec.target.kind = TargetKind::Differential(DifferentialTarget::default());
        let report = run(spec, 100);
        let [narrowed] = report.identity.effective_constraints.as_slice() else {
            panic!(
                "one narrowed hole: {:?}",
                report.identity.effective_constraints
            );
        };
        assert_eq!(narrowed.side, side);
        // No case is spent on a negative value either grammar refuses.
        assert!(report.totals.rejections.is_empty(), "{:?}", report.totals);
    }
}
