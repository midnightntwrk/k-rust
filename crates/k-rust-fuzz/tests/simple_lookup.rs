//! SIMPLE's variable lookup is decided without a solver (R1-SIMPLE; findings
//! MAIN-SIMPLE-DIV-GUARD-KILL-LOST and MAIN-PORTABLE-STRING-HALT-SMT).
//!
//! SIMPLE reads a variable with `<k> X:Id => V ...</k> <env>... X |-> L ...</env>
//! <store>... L |-> V:Val ...</store>` (`simple.md:573`). On a concrete program every map in
//! that match is a map of literals, so one-way matching decides the lookup. When the known-key
//! map observation was offered before that matching, each lookup stated `\ceil` and equality
//! guards over the typed projection of the stored value: a build without a solver halted every
//! case at the first lookup (`halt-smt`), and TRIAL3's kill of `div-guard-dropped` was lost in
//! both profiles.

mod support;

use std::{collections::BTreeMap, sync::Arc};

use k_rust::diagnostic::DiagnosticCode;
use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl,
    HoleLocation, OutcomeClass, ProgramInput, ProgramSource, ProposerConfig, SpanAddress, Target,
    TargetKind,
    report::KillKind,
    spec::{CompiledDefinition, DEFAULT_REJECTION_CAP, ProgramText},
    target::DifferentialTarget,
    values::{Constraints, GenerationBounds, IntRange, Value},
};
use num_bigint::BigInt;

const SIMPLE: &str = include_str!("data/simple/simple.md");
/// TRIAL3's `arith` program (`kink/testdata/k/overload` SIMPLE corpus).
const ARITH: &str = include_str!("data/simple/arith.simple");
/// SIMPLE's division rule (`simple.md:607`), whose guard TRIAL3's `div-guard-dropped` removes.
const DIVISION: &str = "rule I1 / I2 => I1 /Int I2 requires I2 =/=K 0\n";

fn compile(source: &str) -> Arc<CompiledDefinition> {
    Arc::new(support::compile_source_with(
        "simple/simple.md",
        source,
        "SIMPLE-UNTYPED",
        &[DiagnosticCode::CellCollectionVarWithoutInitial],
    ))
}

/// An `Int` hole named `name` at `literal` in `find`, over `0..=100` as in TRIAL3's template.
fn int_hole(name: &str, find: &str, literal: &str) -> HoleDecl {
    HoleDecl {
        name: name.into(),
        sort: "Int".into(),
        location: HoleLocation::Span(SpanAddress {
            program: "arith.simple".into(),
            line: None,
            column: None,
            find: find.into(),
            literal: literal.into(),
        }),
        constraints: Constraints {
            range: Some(IntRange {
                min: Some(BigInt::from(0)),
                max: Some(BigInt::from(100)),
            }),
            ..Constraints::default()
        },
        allow_refused_sort: false,
    }
}

/// TRIAL3's `arith-holes` template against `div-guard-dropped`, reduced to two cases: the
/// anchors (`a = 17, b = 5`), which both definitions run to the same end, and TRIAL3's witness
/// (`a = 0, b = 0`). There the baseline is stuck at `0 / 0` and the mutant takes the step to
/// the undefined `0 /Int 0`: the baseline's end is removed, a kill. Both cases are judged; no
/// lookup leaves a baseline incomplete.
#[test]
fn div_guard_dropped_is_killed_on_the_arith_template() {
    assert_eq!(SIMPLE.matches(DIVISION).count(), 1);
    let baseline = compile(SIMPLE);
    let mutant = compile(&SIMPLE.replace(DIVISION, "rule I1 / I2 => I1 /Int I2\n"));
    let report = Campaign::new(CampaignSpec {
        definitions: Definitions {
            baseline,
            mutant: Some(mutant),
        },
        program: ProgramInput::Source(ProgramSource {
            program: Some(ProgramText {
                name: "arith.simple".into(),
                text: ARITH.into(),
                start_sort: "Stmt".into(),
            }),
            config_vars: Vec::new(),
        }),
        holes: vec![
            int_hole("A", "var a = 17", "17"),
            int_hole("B", "b = 5;", "5"),
        ],
        target: Target {
            kind: TargetKind::Differential(DifferentialTarget::default()),
            run_to_completion: false,
            negated_property: false,
            data_end: true,
            comparable: false,
            query_confirmable: false,
        },
        options: CaseOptions::default(),
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: vec![BTreeMap::from([
                ("A".to_owned(), Value::Int(BigInt::from(0))),
                ("B".to_owned(), Value::Int(BigInt::from(0))),
            ])],
            weights: BTreeMap::new(),
        },
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 0,
        identity: CallerIdentity {
            k_rust_revision: "r1-simple-test".into(),
            thread_stack_size: None,
        },
    })
    .expect("the campaign is valid")
    .run(Budget::Cases(2), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    assert!(
        report.totals.baseline_incomplete_reasons.is_empty()
            && report.totals.unsupported_reasons.is_empty(),
        "{:?}",
        report.totals
    );
    assert_eq!(
        report.totals.classes,
        BTreeMap::from([(OutcomeClass::Miss, 1), (OutcomeClass::Hit, 1)]),
        "{:?}",
        report.totals
    );
    let witness = report.witness().expect("a kill");
    assert_eq!(witness.first.kill, Some(KillKind::RemovedEnd));
    let holes: Vec<_> = witness
        .first
        .holes
        .iter()
        .map(|hole| (hole.name.as_str(), &hole.value))
        .collect();
    assert_eq!(
        holes,
        [
            ("A", &Value::Int(BigInt::from(0))),
            ("B", &Value::Int(BigInt::from(0)))
        ]
    );
}
