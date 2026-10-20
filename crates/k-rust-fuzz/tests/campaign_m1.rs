//! M1 acceptance of the engine (ARCHITECTURE 11, impl.toml FZ-06), against the real holes,
//! values, execution and target modules and the fixtures of `tests/data`.
//!
//! Every campaign fixes its seed and asserts on exact classes or report fields (impl.toml
//! `[common].determinism`). The expected classes follow ARCHITECTURE 5.3 as amended by D13.

mod support;

use std::{collections::BTreeMap, path::Path, sync::Arc};

use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignError, CampaignSpec, CaseOptions, Definitions,
    HoleDecl, HoleLocation, OutcomeClass, ProgramInput, ProposerConfig, SpanAddress, Target,
    TargetKind, Value,
    report::{CampaignOutcome, FuzzReport, HitLabel},
    spec::{DEFAULT_REJECTION_CAP, ProposerKind},
    target::{PatternAt, PatternTarget, RuleMode, RuleRef, RuleTarget},
    values::{Constraints, GenerationBounds},
};
use num_bigint::BigInt;
use support::{CHOSEN, Fixture, IMP, RULES};

/// An `Int` hole at `literal` inside the unique text `find` of `program`.
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

/// A pattern matched on a clean final leaf.
fn final_pattern(pattern: &str, negated_property: bool) -> Target {
    Target {
        kind: TargetKind::Pattern(PatternTarget {
            pattern: pattern.into(),
            at: PatternAt::Final,
        }),
        run_to_completion: false,
        negated_property,
    }
}

/// Only the blind proposer, after the anchors.
fn blind() -> ProposerConfig {
    ProposerConfig::default()
}

/// Only these explicit assignments, without the anchors and without generation.
fn explicit(assignments: &[&[(&str, i64)]]) -> ProposerConfig {
    ProposerConfig {
        anchors_first: false,
        explicit: assignments
            .iter()
            .map(|assignment| {
                assignment
                    .iter()
                    .map(|(name, value)| ((*name).to_owned(), Value::Int(BigInt::from(*value))))
                    .collect()
            })
            .collect(),
        weights: BTreeMap::new(),
    }
}

/// Only the anchors.
fn anchors_only() -> ProposerConfig {
    ProposerConfig {
        anchors_first: true,
        explicit: Vec::new(),
        weights: BTreeMap::new(),
    }
}

struct Setup {
    fixture: &'static Fixture,
    program: &'static str,
    holes: Vec<HoleDecl>,
    target: Target,
    proposers: ProposerConfig,
    options: CaseOptions,
    seed: u64,
}

impl Setup {
    fn new(fixture: &'static Fixture, program: &'static str, target: Target) -> Self {
        Self {
            fixture,
            program,
            holes: Vec::new(),
            target,
            proposers: blind(),
            options: CaseOptions::default(),
            seed: 0x5eed,
        }
    }

    fn spec(&self) -> CampaignSpec {
        let compiled = self.fixture.compiled();
        CampaignSpec {
            definitions: Definitions {
                baseline: Arc::new(compiled.definition()),
                mutant: None,
            },
            program: ProgramInput::Source(compiled.program_source(self.program)),
            holes: self.holes.clone(),
            target: self.target.clone(),
            options: self.options.clone(),
            proposers: self.proposers.clone(),
            bounds: GenerationBounds::default(),
            rejection_cap: DEFAULT_REJECTION_CAP,
            seed: self.seed,
            identity: CallerIdentity {
                k_rust_revision: "fz26-test".into(),
                thread_stack_size: None,
            },
        }
    }

    fn run(&self, budget: Budget) -> FuzzReport {
        let mut campaign = Campaign::new(self.spec()).expect("the campaign is valid");
        campaign.run(budget, None)
    }
}

fn classes(report: &FuzzReport) -> Vec<(OutcomeClass, u64)> {
    report
        .totals
        .classes
        .iter()
        .map(|(class, count)| (*class, *count))
        .collect()
}

fn int_of(value: &Value) -> BigInt {
    match value {
        Value::Int(n) => n.clone(),
        other => panic!("not an Int: {other:?}"),
    }
}

/// `a` and `b` of `commute.imp` differ at a clean natural end.
const COMMUTE_VIOLATION: &str = concat!(
    r#"<k> .K </k> <state> (#token("a", "Id") |-> A:Int) (#token("b", "Id") |-> B:Int) "#,
    r#"_:Map </state> requires A =/=Int B"#
);

/// `r` of `le.imp` is not 1 at a clean natural end: the program's claim that the anchors'
/// `x <= y` branch is taken fails.
const LE_VIOLATION: &str =
    r#"<k> .K </k> <state> (#token("r", "Id") |-> R:Int) _:Map </state> requires R =/=Int 1"#;

/// Matches every configuration: a target any leaf would reach if it were judged at all.
const ANYTHING: &str = "<k> _:K </k>";

fn commute() -> Setup {
    let mut setup = Setup::new(
        &IMP,
        "imp/commute.imp",
        final_pattern(COMMUTE_VIOLATION, true),
    );
    setup.holes = vec![
        int_hole("X", "imp/commute.imp", "x = 3;", "3"),
        int_hole("Y", "imp/commute.imp", "y = 5;", "5"),
    ];
    setup
}

fn le() -> Setup {
    let mut setup = Setup::new(&IMP, "imp/le.imp", final_pattern(LE_VIOLATION, true));
    setup.holes = vec![
        int_hole("X", "imp/le.imp", "x = 3;", "3"),
        int_hole("Y", "imp/le.imp", "y = 5;", "5"),
    ];
    setup
}

#[test]
fn commutativity_of_int_addition_has_no_confirmed_counterexample() {
    const N: u64 = 64;
    let report = commute().run(Budget::Cases(N));
    assert!(
        matches!(report.outcome, CampaignOutcome::NoWitnessFound { .. }),
        "{:?}",
        report.outcome
    );
    assert_eq!(classes(&report), [(OutcomeClass::Miss, N)]);
    assert_eq!(report.totals.cases, N);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    let statement = &report.no_witness().expect("a statement").statement;
    assert!(statement.contains("not a proof"), "{statement}");
    assert!(statement.contains("one-path mode"), "{statement}");
}

#[test]
fn x_le_y_has_a_confirmed_counterexample_whose_values_violate_it() {
    let report = le().run(Budget::Cases(200));
    let witness = report.witness().expect("a confirmed counterexample");
    assert_eq!(witness.label, HitLabel::PropertyFailure);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    // The anchors (3, 5) satisfy x <= y, so the first case is a miss and the witness comes from
    // a later case.
    assert!(report.totals.cases >= 2);
    assert_eq!(report.totals.classes.get(&OutcomeClass::Hit), Some(&1));
    for case in [Some(&witness.first), witness.shrunk.as_ref()]
        .into_iter()
        .flatten()
    {
        assert_eq!(case.class, OutcomeClass::Hit);
        let names: Vec<&str> = case.holes.iter().map(|hole| hole.name.as_str()).collect();
        assert_eq!(names, ["X", "Y"]);
        let (x, y) = (int_of(&case.holes[0].value), int_of(&case.holes[1].value));
        assert!(x > y, "the witness must violate x <= y: x = {x}, y = {y}");
        assert_eq!(case.holes[0].k_text, x.to_string());
        assert_eq!(case.sides.len(), 1);
        assert!(
            case.sides[0].final_configurations[0].contains(r#"\dv{SortInt{}}("0")"#),
            "{:?}",
            case.sides[0].final_configurations
        );
    }
    if let Some(shrunk) = &witness.shrunk {
        let size = |case: &k_rust_fuzz::report::WitnessCase| -> BigInt {
            case.holes
                .iter()
                .map(|hole| {
                    let n = int_of(&hole.value);
                    if n < BigInt::from(0) { -n } else { n }
                })
                .sum()
        };
        assert!(size(shrunk) <= size(&witness.first));
    }
}

/// Run `setup` on exactly its explicit or anchor proposals and return the one class.
fn single_class(setup: &Setup) -> (OutcomeClass, FuzzReport) {
    let report = setup.run(Budget::Cases(1));
    assert_eq!(report.totals.cases, 1, "{report:?}");
    assert_eq!(report.witness(), None, "never a hit: {report:?}");
    let class = *report
        .totals
        .classes
        .keys()
        .next()
        .expect("the case has a class");
    (class, report)
}

/// A property violation stated, as negated properties are, over a natural end: here every
/// natural end violates it, so any run that ended naturally would be a hit.
const ANY_NATURAL_END: &str = "<k> .K </k>";

/// `ANYTHING` under `run-to-completion`: a reaching leaf must also be a natural end to hit.
fn anything_to_completion() -> Target {
    Target {
        run_to_completion: true,
        ..final_pattern(ANYTHING, true)
    }
}

#[test]
fn a_stuck_run_is_never_a_hit() {
    // `10 / 0` is left on `<k>`: a clean abnormal stop, which is not a natural end.
    let mut setup = Setup::new(&IMP, "imp/div.imp", final_pattern(ANY_NATURAL_END, true));
    setup.holes = vec![int_hole("Y", "imp/div.imp", "y = 2;", "2")];
    setup.proposers = explicit(&[&[("Y", 0)]]);
    assert_eq!(single_class(&setup).0, OutcomeClass::Stuck);
    // A target the stuck leaf does match, but under run-to-completion: reached, not finished.
    setup.target = anything_to_completion();
    assert_eq!(single_class(&setup).0, OutcomeClass::ReachedUnfinished);
}

#[test]
fn a_bounded_run_is_never_a_hit() {
    let mut setup = Setup::new(&IMP, "imp/loop.imp", final_pattern(ANY_NATURAL_END, true));
    setup.holes = vec![int_hole("N", "imp/loop.imp", "n = 10;", "10")];
    setup.proposers = anchors_only();
    let depth = CaseOptions {
        max_depth: Some(20),
        ..CaseOptions::default()
    };
    let work = CaseOptions {
        max_work: Some(20),
        ..CaseOptions::default()
    };
    setup.options = depth.clone();
    assert_eq!(single_class(&setup).0, OutcomeClass::DepthBound);
    setup.options = work.clone();
    assert_eq!(single_class(&setup).0, OutcomeClass::WorkBound);
    // The cut leaf matches `ANYTHING`; a reaching leaf whose run was cut is never a hit.
    setup.target = anything_to_completion();
    for options in [depth, work] {
        setup.options = options;
        assert_eq!(single_class(&setup).0, OutcomeClass::ReachedUnfinished);
    }
    setup.target = final_pattern(ANYTHING, true);
    assert_eq!(single_class(&setup).0, OutcomeClass::Unsupported);
}

#[test]
fn an_undefined_step_is_never_a_hit() {
    // Rule `div` is covered by `div(10, 0)` (its right-hand side is undefined) but fires on no
    // clean leaf.
    let mut setup = Setup::new(
        &RULES,
        "rules/div.pgm",
        Target {
            kind: TargetKind::Rule(RuleTarget {
                rule: RuleRef::Label("RULES.div".into()),
                mode: RuleMode::Fired,
            }),
            run_to_completion: false,
            negated_property: false,
        },
    );
    setup.holes = vec![int_hole("B", "rules/div.pgm", "2)", "2")];
    setup.proposers = explicit(&[&[("B", 0)]]);
    assert_eq!(single_class(&setup).0, OutcomeClass::Undefined);
}

#[test]
fn a_run_that_reads_an_implementation_chosen_value_is_never_a_hit() {
    // `listKeys(1, 2)` ends naturally, but its `<out>` holds the listing order of two keys,
    // which the definition leaves open: the leaf is not clean, so neither a hit nor a pass.
    let mut setup = Setup::new(
        &CHOSEN,
        "chosen/keys.pgm",
        final_pattern(ANY_NATURAL_END, true),
    );
    setup.holes = vec![int_hole("B", "chosen/keys.pgm", "2)", "2")];
    setup.proposers = anchors_only();
    assert_eq!(single_class(&setup).0, OutcomeClass::Unsupported);
}

#[test]
fn the_program_file_is_byte_identical_before_and_after() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/imp/le.imp");
    let directory = path.parent().expect("a directory");
    let listing = || {
        let mut names: Vec<_> = std::fs::read_dir(directory)
            .expect("readable")
            .map(|entry| entry.expect("an entry").file_name())
            .collect();
        names.sort();
        names
    };
    let before = std::fs::read(&path).expect("readable");
    let files_before = listing();
    let setup = le();
    let spec = setup.spec();
    let ProgramInput::Source(source) = &spec.program else {
        panic!("a source program")
    };
    assert_eq!(
        source.program.as_ref().expect("a $PGM").text.as_bytes(),
        before,
        "the fixture text is the file"
    );
    let mut campaign = Campaign::new(spec.clone()).expect("valid");
    let report = campaign.run(Budget::Cases(50), None);
    assert!(report.witness().is_some());
    assert_eq!(std::fs::read(&path).expect("readable"), before);
    assert_eq!(listing(), files_before, "no file was written beside it");
    let ProgramInput::Source(after) = &campaign.spec().program else {
        panic!("a source program")
    };
    assert_eq!(after, source, "the campaign's program is unmodified");
}

#[test]
fn a_second_run_reports_what_a_fresh_campaign_reports() {
    let setup = le();
    let mut campaign = Campaign::new(setup.spec()).expect("valid");
    let first = campaign.run(Budget::Cases(30), None).to_canonical_json();
    let second = campaign.run(Budget::Cases(30), None).to_canonical_json();
    assert_eq!(first, second);
    assert_eq!(first, setup.run(Budget::Cases(30)).to_canonical_json());
}

#[test]
fn a_proposer_this_milestone_does_not_provide_is_refused() {
    let mut setup = le();
    setup.proposers.weights.insert(ProposerKind::Climb, 1);
    match Campaign::new(setup.spec()) {
        Err(CampaignError::InvalidOptions { message }) => {
            assert!(message.contains("climb"), "{message}");
        }
        Err(other) => panic!("{other}"),
        Ok(_) => panic!("the climb proposer is not provided in M1"),
    }
}

#[test]
fn a_mutant_without_a_differential_target_is_refused() {
    let setup = le();
    let mut spec = setup.spec();
    spec.definitions.mutant = Some(Arc::clone(&spec.definitions.baseline));
    assert!(matches!(
        Campaign::new(spec),
        Err(CampaignError::DefinitionsMismatch)
    ));
}
