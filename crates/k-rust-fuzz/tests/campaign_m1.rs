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
    exec::UnjudgedReason,
    report::{CampaignOutcome, FuzzReport, HitLabel},
    spec::{DEFAULT_REJECTION_CAP, ProposerKind},
    target::{PatternAt, PatternTarget, RuleMode, RuleRef, RuleTarget},
    values::{Constraints, GenerationBounds},
};
use num_bigint::BigInt;
use support::{CHOSEN, Fixture, GRAPH, IMP, LEDGER, OV, OV_SIZE, R3_PLAINQ, RULES, SHAPE, VALUE};

/// An `Int` hole at `literal` inside the unique text `find` of `program`.
fn int_hole(name: &str, program: &str, find: &str, literal: &str) -> HoleDecl {
    HoleDecl {
        name: name.into(),
        sort: "Int".into(),
        location: HoleLocation::Span(SpanAddress {
            program: program.into(),
            line: None,
            column: None,
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
        data_end: true,
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
        assert_eq!(case.holes[0].k_text, Some(x.to_string()));
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
    // A cut leaf is not an end, so a final pattern is not matched on it at all (D16): the
    // case takes its bound's class, with or without run-to-completion.
    for target in [anything_to_completion(), final_pattern(ANYTHING, true)] {
        setup.target = target;
        setup.options = depth.clone();
        assert_eq!(single_class(&setup).0, OutcomeClass::DepthBound);
        setup.options = work.clone();
        assert_eq!(single_class(&setup).0, OutcomeClass::WorkBound);
    }
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
            data_end: true,
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

/// A pattern whose `requires` reads a variable its configuration does not bind is refused with
/// the variable's name (FZ-POLISH S3): such a variable is almost always a misspelling, and the
/// engine decides a condition on it only when it is trivially true or false. A variable the configuration binds and a pattern
/// without `requires` are accepted.
#[test]
fn a_pattern_whose_requires_reads_an_unbound_variable_is_refused() {
    for (pattern, unbound) in [
        ("<k> .K </k> <state> M </state> requires R >Int 0", "R"),
        (
            "<k> .K </k> <state> M </state> requires R >Int 0 andBool Q <Int R",
            "Q`, `R",
        ),
    ] {
        let mut setup = le();
        setup.target = final_pattern(pattern, true);
        match Campaign::new(setup.spec()) {
            Err(error @ CampaignError::Target(_)) => {
                let message = error.to_string();
                assert!(
                    message.contains(&format!("`{unbound}`")) && message.contains("requires"),
                    "{message}"
                );
                // The reason stated is the honest one (review round 1): a condition that does
                // not depend on the variable (`R ==Int R`) can hold, so no claim that no case
                // could reach the pattern.
                assert!(message.contains("almost always a misspelling"), "{message}");
                assert!(!message.contains("no case could reach"), "{message}");
            }
            Err(other) => panic!("{pattern}: {other}"),
            Ok(_) => panic!("{pattern}: accepted"),
        }
    }
    for pattern in [LE_VIOLATION, "<k> .K </k> <state> M </state>"] {
        let mut setup = le();
        setup.target = final_pattern(pattern, true);
        if let Err(error) = Campaign::new(setup.spec()) {
            panic!("{pattern}: {error}");
        }
    }
}

/// A negated property whose pattern names a key no end holds (`rr` for `r`) holds vacuously:
/// every case is a `miss`, as for a property that holds. The report counts the clean end
/// leaves that matched the pattern's configuration without its `requires`, and warns when
/// none did (FZ-POLISH S2).
#[test]
fn a_vacuous_negated_property_is_told_apart_from_one_that_holds() {
    let misspelled = LE_VIOLATION.replace(r#"#token("r", "Id")"#, r#"#token("rr", "Id")"#);
    let mut setup = le();
    setup.target = final_pattern(&misspelled, true);
    let report = setup.run(Budget::Cases(20));
    assert_eq!(classes(&report), [(OutcomeClass::Miss, 20)]);
    let vacuous = |report: &FuzzReport| {
        report
            .warnings
            .iter()
            .any(|warning| warning.contains("pattern body: no end of the"))
    };
    assert!(vacuous(&report), "{:?}", report.warnings);
    assert_eq!(report.totals.pattern_body_matches, Some(0));
    assert!(
        report
            .to_canonical_json()
            .contains("\"pattern-body-matches\":0")
    );
    // The property `x <= y => r == 1` holds on the anchors (3, 5): its body matches, no warning.
    let mut holds = le();
    holds.proposers = anchors_only();
    let report = holds.run(Budget::Cases(1));
    assert_eq!(classes(&report), [(OutcomeClass::Miss, 1)]);
    assert!(!vacuous(&report), "{:?}", report.warnings);
    assert_eq!(report.totals.pattern_body_matches, Some(1));
    // A rule target reports no count.
    let report = Setup::new(&IMP, "imp/le.imp", fired("IMP.assign")).run(Budget::Cases(1));
    assert_eq!(report.totals.pattern_body_matches, None);
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

#[test]
fn a_campaign_without_shrinking_reports_its_first_witness_only() {
    let mut setup = le();
    setup.options.shrink = false;
    let shrinking = le().run(Budget::Cases(200));
    let report = setup.run(Budget::Cases(200));
    let witness = report.witness().expect("a witness");
    assert_eq!(witness.shrunk, None);
    assert!(!report.identity.options.shrink);
    // The same cases ran; only the shrink runs are missing from the work.
    assert_eq!(report.totals.cases, shrinking.totals.cases);
    assert_eq!(witness.first, shrinking.witness().expect("a witness").first);
    assert!(report.totals.work < shrinking.totals.work);
}

/// A `fired` rule target on the rule labelled `label`.
fn fired(label: &str) -> Target {
    Target {
        kind: TargetKind::Rule(RuleTarget {
            rule: RuleRef::Label(label.into()),
            mode: RuleMode::Fired,
        }),
        run_to_completion: false,
        negated_property: false,
        data_end: true,
    }
}

fn unreachable_warnings(report: &FuzzReport) -> Vec<&String> {
    report
        .warnings
        .iter()
        .filter(|warning| warning.starts_with("statically-unreachable"))
        .collect()
}

#[test]
fn a_statically_unreachable_rule_target_is_warned_and_the_campaign_runs() {
    // GRAPH: `start(N)` enables `go`, then `finish`; only `stray` produces what `other` needs.
    let campaign = |label: &str| {
        let mut setup = Setup::new(&GRAPH, "graph/start.pgm", fired(label));
        setup.holes = vec![int_hole("N", "graph/start.pgm", "start(5)", "5")];
        setup.run(Budget::Cases(8))
    };
    let report = campaign("other");
    let warnings = unreachable_warnings(&report);
    assert_eq!(warnings.len(), 1, "{:?}", report.warnings);
    assert!(warnings[0].contains("is not reachable"), "{}", warnings[0]);
    assert_eq!(report.totals.cases, 8);
    assert_eq!(classes(&report), [(OutcomeClass::Miss, 8)]);
    // Every case's applied rules are in the graph's reach: the self-check finds no defect.
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    let report = campaign("finish");
    assert!(
        unreachable_warnings(&report).is_empty(),
        "{:?}",
        report.warnings
    );
    assert!(report.witness().is_some(), "{:?}", report.outcome);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
}

#[test]
fn the_rule_graph_entry_is_the_hole_template_not_the_anchor() {
    // VALUE: `$N` is the whole `<k>` cell. Keyed on the anchor 5, `zero` would look
    // unreachable; keyed on the template's variable of sort `Int`, it is an entry rule.
    let mut setup = Setup::new(&VALUE, "graph/value.pgm", fired("zero"));
    setup.holes = vec![HoleDecl {
        name: "N".into(),
        sort: "Int".into(),
        location: HoleLocation::ConfigVar { name: "N".into() },
        constraints: Constraints::default(),
        allow_refused_sort: false,
    }];
    setup.proposers = explicit(&[&[("N", 5)], &[("N", 0)]]);
    let report = setup.run(Budget::Cases(4));
    assert!(
        unreachable_warnings(&report).is_empty(),
        "{:?}",
        report.warnings
    );
    assert!(report.witness().is_some(), "{:?}", report.outcome);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
}

/// A campaign over SHAPE's initial configuration as a KORE template: the `$SHAPE` value
/// `inj{SortCircle{}, SortKItem{}}(circle(9))` is replaced by
/// `inj{SortShape{}, SortKItem{}}(VarS:SortShape{})`, the hole `S` of the data sort `Shape`,
/// which has no constructor of its own, with the target `boxed` fired.
fn shape_template_spec(definition: k_rust_fuzz::CompiledDefinition) -> CampaignSpec {
    let anchor = r#"inj{SortCircle{}, SortKItem{}}(Lblcircle{}(\dv{SortInt{}}("9")))"#;
    let initial = SHAPE.compiled().initial("graph/shape.pgm").to_string();
    assert_eq!(initial.matches(anchor).count(), 1, "{initial}");
    let template = k_rust::kore::parser::parse_pattern(
        &initial.replace(anchor, "inj{SortShape{}, SortKItem{}}(VarS:SortShape{})"),
    )
    .expect("the template parses");
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(definition),
            mutant: None,
        },
        program: ProgramInput::KoreTemplate(template),
        holes: vec![HoleDecl {
            name: "S".into(),
            sort: "Shape".into(),
            location: HoleLocation::KoreVariable {
                name: "VarS".into(),
            },
            constraints: Constraints::default(),
            allow_refused_sort: false,
        }],
        target: fired("boxed"),
        options: CaseOptions::default(),
        proposers: blind(),
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 3,
        identity: CallerIdentity {
            k_rust_revision: "fz26-test".into(),
            thread_stack_size: None,
        },
    }
}

#[test]
fn a_kore_template_data_hole_is_injected_to_its_sort_and_finds_the_witness() {
    // Phase-1 review S1: a value of `Circle` or `Square` is substituted under an injection to
    // the variable's sort `Shape`, so the backend accepts every case; and a template needs no
    // K text, so a definition without the compiler's syntax outputs runs it too.
    let with_syntax = SHAPE.compiled().definition();
    let mut without_syntax = with_syntax.clone();
    without_syntax.syntax_definition_kore.clear();
    without_syntax.macros_kore.clear();
    for (name, definition, has_text) in [
        ("with K-text syntax", with_syntax, true),
        ("without K-text syntax", without_syntax, false),
    ] {
        let report = Campaign::new(shape_template_spec(definition))
            .unwrap_or_else(|error| panic!("{name}: {error}"))
            .run(Budget::Cases(40), None);
        assert!(
            report.engine_defects.is_empty(),
            "{name}: {:?}",
            report.engine_defects
        );
        assert_eq!(
            report.totals.classes.get(&OutcomeClass::Rejected),
            None,
            "{name}: {:?}",
            report.totals
        );
        let witness = report
            .witness()
            .unwrap_or_else(|| panic!("{name}: a witness, not {:?}", report.outcome));
        assert_eq!(
            witness.krun_command, None,
            "{name}: no krun run is a template"
        );
        for case in [Some(&witness.first), witness.shrunk.as_ref()]
            .into_iter()
            .flatten()
        {
            let hole = &case.holes[0];
            assert!(
                matches!(&hole.value, Value::Apply { symbol, .. } if symbol == "Lblsquare"),
                "{name}: {:?}",
                hole.value
            );
            assert_eq!(hole.k_text.is_some(), has_text, "{name}: {:?}", hole.k_text);
            assert!(
                case.sides[0]
                    .initial_configuration
                    .contains("inj{SortSquare{}, SortShape{}}(Lblsquare{}("),
                "{name}: {}",
                case.sides[0].initial_configuration
            );
        }
    }
}

/// FZ-DATAEND (TRIAL2 S-T2): a run-to-completion rule hit's end must be data, as the
/// differential judge's ends must, unless the target waives it. `OV`'s rule ends with an
/// irreducible overload application (data); `OV_SIZE`'s with an unevaluated total function
/// (not data): its reaching natural end is `unsupported`, and a hit only with `data_end` off.
#[test]
fn a_run_to_completion_rule_hit_needs_a_data_end() {
    let target = |data_end| Target {
        run_to_completion: true,
        data_end,
        ..fired("OV.store")
    };
    let setup = |fixture, data_end| {
        let mut setup = Setup::new(fixture, "ov/three.pgm", target(data_end));
        setup.holes = vec![int_hole("N", "ov/three.pgm", "3", "3")];
        setup.proposers = anchors_only();
        setup
    };
    let data = setup(&OV, true).run(Budget::Cases(1));
    let witness = data.witness().expect("the anchor's end is data");
    assert!(
        witness.clean_leaf_facts.contains(&"end-data".to_owned()),
        "{:?}",
        witness.clean_leaf_facts
    );
    let function = setup(&OV_SIZE, true).run(Budget::Cases(1));
    assert!(function.witness().is_none(), "{:?}", function.outcome);
    assert_eq!(classes(&function), [(OutcomeClass::Unsupported, 1)]);
    // Its own reason, never `natural-end-undecided` or `engine-defect` (INT7).
    assert_eq!(
        function.totals.unsupported_reasons,
        std::collections::BTreeMap::from([(UnjudgedReason::ReachedEndNotData, 1)])
    );
    let waived = setup(&OV_SIZE, false).run(Budget::Cases(1));
    let witness = waived.witness().expect("a reach-only hit");
    assert!(!witness.clean_leaf_facts.contains(&"end-data".to_owned()));
}

/// INT7, then FZ-POLISH: a run-to-completion hit on a definition whose full critical-pair check
/// reports a pair (R3-PLAINQ's `q(_) => a` against `q(_) => bb`) has no data end, even when the
/// end is a constructor term. That holds of every case and is known before the first, so the
/// campaign runs no case and ends `not-comparable`, its warning naming the definition and the
/// report listing the finding. With `data-end = false` the cases run.
#[test]
fn a_data_end_hit_on_a_definition_without_data_names_the_definition() {
    let mut setup = Setup::new(
        &R3_PLAINQ,
        "r3-plainq/go.pgm",
        Target {
            run_to_completion: true,
            ..final_pattern("<k> .K </k> <s> a </s>", false)
        },
    );
    setup.holes = vec![int_hole("N", "r3-plainq/go.pgm", "3", "3")];
    setup.proposers = anchors_only();
    let report = setup.run(Budget::Cases(1));
    assert!(
        matches!(
            &report.outcome,
            k_rust_fuzz::report::CampaignOutcome::NotComparable { sides, .. }
                if sides == &[k_rust_fuzz::report::DefinitionRole::Baseline]
        ),
        "{:?}",
        report.outcome
    );
    assert_eq!(report.totals.cases, 0);
    assert!(
        report
            .warnings
            .iter()
            .any(|warning| warning.starts_with("definition-not-confluent (baseline): ")),
        "{:?}",
        report.warnings
    );
    assert_eq!(report.definition_findings.len(), 1);
    setup.target.data_end = false;
    let waived = setup.run(Budget::Cases(1));
    assert_eq!(waived.totals.cases, 1, "{:?}", waived.outcome);
    assert!(waived.definition_findings.is_empty());
}

/// FZ-DATAEND review S1: a negated property's counterexample is decided by its match, so it
/// needs no data end. On `OV_SIZE` the end holds the unevaluated `size(...)`, and the pattern
/// `<s> S </s>` at a natural end is violated by every input: a property failure, not
/// `unsupported`.
#[test]
fn a_property_counterexample_needs_no_data_end() {
    let mut setup = Setup::new(
        &OV_SIZE,
        "ov/three.pgm",
        Target {
            run_to_completion: true,
            ..final_pattern("<k> .K </k> <s> S </s>", true)
        },
    );
    setup.holes = vec![int_hole("N", "ov/three.pgm", "3", "3")];
    setup.proposers = anchors_only();
    let report = setup.run(Budget::Cases(1));
    let witness = report.witness().expect("a property failure");
    assert_eq!(witness.label, HitLabel::PropertyFailure);
    assert!(!witness.clean_leaf_facts.contains(&"end-data".to_owned()));
}

/// A witness case carries its instantiated configuration-variable bindings beside the
/// instantiated program (fz26 KF-T3b): a span hole inside a binding's text (`$TX`) is replaced
/// in that binding, so a client can re-enter the witness without the crate's instantiator.
#[test]
fn a_witness_carries_its_instantiated_bindings() {
    // LEDGER: `settle` with `$TX = transfer(30, 1)` on an account of 100; an amount above 99
    // makes the `refuse` rule fire.
    let mut setup = Setup::new(&LEDGER, "ledger/settle.pgm", fired("refuse"));
    setup.holes = vec![int_hole("A", "$TX", "transfer(30, 1)", "30")];
    setup.proposers = explicit(&[&[("A", 250)]]);
    setup.options.shrink = false;
    let report = setup.run(Budget::Cases(1));
    let witness = report.witness().expect("a witness");
    let case = &witness.first;
    assert_eq!(case.program.as_deref(), Some("settle\n"));
    assert_eq!(
        case.config_vars,
        BTreeMap::from([("TX".to_owned(), "transfer(250, 1)".to_owned())])
    );
    // The field is in the report's JSON, and reads back.
    let json = serde_json::to_value(case).expect("encodes");
    assert_eq!(json["config-vars"]["TX"], "transfer(250, 1)");
    // A program without bindings has none, and the JSON omits the field.
    let report = le().run(Budget::Cases(200));
    let case = &report.witness().expect("a witness").first;
    assert!(case.config_vars.is_empty());
    let json = serde_json::to_value(case).expect("encodes");
    assert!(json.get("config-vars").is_none(), "{json}");
}
