//! The engine's wiring of the differential target (ARCHITECTURE 4.3, 7): both sides run per
//! case, confirmation re-runs both, equivalent definitions run no case. The judge itself is
//! FZ-08's and is tested in `src/target/differential.rs`.

mod support;

use std::{collections::BTreeMap, sync::Arc};

use k_rust_fuzz::{
    BackendRoute, Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions,
    HoleDecl, HoleLocation, OutcomeClass, ProgramInput, ProposerConfig, SpanAddress, Target,
    TargetKind,
    report::{CampaignOutcome, DefinitionRole, HitLabel, KillKind, Reaching},
    spec::DEFAULT_REJECTION_CAP,
    spec::PathMode,
    target::DifferentialTarget,
    values::{Constraints, GenerationBounds, IntRange, Value},
};
use num_bigint::BigInt;
use support::{
    CLAIMSTEP, CLAIMSTEP_PARTIAL, CLAIMSTEP_PRESERVES, CLAIMSTEP_TOTAL, COIN, COIN_KILL,
    COIN_LAYOUT, COIN_PRIO, COIN_SWAPPED, DIAMOND, DIAMOND_PLUS, Fixture, IMP_ADD_COMMUTED,
    IMP_DECL_ALLOWS_REDECLARATION, IMP_DIFF, IMP_DIV_GUARD_DROPPED, MAC, MAC_KILL,
};

fn spec(mutant: &'static Fixture) -> CampaignSpec {
    spec_on(&COIN, mutant, "coin/flip.pgm", None)
}

/// A differential campaign over the hole `N` on the `3` of `program`, on the fixtures' route or
/// on `route`.
fn spec_on(
    baseline: &'static Fixture,
    mutant: &'static Fixture,
    program: &str,
    route: Option<&BackendRoute>,
) -> CampaignSpec {
    let definition = |fixture: &'static Fixture| {
        let compiled = fixture.compiled();
        Arc::new(route.cloned().map_or_else(
            || compiled.definition(),
            |route| compiled.definition_on(route),
        ))
    };
    CampaignSpec {
        definitions: Definitions {
            baseline: definition(baseline),
            mutant: Some(definition(mutant)),
        },
        program: ProgramInput::Source(baseline.compiled().program_source(program)),
        holes: vec![HoleDecl {
            name: "N".into(),
            sort: "Int".into(),
            location: HoleLocation::Span(SpanAddress {
                program: program.into(),
                line: None,
                find: "3".into(),
                literal: "3".into(),
            }),
            constraints: Constraints::default(),
            allow_refused_sort: false,
        }],
        target: Target {
            kind: TargetKind::Differential(DifferentialTarget::default()),
            run_to_completion: false,
            negated_property: false,
        },
        options: CaseOptions::default(),
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: vec![BTreeMap::from([(
                "N".to_owned(),
                Value::Int(BigInt::from(10)),
            )])],
            weights: ProposerConfig::default().weights,
        },
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 7,
        identity: CallerIdentity {
            k_rust_revision: "fz26-test".into(),
            thread_stack_size: None,
        },
    }
}

#[test]
fn a_mutant_that_adds_an_end_is_killed_by_a_confirmed_witness() {
    let report = Campaign::new(spec(&COIN_KILL))
        .expect("valid")
        .run(Budget::Cases(64), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    let witness = report.witness().expect("a kill");
    assert_eq!(witness.label, HitLabel::Hit);
    assert_eq!(
        witness.krun_command, None,
        "no single krun run is a differential pair"
    );
    for case in [Some(&witness.first), witness.shrunk.as_ref()]
        .into_iter()
        .flatten()
    {
        let Value::Int(n) = &case.holes[0].value else {
            panic!("an Int")
        };
        assert!(*n > BigInt::from(10), "only N > 10 adds an end: {n}");
        assert_eq!(case.kill, Some(KillKind::AddedEnd));
        assert_eq!(
            case.reaching,
            Reaching {
                role: DefinitionRole::Mutant,
                leaf: Some(0),
                step: None
            }
        );
        let roles: Vec<DefinitionRole> = case.sides.iter().map(|side| side.role).collect();
        assert_eq!(roles, [DefinitionRole::Baseline, DefinitionRole::Mutant]);
        assert_eq!(
            case.sides[0].final_configurations.len(),
            2,
            "heads and tails"
        );
        assert_eq!(
            case.sides[1].final_configurations.len(),
            1,
            "the mutant's single end, which kills"
        );
    }
    // The anchor 3 and the explicit 10 are within the baseline's behaviour.
    assert!(report.totals.cases >= 3);
    if let Some(shrunk) = &witness.shrunk {
        assert_eq!(shrunk.holes[0].value, Value::Int(BigInt::from(11)));
    }
    assert_eq!(report.identity.definitions.len(), 2);
}

#[test]
fn equivalent_definitions_end_the_campaign_before_any_case() {
    let report = Campaign::new(spec(&COIN_LAYOUT))
        .expect("valid")
        .run(Budget::Cases(64), None);
    assert_eq!(report.outcome, CampaignOutcome::Equivalent);
    assert_eq!(report.totals.cases, 0);
}

#[test]
fn a_macro_only_mutant_is_killed_on_both_routes() {
    // Phase-1 review B1: equal definition.kore, unequal macros.kore. `inc(N)` ends with N + 1 on
    // the baseline and N + 2 on the mutant, so the anchor itself kills.
    for route in [None, Some(BackendRoute::FromDefinition)] {
        let report = Campaign::new(spec_on(&MAC, &MAC_KILL, "mac/inc.pgm", route.as_ref()))
            .expect("valid")
            .run(Budget::Cases(16), None);
        assert_ne!(report.outcome, CampaignOutcome::Equivalent, "{route:?}");
        assert!(
            report.engine_defects.is_empty(),
            "{route:?}: {:?}",
            report.engine_defects
        );
        let witness = report
            .witness()
            .unwrap_or_else(|| panic!("{route:?}: a kill, not {:?}", report.outcome));
        assert_eq!(witness.first.kill, Some(KillKind::AddedEnd), "{route:?}");
        assert_eq!(
            witness.first.holes[0].value,
            Value::Int(BigInt::from(3)),
            "{route:?}: the anchor kills"
        );
        assert!(
            witness.first.sides[1].final_configurations[0].contains(r#"\dv{SortInt{}}("5")"#),
            "{route:?}: {:?}",
            witness.first.sides[1].final_configurations
        );
    }
}

#[test]
fn incomplete_baselines_under_all_paths_name_the_depth_bound() {
    // Phase-1 review S2: `count(N)` needs max_depth N + 2, so for N in [3, 50] every baseline
    // is cut at max_depth 3, and no path of any input was explored to its end.
    let mut spec = spec_on(&COIN, &COIN_KILL, "coin/count.pgm", None);
    spec.options = CaseOptions {
        paths: PathMode::AllPaths,
        max_depth: Some(3),
        ..CaseOptions::default()
    };
    spec.holes[0].constraints.range = Some(IntRange {
        min: Some(BigInt::from(3)),
        max: Some(BigInt::from(50)),
    });
    spec.proposers.explicit.clear();
    let report = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(10), None);
    assert_eq!(
        report.totals.classes,
        BTreeMap::from([(k_rust_fuzz::OutcomeClass::BaselineIncomplete, 10)])
    );
    let statement = &report.no_witness().expect("no witness").statement;
    for expected in [
        "10 cases had an incomplete baseline, so no kill could be judged.",
        "In 10 of them a baseline path stopped at max-depth 3: raise max-depth.",
    ] {
        assert!(
            statement.contains(expected),
            "missing {expected:?} in {statement:?}"
        );
    }
    assert!(
        !statement.contains("Every path of each input was explored"),
        "{statement}"
    );
}

// ---- how each run ended (FZ-DIFFEND; TRIAL2 B-T1, S-T6)

/// An `Int` hole on `literal` inside `find` of `program`, in `[0, max]`.
fn int_hole(name: &str, program: &str, find: &str, literal: &str, max: i64) -> HoleDecl {
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
                max: Some(BigInt::from(max)),
            }),
            ..Constraints::default()
        },
        allow_refused_sort: false,
    }
}

/// TRIAL2's campaign shape: `holes` on `program`, the explicit `explicit` after the anchors,
/// max-work 20000 (TRIAL2's IMP campaigns), in `paths`.
fn trial_spec(
    baseline: &'static Fixture,
    mutant: &'static Fixture,
    program: &str,
    holes: Vec<HoleDecl>,
    explicit: Vec<BTreeMap<String, Value>>,
    paths: PathMode,
) -> CampaignSpec {
    let mut spec = spec_on(baseline, mutant, program, None);
    spec.holes = holes;
    spec.proposers.explicit = explicit;
    spec.options = CaseOptions {
        paths,
        max_work: Some(20_000),
        ..CaseOptions::default()
    };
    spec
}

/// TRIAL2's `primes` template: every data literal a hole (M, N, I, T), as in
/// `div-guard-dropped-primes.toml`.
fn primes_holes() -> Vec<HoleDecl> {
    let program = "imp-diff/primes.imp";
    vec![
        int_hole("M", program, "m = 4;", "4", 8),
        int_hole("N", program, "n = 2;", "2", 8),
        int_hole("I", program, "i = 2;", "2", 8),
        int_hole("T", program, "t = 1;", "1", 3),
    ]
}

fn int_assignment(pairs: &[(&str, i64)]) -> BTreeMap<String, Value> {
    pairs
        .iter()
        .map(|(name, value)| ((*name).to_owned(), Value::Int(BigInt::from(*value))))
        .collect()
}

fn hole_text(case: &k_rust_fuzz::report::WitnessCase, name: &str) -> Value {
    case.holes
        .iter()
        .find(|hole| hole.name == name)
        .unwrap_or_else(|| panic!("no hole {name}"))
        .value
        .clone()
}

#[test]
fn an_undefined_step_where_the_baseline_stops_is_a_confirmed_removed_end() {
    // TRIAL2 B-T1, `div-guard-dropped` on `primes`: with I = 0, `q = n/i;` leaves `2 / 0`, to
    // which no baseline rule applies (an abnormal stop), while the mutant's division rule
    // applies and its result `2 /Int 0` is undefined. The mutant's set of final configurations
    // is empty, so the baseline's stop is an end the mutant removed. The default mode (one
    // path) decides it.
    let report = Campaign::new(trial_spec(
        &IMP_DIFF,
        &IMP_DIV_GUARD_DROPPED,
        "imp-diff/primes.imp",
        primes_holes(),
        vec![int_assignment(&[("I", 0)])],
        PathMode::OnePath,
    ))
    .expect("valid")
    .run(Budget::Cases(8), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    let witness = report
        .witness()
        .unwrap_or_else(|| panic!("a kill, not {:?}", report.outcome));
    assert_eq!(witness.label, HitLabel::Hit);
    for case in [Some(&witness.first), witness.shrunk.as_ref()]
        .into_iter()
        .flatten()
    {
        assert_eq!(case.kill, Some(KillKind::RemovedEnd));
        assert_eq!(case.reaching.role, DefinitionRole::Baseline);
        assert_eq!(hole_text(case, "I"), Value::Int(BigInt::from(0)));
        let baseline_end = &case.sides[0].final_configurations
            [usize::try_from(case.reaching.leaf.expect("a leaf")).expect("fits")];
        assert!(
            baseline_end.contains("Slsh"),
            "the baseline stops at the division: {baseline_end}"
        );
    }
}

#[test]
fn an_undefined_redeclaration_where_the_baseline_stops_is_killed() {
    // TRIAL2 item 7, `decl-allows-redeclaration` on `sum` with the `Id` hole: `int n, n;`
    // stops on the baseline (the declaration rule requires a fresh name) and is an undefined
    // step on the mutant (the map `n |-> 0` joined with a map that already binds `n`).
    let mut hole = HoleDecl {
        name: "V".into(),
        sort: "Id".into(),
        location: HoleLocation::Span(SpanAddress {
            program: "imp-diff/sum.imp".into(),
            line: None,
            find: "int n, sum;".into(),
            literal: "sum".into(),
        }),
        constraints: Constraints::default(),
        allow_refused_sort: true,
    };
    let token = |text: &str| Value::Token {
        sort: "Id".into(),
        text: text.into(),
    };
    hole.constraints.choices = Some(vec![token("n"), token("sum")]);
    let report = Campaign::new(trial_spec(
        &IMP_DIFF,
        &IMP_DECL_ALLOWS_REDECLARATION,
        "imp-diff/sum.imp",
        vec![hole],
        vec![BTreeMap::from([("V".to_owned(), token("n"))])],
        PathMode::OnePath,
    ))
    .expect("valid")
    .run(Budget::Cases(8), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    let witness = report
        .witness()
        .unwrap_or_else(|| panic!("a kill, not {:?}", report.outcome));
    assert_eq!(witness.first.kill, Some(KillKind::RemovedEnd));
    assert_eq!(hole_text(&witness.first, "V"), token("n"));
}

#[test]
fn the_equivalent_mutant_is_never_killed() {
    // TRIAL2 item 6, `add-commuted` on `sum`: `+Int` is commutative and the rule fires only on
    // two `Int` values, so the mutant ends where the baseline does on every input.
    let program = "imp-diff/sum.imp";
    for paths in [PathMode::OnePath, PathMode::AllPaths] {
        let report = Campaign::new(trial_spec(
            &IMP_DIFF,
            &IMP_ADD_COMMUTED,
            program,
            vec![
                int_hole("N", program, "n = 3;", "3", 8),
                int_hole("S", program, "sum = 0;", "0", 8),
                int_hole("D", program, "n + -1;", "1", 8),
            ],
            Vec::new(),
            paths,
        ))
        .expect("valid")
        .run(Budget::Cases(ADD_COMMUTED_CASES), None);
        assert!(
            report.engine_defects.is_empty(),
            "{paths:?}: {:?}",
            report.engine_defects
        );
        assert!(
            report.no_witness().is_some(),
            "{paths:?}: no kill, not {:?}",
            report.outcome
        );
        assert_eq!(report.totals.classes.get(&OutcomeClass::Hit), None);
    }
}

/// The cases of [`the_equivalent_mutant_is_never_killed`] per mode (a debug build runs about
/// 20 cases a second; the report's measurement ran 3000 in the release build).
const ADD_COMMUTED_CASES: u64 = 300;

#[test]
fn single_paths_that_differ_inside_one_set_of_ends_are_never_killed() {
    // FZ-08's coin-swapped: the mutant's single path ends with N + 1 where the baseline's ends
    // with N, but both sets of ends are {N, N + 1}. Under state sets, in both modes, no case
    // kills (the one-path mode re-runs the mutant on all paths when its one path misses a
    // baseline end, and then finds the same set).
    for paths in [PathMode::OnePath, PathMode::AllPaths] {
        let mut spec = spec(&COIN_SWAPPED);
        spec.options.paths = paths;
        let report = Campaign::new(spec)
            .expect("valid")
            .run(Budget::Cases(64), None);
        assert!(
            report.engine_defects.is_empty(),
            "{paths:?}: {:?}",
            report.engine_defects
        );
        assert!(
            report.no_witness().is_some(),
            "{paths:?}: {:?}",
            report.outcome
        );
        assert_eq!(
            report.totals.classes,
            BTreeMap::from([(OutcomeClass::Miss, report.totals.cases)]),
            "{paths:?}"
        );
    }
}

#[test]
fn an_undefined_step_that_contradicts_a_claim_is_no_evidence() {
    // The baseline stops on `go(0)`. Each mutant's step on `go(0)` is undefined: without a claim
    // (a removed end), against a `total` claim and against a `preserves-definedness` claim.
    // A contradicted claim makes the mutant's theory inconsistent on that input, so its empty
    // set of ends is no evidence: the case is `unsupported`, never a kill.
    let explicit = || {
        vec![BTreeMap::from([(
            "N".to_owned(),
            Value::Int(BigInt::from(0)),
        )])]
    };
    for paths in [PathMode::OnePath, PathMode::AllPaths] {
        let mut killed = spec_on(&CLAIMSTEP, &CLAIMSTEP_PARTIAL, "claimstep/go.pgm", None);
        killed.holes[0] = int_hole("N", "claimstep/go.pgm", "5", "5", 9);
        killed.proposers.explicit = explicit();
        killed.options.paths = paths;
        let report = Campaign::new(killed.clone())
            .expect("valid")
            .run(Budget::Cases(4), None);
        let witness = report
            .witness()
            .unwrap_or_else(|| panic!("{paths:?}: a kill, not {:?}", report.outcome));
        assert_eq!(witness.first.kill, Some(KillKind::RemovedEnd), "{paths:?}");
        for mutant in [&CLAIMSTEP_TOTAL, &CLAIMSTEP_PRESERVES] {
            let mut spec = killed.clone();
            spec.definitions.mutant = Some(Arc::new(mutant.compiled().definition()));
            let report = Campaign::new(spec)
                .expect("valid")
                .run(Budget::Cases(32), None);
            assert!(
                report.engine_defects.is_empty(),
                "{}: {:?}",
                mutant.file,
                report.engine_defects
            );
            assert!(
                report.no_witness().is_some(),
                "{} {paths:?}: {:?}",
                mutant.file,
                report.outcome
            );
            assert!(
                report.totals.classes.get(&OutcomeClass::Unsupported) >= Some(&1),
                "{} {paths:?}: go(0) is unsupported: {:?}",
                mutant.file,
                report.totals.classes
            );
        }
    }
}

#[test]
fn a_mutant_that_removes_an_end_is_killed_in_the_one_path_mode_too() {
    // FZ-08's coin-prio: `flip(N)` has the single end N + 1, inside the baseline's set {N, N + 1}.
    // Its one path cannot show that N is missing; the one-path mode re-runs the mutant on all
    // paths because a removed end is the only kill left, and the anchor is killed.
    let report = Campaign::new(spec(&COIN_PRIO))
        .expect("valid")
        .run(Budget::Cases(4), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    let witness = report
        .witness()
        .unwrap_or_else(|| panic!("a kill, not {:?}", report.outcome));
    assert_eq!(witness.first.kill, Some(KillKind::RemovedEnd));
    assert_eq!(
        witness.first.holes[0].value,
        Value::Int(BigInt::from(3)),
        "the anchor kills"
    );
    assert_eq!(
        witness.first.sides[1].final_configurations.len(),
        1,
        "the mutant's complete set, from its all-paths run"
    );
}

#[test]
fn a_mark_that_a_state_set_merge_moved_to_the_result_list_is_no_evidence() {
    // DIAMOND's two paths converge on d(N); only the `c` path reads a chosen value, and under
    // state sets its mark is on the result's list, not on the merged leaf. As the baseline it
    // makes every case `baseline-incomplete`; as the mutant on all paths every would-be kill
    // (d(N) is not the other side's d(N + 1)) `unsupported`; on one path the mutant follows `b`,
    // which reads nothing, so its end d(N) kills.
    let spec = |baseline, mutant, paths| {
        let mut spec = spec_on(baseline, mutant, "diamond/go.pgm", None);
        spec.holes[0] = int_hole("N", "diamond/go.pgm", "5", "5", 9);
        spec.proposers.explicit.clear();
        spec.options.paths = paths;
        // A depth bound, not the default work bound, under which every leaf carries every mark.
        spec.options.max_depth = Some(50);
        spec
    };
    for paths in [PathMode::OnePath, PathMode::AllPaths] {
        let report = Campaign::new(spec(&DIAMOND, &DIAMOND_PLUS, paths))
            .expect("valid")
            .run(Budget::Cases(4), None);
        assert_eq!(
            report.totals.classes,
            BTreeMap::from([(OutcomeClass::BaselineIncomplete, 4)]),
            "{paths:?}"
        );
    }
    let report = Campaign::new(spec(&DIAMOND_PLUS, &DIAMOND, PathMode::AllPaths))
        .expect("valid")
        .run(Budget::Cases(4), None);
    assert_eq!(
        report.totals.classes,
        BTreeMap::from([(OutcomeClass::Unsupported, 4)])
    );
    let report = Campaign::new(spec(&DIAMOND_PLUS, &DIAMOND, PathMode::OnePath))
        .expect("valid")
        .run(Budget::Cases(4), None);
    assert_eq!(
        report.witness().map(|witness| witness.first.kill),
        Some(Some(KillKind::AddedEnd)),
        "{:?}",
        report.outcome
    );
}
