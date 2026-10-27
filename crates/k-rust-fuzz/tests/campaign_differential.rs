//! The engine's wiring of the differential target (ARCHITECTURE 4.3, 7): both sides run per
//! case, confirmation re-runs both, equivalent definitions run no case. The judge itself is
//! FZ-08's and is tested in `src/target/differential.rs`.

mod support;

use std::{collections::BTreeMap, sync::Arc};

use k_rust_fuzz::{
    BackendRoute, Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions,
    HoleDecl, HoleLocation, OutcomeClass, ProgramInput, ProposerConfig, SpanAddress, Target,
    TargetKind,
    exec::UnjudgedReason,
    report::{
        CampaignOutcome, DefinitionRole, DomainTotals, FindingKind, FindingVerdict, HitLabel,
        KillKind, Reaching,
    },
    spec::DEFAULT_REJECTION_CAP,
    spec::PathMode,
    target::DifferentialTarget,
    values::{Constraints, GenerationBounds, IntRange, Value},
};
use num_bigint::BigInt;
use support::{
    CLAIMSTEP, CLAIMSTEP_PARTIAL, CLAIMSTEP_PRESERVES, CLAIMSTEP_TOTAL, COIN, COIN_KILL,
    COIN_LAYOUT, COIN_PRIO, COIN_SWAPPED, DIA, DIA_M, DIAMOND, DIAMOND_PLUS, Fixture,
    IMP_ADD_BECOMES_SUB, IMP_ADD_COMMUTED, IMP_AND_TRUE_IGNORES_RHS, IMP_DECL_ALLOWS_REDECLARATION,
    IMP_DIFF, IMP_DIV_GUARD_DROPPED, INIT, INIT_C, INIT_M, KPLACE, KPLACE_M, LIST_ROW, LIST_ROW_M,
    MAC, MAC_KILL, OV, OV_INTS, OV_PREPEND, OV_SIZE, OWISE, OWISE_M, OWISE_X, R2_ADDMEMBER,
    R2_ADDMEMBER_M, R2_ANYW, R2_ANYW_M, R2_OVER, R2_OVER_M, R2_SPOOF, R2_SPOOF_M, R3_MODOV,
    R3_MODOV_M, R3_PLAINQ, R3_PLAINQ_M, R3_PROPAGATE, R3_PROPAGATE_M, R4_EMPTY, R4_EMPTY_M,
    R4_HOOKITE, R4_HOOKITE_M, R4_PARTNORULE, R4_PARTNORULE_M, REPLACE_PRIORITY, REPLACE_PRIORITY_M,
    RERUN, RERUN_DROP,
};
#[cfg(feature = "z3")]
use support::{R2_PARAM, R2_PARAM_M};

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
                column: None,
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
            data_end: true,
            comparable: false,
            query_confirmable: false,
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
    // A krun line per side (FZ-POLISH S10, S-T7): the baseline on all paths, the mutant's added
    // end on its one path, each on its own compiled directory, with the instantiated program.
    let case = witness.shrunk.as_ref().unwrap_or(&witness.first);
    let program = case.program.as_deref().expect("the instantiated program");
    let Value::Int(n) = &case.holes[0].value else {
        panic!("an Int")
    };
    assert_eq!(program.trim_end(), format!("flip({n})"));
    let baseline = witness
        .krun_command
        .as_deref()
        .expect("a baseline krun line");
    assert!(
        baseline.starts_with("krust krun --definition <definition-dir> ")
            && baseline.contains(" --strategy all ")
            && baseline.contains(&format!("-e 'flip({n})")),
        "{baseline}"
    );
    let mutant = witness
        .mutant_krun_command
        .as_deref()
        .expect("a mutant krun line");
    assert!(
        mutant.starts_with("krust krun --definition <mutant-dir> ")
            && mutant.contains(" --strategy any ")
            && mutant.contains(&format!("-e 'flip({n})")),
        "{mutant}"
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
                step: None,
                configuration: None,
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
        "In 10 of them a baseline path stopped at max-depth 3: raise max-depth if the program ends \
         on those values",
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
            column: None,
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
    // GUIDE-USABILITY 7 (FZ-ENGINE-R4): the coverage is the mutant's, and a rule the baseline
    // shares (the same unique id) is named where the baseline writes it, in `imp.k`; only the
    // edited division rule, which the baseline lacks, is named in the mutant's file.
    let names = &report.totals.coverage.names;
    let sources = |file: &str| {
        names
            .values()
            .filter(|name| name.locations.iter().any(|at| at.source == file))
            .count()
    };
    assert!(sources("imp.k") > 1, "{names:?}");
    assert!(sources("imp-div-guard-dropped.k") <= 1, "{names:?}");
}

/// Each witness side records its run's work and, at an undefined step, the rule whose step is
/// undefined (FZ-COMPARABLE-B, S4 and S5): `div-guard-dropped`'s mutant takes its division rule
/// at `2 / 0`, whose result is undefined, so its one leaf is `trivial` and names that rule, while
/// the baseline's stuck leaf names none.
#[test]
fn a_witness_names_each_sides_work_and_the_rule_of_an_undefined_step() {
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
    let witness = report
        .witness()
        .unwrap_or_else(|| panic!("a kill, not {:?}", report.outcome));
    for case in [Some(&witness.first), witness.shrunk.as_ref()]
        .into_iter()
        .flatten()
    {
        let [baseline, mutant] = case.sides.as_slice() else {
            panic!("two sides: {:?}", case.sides);
        };
        assert!(baseline.work.is_some_and(|work| work > 0), "{baseline:?}");
        assert!(mutant.work.is_some_and(|work| work > 0), "{mutant:?}");
        assert!(baseline.undefined_rules.is_empty(), "{baseline:?}");
        assert_eq!(mutant.halts, [k_rust::backend::HaltReasonOutput::Trivial]);
        let [Some(rule)] = mutant.undefined_rules.as_slice() else {
            panic!("the mutant's undefined step names its rule: {mutant:?}");
        };
        assert_eq!(rule.len(), 64, "a unique id: {rule}");
    }
    // The fields read back.
    let text = report.to_canonical_json();
    assert!(text.contains(r#""undefined-rules":[""#), "{text}");
    assert_eq!(k_rust_fuzz::FuzzReport::from_json(&text).ok(), Some(report));
}

/// A filter that accepts every case gives the unfiltered campaign's report, byte for byte, apart
/// from `identity.filter` (FZ-COMPARABLE-B review M8): the filter only removes candidates, on a
/// campaign whose witness is confirmed and shrunk.
#[test]
fn an_accepting_filter_gives_the_unfiltered_report() {
    struct Accept(usize);
    impl k_rust_fuzz::WitnessFilter for Accept {
        fn id(&self) -> String {
            "accept-all".into()
        }
        fn judge(
            &mut self,
            _case: &k_rust_fuzz::report::WitnessCase,
        ) -> Result<(), k_rust_fuzz::FilterRefusal> {
            self.0 += 1;
            Ok(())
        }
    }
    let spec = || {
        trial_spec(
            &IMP_DIFF,
            &IMP_DIV_GUARD_DROPPED,
            "imp-diff/primes.imp",
            primes_holes(),
            vec![int_assignment(&[("I", 0), ("M", 7)])],
            PathMode::OnePath,
        )
    };
    let unfiltered = Campaign::new(spec())
        .expect("valid")
        .run(Budget::Cases(8), None);
    let mut filter = Accept(0);
    let mut filtered =
        Campaign::new(spec())
            .expect("valid")
            .run_filtered(Budget::Cases(8), None, &mut filter);
    assert!(
        filter.0 > 0,
        "the filter judged the hit and its shrink candidates"
    );
    assert!(
        unfiltered
            .witness()
            .is_some_and(|witness| witness.shrunk.is_some()),
        "{:?}",
        unfiltered.outcome
    );
    assert_eq!(
        filtered.identity.filter.take().as_deref(),
        Some("accept-all")
    );
    assert_eq!(filtered.to_canonical_json(), unfiltered.to_canonical_json());
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
            column: None,
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

/// Final review S1 (FZ-ENGINE-R4): on `go(0)` the mutant's initial state has no instance (its
/// initializer `f` is undefined there), so the mutant gives the input no run and its set of ends
/// is empty, while the baseline ends with `0` in `<x>`. That is a removed end, in both path
/// modes (the mutant has no path to re-run), not a rejected input; the other values agree.
#[test]
fn a_mutant_whose_initial_state_has_no_instance_loses_the_baseline_end() {
    for paths in [PathMode::AllPaths, PathMode::OnePath] {
        let mut spec = spec_on(&INIT, &INIT_M, "init/go.pgm", None);
        spec.holes[0].constraints.range = Some(IntRange {
            min: Some(BigInt::from(0)),
            max: Some(BigInt::from(3)),
        });
        spec.proposers.explicit = vec![BTreeMap::from([(
            "N".to_owned(),
            Value::Int(BigInt::from(1)),
        )])];
        spec.options.paths = paths;
        let report = Campaign::new(spec)
            .expect("valid")
            .run(Budget::Cases(20), None);
        assert!(
            report.engine_defects.is_empty(),
            "{:?}",
            report.engine_defects
        );
        let witness = report
            .witness()
            .unwrap_or_else(|| panic!("{paths:?}: a kill, not {:?}", report.outcome));
        assert_eq!(witness.first.kill, Some(KillKind::RemovedEnd), "{paths:?}");
        assert_eq!(witness.first.holes[0].value, Value::Int(BigInt::from(0)));
        assert_eq!(witness.first.reaching.role, DefinitionRole::Baseline);
        assert!(
            !report.totals.classes.contains_key(&OutcomeClass::Rejected),
            "{paths:?}: {:?}",
            report.totals.classes
        );
    }
}

/// Final review N1 (FZ-ENGINE-R4): the mutant's end `<k> done(3) </k>` names a constructor the
/// baseline does not declare, so it is no term of the baseline's signature and none of the
/// baseline's ends; it is data in the mutant, so the case is an added end, not
/// `mutant-end-not-data`.
#[test]
fn an_end_naming_a_symbol_the_baseline_lacks_is_an_added_end() {
    let mut spec = spec_on(&INIT, &INIT_C, "init/go.pgm", None);
    spec.proposers.explicit = Vec::new();
    let report = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(2), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    let witness = report.witness().unwrap_or_else(|| {
        panic!(
            "a kill, not {:?} with {:?}",
            report.outcome, report.totals.unsupported_reasons
        )
    });
    assert_eq!(witness.first.kill, Some(KillKind::AddedEnd));
    assert_eq!(witness.first.reaching.role, DefinitionRole::Mutant);
    let mutant_ends = &witness.first.sides[1].final_configurations;
    assert!(
        mutant_ends.iter().any(|end| end.contains("Lbldone")),
        "{mutant_ends:?}"
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

#[test]
fn a_re_run_case_is_judged_and_explained_by_the_re_run() {
    // INT7 (the merge of FZ-DIFFEND and FZ-UNSUPPORTED): RERUN_DROP's one path reaches a(N),
    // inside the baseline's set, and misses the baseline's data end c(N), so the one-path mode
    // re-runs it on all paths. The class, the reason and the cut come from that all-paths
    // result in the all-paths mode: its set {a(N), c(N)} lacks the baseline's b(opaque(N)),
    // which is not data, so no case can be judged. Judging the one path in the one-path mode
    // would give `miss`; judging it as an all-paths set would remove c(N), a false kill.
    for paths in [PathMode::OnePath, PathMode::AllPaths] {
        let mut spec = spec_on(&RERUN, &RERUN_DROP, "rerun/go.pgm", None);
        spec.holes[0] = int_hole("N", "rerun/go.pgm", "5", "5", 9);
        spec.proposers.explicit.clear();
        spec.options.paths = paths;
        let report = Campaign::new(spec)
            .expect("valid")
            .run(Budget::Cases(4), None);
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
            BTreeMap::from([(OutcomeClass::Unsupported, 4)]),
            "{paths:?}"
        );
        assert_eq!(
            report.totals.unsupported_reasons,
            BTreeMap::from([(UnjudgedReason::BaselineEndNotData, 4)]),
            "{paths:?}"
        );
    }
}

// ---- ends that hold overload applications (FZ-DATAEND; FZ-OVERLIST, TRIAL2 S-T1)

/// `h(N)` on `baseline` and `mutant`, the anchor and 16 cases.
fn ov_report(baseline: &'static Fixture, mutant: &'static Fixture) -> k_rust_fuzz::FuzzReport {
    let report = Campaign::new(spec_on(baseline, mutant, "ov/three.pgm", None))
        .expect("valid")
        .run(Budget::Cases(16), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    report
}

/// Every case that ran is `unsupported` (a negative value does not parse as `h`'s argument and is
/// `rejected`), and some case ran.
fn assert_only_unsupported(report: &k_rust_fuzz::FuzzReport) {
    let classes = &report.totals.classes;
    assert!(
        classes.contains_key(&OutcomeClass::Unsupported),
        "{classes:?}"
    );
    assert!(
        classes
            .keys()
            .all(|class| matches!(class, OutcomeClass::Unsupported | OutcomeClass::Rejected)),
        "{classes:?}"
    );
}

/// The baseline ends with `_,_Exps(3, .Ids)`, the mutant with `_,_Exps(0, _,_Exps(3, .Ids))`:
/// irreducible applications of the overload head `_,_Exps`, which both definitions give the same
/// overload equations. Both ends are data, so the anchor kills; before FZ-DATAEND condition 4
/// read only free constructors and every case was `unsupported`.
#[test]
fn an_end_holding_an_irreducible_overload_application_is_compared() {
    let report = ov_report(&OV, &OV_PREPEND);
    let witness = report.witness().expect("a kill");
    assert_eq!(witness.first.kill, Some(KillKind::AddedEnd));
    assert_eq!(witness.first.holes[0].value, Value::Int(BigInt::from(3)));
    assert!(
        witness
            .clean_leaf_facts
            .contains(&"mutant-end-data".to_owned()),
        "{:?}",
        witness.clean_leaf_facts
    );
}

/// The mutant adds a list to the family, so `_,_Exps` has an overload equation the baseline
/// lacks: an application of it that is a normal form of the baseline is reducible in the mutant,
/// and the two definitions do not name the same values with it. The baseline's end holds one, so
/// no end is compared: never a kill.
#[test]
fn a_mutant_whose_overload_equations_differ_is_never_killed_through_them() {
    let report = ov_report(&OV, &OV_INTS);
    assert_not_comparable(&report, &[DefinitionRole::Mutant]);
}

/// An end that holds an unevaluated total function application is not data, on either side:
/// its value is whatever a model makes of the function, which may be the other side's end.
#[test]
fn an_end_holding_a_function_application_is_never_compared() {
    for (baseline, mutant, reason) in [
        (&OV, &OV_SIZE, UnjudgedReason::MutantEndNotData),
        (&OV_SIZE, &OV, UnjudgedReason::BaselineEndNotData),
    ] {
        let report = ov_report(baseline, mutant);
        assert!(report.witness().is_none(), "{:?}", report.outcome);
        assert_only_unsupported(&report);
        // Both definitions are confluent: the side whose end is not data is named (INT7).
        assert_eq!(
            report.totals.unsupported_reasons.keys().collect::<Vec<_>>(),
            vec![&reason],
            "{}",
            baseline.file
        );
    }
}

/// FZ-DATAEND review B2: in a broken overload family (`.Exps` lowers to both `.Ids` and `.Vals`,
/// a pair that does not join) the overload axioms equate the constructor terms `.Ids` and
/// `.Vals`. The baseline stores one and the mutant the other: one value, so never a kill, though
/// both ends are constructor terms. Main and fz26/diffend kill it.
#[test]
fn constructor_ends_a_broken_overload_family_equates_are_never_compared() {
    let report = Campaign::new(spec_on(&DIA, &DIA_M, "dia/go.pgm", None))
        .expect("valid")
        .run(Budget::Cases(8), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    assert_not_comparable(&report, &[DefinitionRole::Baseline, DefinitionRole::Mutant]);
}

/// FZ-DATAEND review B1: `f_K(kseq(inj(X), dotk)) = f_Exp(X)` is an overload equation of another
/// shape than the argument covers. The baseline's end `f_K(bar ~> .K)` is irreducible there, and
/// the mutant, which adds `Exp ::= Bar`, ends with its lowering `f_Exp(bar)`: one value of the
/// mutant. `f_K` is no data head, so never a kill (the first FZ-DATAEND head killed it).
#[test]
fn an_overload_of_another_shape_is_never_compared_through() {
    let report = Campaign::new(spec_on(&KPLACE, &KPLACE_M, "kplace/go.pgm", None))
        .expect("valid")
        .run(Budget::Cases(8), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    assert_not_comparable(&report, &[DefinitionRole::Baseline, DefinitionRole::Mutant]);
}

// ---- each end judged by both definitions (FZ-DATAEND review round 2)

/// 8 cases of `go(N)` on `baseline` and `mutant`, without engine defects.
fn r2_report(
    baseline: &'static Fixture,
    mutant: &'static Fixture,
    program: &str,
) -> k_rust_fuzz::FuzzReport {
    let report = Campaign::new(spec_on(baseline, mutant, program, None))
        .expect("valid")
        .run(Budget::Cases(8), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    report
}

/// R2-B1: the mutant adds `Nm ::= MInt{8}`, so the baseline's normal form
/// `f_Exp(inj{MInt{8},Exp}(2p8))` lowers in the mutant to the mutant's end. Data in the baseline,
/// not in the mutant: never a kill (the round-1 head killed it). Parametric sorts need Z3 sort
/// inference to compile.
#[cfg(feature = "z3")]
#[test]
fn an_end_a_parametric_subsort_makes_reducible_in_the_mutant_is_never_compared() {
    let report = r2_report(&R2_PARAM, &R2_PARAM_M, "r2-param/go.pgm");
    assert!(report.witness().is_none(), "{:?}", report.outcome);
    assert_only_unsupported(&report);
}

/// R2-B2: the mutant adds the overload member `Bot ::= f(Bot)`, so the baseline's free
/// constructor `f_Nm` is an overload head of the mutant, and `f_Nm(inj(b))` its lowering's
/// source. Never a kill (main and fz26/diffend kill it).
#[test]
fn an_end_an_added_overload_member_lowers_is_never_compared() {
    let report = r2_report(&R2_ADDMEMBER, &R2_ADDMEMBER_M, "r2-addmember/go.pgm");
    assert!(report.witness().is_none(), "{:?}", report.outcome);
    assert_only_unsupported(&report);
}

/// R2-B2 without overloads: the mutant adds `rule c(1) => d [anywhere]`, so the baseline's end
/// `c(1)` is the mutant's end `d` in the mutant's theory. Never a kill (main kills it).
#[test]
fn an_end_an_added_anywhere_rule_rewrites_is_never_compared() {
    let report = r2_report(&R2_ANYW, &R2_ANYW_M, "r2-anyw/go.pgm");
    assert!(report.witness().is_none(), "{:?}", report.outcome);
    assert_only_unsupported(&report);
}

/// R2-S1, revised by round 3: an unused overload placed across `K` is a premise violation the
/// load reports, so the definition's equations are not shown confluent and none of its ends is
/// data, `kseq` and `dotk` included: the ends `1` and `2` are not compared, and the report says
/// why.
#[test]
fn an_unused_k_placed_overload_leaves_the_definition_without_data() {
    let report = r2_report(&R2_OVER, &R2_OVER_M, "r2-over/go.pgm");
    assert_not_comparable(&report, &[DefinitionRole::Baseline, DefinitionRole::Mutant]);
}

/// A definition without data makes every case unjudgeable, which is known before the first
/// case (FZ-POLISH, not comparable at setup): the campaign runs no case and ends
/// `not-comparable`, naming the definitions `sides` without data; the report names, for each,
/// why (one warning, and every finding in `definition-findings`).
fn assert_not_comparable(report: &k_rust_fuzz::FuzzReport, sides: &[DefinitionRole]) {
    match &report.outcome {
        CampaignOutcome::NotComparable {
            sides: named,
            statement,
        } => {
            assert_eq!(named, sides);
            assert!(statement.contains("No case was run"), "{statement}");
        }
        other => panic!("not comparable expected: {other:?}"),
    }
    assert_eq!(report.totals.cases, 0, "{:?}", report.totals);
    assert!(report.totals.classes.is_empty(), "{:?}", report.totals);
    for side in sides {
        let name = match side {
            DefinitionRole::Baseline => "baseline",
            DefinitionRole::Mutant => "mutant",
        };
        let prefix = format!("definition-not-confluent ({name}): ");
        assert!(
            report
                .warnings
                .iter()
                .any(|warning| warning.starts_with(&prefix)),
            "{prefix} missing in {:?}",
            report.warnings
        );
        assert!(
            report
                .definition_findings
                .iter()
                .any(|finding| finding.side == *side && !finding.assumed),
            "no finding of the {name}: {:?}",
            report.definition_findings
        );
    }
}

// ---- definitions whose equations are not confluent (FZ-DATAEND review round 3)

/// R3-B1: `p(_:Id, _:Ids) => a` and `p(_:Exp, _:Exps) => bb` overlap modulo the overload axiom,
/// so the theory equates `a` with `bb` and through every equation that tells them apart. The
/// definitions' checks report the pair: no end is data, never a kill (main and fz26/diffend kill
/// it), and the report carries the finding.
#[test]
fn a_definition_whose_check_reports_a_pair_has_no_data() {
    let report = r2_report(&R3_MODOV, &R3_MODOV_M, "r3-modov/go.pgm");
    assert_not_comparable(&report, &[DefinitionRole::Baseline, DefinitionRole::Mutant]);
}

/// An equivalent pair is reported `equivalent` before a finding makes it not comparable, with
/// a witness filter as without one (FZ-COMPARABLE-B review D1): the definitions denote the same
/// theory, which no data judgement changes.
#[test]
fn an_equivalent_pair_without_data_is_equivalent() {
    struct Accept;
    impl k_rust_fuzz::WitnessFilter for Accept {
        fn id(&self) -> String {
            "accept-all".into()
        }
        fn judge(
            &mut self,
            _case: &k_rust_fuzz::report::WitnessCase,
        ) -> Result<(), k_rust_fuzz::FilterRefusal> {
            Ok(())
        }
    }
    let spec = || spec_on(&R3_MODOV, &R3_MODOV, "r3-modov/go.pgm", None);
    let report = Campaign::new(spec())
        .expect("valid")
        .run(Budget::Cases(8), None);
    assert!(
        matches!(report.outcome, CampaignOutcome::Equivalent),
        "{:?}",
        report.outcome
    );
    let mut filtered =
        Campaign::new(spec())
            .expect("valid")
            .run_filtered(Budget::Cases(8), None, &mut Accept);
    assert_eq!(
        filtered.identity.filter.take().as_deref(),
        Some("accept-all")
    );
    assert_eq!(filtered.to_canonical_json(), report.to_canonical_json());
}

/// A witness filter whose `id` panics aborts the run with `client-panic` before anything else
/// ends it (review M4): before a run of cases, and before an equivalent pair's outcome. The
/// identity is read first on every path, the rebuild of a second run's backends included.
#[test]
fn a_panicking_filter_identity_aborts_every_run_with_client_panic() {
    struct Nameless;
    impl k_rust_fuzz::WitnessFilter for Nameless {
        fn id(&self) -> String {
            panic!("no name")
        }
        fn judge(
            &mut self,
            _case: &k_rust_fuzz::report::WitnessCase,
        ) -> Result<(), k_rust_fuzz::FilterRefusal> {
            Ok(())
        }
    }
    for mutant in [&IMP_DIV_GUARD_DROPPED, &IMP_DIFF] {
        let mut campaign = Campaign::new(trial_spec(
            &IMP_DIFF,
            mutant,
            "imp-diff/primes.imp",
            primes_holes(),
            Vec::new(),
            PathMode::OnePath,
        ))
        .expect("valid");
        for _ in 0..2 {
            let report = campaign.run_filtered(Budget::Cases(2), None, &mut Nameless);
            let CampaignOutcome::Aborted { kind, reason, .. } = &report.outcome else {
                panic!("{:?}", report.outcome);
            };
            assert_eq!(*kind, k_rust_fuzz::report::AbortKind::ClientPanic);
            assert!(reason.contains("in `id`"), "{reason}");
            assert_eq!(report.totals.cases, 0);
        }
    }
}

/// R3-B1: the broken diamond's identification of `.Ids` with `.Vals` reaches `a` and `bb`
/// through `pick`. Never a kill (main and fz26/diffend kill it).
#[test]
fn an_identification_reached_through_a_function_is_never_a_kill() {
    let report = r2_report(&R3_PROPAGATE, &R3_PROPAGATE_M, "r3-propagate/go.pgm");
    assert_not_comparable(&report, &[DefinitionRole::Baseline, DefinitionRole::Mutant]);
}

/// R3-S1: `q(_) => a` and `q(_) => bb` equate `a` with `bb`; the load's check does not pair them
/// (they withdraw no value claim), the full check the campaign runs at setup does. Never a kill.
#[test]
fn a_function_pair_only_the_full_check_finds_is_never_a_kill() {
    let report = r2_report(&R3_PLAINQ, &R3_PLAINQ_M, "r3-plainq/go.pgm");
    assert_not_comparable(&report, &[DefinitionRole::Baseline, DefinitionRole::Mutant]);
}

/// FZ-POLISH review round 3: R3-S1's pair is genuine: at `q(0)` both equations apply and the
/// input has two normal forms, `a` and `bb`. The finding names both equations by their written
/// positions (no 64-hex id, no KORE name), and carries the name `assume-joined` takes.
#[test]
fn a_pair_whose_input_has_two_normal_forms_is_genuine() {
    let report = r2_report(&R3_PLAINQ, &R3_PLAINQ_M, "r3-plainq/go.pgm");
    let baseline = report
        .definition_findings
        .iter()
        .filter(|finding| finding.side == DefinitionRole::Baseline)
        .collect::<Vec<_>>();
    let [finding] = baseline[..] else {
        panic!("one baseline finding: {:?}", report.definition_findings);
    };
    assert_eq!(finding.verdict, FindingVerdict::Genuine, "{finding:?}");
    let instance = finding.instance.as_ref().expect("the instance");
    assert_eq!(instance.overlap, "q ( 0 )", "{instance:?}");
    let mut values = instance.values.clone();
    values.sort();
    assert_eq!(values, ["a", "bb"]);
    // Both values are data: no stuck application (S2B-T3).
    assert_eq!(instance.stuck, [None, None], "{instance:?}");
    assert!(
        finding
            .reason
            .ends_with("k-rust's result for it depends on the order it tries the equations"),
        "{}",
        finding.reason
    );
    assert_eq!(finding.kind, FindingKind::Pair);
    assert_eq!(finding.position.as_deref(), Some("root"));
    // Named relative to the main module's file, `r3-plainq/b.k` (FZ-REPLAY-WHOLE S1).
    for equation in &finding.equations {
        assert!(equation.starts_with("b.k:"), "{equation}");
    }
    let name = finding.name.as_deref().expect("a pair's name");
    assert!(
        name.starts_with("b.k:") && name.ends_with("@root"),
        "{name}"
    );
    assert_readable(&format!("{finding:?}"));
}

/// No mangled KORE symbol and no 64-hex id in `text`.
fn assert_readable(text: &str) {
    assert!(!text.contains("Lbl"), "{text}");
    assert!(
        !text
            .split(|character: char| !character.is_ascii_hexdigit())
            .any(|word| word.len() == 64),
        "{text}"
    );
}

/// FZ-POLISH review B1 (a): OWISE's two `owise` equations give the constructors `a` and `bb`
/// of one sort where both apply. The finding is genuine, and its instance is `g(1)`: at `g(0)`
/// the priority-50 equation applies, so the owise equations do not. The reason says what the
/// instance shows.
#[test]
fn a_genuine_instance_is_one_where_both_equations_apply() {
    let report = r2_report(&OWISE, &OWISE_M, "owise/go.pgm");
    assert_not_comparable(&report, &[DefinitionRole::Baseline, DefinitionRole::Mutant]);
    let genuine = report
        .definition_findings
        .iter()
        .filter(|finding| finding.verdict == FindingVerdict::Genuine)
        .collect::<Vec<_>>();
    assert_eq!(genuine.len(), 2, "{:?}", report.definition_findings);
    for finding in genuine {
        let instance = finding.instance.as_ref().expect("the instance");
        assert_eq!(instance.overlap, "g ( 1 )", "{instance:?}");
        let mut values = instance.values.clone();
        values.sort();
        assert_eq!(values, ["a", "bb"]);
        assert!(
            finding
                .reason
                .starts_with("at g ( 1 ) both equations apply and the input has two normal forms")
                && finding.reason.ends_with(
                    "k-rust's result for it depends on the order it tries the equations"
                ),
            "{}",
            finding.reason
        );
        assert_readable(&format!("{finding:?}"));
    }
}

/// FZ-POLISH review S2: R3-PROPAGATE's overload-axiom pairs have reducts that differ only by the
/// source sorts of injections; their texts are written apart (with the sorts) instead of reading
/// alike. Review S3: compiler-generated overload axioms are named
/// (`overload:GREATER:LESSER`), so the pairs can be assumed joined.
#[test]
fn reducts_that_differ_only_by_injection_sorts_are_written_apart_and_named() {
    let report = r2_report(&R3_PROPAGATE, &R3_PROPAGATE_M, "r3-propagate/go.pgm");
    assert!(!report.definition_findings.is_empty());
    for finding in &report.definition_findings {
        if let [left, right] = &finding.reducts[..] {
            assert_ne!(left, right, "{finding:?}");
        }
        let name = finding.name.as_deref().expect("every pair is named");
        assert!(name.contains("overload:"), "{name}");
        // Readable (round 2): the overloaded pair by its K labels, quoted, never mangled KORE.
        assert!(!name.contains("Lbl"), "{name}");
    }
    let mut names = report
        .definition_findings
        .iter()
        .filter_map(|finding| finding.name.clone())
        .collect::<Vec<_>>();
    names.sort();
    names.dedup();
    let mut spec = spec_on(&R3_PROPAGATE, &R3_PROPAGATE_M, "r3-propagate/go.pgm", None);
    spec.options.assume_joined = names;
    let assumed = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(1), None);
    assert!(
        assumed
            .definition_findings
            .iter()
            .all(|finding| finding.assumed),
        "{:?}",
        assumed.definition_findings
    );
}

/// FZ-POLISH review S5: `baseline:` restricts a name to the baseline, so the mutant keeps its
/// finding; with `mutant:` the baseline's name matches nothing and is refused.
#[test]
fn a_side_prefix_restricts_an_assumed_pair_to_one_definition() {
    let names = plainq_pair_names();
    let mut spec = spec_on(&R3_PLAINQ, &R3_PLAINQ_M, "r3-plainq/go.pgm", None);
    spec.options.assume_joined = vec![format!("baseline:{}", names[0])];
    let report = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(1), None);
    assert_not_comparable(&report, &[DefinitionRole::Mutant]);
    let mut spec = spec_on(&R3_PLAINQ, &R3_PLAINQ_M, "r3-plainq/go.pgm", None);
    spec.options.assume_joined = vec![format!("mutant:{}", names[0])];
    assert!(Campaign::new(spec).is_err());
}

/// FZ-POLISH review S5: an unprefixed name applies on each definition where it matches and must
/// name the same equations on both. `OW.ow1,OW.ow2@root` names `OWISE`'s owise pair on both of
/// `OWISE` and `OWISE_M` (the same equations): accepted, with a warning that the assumed pair is
/// genuine. On `OWISE_X` the labels sit on other equations: refused as ambiguous, and accepted
/// with a side prefix per definition.
#[test]
fn an_assumed_name_matching_different_pairs_on_the_two_sides_is_refused() {
    let labels = "OW.ow1,OW.ow2@root".to_owned();
    let mut spec = spec_on(&OWISE, &OWISE_M, "owise/go.pgm", None);
    spec.options.assume_joined = vec![labels.clone()];
    let run = Campaign::new(spec)
        .expect("one pair on both sides")
        .run(Budget::Cases(1), None);
    assert!(
        run.warnings.iter().any(|warning| {
            warning.starts_with("assume-joined (baseline): ") && warning.contains("is genuine")
        }),
        "{:?}",
        run.warnings
    );
    let mut spec = spec_on(&OWISE, &OWISE_X, "owise/go.pgm", None);
    spec.options.assume_joined = vec![labels.clone()];
    let error = Campaign::new(spec).err().expect("refused");
    assert!(
        error.to_string().contains("different equation pairs"),
        "{error}"
    );
    let mut spec = spec_on(&OWISE, &OWISE_X, "owise/go.pgm", None);
    spec.options.assume_joined = vec![format!("baseline:{labels}"), format!("mutant:{labels}")];
    assert!(Campaign::new(spec).is_ok());
}

/// The names of R3-PLAINQ's pair in each definition, as the report's findings give them: the
/// baseline's (in `b.k`), then the mutant's (in `m.k`).
fn plainq_pair_names() -> Vec<String> {
    let report = r2_report(&R3_PLAINQ, &R3_PLAINQ_M, "r3-plainq/go.pgm");
    [DefinitionRole::Baseline, DefinitionRole::Mutant]
        .into_iter()
        .map(|side| {
            report
                .definition_findings
                .iter()
                .find(|finding| finding.side == side)
                .and_then(|finding| finding.name.clone())
                .expect("a pair's name")
        })
        .collect()
}

/// FZ-POLISH, assume-joined: naming R3-PLAINQ's pair reads both definitions as if it joined, so
/// their ends are data and the cases run; under that premise the mutant's `bb` against the
/// baseline's `a` is a kill. The report's identity records the assumption, a warning states
/// that the verdict holds only under it, and the findings are kept, marked assumed. (The
/// assumption is false here: the definitions do equate `a` and `bb`. The kill is sound only
/// relative to it, which is what the warning says.)
#[test]
fn an_assumed_pair_lets_the_cases_run_under_the_stated_premise() {
    let names = plainq_pair_names();
    // The baseline's pair alone leaves the mutant without data.
    let mut spec = spec_on(&R3_PLAINQ, &R3_PLAINQ_M, "r3-plainq/go.pgm", None);
    spec.options.assume_joined = vec![names[0].clone()];
    let report = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(8), None);
    assert_not_comparable(&report, &[DefinitionRole::Mutant]);
    let mut spec = spec_on(&R3_PLAINQ, &R3_PLAINQ_M, "r3-plainq/go.pgm", None);
    spec.options.assume_joined.clone_from(&names);
    let report = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(8), None);
    assert!(report.witness().is_some(), "{:?}", report.outcome);
    assert_eq!(report.identity.options.assume_joined, names);
    assert!(
        report
            .warnings
            .iter()
            .any(|warning| warning.starts_with("assume-joined: ")
                && names.iter().all(|name| warning.contains(name.as_str()))),
        "{:?}",
        report.warnings
    );
    assert!(
        report
            .definition_findings
            .iter()
            .all(|finding| finding.assumed),
        "{:?}",
        report.definition_findings
    );
    // A trailing part of the path names the pair too.
    let longer = names
        .iter()
        .map(|name| {
            let (first, rest) = name.split_once(',').expect("two equations");
            format!("r3-plainq/{first},r3-plainq/{rest}")
        })
        .collect::<Vec<_>>();
    let mut spec = spec_on(&R3_PLAINQ, &R3_PLAINQ_M, "r3-plainq/go.pgm", None);
    spec.options.assume_joined = longer;
    let report = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(1), None);
    assert!(report.witness().is_some(), "{:?}", report.outcome);
}

/// FZ-POLISH, assume-joined: a name that matches no pair finding is refused, as is a name given
/// to a campaign that reads no data end.
#[test]
fn an_assumed_pair_that_names_no_finding_is_refused() {
    let mut plainq = spec_on(&R3_PLAINQ, &R3_PLAINQ_M, "r3-plainq/go.pgm", None);
    plainq.options.assume_joined = vec!["b.k:1:1,b.k:2:1@root".into()];
    let error = Campaign::new(plainq).err().expect("refused");
    assert!(
        error.to_string().contains("matches no unjoined pair"),
        "{error}"
    );
    let mut plainq = spec_on(&R3_PLAINQ, &R3_PLAINQ_M, "r3-plainq/go.pgm", None);
    plainq.options.assume_joined = vec!["not a name".into()];
    assert!(Campaign::new(plainq).is_err());
    // COIN's definitions have data and no finding.
    let mut coin = spec(&COIN_KILL);
    coin.options.assume_joined = plainq_pair_names();
    assert!(Campaign::new(coin).is_err());
}

// ---- pairs over a sort with no normal form (FZ-DATAEND review round 4, FZ-EMPTYSORT)

/// R4: `f(_:S) => a` and `f(_:S) => bb` overlap only over a sort with no normal form: `S` has no
/// production (`r4-empty`), or only the partial function `g`, which no rule rewrites
/// (`r4-partnorule`). Every model has an element `s` of `S`, so `a = f(s) = bb` there; the full
/// check reports the pair, naming `S`, and no end is data, so the campaign is not comparable
/// at setup (FZ-POLISH) and runs no case. Never a kill (main killed both).
#[test]
fn a_pair_over_a_sort_with_no_normal_form_leaves_the_definition_without_data() {
    for (baseline, mutant, program) in [
        (&R4_EMPTY, &R4_EMPTY_M, "r4-empty/go.pgm"),
        (&R4_PARTNORULE, &R4_PARTNORULE_M, "r4-partnorule/go.pgm"),
    ] {
        let report = r2_report(baseline, mutant, program);
        assert!(
            report.witness().is_none(),
            "{program}: {:?}",
            report.outcome
        );
        assert_not_comparable(&report, &[DefinitionRole::Baseline, DefinitionRole::Mutant]);
        for side in [DefinitionRole::Baseline, DefinitionRole::Mutant] {
            assert!(
                report
                    .definition_findings
                    .iter()
                    .any(|finding| finding.side == side
                    && finding.reason.contains("a sort with no normal form")
                    && finding.reason.contains("SortS")
                    // No normal form of `S` exists to build an instance from.
                    && finding.verdict == FindingVerdict::Undecided),
                "{program}: {:?}",
                report.definition_findings
            );
        }
    }
}

/// TRIAL2 item 5 (FZ-POLISH N-T2): blind sampling at seed 8 kills `and-true-ignores-rhs` on
/// `primes.imp` with `M = 8, N = 8, I = 1, T = 0`, as TRIAL2's seed did. `M` cannot shrink while
/// `N` is 8 (the outer loop `n <= m` is not entered), and only once `N` has shrunk to 0 does
/// `M = 1` kill; shrinking repeats its passes over every hole, value trees included, so `M` ends
/// at 1 (TRIAL2 was left with `M = 8`, its tree having been spent before `N` moved).
#[test]
fn shrinking_revisits_every_hole_and_ends_at_m_1() {
    let mut spec = trial_spec(
        &IMP_DIFF,
        &IMP_AND_TRUE_IGNORES_RHS,
        "imp-diff/primes.imp",
        primes_holes(),
        Vec::new(),
        PathMode::OnePath,
    );
    spec.seed = 8;
    let report = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(300), None);
    let witness = report.witness().expect("a kill");
    let show = |case: &k_rust_fuzz::report::WitnessCase| {
        case.holes
            .iter()
            .map(|hole| format!("{}={}", hole.name, hole.k_text.as_deref().unwrap_or("?")))
            .collect::<Vec<_>>()
            .join(", ")
    };
    assert_eq!(show(&witness.first), "M=8, N=8, I=1, T=0");
    let shrunk = witness.shrunk.as_ref().expect("a shrunk witness");
    assert_eq!(show(shrunk), "M=1, N=0, I=1, T=0");
}

/// TRIAL2 S-T5 (FZ-POLISH): `add-becomes-sub` turns `sum.imp`'s countdown `n = n + -D;` into a
/// count-up, so for `n > 0` and `D > 0` the mutant's loop does not end while the baseline's
/// does. Such cases stop at max-work on the mutant; the statement says the baseline ended
/// within so much work and that the mutant may not terminate, and does not advise raising
/// max-work for them. With `D = 0` the baseline's own loop does not end either: that case is
/// `baseline-incomplete`, and its advice to raise max-work stands.
#[test]
fn a_mutant_that_stops_at_max_work_where_the_baseline_ended_is_not_told_to_raise_it() {
    let program = "imp-diff/sum.imp";
    let mut spec = trial_spec(
        &IMP_DIFF,
        &IMP_ADD_BECOMES_SUB,
        program,
        vec![
            int_hole("N", program, "n = 3;", "3", 8),
            int_hole("S", program, "sum = 0;", "0", 8),
            int_hole("D", program, "n + -1;", "1", 8),
        ],
        vec![int_assignment(&[("N", 2), ("S", 0), ("D", 0)])],
        PathMode::OnePath,
    );
    spec.options.max_work = Some(3000);
    let report = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(6), None);
    let statement = &report.no_witness().expect("no kill").statement;
    let work_bound = report.totals.classes.get(&OutcomeClass::WorkBound).copied();
    assert!(work_bound.is_some_and(|count| count > 0), "{statement}");
    assert!(
        statement.contains(
            "stopped at max-work 3000 on the mutant, where the baseline reached all its ends \
             within"
        ),
        "{statement}"
    );
    assert!(
        statement.contains("the mutant may not terminate on this program"),
        "{statement}"
    );
    // The same fact as a field (final review ux S6).
    let diverging = report.totals.diverging.expect("diverging cases");
    assert!(
        diverging.cases > 0 && diverging.cases <= work_bound.unwrap_or(0),
        "{diverging:?}"
    );
    assert!(diverging.baseline_work > 0, "{diverging:?}");
    assert!(
        !statement.contains("cases stopped at max-work 3000: raise max-work")
            && !statement.contains("case stopped at max-work 3000: raise max-work"),
        "{statement}"
    );
    // The explicit `D = 0` case: the baseline does not end, and the old advice stands.
    assert!(
        report
            .totals
            .classes
            .get(&OutcomeClass::BaselineIncomplete)
            .is_some_and(|count| *count > 0),
        "{statement}"
    );
    assert!(
        statement.contains("a baseline path stopped at max-work 3000: raise max-work"),
        "{statement}"
    );
}

/// TRIAL2 N-T1 (FZ-POLISH): a campaign whose holes all have finite domains ends once every
/// assignment has run. An `Id` hole with the two choices `sum` (the anchor) and `n` on the
/// equivalent `add-commuted` has two assignments: the campaign stops with `domain exhausted`
/// after exactly two cases, not after its budget of 50. No assignment runs twice: a proposal
/// that repeats one is replaced by an unseen one (at seed 7 the first blind draw repeats the
/// anchor).
#[test]
fn a_finite_domain_is_exhausted_after_its_assignments() {
    let token = |text: &str| Value::Token {
        sort: "Id".into(),
        text: text.into(),
    };
    let hole = HoleDecl {
        name: "V".into(),
        sort: "Id".into(),
        location: HoleLocation::Span(SpanAddress {
            program: "imp-diff/sum.imp".into(),
            line: None,
            column: None,
            find: "int n, sum;".into(),
            literal: "sum".into(),
        }),
        constraints: Constraints {
            choices: Some(vec![token("sum"), token("n")]),
            ..Constraints::default()
        },
        allow_refused_sort: true,
    };
    let report = Campaign::new(trial_spec(
        &IMP_DIFF,
        &IMP_ADD_COMMUTED,
        "imp-diff/sum.imp",
        vec![hole],
        Vec::new(),
        PathMode::OnePath,
    ))
    .expect("valid")
    .run(Budget::Cases(50), None);
    let statement = &report.no_witness().expect("no kill").statement;
    assert_eq!(report.totals.cases, 2, "{statement}");
    assert!(
        statement.contains("Domain exhausted: every one of the 2 assignments"),
        "{statement}"
    );
    assert!(!statement.contains("The budget was spent"), "{statement}");
    // The same fact as a field (final review ux S6), and where coverage last grew.
    assert_eq!(
        report.totals.domain,
        Some(DomainTotals {
            assignments: 2,
            tried: 2,
            exhausted: true,
        })
    );
    assert!(
        report
            .totals
            .coverage_last_grew
            .is_some_and(|case| case < 2),
        "{:?}",
        report.totals.coverage_last_grew
    );
}

/// TRIAL2 N-T3 (FZ-POLISH): a token choice written as a plain string is refused with the form
/// a token is written in.
#[test]
fn a_token_choice_written_as_a_string_is_refused_with_the_token_form() {
    let hole = HoleDecl {
        name: "V".into(),
        sort: "Id".into(),
        location: HoleLocation::Span(SpanAddress {
            program: "imp-diff/sum.imp".into(),
            line: None,
            column: None,
            find: "int n, sum;".into(),
            literal: "sum".into(),
        }),
        constraints: Constraints {
            choices: Some(vec![Value::String("n".into())]),
            ..Constraints::default()
        },
        allow_refused_sort: true,
    };
    let error = Campaign::new(trial_spec(
        &IMP_DIFF,
        &IMP_ADD_COMMUTED,
        "imp-diff/sum.imp",
        vec![hole],
        Vec::new(),
        PathMode::OnePath,
    ))
    .err()
    .expect("refused")
    .to_string();
    assert!(
        error.contains(r#"{ token = { sort = "Id", text = "n" } }"#),
        "{error}"
    );
}

/// FZ-POLISH N-T1, review round 1: three holes of four values each (64 assignments) under blind
/// sampling end after exactly 64 cases, each assignment once, at every seed (the review measured
/// 722, 418 and 1059 cases when repeats ran).
#[test]
fn a_finite_product_is_exhausted_in_exactly_its_size_of_cases() {
    let program = "imp-diff/sum.imp";
    for seed in [1, 2, 3] {
        let mut spec = trial_spec(
            &IMP_DIFF,
            &IMP_ADD_COMMUTED,
            program,
            vec![
                int_hole("N", program, "n = 3;", "3", 3),
                int_hole("S", program, "sum = 0;", "0", 3),
                int_hole("D", program, "n + -1;", "1", 3),
            ],
            Vec::new(),
            PathMode::OnePath,
        );
        spec.seed = seed;
        let report = Campaign::new(spec)
            .expect("valid")
            .run(Budget::Cases(2000), None);
        let statement = &report.no_witness().expect("no kill").statement;
        assert_eq!(report.totals.cases, 64, "seed {seed}: {statement}");
        assert!(
            statement.contains("Domain exhausted: every one of the 64 assignments"),
            "seed {seed}: {statement}"
        );
    }
}

/// R4 (r4-hookite): `sel(_, _, Y) => Y` at a symbol hooked to `KEQUAL.ite` disagrees with the
/// builtin, which gives `sel(true, a, bb) = a`, so the theory equates `a` with `bb`. The full
/// check pairs the equation with the hook's written meaning and reports it: no end is data, so
/// the campaign is not comparable at setup, never a kill (main kills it).
#[test]
fn an_equation_that_disagrees_with_its_hook_leaves_the_definition_without_data() {
    let report = r2_report(&R4_HOOKITE, &R4_HOOKITE_M, "r4-hookite/go.pgm");
    assert!(report.witness().is_none(), "{:?}", report.outcome);
    assert_not_comparable(&report, &[DefinitionRole::Baseline, DefinitionRole::Mutant]);
    // The finding is about the one equation against the hook's builtin, never genuine (the
    // evaluator applies the builtin first, so k-rust's result does not depend on an order).
    for side in [DefinitionRole::Baseline, DefinitionRole::Mutant] {
        assert!(
            report
                .definition_findings
                .iter()
                .any(|finding| finding.side == side
                    && finding.kind == FindingKind::Equation
                    && finding.verdict == FindingVerdict::Undecided
                    && finding
                        .reason
                        .contains("not shown to agree with its hook `KEQUAL.ite`")),
            "{:?}",
            report.definition_findings
        );
    }
}

/// Every finding that keeps a definition without data can be assumed, a hook finding too
/// (INT8). r4-hookite's finding is named `hook:b.k:18:3` on the baseline and `hook:m.k:18:3` on
/// the mutant: the equation `sel(_, _, Y) => Y` by its written position, as `definition-findings`
/// prints it. Assumed on the baseline alone, the mutant still has no data. Assumed on both, the
/// cases run and the anchor kills (`a` against `bb`), but only for the definitions read as if
/// `sel`'s equation agreed with `KEQUAL.ite`: the premise is in the identity and in a warning,
/// and the findings are kept, marked assumed. (The premise is false here, as for the assumed
/// pairs above: the kill holds only relative to it.)
#[test]
fn an_assumed_hook_finding_lets_the_cases_run_under_the_stated_premise() {
    let report = r2_report(&R4_HOOKITE, &R4_HOOKITE_M, "r4-hookite/go.pgm");
    let printed = report
        .definition_findings
        .iter()
        .map(|finding| finding.name.clone().expect("every finding is named"))
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        printed.into_iter().collect::<Vec<_>>(),
        vec!["hook:b.k:18:3".to_owned(), "hook:m.k:18:3".to_owned()]
    );
    let mut spec = spec_on(&R4_HOOKITE, &R4_HOOKITE_M, "r4-hookite/go.pgm", None);
    spec.options.assume_joined = vec!["hook:b.k:18:3".into()];
    let report = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(8), None);
    assert_not_comparable(&report, &[DefinitionRole::Mutant]);
    let names = vec![
        "hook:b.k:18:3".to_owned(),
        "mutant:hook:m.k:18:3".to_owned(),
    ];
    let mut spec = spec_on(&R4_HOOKITE, &R4_HOOKITE_M, "r4-hookite/go.pgm", None);
    spec.options.assume_joined.clone_from(&names);
    let report = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(8), None);
    assert!(report.witness().is_some(), "{:?}", report.outcome);
    assert_eq!(report.identity.options.assume_joined, names);
    assert!(
        report
            .warnings
            .iter()
            .any(|warning| warning.starts_with("assume-joined: ")
                && warning.contains("`hook:b.k:18:3`")
                && warning.contains("not for the definitions as written")),
        "{:?}",
        report.warnings
    );
    assert!(
        !report.definition_findings.is_empty()
            && report
                .definition_findings
                .iter()
                .all(|finding| finding.assumed && finding.kind == FindingKind::Equation),
        "{:?}",
        report.definition_findings
    );
    // A `hook:` name for an equation without a hook finding names nothing, and is refused.
    let mut spec = spec_on(&R4_HOOKITE, &R4_HOOKITE_M, "r4-hookite/go.pgm", None);
    spec.options.assume_joined = vec!["hook:b.k:20:3".into()];
    let error = Campaign::new(spec).err().expect("refused").to_string();
    assert!(
        error.contains("matches no unjoined pair, nor any other finding"),
        "{error}"
    );
}

/// R2-S1's premise violation (an unused overload placed across `K`) is an overload precondition
/// row, which can be assumed: it is named `precondition:...` in `definition-findings`, and those
/// names, assumed, let the cases run (INT8).
#[test]
fn an_assumed_precondition_row_lets_the_cases_run() {
    let report = r2_report(&R2_OVER, &R2_OVER_M, "r2-over/go.pgm");
    let preconditions = report
        .definition_findings
        .iter()
        .filter(|finding| finding.kind == FindingKind::Precondition)
        .collect::<Vec<_>>();
    assert!(
        !preconditions.is_empty(),
        "{:?}",
        report.definition_findings
    );
    // An overload row, which can be assumed: not a decided row.
    assert!(
        preconditions
            .iter()
            .all(|finding| finding.verdict == FindingVerdict::Undecided),
        "{preconditions:?}"
    );
    let mut names = report
        .definition_findings
        .iter()
        .map(|finding| {
            let name = finding.name.clone().expect("every finding is named");
            let side = match finding.side {
                DefinitionRole::Baseline => "baseline",
                DefinitionRole::Mutant => "mutant",
            };
            format!("{side}:{name}")
        })
        .collect::<Vec<_>>();
    assert!(
        preconditions.iter().all(|finding| finding
            .name
            .as_deref()
            .is_some_and(|name| name.starts_with("precondition:"))),
        "{preconditions:?}"
    );
    names.sort();
    names.dedup();
    let mut spec = spec_on(&R2_OVER, &R2_OVER_M, "r2-over/go.pgm", None);
    spec.options.assume_joined = names;
    let report = Campaign::new(spec)
        .expect("valid")
        .run(Budget::Cases(2), None);
    assert!(
        !matches!(report.outcome, CampaignOutcome::NotComparable { .. }),
        "{:?}",
        report.outcome
    );
    assert!(report.totals.cases > 0);
    assert!(
        report
            .definition_findings
            .iter()
            .all(|finding| finding.assumed)
    );
}

/// INT8 follow-ups review B1: `rule ListItem(1) => ListItem(2)` on both sides rewrites a
/// collection-headed term, which the data judgement reads as free. That is a decided fact about
/// the definition as written (`ListItem(1)` is no normal form), not a limit of the check: the
/// rows are `decided`, and their names are refused, since no assumption about the definition as
/// written makes such terms normal forms. Accepting them gave a false kill (`ListItem(1)`
/// against `ListItem(2)`, which both theories equate).
#[test]
fn a_decided_precondition_row_cannot_be_assumed() {
    let report = r2_report(&LIST_ROW, &LIST_ROW_M, "list-row/go.pgm");
    assert!(report.witness().is_none(), "{:?}", report.outcome);
    assert_not_comparable(&report, &[DefinitionRole::Baseline, DefinitionRole::Mutant]);
    for finding in &report.definition_findings {
        assert_eq!(finding.kind, FindingKind::Precondition, "{finding:?}");
        assert_eq!(finding.verdict, FindingVerdict::Decided, "{finding:?}");
        assert!(
            finding.reason.contains("not distinct normal forms")
                && finding.reason.contains("never applies")
                && !finding.reason.contains("limit"),
            "{finding:?}"
        );
    }
    let mut spec = spec_on(&LIST_ROW, &LIST_ROW_M, "list-row/go.pgm", None);
    spec.options.assume_joined = vec![
        "baseline:precondition:b.k:11:3".into(),
        "mutant:precondition:m.k:11:3".into(),
    ];
    let refused = Campaign::new(spec);
    assert!(refused.is_err(), "accepted: a false kill follows");
    let error = refused.err().expect("refused").to_string();
    assert!(
        error.contains("cannot be assumed") && error.contains("change that equation"),
        "{error}"
    );
}

/// FZ-CONFLUENCE review A (B1): with `rule replace(S, _, _, _) => S [priority(10)]`, domains.md's
/// `replaceAll(S, T, R) => replace(S, T, R, countAllOccurrences(S, T))` gives
/// `replaceAll("ab", "a", "c") = "ab"` while the builtin gives `"cb"`. `replaceAll`'s written
/// meaning names only builtins, so the equation is not shown to agree with its hook: no end is
/// data, never a kill (the first written meaning, through `replace`, killed it).
#[test]
fn an_equation_agreeing_with_its_hook_only_through_the_definition_has_no_data() {
    let report = r2_report(
        &REPLACE_PRIORITY,
        &REPLACE_PRIORITY_M,
        "replace-priority/go.pgm",
    );
    assert!(report.witness().is_none(), "{:?}", report.outcome);
    assert_not_comparable(&report, &[DefinitionRole::Baseline, DefinitionRole::Mutant]);
}

/// FZ-CONFLUENCE review A round 2 (R2-B1): a `replace`-hooked symbol named and placed like
/// domains.md's, with false rows, does not qualify for `replaceAll`'s lemma (the guard reads the
/// rows' content), so the false `myReplaceAll` equation is reported: never a kill (f202abd30's
/// origin guard killed it).
#[test]
fn a_replace_spoofing_domains_origin_is_not_read_as_domains_replace() {
    let report = r2_report(&R2_SPOOF, &R2_SPOOF_M, "r2-spoof/go.pgm");
    assert!(report.witness().is_none(), "{:?}", report.outcome);
    assert_not_comparable(&report, &[DefinitionRole::Baseline, DefinitionRole::Mutant]);
}
