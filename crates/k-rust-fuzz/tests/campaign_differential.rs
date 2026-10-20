//! The engine's wiring of the differential target (ARCHITECTURE 4.3, 7): both sides run per
//! case, confirmation re-runs both, equivalent definitions run no case. The judge itself is
//! FZ-08's and is tested in `src/target/differential.rs`.

mod support;

use std::{collections::BTreeMap, sync::Arc};

use k_rust_fuzz::{
    BackendRoute, Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions,
    HoleDecl, HoleLocation, ProgramInput, ProposerConfig, SpanAddress, Target, TargetKind,
    report::{CampaignOutcome, DefinitionRole, HitLabel, KillKind, Reaching},
    spec::DEFAULT_REJECTION_CAP,
    spec::PathMode,
    target::DifferentialTarget,
    values::{Constraints, GenerationBounds, IntRange, Value},
};
use num_bigint::BigInt;
use support::{COIN, COIN_KILL, COIN_LAYOUT, Fixture, MAC, MAC_KILL};

fn spec(mutant: &'static Fixture) -> CampaignSpec {
    spec_on(&COIN, mutant, "coin/flip.pgm", None)
}

/// A differential campaign over the hole `N` on the `3` of `program`, on the fixtures' route or
/// on `route`.
fn spec_on(
    baseline: &'static Fixture,
    mutant: &'static Fixture,
    program: &str,
    route: Option<BackendRoute>,
) -> CampaignSpec {
    let definition = |fixture: &'static Fixture| {
        let compiled = fixture.compiled();
        Arc::new(route.clone().map_or_else(
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
                leaf: Some(0)
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
        let report = Campaign::new(spec_on(&MAC, &MAC_KILL, "mac/inc.pgm", route.clone()))
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
