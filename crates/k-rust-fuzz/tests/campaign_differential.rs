//! The engine's wiring of the differential target (ARCHITECTURE 4.3, 7): both sides run per
//! case, confirmation re-runs both, equivalent definitions run no case. The judge itself is
//! FZ-08's and is tested in `src/target/differential.rs`.

mod support;

use std::{collections::BTreeMap, sync::Arc};

use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl,
    HoleLocation, ProgramInput, ProposerConfig, SpanAddress, Target, TargetKind,
    report::{CampaignOutcome, DefinitionRole, HitLabel},
    spec::DEFAULT_REJECTION_CAP,
    target::DifferentialTarget,
    values::{Constraints, GenerationBounds, Value},
};
use num_bigint::BigInt;
use support::{COIN, COIN_KILL, COIN_LAYOUT, Fixture};

fn spec(mutant: &'static Fixture) -> CampaignSpec {
    let baseline = COIN.compiled();
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(baseline.definition()),
            mutant: Some(Arc::new(mutant.compiled().definition())),
        },
        program: ProgramInput::Source(baseline.program_source("coin/flip.pgm")),
        holes: vec![HoleDecl {
            name: "N".into(),
            sort: "Int".into(),
            location: HoleLocation::Span(SpanAddress {
                program: "coin/flip.pgm".into(),
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
            "the killing end"
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
