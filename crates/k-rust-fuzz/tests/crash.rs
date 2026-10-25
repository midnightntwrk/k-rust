//! Crash findings (FZ-CRASH, D30, D32): a panic or an internal error during a case is a finding
//! with its input, and the campaign goes on; a panic in the client's own observer aborts the
//! campaign, naming the case and its hole values.
//!
//! The tests read the report's canonical JSON, the form every client reads.

mod support;

use std::{collections::BTreeMap, sync::Arc};

use k_rust::kore::ast::Pattern as KorePattern;
use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl,
    HoleLocation, ProgramInput, ProposerConfig, SpanAddress, Target, TargetKind, Value,
    spec::DEFAULT_REJECTION_CAP,
    target::{ConfigurationView, Observer, ObserverTarget, ObserverVerdict},
    values::{Constraints, GenerationBounds},
};
use serde_json::Value as Json;
use support::IMP;

fn int_hole(name: &str, find: &str, literal: &str) -> HoleDecl {
    HoleDecl {
        name: name.into(),
        sort: "Int".into(),
        location: HoleLocation::Span(SpanAddress {
            program: "imp/le.imp".into(),
            line: None,
            column: None,
            find: find.into(),
            literal: literal.into(),
        }),
        constraints: Constraints::default(),
        allow_refused_sort: false,
    }
}

/// Panics when a configuration's `<state>` cell holds the integer 7: in `le.imp` only `x` can,
/// so exactly when the hole `X` is 7.
struct PanicsAtSeven;

impl Observer for PanicsAtSeven {
    type State = ();

    fn start(&self) {}

    fn branch(&self, (): &()) {}

    fn step(
        &self,
        (): &mut (),
        _pre: &ConfigurationView,
        post: &ConfigurationView,
    ) -> ObserverVerdict {
        let mut work: Vec<&KorePattern> = post.cell("state").into_iter().collect();
        while let Some(next) = work.pop() {
            if let KorePattern::DomainValue { value, .. } = next
                && value.as_utf8().ok() == Some("7")
            {
                panic!("the observer met x = 7");
            }
            work.extend(k_rust::kore::walk::children(next));
        }
        ObserverVerdict::Nothing
    }
}

fn int(n: i64) -> Value {
    Value::Int(n.into())
}

/// (A) A panic in the client's observer is the client's defect, not k-rust's: the campaign
/// aborts with kind `client-panic`, naming the case and its hole values, instead of the panic
/// escaping `Campaign::run`. The observer is shared by every case and cannot be rebuilt, so
/// the campaign cannot go on.
#[test]
fn a_panicking_observer_aborts_the_campaign_with_its_case() {
    let compiled = IMP.compiled();
    let spec = CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(compiled.definition()),
            mutant: None,
        },
        program: ProgramInput::Source(compiled.program_source("imp/le.imp")),
        holes: vec![int_hole("X", "x = 3;", "3"), int_hole("Y", "y = 5;", "5")],
        target: Target {
            kind: TargetKind::Observer(ObserverTarget::new("panics-at-7", PanicsAtSeven)),
            run_to_completion: false,
            negated_property: false,
            data_end: false,
            comparable: false,
            query_confirmable: false,
        },
        options: CaseOptions::default(),
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: vec![
                BTreeMap::from([("X".to_owned(), int(1)), ("Y".to_owned(), int(2))]),
                BTreeMap::from([("X".to_owned(), int(7)), ("Y".to_owned(), int(5))]),
                BTreeMap::from([("X".to_owned(), int(2)), ("Y".to_owned(), int(3))]),
            ],
            weights: BTreeMap::new(),
        },
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 1,
        identity: CallerIdentity::default(),
    };
    let mut campaign = Campaign::new(spec).expect("the observer campaign is valid");
    let report = campaign.run(Budget::Cases(10), None);
    let json: Json = serde_json::from_str(&report.to_canonical_json()).expect("JSON");
    let outcome = &json["outcome"];
    assert_eq!(outcome["status"], "aborted", "{outcome}");
    assert_eq!(outcome["kind"], "client-panic", "{outcome}");
    // The anchors (3, 5) ran as case 0, (1, 2) as case 1, and (7, 5) panicked as case 2.
    assert_eq!(outcome["case"], 2, "{outcome}");
    let holes: Vec<(String, Json)> = outcome["holes"]
        .as_array()
        .expect("the hole values")
        .iter()
        .map(|hole| {
            (
                hole["name"].as_str().unwrap_or("").to_owned(),
                hole["value"].clone(),
            )
        })
        .collect();
    assert_eq!(
        holes,
        vec![
            ("X".to_owned(), serde_json::json!({"int": "7"})),
            ("Y".to_owned(), serde_json::json!({"int": "5"})),
        ],
        "{outcome}"
    );
    let panic = &outcome["panic"];
    assert!(
        panic["message"]
            .as_str()
            .is_some_and(|message| message.contains("the observer met x = 7")),
        "{outcome}"
    );
    assert!(
        outcome["reason"]
            .as_str()
            .is_some_and(|reason| reason.contains("observer")),
        "{outcome}"
    );
    // The campaign ran two cases before the observer's panic, and no case after it.
    assert_eq!(json["totals"]["cases"], 2, "{}", json["totals"]);
}
