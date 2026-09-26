//! Versioned, deterministic step-3 execution and pattern report.

use std::fmt::Debug;

use k_rust::kore::{ast::Pattern, codec};
use kink_pattern::{Evaluation, EventAttribution, PathInput, PatternFailure, PatternOutcome};
use serde_json::{Value, json};

use crate::{
    bridge::{BridgeFailure, BridgedPaths},
    execution::{AdaptedExecution, AdaptedLeaf, ExecutionAdapterFailure, ExecutionBudget},
    feasibility::LeafFeasibility,
};

/// The backend profile that produced the execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReportProfile {
    NoZ3,
    Z3,
}

impl ReportProfile {
    #[must_use]
    pub const fn from_smt(smt: bool) -> Self {
        if smt { Self::Z3 } else { Self::NoZ3 }
    }

    const fn name(self) -> &'static str {
        match self {
            Self::NoZ3 => "no-z3",
            Self::Z3 => "z3",
        }
    }
}

/// A failed stage and the name of its failure variant, without diagnostic payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReportError {
    stage: &'static str,
    kind: &'static str,
}

impl ReportError {
    #[must_use]
    pub const fn adapter(failure: &ExecutionAdapterFailure) -> Self {
        let kind = match failure {
            ExecutionAdapterFailure::SolverProfileMismatch => "SolverProfileMismatch",
            ExecutionAdapterFailure::InvalidState(_) => "InvalidState",
            ExecutionAdapterFailure::Backend(_) => "Backend",
            ExecutionAdapterFailure::ContractViolation(_) => "ContractViolation",
            ExecutionAdapterFailure::UninhabitedVariable(_) => "UninhabitedVariable",
            ExecutionAdapterFailure::Observation(_) => "Observation",
        };
        Self {
            stage: "adapter",
            kind,
        }
    }

    #[must_use]
    pub const fn bridge(failure: &BridgeFailure) -> Self {
        let kind = match failure {
            BridgeFailure::NoLeaves => "NoLeaves",
            BridgeFailure::ContractViolation(_) => "ContractViolation",
            BridgeFailure::UnsupportedPayload => "UnsupportedPayload",
            BridgeFailure::UndecodablePayload(_) => "UndecodablePayload",
            BridgeFailure::UndecodableState(_) => "UndecodableState",
            BridgeFailure::UndecidedStateSort => "UndecidedStateSort",
            BridgeFailure::DuplicatePathIdentity(_) => "DuplicatePathIdentity",
        };
        Self {
            stage: "bridge",
            kind,
        }
    }

    #[must_use]
    pub const fn evaluation(failure: &PatternFailure) -> Self {
        Self {
            stage: "evaluation",
            kind: match failure.kind() {
                kink_pattern::PatternFailureKind::MalformedPlan => "MalformedPlan",
                kink_pattern::PatternFailureKind::UnknownConstructor => "UnknownConstructor",
                kink_pattern::PatternFailureKind::InvalidVariable => "InvalidVariable",
                kink_pattern::PatternFailureKind::InvalidArm => "InvalidArm",
                kink_pattern::PatternFailureKind::InvalidPayload => "InvalidPayload",
                kink_pattern::PatternFailureKind::InvalidSideTable => "InvalidSideTable",
                kink_pattern::PatternFailureKind::VocabularyMismatch => "VocabularyMismatch",
                kink_pattern::PatternFailureKind::TestMismatch => "TestMismatch",
                kink_pattern::PatternFailureKind::BoundsMismatch => "BoundsMismatch",
                kink_pattern::PatternFailureKind::TerminalMismatch => "TerminalMismatch",
                kink_pattern::PatternFailureKind::InvalidOrigin => "InvalidOrigin",
                kink_pattern::PatternFailureKind::InvalidTerm => "InvalidTerm",
                kink_pattern::PatternFailureKind::InvalidPath => "InvalidPath",
                kink_pattern::PatternFailureKind::InvalidCollection => "InvalidCollection",
                kink_pattern::PatternFailureKind::InputError => "InputError",
            },
        }
    }
}

/// The completed pipeline, or a failure that prevented a completed pipeline.
pub enum ReportResult<'a> {
    Ok {
        execution: &'a AdaptedExecution,
        bridged: &'a BridgedPaths,
        evaluation: &'a Evaluation,
    },
    Error(ReportError),
}

/// Inputs of one report. Use `ReportProfile::from_smt(backend.capabilities().smt)`.
pub struct ReportInput<'a> {
    pub profile: ReportProfile,
    pub test_id: &'a str,
    pub budget: &'a ExecutionBudget,
    pub result: ReportResult<'a>,
}

/// Renders a unit enum's Debug name in kebab case.
fn enum_name(value: impl Debug) -> String {
    let mut name = String::new();
    for (index, character) in format!("{value:?}").chars().enumerate() {
        if character.is_uppercase() {
            if index != 0 {
                name.push('-');
            }
            name.extend(character.to_lowercase());
        } else {
            name.push(character);
        }
    }
    name
}

fn term(pattern: &Pattern) -> Value {
    codec::to_value(pattern).expect("evaluated KORE term encodes as KORE JSON")
}

fn leaf_key(leaf: &AdaptedLeaf) -> String {
    if leaf.branch.identity.is_empty() {
        "root".to_owned()
    } else {
        leaf.branch
            .identity
            .iter()
            .map(|id| format!("{}@{}", id.rule, id.target))
            .collect::<Vec<_>>()
            .join("/")
    }
}

fn ground_leaf(leaf: &AdaptedLeaf, path: &PathInput) -> bool {
    let Pattern::Top { sort } = &path.path_predicate else {
        return false;
    };
    let Ok(state) = codec::from_value(&leaf.branch.state) else {
        return false;
    };
    let conjuncts = state.into_conjuncts_at(sort);
    matches!(conjuncts.as_slice(), [term] if matches!(term,
        Pattern::Application { .. }
        | Pattern::AssociativeApplication { .. }
        | Pattern::DomainValue { .. }
        | Pattern::String(_)
        | Pattern::Variable(_)) && term.free_variables().is_empty())
}

fn feasibility(path: &PathInput, execution: &AdaptedExecution) -> &'static str {
    let leaf = path.path_key.as_ref().and_then(|key| {
        execution
            .leaves()
            .iter()
            .find(|leaf| leaf_key(leaf) == *key)
    });
    match leaf {
        Some(leaf) if ground_leaf(leaf, path) => "ground",
        Some(leaf) if leaf.feasibility == LeafFeasibility::Syntactic => "syntactic",
        _ => "unknown",
    }
}

fn path_value(path: &PathInput, execution: &AdaptedExecution) -> Value {
    let events = path
        .events
        .iter()
        .map(|event| {
            json!({
                "index": event.index,
                "constructor": event.constructor,
                "payload": event.payload.iter().map(term).collect::<Vec<_>>(),
                "attribution": match event.attribution {
                    EventAttribution::Certain => "certain",
                    EventAttribution::Unknown(_) => "unknown",
                },
                "rule": { "module": event.origin.rule.module, "index": event.origin.rule.index },
                "transition": {
                    "rule": event.origin.transition.rule,
                    "target": event.origin.transition.target,
                },
                "transition_ordinal": event.transition_ordinal,
                "emission_ordinal": event.emission_ordinal,
            })
        })
        .collect::<Vec<_>>();
    json!({
        "ordinal": path.path_ordinal,
        "key": path.path_key,
        "complete": path.complete,
        "stop": enum_name(path.stop),
        "execution_stop": enum_name(path.execution_stop),
        "feasibility": feasibility(path, execution),
        "predicate": term(&path.path_predicate),
        "terminal": path.execution_terminal.as_ref().map(|terminal| term(&terminal.state)),
        "events": events,
    })
}

/// Builds the exact version-1 step-3 report schema.
#[must_use]
pub fn step3_report(input: ReportInput<'_>) -> Value {
    let budget = input.budget;
    let budget = json!({
        "time_ms": u64::try_from(budget.time.as_millis()).unwrap_or(u64::MAX),
        "max_simplification_iterations": budget.max_simplification_iterations,
        "max_depth": budget.max_depth,
        "max_breadth": budget.max_breadth.map(|width| width.get()),
    });
    let result = match input.result {
        ReportResult::Ok { evaluation, .. } if evaluation.outcome == PatternOutcome::Error => {
            ReportResult::Error(ReportError {
                stage: "evaluation",
                kind: "InputError",
            })
        }
        result => result,
    };
    let (outcome, failure, error, complete_coverage, collection, paths, witnesses, primary_witness) =
        match result {
            ReportResult::Error(error) => (
                "error".to_owned(),
                None,
                json!({ "stage": error.stage, "kind": error.kind }),
                false,
                json!({ "stop": "error", "pending_work": 0 }),
                Vec::new(),
                Vec::new(),
                None,
            ),
            ReportResult::Ok {
                execution,
                bridged,
                evaluation,
            } => {
                let paths = bridged
                    .paths
                    .iter()
                    .map(|path| path_value(path, execution))
                    .collect();
                let witnesses = evaluation
                    .witnesses
                    .iter()
                    .map(|witness| {
                        json!({
                            "path_ordinal": witness.path_ordinal,
                            "path_key": witness.path_key,
                            "arm_ordinal": witness.arm_ordinal,
                            "event_indices": witness.event_indices,
                            "bindings": witness.bindings.iter().map(|binding| json!({
                                "name": binding.name,
                                "term": term(&binding.term),
                            })).collect::<Vec<_>>(),
                            "assumptions": witness.assumptions.iter().map(|relation| json!({
                                "left": term(&relation.left),
                                "right": term(&relation.right),
                            })).collect::<Vec<_>>(),
                            "path_predicate": term(&witness.path_predicate),
                            "stop": enum_name(witness.stop_reason),
                        })
                    })
                    .collect();
                (
                    enum_name(evaluation.outcome),
                    evaluation.failure.map(enum_name),
                    Value::Null,
                    evaluation.complete_coverage,
                    json!({
                        "stop": enum_name(bridged.collection.stop),
                        "pending_work": bridged.collection.pending_work,
                    }),
                    paths,
                    witnesses,
                    evaluation.primary_witness,
                )
            }
        };
    json!({
        "schema": "kink-step3-report",
        "version": 1,
        "profile": input.profile.name(),
        "test_id": input.test_id,
        "budget": budget,
        "outcome": outcome,
        "failure": failure,
        "error": error,
        "complete_coverage": complete_coverage,
        "collection": collection,
        "paths": paths,
        "witnesses": witnesses,
        "primary_witness": primary_witness,
    })
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet, num::NonZeroUsize, time::Duration};

    use k_rust::{
        backend::TransitionIdOutput,
        kore::{ast::Pattern, parser::parse_pattern},
    };
    use kink_patch::SentenceRef;
    use kink_pattern::{
        Binding, CollectionEvidence, CollectionStop, Constructor, Event, EventAttribution,
        EventOrigin, ExecutionStop, ExecutionTerminal, ExecutionTerminalKind, PathStop,
        SearchPolicy, TermRelation, Witness,
    };

    use super::*;
    use crate::{
        execution::{AdaptedLeaf, HaltClass},
        observation::AdaptedBranch,
    };

    fn pattern(source: &str) -> Pattern {
        parse_pattern(source).expect("KORE pattern")
    }

    fn budget() -> ExecutionBudget {
        ExecutionBudget {
            time: Duration::from_millis(1250),
            max_simplification_iterations: 42,
            max_depth: Some(3),
            max_breadth: Some(NonZeroUsize::new(2).expect("nonzero")),
        }
    }

    fn fixture() -> (AdaptedExecution, BridgedPaths, Evaluation) {
        let state = pattern("Lblend{}()");
        let predicate = pattern(r"\top{SortS{}}()");
        let variable = pattern("X:SortS{}");
        let transition = TransitionIdOutput {
            rule: "r".to_owned(),
            target: "t".to_owned(),
        };
        let leaf = AdaptedLeaf {
            halt: HaltClass::Stuck,
            branch: AdaptedBranch {
                identity: vec![transition.clone()],
                state: term(&state),
                depth: 1,
                trace: Vec::new(),
                events: Vec::new(),
                rollbacks: Vec::new(),
            },
            feasibility: LeafFeasibility::Syntactic,
            diagnostics: Vec::new(),
            candidate_diagnostics: Vec::new(),
            remainder_diagnostics: Vec::new(),
        };
        let event = Event {
            index: 0,
            constructor: "write".to_owned(),
            payload: vec![variable.clone()],
            origin: EventOrigin {
                rule: SentenceRef::new("M", 7),
                transition,
            },
            attribution: EventAttribution::Certain,
            transition_ordinal: 1,
            emission_ordinal: 0,
        };
        let path = PathInput {
            test_id: "t".to_owned(),
            path_ordinal: 0,
            path_key: Some("r@t".to_owned()),
            complete: true,
            stop: PathStop::Terminal,
            execution_stop: ExecutionStop::Terminal,
            execution_terminal: Some(ExecutionTerminal {
                kind: ExecutionTerminalKind::Normal,
                state,
            }),
            events: vec![event.clone()],
            path_predicate: predicate.clone(),
            equivalences: Vec::new(),
            inequalities: Vec::new(),
        };
        let witness = Witness {
            path_ordinal: 0,
            path_key: Some("r@t".to_owned()),
            arm_ordinal: 1,
            event_indices: vec![0],
            events: vec![event],
            bindings: vec![Binding {
                name: "A".to_owned(),
                term: variable.clone(),
            }],
            assumptions: vec![TermRelation {
                left: variable.clone(),
                right: variable,
            }],
            path_predicate: predicate,
            stop_reason: PathStop::Terminal,
            execution_stop_reason: ExecutionStop::Terminal,
        };
        (
            AdaptedExecution {
                leaves: vec![leaf],
                effects: Vec::new(),
                timed_out: false,
            },
            BridgedPaths {
                paths: vec![path],
                collection: CollectionEvidence {
                    stop: CollectionStop::SearchExhausted,
                    pending_work: 0,
                    empty_search_decision: None,
                },
            },
            Evaluation {
                outcome: PatternOutcome::Match,
                complete_coverage: true,
                witnesses: vec![witness],
                primary_witness: Some(0),
                failure: None,
                search_policy: SearchPolicy::Exhaustive,
                bounds: budget().bounds(),
            },
        )
    }

    fn success_report() -> Value {
        let (execution, bridged, evaluation) = fixture();
        step3_report(ReportInput {
            profile: ReportProfile::from_smt(false),
            test_id: "t",
            budget: &budget(),
            result: ReportResult::Ok {
                execution: &execution,
                bridged: &bridged,
                evaluation: &evaluation,
            },
        })
    }

    fn keys(value: &Value) -> BTreeSet<&str> {
        value
            .as_object()
            .expect("object")
            .keys()
            .map(String::as_str)
            .collect()
    }

    #[test]
    fn report_schema_keys_are_exact() {
        let report = success_report();
        assert_eq!(
            keys(&report),
            BTreeSet::from([
                "schema",
                "version",
                "profile",
                "test_id",
                "budget",
                "outcome",
                "failure",
                "error",
                "complete_coverage",
                "collection",
                "paths",
                "witnesses",
                "primary_witness",
            ])
        );
        assert_eq!(
            keys(&report["budget"]),
            BTreeSet::from([
                "time_ms",
                "max_simplification_iterations",
                "max_depth",
                "max_breadth",
            ])
        );
        assert_eq!(
            keys(&report["collection"]),
            BTreeSet::from(["stop", "pending_work"])
        );
        let path = &report["paths"][0];
        assert_eq!(
            keys(path),
            BTreeSet::from([
                "ordinal",
                "key",
                "complete",
                "stop",
                "execution_stop",
                "feasibility",
                "predicate",
                "terminal",
                "events",
            ])
        );
        let event = &path["events"][0];
        assert_eq!(
            keys(event),
            BTreeSet::from([
                "index",
                "constructor",
                "payload",
                "attribution",
                "rule",
                "transition",
                "transition_ordinal",
                "emission_ordinal",
            ])
        );
        assert_eq!(keys(&event["rule"]), BTreeSet::from(["module", "index"]));
        assert_eq!(
            keys(&event["transition"]),
            BTreeSet::from(["rule", "target"])
        );
        let witness = &report["witnesses"][0];
        assert_eq!(
            keys(witness),
            BTreeSet::from([
                "path_ordinal",
                "path_key",
                "arm_ordinal",
                "event_indices",
                "bindings",
                "assumptions",
                "path_predicate",
                "stop",
            ])
        );
        assert_eq!(
            keys(&witness["bindings"][0]),
            BTreeSet::from(["name", "term"])
        );
        assert_eq!(
            keys(&witness["assumptions"][0]),
            BTreeSet::from(["left", "right"])
        );
        assert_eq!(report["schema"], "kink-step3-report");
        assert_eq!(report["version"], 1);
        assert_eq!(report["profile"], "no-z3");
        assert_eq!(report["outcome"], "match");
        assert_eq!(path["stop"], "terminal");
        assert_eq!(path["feasibility"], "ground");
        assert_eq!(report["collection"]["stop"], "search-exhausted");
        assert_eq!(witness["stop"], "terminal");
        assert_eq!(
            witness["assumptions"][0]["left"],
            term(&pattern("X:SortS{}"))
        );
        assert_eq!(report["budget"]["time_ms"], 1250);
    }

    #[test]
    fn report_maps_failures_to_error() {
        let malformed = kink_pattern::EventVocabulary::new(vec![
            Constructor {
                name: "x".to_owned(),
                payload_sorts: Vec::new(),
            },
            Constructor {
                name: "x".to_owned(),
                payload_sorts: Vec::new(),
            },
        ])
        .expect_err("duplicate constructor");
        for (error, stage, kind) in [
            (
                ReportError::adapter(&ExecutionAdapterFailure::InvalidState("detail".to_owned())),
                "adapter",
                "InvalidState",
            ),
            (
                ReportError::bridge(&BridgeFailure::UndecodableState("detail".to_owned())),
                "bridge",
                "UndecodableState",
            ),
            (
                ReportError::evaluation(&malformed),
                "evaluation",
                "UnknownConstructor",
            ),
        ] {
            let report = step3_report(ReportInput {
                profile: ReportProfile::NoZ3,
                test_id: "t",
                budget: &budget(),
                result: ReportResult::Error(error),
            });
            assert_eq!(report["outcome"], "error");
            assert_eq!(report["paths"], json!([]));
            assert_eq!(report["witnesses"], json!([]));
            assert_eq!(report["error"], json!({ "stage": stage, "kind": kind }));
            assert_eq!(keys(&report["error"]), BTreeSet::from(["stage", "kind"]));
        }
        let (execution, bridged, mut evaluation) = fixture();
        evaluation.outcome = PatternOutcome::Error;
        let report = step3_report(ReportInput {
            profile: ReportProfile::NoZ3,
            test_id: "t",
            budget: &budget(),
            result: ReportResult::Ok {
                execution: &execution,
                bridged: &bridged,
                evaluation: &evaluation,
            },
        });
        assert_eq!(report["outcome"], "error");
        assert_eq!(
            report["error"],
            json!({ "stage": "evaluation", "kind": "InputError" })
        );
        assert_eq!(report["paths"], json!([]));
        assert_eq!(report["witnesses"], json!([]));
        assert!(report["failure"].is_null());
    }

    #[test]
    fn report_renders_bounded_feasibility_and_unknown() {
        let (mut execution, mut bridged, mut evaluation) = fixture();
        execution.leaves[0].branch.state = term(&pattern("X:SortS{}"));
        bridged.paths[0].complete = false;
        bridged.paths[0].stop = PathStop::DepthLimit;
        bridged.paths[0].execution_stop = ExecutionStop::DepthLimit;
        bridged.paths[0].execution_terminal = None;
        bridged.collection.stop = CollectionStop::DepthLimit;
        bridged.collection.pending_work = 1;
        evaluation.outcome = PatternOutcome::Unknown;
        evaluation.complete_coverage = false;
        evaluation.witnesses.clear();
        evaluation.primary_witness = None;
        evaluation.failure = Some(PathStop::DepthLimit);
        let render = |execution: &AdaptedExecution| {
            step3_report(ReportInput {
                profile: ReportProfile::NoZ3,
                test_id: "t",
                budget: &budget(),
                result: ReportResult::Ok {
                    execution,
                    bridged: &bridged,
                    evaluation: &evaluation,
                },
            })
        };
        let report = render(&execution);
        assert_eq!(report["outcome"], "unknown");
        assert_eq!(report["failure"], "depth-limit");
        assert_eq!(report["collection"]["stop"], "depth-limit");
        assert_eq!(report["paths"][0]["stop"], "depth-limit");
        assert_eq!(report["paths"][0]["execution_stop"], "depth-limit");
        assert_eq!(report["paths"][0]["feasibility"], "syntactic");
        execution.leaves[0].feasibility = LeafFeasibility::Unknown;
        assert_eq!(render(&execution)["paths"][0]["feasibility"], "unknown");
    }

    #[test]
    fn report_has_no_timing() {
        fn inspect(value: &Value, path: &str) {
            match value {
                Value::Object(map) => {
                    for (key, value) in map {
                        assert!(!key.contains("elapsed") && !key.contains("duration"));
                        if key == "time_ms" {
                            assert_eq!(path, "budget");
                        }
                        inspect(value, key);
                    }
                }
                Value::Array(values) => values.iter().for_each(|value| inspect(value, path)),
                _ => {}
            }
        }
        inspect(&success_report(), "");
    }
}
