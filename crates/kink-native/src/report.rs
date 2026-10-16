//! Versioned, deterministic step-3 execution and pattern report.

use std::fmt::Debug;

use k_rust::backend::BackendOptions;
use k_rust::kore::{ast::Pattern, codec};
use kink_pattern::{Evaluation, EventPresence, PathInput, PatternFailure, PatternOutcome};
use serde_json::{Value, json};

use crate::{
    bridge::{BridgeFailure, BridgedPaths, discarded, leaf_keys},
    execution::{
        AdaptedExecution, AdaptedLeaf, ExecutionAdapterFailure, ExecutionBudget, SolverProfile,
    },
    feasibility::LeafFeasibility,
};

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
            BridgeFailure::UndecodableState(_) => "UndecodableState",
            BridgeFailure::UndecidedStateSort => "UndecidedStateSort",
            BridgeFailure::DuplicatePathIdentity(_) => "DuplicatePathIdentity",
            BridgeFailure::ClassifiedUndefinedStep => "ClassifiedUndefinedStep",
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

/// Inputs of one report.
pub struct ReportInput<'a> {
    /// The profile the adapter expected ([`crate::execution::ExecutionAdapter::profile`]); a
    /// completed pipeline implies the backend ran in it.
    pub profile: SolverProfile,
    pub test_id: &'a str,
    pub budget: &'a ExecutionBudget,
    /// The backend's SMT options. They decide when Z3 answers `unknown`, so they are part of
    /// the budget (README R4); a no-Z3 backend ignores them.
    pub backend_options: BackendOptions,
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

/// The execution leaf of `path`.
fn path_leaf<'e>(path: &PathInput, execution: &'e AdaptedExecution) -> Option<&'e AdaptedLeaf> {
    let key = path.path_key.as_ref()?;
    execution
        .leaves()
        .iter()
        .zip(leaf_keys(execution.leaves()))
        .find_map(|(leaf, leaf_key)| (leaf_key == *key).then_some(leaf))
}

fn feasibility(path: &PathInput, execution: &AdaptedExecution) -> &'static str {
    match path_leaf(path, execution) {
        Some(leaf) if ground_leaf(leaf, path) => "ground",
        Some(leaf) => match leaf.feasibility {
            LeafFeasibility::Syntactic => "syntactic",
            LeafFeasibility::Solver => "solver",
            LeafFeasibility::Unsat => "unsat",
            LeafFeasibility::Unknown => "unknown",
        },
        None => "unknown",
    }
}

/// The leaves the bridge discarded as proved to have no instance, in leaf order.
fn discarded_values(execution: &AdaptedExecution) -> Vec<Value> {
    execution
        .leaves()
        .iter()
        .zip(leaf_keys(execution.leaves()))
        .filter_map(|(leaf, key)| {
            discarded(leaf).map(|reason| {
                json!({
                    "key": key,
                    "halt": enum_name(leaf.halt),
                    "reason": reason.name(),
                })
            })
        })
        .collect()
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
                "presence": match &event.presence {
                    EventPresence::Certain => "certain",
                    EventPresence::Conditional(_) => "conditional",
                    EventPresence::Undecided => "undecided",
                },
                "relations": match &event.presence {
                    EventPresence::Conditional(relations) => relations.iter().map(|relation| json!({
                        "left": term(&relation.left), "right": term(&relation.right)
                    })).collect::<Vec<_>>(),
                    _ => Vec::new(),
                },
                "step": event.step,
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
        "cause": path_leaf(path, execution)
            .and_then(|leaf| leaf.cause.as_ref())
            .map(|cause| serde_json::to_value(cause).expect("an indeterminate cause encodes as JSON")),
        "predicate": term(&path.path_predicate),
        "terminal": path.execution_terminal.as_ref().map(|terminal| term(&terminal.state)),
        "undefined_rule": path_leaf(path, execution)
            .and_then(|leaf| leaf.undefined_rule.as_ref())
            .map(|rule| json!({ "id": rule.id, "label": rule.label })),
        "events": events,
    })
}

/// The report schema version. Version 2 (SYM-3B-01) adds the SMT options to `budget`; version 3
/// (SYM-3B-02) adds `discarded` and the path feasibility values `"solver"` and `"unsat"`;
/// version 4 adds the path `cause`, the k-rust `SearchFailure` of an indeterminate leaf (null
/// otherwise); version 5 adds the stop `"undefined-step"` of a `Trivial` leaf, whose `terminal` is
/// its pre-step term; paths now use raw leaf ordinals (`bridge::leaf_keys`). Version 6
/// adds the path `undefined_rule`, the compiled `id` and qualified `label` of the rule whose
/// application is the undefined step of a `Trivial` leaf (null for every other path, and for a
/// `Trivial` leaf k-rust names no rule for).
pub const REPORT_VERSION: u64 = 6;

/// Builds the exact version-6 step-3 report schema.
#[must_use]
pub fn step3_report(input: ReportInput<'_>) -> Value {
    let budget = input.budget;
    let budget = json!({
        "time_ms": u64::try_from(budget.time.as_millis()).unwrap_or(u64::MAX),
        "max_simplification_iterations": budget.max_simplification_iterations,
        "max_depth": budget.max_depth,
        "max_breadth": budget.max_breadth.map(|width| width.get()),
        "smt_timeout_ms": input.backend_options.smt_timeout_ms,
        "smt_retry_limit": input.backend_options.smt_retry_limit,
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
    let (
        outcome,
        failure,
        error,
        complete_coverage,
        collection,
        paths,
        discarded,
        witnesses,
        primary_witness,
    ) = match result {
        ReportResult::Error(error) => (
            "error".to_owned(),
            None,
            json!({ "stage": error.stage, "kind": error.kind }),
            false,
            json!({ "stop": "error", "pending_work": 0 }),
            Vec::new(),
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
                discarded_values(execution),
                witnesses,
                evaluation.primary_witness,
            )
        }
    };
    json!({
        "schema": "kink-step3-report",
        "version": REPORT_VERSION,
        "profile": input.profile.name(),
        "test_id": input.test_id,
        "budget": budget,
        "outcome": outcome,
        "failure": failure,
        "error": error,
        "complete_coverage": complete_coverage,
        "collection": collection,
        "paths": paths,
        "discarded": discarded,
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
    use kink_pattern::{
        Binding, CollectionEvidence, CollectionStop, Constructor, Event, EventPresence,
        ExecutionStop, ExecutionTerminal, ExecutionTerminalKind, PathStop, SearchPolicy,
        TermRelation, Witness,
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

    const fn backend_options() -> BackendOptions {
        BackendOptions {
            smt_timeout_ms: 4000,
            smt_retry_limit: 2,
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
            },
            feasibility: LeafFeasibility::Syntactic,
            cause: None,
            diagnostics: Vec::new(),
            candidate_diagnostics: Vec::new(),
            remainder_diagnostics: Vec::new(),
            undefined_rule: None,
            contradicted_total: None,
        };
        let event = Event {
            index: 0,
            constructor: "write".to_owned(),
            payload: vec![variable.clone()],
            presence: EventPresence::Certain,
            step: 1,
            emission_ordinal: 0,
        };
        let path = PathInput {
            test_id: "t".to_owned(),
            path_ordinal: 0,
            path_key: Some("leaf:0".to_owned()),
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
            path_key: Some("leaf:0".to_owned()),
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
                stack_stops: 0,
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
            profile: SolverProfile::NoZ3,
            test_id: "t",
            budget: &budget(),
            backend_options: backend_options(),
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
                "discarded",
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
                "smt_timeout_ms",
                "smt_retry_limit",
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
                "cause",
                "predicate",
                "terminal",
                "undefined_rule",
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
                "presence",
                "relations",
                "step",
                "emission_ordinal",
            ])
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
        assert_eq!(report["version"], 6);
        assert_eq!(path["cause"], Value::Null);
        assert_eq!(path["undefined_rule"], Value::Null);
        assert_eq!(report["discarded"], json!([]));
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
        assert_eq!(report["budget"]["smt_timeout_ms"], 4000);
        assert_eq!(report["budget"]["smt_retry_limit"], 2);
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
                profile: SolverProfile::NoZ3,
                test_id: "t",
                budget: &budget(),
                backend_options: backend_options(),
                result: ReportResult::Error(error),
            });
            assert_eq!(report["outcome"], "error");
            assert_eq!(report["paths"], json!([]));
            assert_eq!(report["discarded"], json!([]));
            assert_eq!(report["witnesses"], json!([]));
            assert_eq!(report["error"], json!({ "stage": stage, "kind": kind }));
            assert_eq!(keys(&report["error"]), BTreeSet::from(["stage", "kind"]));
        }
        let (execution, bridged, mut evaluation) = fixture();
        evaluation.outcome = PatternOutcome::Error;
        let report = step3_report(ReportInput {
            profile: SolverProfile::NoZ3,
            test_id: "t",
            budget: &budget(),
            backend_options: backend_options(),
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
                profile: SolverProfile::NoZ3,
                test_id: "t",
                budget: &budget(),
                backend_options: backend_options(),
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
        for (feasibility, name) in [
            (LeafFeasibility::Solver, "solver"),
            (LeafFeasibility::Unsat, "unsat"),
            (LeafFeasibility::Unknown, "unknown"),
        ] {
            execution.leaves[0].feasibility = feasibility;
            assert_eq!(render(&execution)["paths"][0]["feasibility"], name);
        }
        // An indeterminate leaf reports k-rust's structured cause.
        execution.leaves[0].halt = HaltClass::Indeterminate;
        execution.leaves[0].cause = Some(k_rust::backend::SearchFailureOutput::Requires {
            rule: "r".to_owned(),
            predicates: Vec::new(),
        });
        assert_eq!(
            render(&execution)["paths"][0]["cause"],
            json!({ "kind": "requires", "rule": "r", "predicates": [] })
        );
    }

    /// A leaf the bridge discards appears under `discarded` with its halt and reason, not
    /// under `paths`.
    #[test]
    fn report_lists_discarded_leaves() {
        let (mut execution, mut bridged, mut evaluation) = fixture();
        let mut vacuous = execution.leaves[0].clone();
        vacuous.halt = HaltClass::Vacuous;
        vacuous.branch.identity.clear();
        vacuous.branch.depth = 0;
        vacuous.branch.state = term(&pattern(r"\bottom{SortS{}}()"));
        let mut refuted = execution.leaves[0].clone();
        refuted.feasibility = LeafFeasibility::Unsat;
        refuted.branch.identity[0].target = "u".to_owned();
        execution.leaves = vec![vacuous, refuted];
        bridged.paths.clear();
        bridged.collection.empty_search_decision = Some(kink_pattern::EmptySearchDecision);
        evaluation.outcome = PatternOutcome::NoMatch;
        evaluation.witnesses.clear();
        evaluation.primary_witness = None;
        let report = step3_report(ReportInput {
            profile: SolverProfile::Z3,
            test_id: "t",
            budget: &budget(),
            backend_options: backend_options(),
            result: ReportResult::Ok {
                execution: &execution,
                bridged: &bridged,
                evaluation: &evaluation,
            },
        });
        assert_eq!(report["paths"], json!([]));
        assert_eq!(
            report["discarded"],
            json!([
                { "key": "leaf:0", "halt": "vacuous", "reason": "vacuous" },
                { "key": "leaf:1", "halt": "stuck", "reason": "unsat" },
            ])
        );
    }

    #[test]
    fn report_profile_is_the_adapter_profile() {
        let (execution, bridged, evaluation) = fixture();
        for (profile, name) in [(SolverProfile::NoZ3, "no-z3"), (SolverProfile::Z3, "z3")] {
            let report = step3_report(ReportInput {
                profile,
                test_id: "t",
                budget: &budget(),
                backend_options: backend_options(),
                result: ReportResult::Ok {
                    execution: &execution,
                    bridged: &bridged,
                    evaluation: &evaluation,
                },
            });
            assert_eq!(report["profile"], name);
        }
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
