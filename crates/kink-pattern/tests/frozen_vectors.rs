use kink_contracts::NativeConformance;
use kink_pattern::{
    ArtifactRef, Binding, CollectionEvidence, CollectionStop, Constructor, DiscoveryAuthority,
    DiscoveryEvidence, DiscoveryRegistry, DiscoveryTuple, EditOriginReceipt, EditReceiptSource,
    EvaluationAuthority, EvaluationOptions, Event, EventOrigin, EventVocabulary, ExecutionBounds,
    ExecutionStop, ExecutionTerminal, ExecutionTerminalKind, OriginMode, PatchOrigin,
    PatchTemplateRole, PathInput, PathStop, PatternOutcome, PatternPlan, ReceiptAuthority,
    SearchPolicy, SelectionPolicy, SemanticSiteOrigin, SideConditionResult, SideConditionRow,
    SideConditionTable, Site, SuppliedPatch, TermRelation, TerminalAuthority,
    aggregate_existential, canonical_binding_digest, derive_candidate_id, derive_instance_id,
    derive_mutant_id, derive_path_identity, derive_site_id, derive_trace_digest, evaluate, select,
    validate_edit_receipts,
};
use kink_portable::{
    Digest, Location, Provenance, SemanticJson, SentenceKind, Term, TermNode, parse_json,
};
use serde_json::Value;
use std::collections::BTreeMap;

const EXECUTION_VECTORS: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../investigations/backend-agnostic-goal-closure/vectors/execution-pattern-vectors.json"
));
const MUTATION_VECTORS: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../investigations/backend-agnostic-goal-closure/vectors/mutation-vectors.json"
));

fn digest(value: &str) -> Digest {
    Digest::parse(value).expect("frozen digest")
}

fn semantic(value: &Value) -> SemanticJson {
    parse_json(&serde_json::to_vec(value).expect("serialize fixture value"))
        .expect("restricted fixture JSON")
}

fn fixed_digest(character: char) -> Digest {
    digest(&character.to_string().repeat(64))
}

fn definition_digest() -> Digest {
    fixed_digest('d')
}

fn observer_digest() -> Digest {
    fixed_digest('e')
}

fn execution_profile_digest() -> Digest {
    fixed_digest('f')
}

fn term(value: &Value) -> Term {
    assert_eq!(value["encoding"], "portable-term-v1");
    let sort = value["sort"].as_str().expect("term sort").to_owned();
    let node = match value["node"]["kind"].as_str().expect("term kind") {
        "token" => TermNode::Token {
            text: value["node"]["text"]
                .as_str()
                .expect("token text")
                .to_owned(),
        },
        "variable" => TermNode::Variable {
            name: value["node"]["name"]
                .as_str()
                .expect("variable name")
                .to_owned(),
        },
        other => panic!("fixture term kind {other} is outside this finite vector helper"),
    };
    Term { sort, node }
}

fn vocabulary(value: &Value) -> EventVocabulary {
    let constructors = value["constructors"]
        .as_array()
        .expect("constructors")
        .iter()
        .map(|item| Constructor {
            name: item["constructor"]
                .as_str()
                .expect("constructor")
                .to_owned(),
            payload_sorts: item["payloadSorts"]
                .as_array()
                .expect("payload sorts")
                .iter()
                .map(|sort| sort.as_str().expect("payload sort").to_owned())
                .collect(),
            origin_mode: match item["originMode"].as_str().expect("origin mode") {
                "emitting-sentence" => OriginMode::EmittingSentence,
                "emitting-sentence-and-semantic-site" => {
                    OriginMode::EmittingSentenceAndSemanticSite
                }
                other => panic!("unexpected origin mode {other}"),
            },
        })
        .collect();
    EventVocabulary::new(
        digest(
            value["eventVocabularyDigest"]
                .as_str()
                .expect("vocabulary digest"),
        ),
        constructors,
    )
    .expect("frozen vocabulary validates")
}

fn side_table(value: &Value) -> SideConditionTable {
    let rows = value["rows"]
        .as_array()
        .expect("side rows")
        .iter()
        .map(|row| SideConditionRow {
            condition_digest: digest(
                row["condition"]["digest"]
                    .as_str()
                    .expect("condition digest"),
            ),
            bindings_digest: digest(row["bindingsDigest"].as_str().expect("bindings digest")),
            path_predicate_digest: digest(
                row["pathPredicateDigest"]
                    .as_str()
                    .expect("predicate digest"),
            ),
            result: match row["result"].as_str().expect("side result") {
                "true" => SideConditionResult::True,
                "false" => SideConditionResult::False,
                "unknown" => SideConditionResult::Unknown,
                other => panic!("unexpected side result {other}"),
            },
        })
        .collect();
    SideConditionTable::new(
        digest(value["tableDigest"].as_str().expect("table digest")),
        rows,
    )
    .expect("frozen side table validates")
}

fn rehash_plan(value: &mut Value) {
    let mut projection = value.clone();
    projection
        .as_object_mut()
        .expect("plan object")
        .remove("patternPlanDigest");
    let id = kink_portable::digest(
        &kink_portable::DigestDomain::new("k-in-k/pattern-plan/v1").expect("plan domain"),
        &semantic(&projection),
    )
    .expect("plan projection is valid semantic JSON");
    value["patternPlanDigest"] = Value::String(id.to_string());
}

fn stop(value: &str) -> PathStop {
    match value {
        "terminal" => PathStop::Terminal,
        "stuck" => PathStop::Stuck,
        "match-found" => PathStop::MatchFound,
        "depth-limit" => PathStop::DepthLimit,
        "time-limit" => PathStop::TimeLimit,
        "branch-limit" => PathStop::BranchLimit,
        "result-limit" => PathStop::ResultLimit,
        "resource-limit" => PathStop::ResourceLimit,
        "solver-unknown" => PathStop::SolverUnknown,
        "backend-limit" => PathStop::BackendLimit,
        "error" => PathStop::Error,
        other => panic!("unexpected stop {other}"),
    }
}

fn execution_stop(stop: PathStop) -> ExecutionStop {
    match stop {
        PathStop::Terminal => ExecutionStop::Terminal,
        PathStop::Stuck => ExecutionStop::Stuck,
        PathStop::MatchFound => ExecutionStop::QuerySatisfied,
        PathStop::DepthLimit => ExecutionStop::DepthLimit,
        PathStop::TimeLimit => ExecutionStop::TimeLimit,
        PathStop::BranchLimit => ExecutionStop::BranchLimit,
        PathStop::ResultLimit => ExecutionStop::ResultLimit,
        PathStop::ResourceLimit => ExecutionStop::ResourceLimit,
        PathStop::SolverUnknown => ExecutionStop::SolverUnknown,
        PathStop::BackendLimit => ExecutionStop::BackendLimit,
        PathStop::Error => ExecutionStop::Error,
    }
}

fn provenance(value: &Value) -> Provenance {
    Provenance {
        lineage_id: digest(value["lineageId"].as_str().expect("origin lineage")),
        content_fingerprint: fixed_digest('1'),
        body_fingerprint: fixed_digest('2'),
        module: value["module"].as_str().expect("origin module").to_owned(),
        label: value
            .get("label")
            .and_then(Value::as_str)
            .map(str::to_owned),
        kind: SentenceKind::Rule,
        source: value["source"].as_str().expect("origin source").to_owned(),
        location: Location {
            start_line: 1,
            start_column: 1,
            end_line: 1,
            end_column: 1,
        },
        generated: false,
        transformation_chain: Vec::new(),
    }
}

fn constructor_origin_mode(data: &Value, constructor: &str) -> OriginMode {
    data["eventVocabularies"]
        .as_object()
        .expect("vocabularies")
        .values()
        .flat_map(|value| value["constructors"].as_array().expect("constructors"))
        .find(|value| value["constructor"].as_str() == Some(constructor))
        .map(
            |value| match value["originMode"].as_str().expect("origin mode") {
                "emitting-sentence" => OriginMode::EmittingSentence,
                "emitting-sentence-and-semantic-site" => {
                    OriginMode::EmittingSentenceAndSemanticSite
                }
                other => panic!("unexpected origin mode {other}"),
            },
        )
        .expect("constructor origin mode")
}

fn semantic_site(emitting: &Provenance) -> SemanticSiteOrigin {
    let term_path = semantic(&serde_json::json!([{"kind": "field", "name": "body"}]));
    let payload = semantic(&serde_json::json!({
        "observerDigest": observer_digest().to_string(),
        "observerVersion": 1,
        "definitionDigest": definition_digest().to_string(),
        "targetLineage": emitting.lineage_id.to_string(),
        "role": "event-origin",
        "termPath": [{"kind": "field", "name": "body"}]
    }));
    SemanticSiteOrigin {
        site_id: kink_portable::digest(
            &kink_portable::DigestDomain::new("k-in-k/observation-site/v1").expect("site domain"),
            &payload,
        )
        .expect("semantic site payload"),
        role: "event-origin".to_owned(),
        term_path,
    }
}

fn path(value: &Value, data: &Value, case_id: &str, path_ordinal: usize) -> PathInput {
    let terms = data["terms"].as_object().expect("terms");
    let events = data["events"].as_object().expect("events");
    let origins = data["origins"].as_object().expect("origins");
    let event_refs = value["eventRefs"].as_array().expect("event refs");
    let concrete_events = event_refs
        .iter()
        .enumerate()
        .map(|(index, reference)| {
            let event = &events[reference.as_str().expect("event ref")];
            let constructor = event["constructor"]
                .as_str()
                .expect("event constructor")
                .to_owned();
            let emitting = provenance(&origins[event["origin"].as_str().expect("origin ref")]);
            let semantic_site = (constructor_origin_mode(data, &constructor)
                == OriginMode::EmittingSentenceAndSemanticSite)
                .then(|| semantic_site(&emitting));
            Event {
                index,
                constructor,
                payload: event["payload"]
                    .as_array()
                    .expect("event payload")
                    .iter()
                    .map(|term_ref| term(&terms[term_ref.as_str().expect("term ref")]))
                    .collect(),
                origin: EventOrigin {
                    emitting_sentence: emitting,
                    semantic_site,
                },
                transition_ordinal: u64::try_from(index).expect("fixture index"),
                emission_ordinal: 0,
            }
        })
        .collect();
    let relations = |field: &str| {
        value
            .get(field)
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .map(|pair| TermRelation {
                left: term(&terms[pair[0].as_str().expect("left term ref")]),
                right: term(&terms[pair[1].as_str().expect("right term ref")]),
            })
            .collect()
    };
    let predicate_ref = value
        .get("pathPredicate")
        .and_then(Value::as_str)
        .unwrap_or("true");
    let path_predicate = terms.get(predicate_ref).map(term).unwrap_or_else(|| Term {
        sort: "Bool".to_owned(),
        node: TermNode::Token {
            text: predicate_ref.to_owned(),
        },
    });
    let stop = stop(value["stopReason"].as_str().expect("path stop"));
    let execution_stop = execution_stop(stop);
    let execution_terminal = match execution_stop {
        ExecutionStop::Terminal | ExecutionStop::Stuck => {
            let kind = if execution_stop == ExecutionStop::Terminal {
                ExecutionTerminalKind::Normal
            } else {
                ExecutionTerminalKind::Stuck
            };
            Some(ExecutionTerminal {
                kind,
                artifact: ArtifactRef {
                    role: "terminal-state".to_owned(),
                    digest: if kind == ExecutionTerminalKind::Normal {
                        fixed_digest('3')
                    } else {
                        fixed_digest('4')
                    },
                },
            })
        }
        _ => None,
    };
    let mut path = PathInput {
        definition_digest: definition_digest(),
        test_id: case_id.to_owned(),
        path_ordinal,
        path_key: value
            .get("pathKey")
            .and_then(Value::as_str)
            .map(str::to_owned),
        path_identity_digest: fixed_digest('0'),
        trace_digest: fixed_digest('0'),
        complete: value["complete"].as_bool().expect("path completeness"),
        stop,
        execution_stop,
        execution_terminal,
        events: concrete_events,
        path_predicate,
        equivalences: relations("equivalences"),
        inequalities: relations("inequalities"),
    };
    path.path_identity_digest = derive_path_identity(&path).expect("derived path identity");
    path.trace_digest = derive_trace_digest(&path).expect("derived trace identity");
    path
}

fn collect_variables(term: &Term, variables: &mut BTreeMap<String, String>) {
    match &term.node {
        TermNode::Variable { name } => {
            let previous = variables.insert(name.clone(), term.sort.clone());
            assert!(previous.is_none_or(|sort| sort == term.sort));
        }
        TermNode::Application { args, .. } => {
            for argument in args {
                collect_variables(argument, variables);
            }
        }
        TermNode::Rewrite { left, right } => {
            collect_variables(left, variables);
            collect_variables(right, variables);
        }
        TermNode::Sequence { items } => {
            for item in items {
                collect_variables(item, variables);
            }
        }
        TermNode::Injection { term, .. } => collect_variables(term, variables),
        TermNode::Token { .. } => {}
    }
}

fn authority(case_id: &str, paths: &[PathInput]) -> EvaluationAuthority {
    let mut provenance_by_lineage = BTreeMap::new();
    let mut trace_constructors = BTreeMap::new();
    let mut variables_by_path = BTreeMap::new();
    let mut terminals = BTreeMap::new();
    for path in paths {
        let mut variables = BTreeMap::new();
        collect_variables(&path.path_predicate, &mut variables);
        for event in &path.events {
            let constructor = Constructor {
                name: event.constructor.clone(),
                payload_sorts: event.payload.iter().map(|term| term.sort.clone()).collect(),
                origin_mode: if event.origin.semantic_site.is_some() {
                    OriginMode::EmittingSentenceAndSemanticSite
                } else {
                    OriginMode::EmittingSentence
                },
            };
            let previous =
                trace_constructors.insert(event.constructor.clone(), constructor.clone());
            assert!(previous.is_none_or(|item| item == constructor));
            provenance_by_lineage.insert(
                event.origin.emitting_sentence.lineage_id.clone(),
                event.origin.emitting_sentence.clone(),
            );
            for term in &event.payload {
                collect_variables(term, &mut variables);
            }
        }
        for relation in path.equivalences.iter().chain(&path.inequalities) {
            collect_variables(&relation.left, &mut variables);
            collect_variables(&relation.right, &mut variables);
        }
        variables_by_path.insert(path.path_identity_digest.clone(), variables);
        if let Some(terminal) = &path.execution_terminal {
            terminals.insert(
                terminal.artifact.digest.clone(),
                TerminalAuthority {
                    kind: terminal.kind,
                    definition_digest: definition_digest(),
                    execution_profile_digest: (terminal.kind
                        == ExecutionTerminalKind::SemanticCrash)
                        .then(execution_profile_digest),
                },
            );
        }
    }
    EvaluationAuthority {
        definition_digest: definition_digest(),
        test_id: case_id.to_owned(),
        observer_digest: observer_digest(),
        observer_version: 1,
        execution_profile_digest: execution_profile_digest(),
        bounds: ExecutionBounds {
            depth: Some(20),
            time_ms: Some(1000),
            branches: Some(8),
            results: Some(8),
        },
        trace_constructors,
        provenance_by_lineage,
        signatures: BTreeMap::new(),
        variables_by_path,
        terminals,
    }
}

fn collection(paths: &[PathInput], search: SearchPolicy) -> CollectionEvidence {
    let stop = if search == SearchPolicy::ExistentialFirst
        && paths.iter().any(|path| path.stop == PathStop::MatchFound)
    {
        CollectionStop::MatchFound
    } else if paths.iter().all(|path| path.complete) {
        CollectionStop::SearchExhausted
    } else {
        match paths
            .iter()
            .find(|path| !path.complete)
            .map(|path| path.stop)
            .unwrap_or(PathStop::Error)
        {
            PathStop::DepthLimit => CollectionStop::DepthLimit,
            PathStop::TimeLimit => CollectionStop::TimeLimit,
            PathStop::BranchLimit => CollectionStop::BranchLimit,
            PathStop::ResultLimit => CollectionStop::ResultLimit,
            PathStop::ResourceLimit => CollectionStop::ResourceLimit,
            PathStop::SolverUnknown => CollectionStop::SolverUnknown,
            PathStop::BackendLimit => CollectionStop::BackendLimit,
            PathStop::Error => CollectionStop::Error,
            PathStop::MatchFound => CollectionStop::MatchFound,
            PathStop::Terminal | PathStop::Stuck => CollectionStop::SearchExhausted,
        }
    };
    CollectionEvidence {
        stop,
        pending_work: u64::from(stop != CollectionStop::SearchExhausted),
        empty_search_decision: None,
    }
}

fn exhaustive_options() -> EvaluationOptions {
    EvaluationOptions {
        stable_path_keys: true,
        search_policy: SearchPolicy::Exhaustive,
        input_error: false,
    }
}

#[test]
fn every_applicable_execution_pattern_vector_matches_the_frozen_denotation() {
    let data: Value = serde_json::from_str(EXECUTION_VECTORS).expect("execution vectors");
    let vocabularies = data["eventVocabularies"].as_object().expect("vocabularies");
    let mut vocabulary_by_digest = BTreeMap::new();
    for value in vocabularies.values() {
        let vocabulary = vocabulary(value);
        vocabulary_by_digest.insert(vocabulary.digest.to_string(), vocabulary);
    }
    let mut plans = BTreeMap::new();
    for (name, value) in data["plans"].as_object().expect("plans") {
        let vocabulary = vocabulary_by_digest
            .get(
                value["eventVocabularyDigest"]
                    .as_str()
                    .expect("plan vocabulary"),
            )
            .expect("resolved vocabulary");
        plans.insert(
            name.clone(),
            PatternPlan::from_json(&semantic(value), vocabulary).expect("frozen plan"),
        );
    }
    for (name, value) in data["queries"].as_object().expect("queries") {
        let plan = plans.get(name).expect("query plan");
        let query =
            kink_pattern::NamedQuery::from_json(&semantic(value), plan).expect("frozen query");
        assert_eq!(query.exported_name, *name);
    }
    let table = side_table(&data["sideConditionTable"]);
    let terms = data["terms"].as_object().expect("terms");
    for case in data["cases"].as_array().expect("cases") {
        let case_id = case["id"].as_str().expect("case ID");
        let query_name = case["query"].as_str().expect("query name");
        let plan = plans.get(query_name).expect("case plan");
        let stable = case
            .get("stablePathKeys")
            .and_then(Value::as_bool)
            .unwrap_or(true);
        let search = match case
            .get("searchPolicy")
            .and_then(Value::as_str)
            .unwrap_or("exhaustive")
        {
            "exhaustive" => SearchPolicy::Exhaustive,
            "existential-first" => SearchPolicy::ExistentialFirst,
            other => panic!("unexpected search policy {other}"),
        };
        let paths = case["paths"]
            .as_array()
            .expect("paths")
            .iter()
            .enumerate()
            .map(|(ordinal, item)| path(item, &data, case_id, ordinal))
            .collect::<Vec<_>>();
        let authority = authority(case_id, &paths);
        let collection = collection(&paths, search);
        let result = evaluate(
            &authority,
            plan,
            &paths,
            &collection,
            Some(&table),
            EvaluationOptions {
                stable_path_keys: stable,
                search_policy: search,
                input_error: case.get("inputFailure").is_some(),
            },
        )
        .unwrap_or_else(|error| panic!("{case_id}: {error}"));
        let expected = &case["expected"];
        let expected_outcome = match expected["outcome"].as_str().expect("outcome") {
            "match" => PatternOutcome::Match,
            "no-match" => PatternOutcome::NoMatch,
            "unknown" => PatternOutcome::Unknown,
            "error" => PatternOutcome::Error,
            other => panic!("unexpected outcome {other}"),
        };
        assert_eq!(result.outcome, expected_outcome, "{case_id}");
        assert_eq!(
            result.complete_coverage,
            expected["completeCoverage"].as_bool().expect("coverage"),
            "{case_id}"
        );
        assert_eq!(
            result.native_conformance,
            NativeConformance::NotProven,
            "{case_id}"
        );
        assert_eq!(result.bounds, authority.bounds, "{case_id}");
        if let Some(expected_failure) = expected.get("failure").and_then(Value::as_str) {
            let expected_stop = if expected_failure == "malformed-result" {
                PathStop::Error
            } else {
                stop(expected_failure)
            };
            assert_eq!(result.failure, Some(expected_stop), "{case_id}");
        } else {
            assert_eq!(result.failure, None, "{case_id}");
        }
        if let Some(search_stopped) = expected.get("searchStopped").and_then(Value::as_bool) {
            assert_eq!(
                collection.stop == CollectionStop::MatchFound,
                search_stopped,
                "{case_id}"
            );
        }
        if let Some(replay_policy) = expected.get("replaySearchPolicy").and_then(Value::as_str) {
            assert_eq!(
                result.search_policy,
                match replay_policy {
                    "exhaustive" => SearchPolicy::Exhaustive,
                    "existential-first" => SearchPolicy::ExistentialFirst,
                    other => panic!("unexpected replay policy {other}"),
                },
                "{case_id}"
            );
        }
        if let Some(expected_witness) = expected.get("witness") {
            let actual = &result.witnesses[result.primary_witness.expect("keyed primary")];
            assert_eq!(
                actual.path_key.as_deref(),
                expected_witness["pathKey"].as_str(),
                "{case_id}"
            );
            let indices = expected_witness["eventIndices"]
                .as_array()
                .expect("indices")
                .iter()
                .map(|item| usize::try_from(item.as_u64().expect("index")).expect("usize index"))
                .collect::<Vec<_>>();
            assert_eq!(actual.event_indices, indices, "{case_id}");
            let source_path = &paths[actual.path_ordinal];
            assert_eq!(actual.stop_reason, source_path.stop, "{case_id}");
            assert_eq!(
                actual.execution_stop_reason, source_path.execution_stop,
                "{case_id}"
            );
            assert_eq!(
                actual.events,
                actual
                    .event_indices
                    .iter()
                    .map(|index| source_path.events[*index].clone())
                    .collect::<Vec<_>>(),
                "{case_id}"
            );
            let expected_replay_key = kink_portable::digest(
                &kink_portable::DigestDomain::new("k-in-k/witness-replay-key/v1")
                    .expect("replay domain"),
                &semantic(&serde_json::json!({
                    "testId": case_id,
                    "pathKey": actual.path_key.as_deref().expect("keyed witness"),
                    "eventIndices": actual.event_indices,
                })),
            )
            .expect("replay key payload");
            assert_eq!(
                actual.replay_key.as_ref(),
                Some(&expected_replay_key),
                "{case_id}"
            );
            assert_eq!(
                actual.arm_ordinal,
                expected_witness
                    .get("armOrdinal")
                    .and_then(Value::as_u64)
                    .unwrap_or(0) as usize,
                "{case_id}"
            );
            let expected_bindings = expected_witness["bindings"].as_object().expect("bindings");
            assert_eq!(actual.bindings.len(), expected_bindings.len(), "{case_id}");
            for binding in &actual.bindings {
                let reference = expected_bindings[&binding.name]
                    .as_str()
                    .expect("binding ref");
                assert_eq!(
                    binding.term,
                    term(&terms[reference]),
                    "{case_id}/{}",
                    binding.name
                );
            }
            if let Some(predicate_ref) = expected_witness
                .get("pathPredicate")
                .and_then(Value::as_str)
            {
                let expected_predicate =
                    terms.get(predicate_ref).map(term).unwrap_or_else(|| Term {
                        sort: "Bool".to_owned(),
                        node: TermNode::Token {
                            text: predicate_ref.to_owned(),
                        },
                    });
                assert_eq!(actual.path_predicate, expected_predicate, "{case_id}");
            } else {
                assert_eq!(
                    actual.path_predicate, source_path.path_predicate,
                    "{case_id}"
                );
            }
        } else {
            assert_eq!(result.primary_witness, None, "{case_id}");
        }
        if let Some(expected_indices) = expected.get("allWitnessIndices") {
            let actual = result
                .witnesses
                .iter()
                .map(|witness| witness.event_indices.clone())
                .collect::<Vec<_>>();
            let expected = expected_indices
                .as_array()
                .expect("all indices")
                .iter()
                .map(|indices| {
                    indices
                        .as_array()
                        .expect("indices")
                        .iter()
                        .map(|item| item.as_u64().expect("index") as usize)
                        .collect()
                })
                .collect::<Vec<Vec<usize>>>();
            assert_eq!(actual, expected, "{case_id}");
        }
        if let Some(expected_paths) = expected.get("allWitnessPaths") {
            let actual = result
                .witnesses
                .iter()
                .map(|witness| witness.path_key.as_deref())
                .collect::<Vec<_>>();
            let expected = expected_paths
                .as_array()
                .expect("all paths")
                .iter()
                .map(Value::as_str)
                .collect::<Vec<_>>();
            assert_eq!(actual, expected, "{case_id}");
        }
        if expected
            .get("permutationInvariant")
            .and_then(Value::as_bool)
            == Some(true)
        {
            let mut reversed = paths.clone();
            reversed.reverse();
            let permuted = evaluate(
                &authority,
                plan,
                &reversed,
                &collection,
                Some(&table),
                EvaluationOptions {
                    stable_path_keys: stable,
                    search_policy: search,
                    input_error: false,
                },
            )
            .expect("permuted evaluation");
            assert_eq!(result, permuted, "{case_id}");
            assert_eq!(
                result.witnesses.len(),
                expected["allWitnessCount"].as_u64().expect("witness count") as usize
            );
        }
    }
}

#[test]
fn normalized_plan_and_query_adversaries_fail_closed() {
    let data: Value = serde_json::from_str(EXECUTION_VECTORS).expect("execution vectors");
    let memory = vocabulary(&data["eventVocabularies"]["memory"]);
    let mut bad = data["plans"]["write-eventually-load"].clone();
    bad["variables"][0]["name"] = Value::String("lowercase".to_owned());
    rehash_plan(&mut bad);
    assert_eq!(
        PatternPlan::from_json(&semantic(&bad), &memory)
            .expect_err("lowercase binding")
            .kind(),
        kink_pattern::PatternFailureKind::InvalidVariable
    );

    let mut bad = data["plans"]["write-eventually-load"].clone();
    let duplicate = bad["arms"][0]["atoms"][0]["payload"][0].clone();
    bad["arms"][0]["atoms"][0]["payload"]
        .as_array_mut()
        .expect("payload")
        .push(duplicate);
    rehash_plan(&mut bad);
    assert_eq!(
        PatternPlan::from_json(&semantic(&bad), &memory)
            .expect_err("duplicate payload position")
            .kind(),
        kink_pattern::PatternFailureKind::InvalidPayload
    );

    let mut bad = data["plans"]["nonlexical-subset-side-condition"].clone();
    bad["sideCondition"]["inputVariables"] = serde_json::json!(["ADDRESS", "VALUE"]);
    rehash_plan(&mut bad);
    assert_eq!(
        PatternPlan::from_json(&semantic(&bad), &memory)
            .expect_err("noncanonical side subset")
            .kind(),
        kink_pattern::PatternFailureKind::InvalidVariable
    );

    let mut bad = data["plans"]["write-eventually-load"].clone();
    bad["extension"] = Value::Object(Default::default());
    assert_eq!(
        PatternPlan::from_json(&semantic(&bad), &memory)
            .expect_err("extension field")
            .kind(),
        kink_pattern::PatternFailureKind::MalformedPlan
    );

    let plan = PatternPlan::from_json(&semantic(&data["plans"]["write-eventually-load"]), &memory)
        .expect("base plan");
    let mut query = data["queries"]["write-eventually-load"].clone();
    query["entryModule"] = Value::String("ANOTHER".to_owned());
    assert_eq!(
        kink_pattern::NamedQuery::from_json(&semantic(&query), &plan)
            .expect_err("stale query identity")
            .kind(),
        kink_pattern::PatternFailureKind::QueryIdentity
    );
}

fn refresh_path(path: &mut PathInput) {
    path.path_identity_digest = derive_path_identity(path).expect("refreshed path identity");
    path.trace_digest = derive_trace_digest(path).expect("refreshed trace identity");
}

#[test]
fn supplied_trace_roots_nested_symbolics_and_empty_exhaustion_fail_closed() {
    let data: Value = serde_json::from_str(EXECUTION_VECTORS).expect("execution vectors");
    let base_case = data["cases"]
        .as_array()
        .expect("cases")
        .iter()
        .find(|case| case["id"] == "single-event")
        .expect("single-event case");
    let case_id = base_case["id"].as_str().expect("case ID");
    let memory = vocabulary(&data["eventVocabularies"]["memory"]);
    let query = base_case["query"].as_str().expect("query");
    let plan = PatternPlan::from_json(&semantic(&data["plans"][query]), &memory)
        .expect("single-event plan");
    let paths = base_case["paths"]
        .as_array()
        .expect("paths")
        .iter()
        .enumerate()
        .map(|(ordinal, value)| path(value, &data, case_id, ordinal))
        .collect::<Vec<_>>();
    let base_authority = authority(case_id, &paths);
    let base_collection = collection(&paths, SearchPolicy::Exhaustive);
    evaluate(
        &base_authority,
        &plan,
        &paths,
        &base_collection,
        None,
        exhaustive_options(),
    )
    .expect("validated root case");

    let mut wrong_definition = paths.clone();
    wrong_definition[0].definition_digest = fixed_digest('6');
    refresh_path(&mut wrong_definition[0]);
    assert_eq!(
        evaluate(
            &base_authority,
            &plan,
            &wrong_definition,
            &base_collection,
            None,
            exhaustive_options(),
        )
        .expect_err("refreshed wrong definition")
        .kind(),
        kink_pattern::PatternFailureKind::DefinitionMismatch
    );

    let mut wrong_terminal = base_authority.clone();
    wrong_terminal
        .terminals
        .values_mut()
        .next()
        .expect("terminal root")
        .definition_digest = fixed_digest('6');
    assert_eq!(
        evaluate(
            &wrong_terminal,
            &plan,
            &paths,
            &base_collection,
            None,
            exhaustive_options(),
        )
        .expect_err("wrong terminal definition")
        .kind(),
        kink_pattern::PatternFailureKind::TerminalMismatch
    );

    let mut wrong_bounds = base_authority.clone();
    wrong_bounds.bounds.time_ms = Some(0);
    assert_eq!(
        evaluate(
            &wrong_bounds,
            &plan,
            &paths,
            &base_collection,
            None,
            exhaustive_options(),
        )
        .expect_err("invalid bounds")
        .kind(),
        kink_pattern::PatternFailureKind::BoundsMismatch
    );

    let mut stale_origin = paths.clone();
    stale_origin[0].events[0]
        .origin
        .emitting_sentence
        .content_fingerprint = fixed_digest('6');
    refresh_path(&mut stale_origin[0]);
    assert_eq!(
        evaluate(
            &base_authority,
            &plan,
            &stale_origin,
            &base_collection,
            None,
            exhaustive_options(),
        )
        .expect_err("stale complete provenance")
        .kind(),
        kink_pattern::PatternFailureKind::InvalidOrigin
    );
    let mut stale_site = paths.clone();
    stale_site[0].events[0]
        .origin
        .semantic_site
        .as_mut()
        .expect("memory event site")
        .site_id = fixed_digest('6');
    refresh_path(&mut stale_site[0]);
    assert_eq!(
        evaluate(
            &base_authority,
            &plan,
            &stale_site,
            &base_collection,
            None,
            exhaustive_options(),
        )
        .expect_err("stale semantic-site identity")
        .kind(),
        kink_pattern::PatternFailureKind::InvalidOrigin
    );

    let relation_case = data["cases"]
        .as_array()
        .expect("cases")
        .iter()
        .find(|case| case["id"] == "shared-binding-mismatch")
        .expect("relation case");
    let relation_id = relation_case["id"].as_str().expect("case ID");
    let relation_query = relation_case["query"].as_str().expect("query");
    let relation_plan = PatternPlan::from_json(&semantic(&data["plans"][relation_query]), &memory)
        .expect("relation plan");
    let mut relation_paths = relation_case["paths"]
        .as_array()
        .expect("paths")
        .iter()
        .enumerate()
        .map(|(ordinal, value)| path(value, &data, relation_id, ordinal))
        .collect::<Vec<_>>();
    let symbol_id = fixed_digest('7');
    let symbolic_application = |name: &str| Term {
        sort: "Address".to_owned(),
        node: TermNode::Application {
            symbol_id: symbol_id.clone(),
            label: "symbolicAddress".to_owned(),
            args: vec![Term {
                sort: "Int".to_owned(),
                node: TermNode::Variable {
                    name: name.to_owned(),
                },
            }],
        },
    };
    relation_paths[0].events[0].payload[0] = symbolic_application("X");
    relation_paths[0].events[1].payload[0] = symbolic_application("Y");
    relation_paths[0].equivalences.clear();
    relation_paths[0].inequalities.clear();
    refresh_path(&mut relation_paths[0]);
    let mut relation_authority = authority(relation_id, &relation_paths);
    relation_authority.signatures.insert(
        symbol_id,
        kink_pattern::TermSignature {
            label: "symbolicAddress".to_owned(),
            result_sort: "Address".to_owned(),
            argument_sorts: vec!["Int".to_owned()],
        },
    );
    let relation_result = evaluate(
        &relation_authority,
        &relation_plan,
        &relation_paths,
        &collection(&relation_paths, SearchPolicy::Exhaustive),
        Some(&side_table(&data["sideConditionTable"])),
        exhaustive_options(),
    )
    .expect("nested symbolic relation is a typed unknown");
    assert_eq!(relation_result.outcome, PatternOutcome::Unknown);
    assert!(!relation_result.complete_coverage);
    assert_eq!(relation_result.failure, Some(PathStop::SolverUnknown));
    let mut stale_signature = relation_authority.clone();
    stale_signature
        .signatures
        .values_mut()
        .next()
        .expect("signature root")
        .label = "anotherSymbol".to_owned();
    assert_eq!(
        evaluate(
            &stale_signature,
            &relation_plan,
            &relation_paths,
            &collection(&relation_paths, SearchPolicy::Exhaustive),
            None,
            exhaustive_options(),
        )
        .expect_err("stale signature root")
        .kind(),
        kink_pattern::PatternFailureKind::InvalidTermGraph
    );
    let mut stale_variables = relation_authority.clone();
    stale_variables
        .variables_by_path
        .values_mut()
        .next()
        .expect("variable root")
        .clear();
    assert_eq!(
        evaluate(
            &stale_variables,
            &relation_plan,
            &relation_paths,
            &collection(&relation_paths, SearchPolicy::Exhaustive),
            None,
            exhaustive_options(),
        )
        .expect_err("stale variable root")
        .kind(),
        kink_pattern::PatternFailureKind::InvalidTermGraph
    );

    let empty_authority = authority("empty-search", &[]);
    let missing_witness = CollectionEvidence {
        stop: CollectionStop::SearchExhausted,
        pending_work: 0,
        empty_search_decision: None,
    };
    assert_eq!(
        evaluate(
            &empty_authority,
            &plan,
            &[],
            &missing_witness,
            None,
            exhaustive_options(),
        )
        .expect_err("empty exhaustion without evidence")
        .kind(),
        kink_pattern::PatternFailureKind::InvalidCollection
    );
    let decision = ArtifactRef {
        role: "empty-search-decision".to_owned(),
        digest: fixed_digest('5'),
    };
    let witnessed_empty = CollectionEvidence {
        empty_search_decision: Some(decision.clone()),
        ..missing_witness
    };
    assert_eq!(
        evaluate(
            &empty_authority,
            &plan,
            &[],
            &witnessed_empty,
            None,
            exhaustive_options(),
        )
        .expect("explicit empty exhaustion")
        .outcome,
        PatternOutcome::NoMatch
    );
    assert_eq!(
        aggregate_existential(&[], false, None),
        PatternOutcome::Unknown
    );
    assert_eq!(
        aggregate_existential(&[], false, Some(&decision)),
        PatternOutcome::NoMatch
    );
    assert_eq!(
        aggregate_existential(
            &[],
            false,
            Some(&ArtifactRef {
                role: "event-trace".to_owned(),
                digest: fixed_digest('5'),
            })
        ),
        PatternOutcome::Error
    );

    for row in data["aggregationCases"]
        .as_array()
        .expect("aggregation cases")
    {
        let components = row["components"]
            .as_array()
            .expect("components")
            .iter()
            .map(|value| match value.as_str().expect("component outcome") {
                "match" => PatternOutcome::Match,
                "no-match" => PatternOutcome::NoMatch,
                "unknown" => PatternOutcome::Unknown,
                "error" => PatternOutcome::Error,
                other => panic!("unexpected component outcome {other}"),
            })
            .collect::<Vec<_>>();
        let expected = match row["expected"].as_str().expect("aggregate outcome") {
            "match" => PatternOutcome::Match,
            "no-match" => PatternOutcome::NoMatch,
            "unknown" => PatternOutcome::Unknown,
            "error" => PatternOutcome::Error,
            other => panic!("unexpected aggregate outcome {other}"),
        };
        assert_eq!(
            aggregate_existential(
                &components,
                row["globalError"].as_bool().expect("global error"),
                Some(&decision),
            ),
            expected
        );
    }
}

#[test]
fn every_frozen_semantic_termination_case_preserves_terminal_evidence() {
    let data: Value = serde_json::from_str(EXECUTION_VECTORS).expect("execution vectors");
    let base_case = data["cases"]
        .as_array()
        .expect("cases")
        .iter()
        .find(|case| case["id"] == "single-event")
        .expect("single-event case");
    let memory = vocabulary(&data["eventVocabularies"]["memory"]);
    let query = base_case["query"].as_str().expect("query");
    let plan = PatternPlan::from_json(&semantic(&data["plans"][query]), &memory)
        .expect("single event plan");
    for row in data["semanticTerminationCases"]
        .as_array()
        .expect("termination cases")
    {
        let case_id = row["id"].as_str().expect("case ID");
        if case_id == "backend-error-before-path" {
            let authority = authority(case_id, &[]);
            let result = evaluate(
                &authority,
                &plan,
                &[],
                &CollectionEvidence {
                    stop: CollectionStop::Error,
                    pending_work: 0,
                    empty_search_decision: None,
                },
                None,
                EvaluationOptions {
                    input_error: true,
                    ..exhaustive_options()
                },
            )
            .expect("global backend error result");
            assert_eq!(result.outcome, PatternOutcome::Error, "{case_id}");
            continue;
        }
        let mut paths = base_case["paths"]
            .as_array()
            .expect("paths")
            .iter()
            .enumerate()
            .map(|(ordinal, value)| path(value, &data, case_id, ordinal))
            .collect::<Vec<_>>();
        paths[0].test_id = case_id.to_owned();
        paths[0].complete = row["complete"].as_bool().expect("complete");
        paths[0].stop = stop(row["stopReason"].as_str().expect("stop"));
        paths[0].execution_stop = execution_stop(paths[0].stop);
        paths[0].execution_terminal = row["executionTerminal"].as_str().map(|kind| {
            assert_eq!(kind, "semantic-crash");
            ExecutionTerminal {
                kind: ExecutionTerminalKind::SemanticCrash,
                artifact: ArtifactRef {
                    role: "semantic-crash".to_owned(),
                    digest: fixed_digest('6'),
                },
            }
        });
        if !row["witness"].as_bool().expect("witness") {
            paths[0].events.clear();
        }
        refresh_path(&mut paths[0]);
        let authority = authority(case_id, &paths);
        let evaluation = evaluate(
            &authority,
            &plan,
            &paths,
            &CollectionEvidence {
                stop: CollectionStop::SearchExhausted,
                pending_work: 0,
                empty_search_decision: None,
            },
            None,
            exhaustive_options(),
        );
        match row["expected"].as_str().expect("expected") {
            "match" => assert_eq!(
                evaluation.expect("crash witness").outcome,
                PatternOutcome::Match,
                "{case_id}"
            ),
            "no-match" => assert_eq!(
                evaluation.expect("crash absence").outcome,
                PatternOutcome::NoMatch,
                "{case_id}"
            ),
            "reject" => assert_eq!(
                evaluation.expect_err("missing crash evidence").kind(),
                kink_pattern::PatternFailureKind::TerminalMismatch,
                "{case_id}"
            ),
            other => panic!("unexpected termination outcome {other}"),
        }
    }
}

fn mutation_site(name: &str, data: &Value) -> Site {
    let value = &data["sites"][name];
    let target_lineage = digest(value["lineage"].as_str().expect("site lineage"));
    let selector_role = if name == "write" { "left" } else { "right" }.to_owned();
    let term_path = semantic(&serde_json::json!([{"kind": "field", "name": "body"}]));
    let bindings = Vec::new();
    Site {
        site_id: derive_site_id(
            "vector-operator",
            1,
            &fixed_digest('a'),
            &target_lineage,
            &selector_role,
            term_path.clone(),
            &bindings,
        )
        .expect("derived vector site"),
        selector_role,
        target_lineage,
        term_path,
        bindings,
    }
}

fn site_name(site_id: &Digest, sites: &[Site], data: &Value) -> String {
    let lineage = &sites
        .iter()
        .find(|site| &site.site_id == site_id)
        .expect("site membership")
        .target_lineage;
    data["sites"]
        .as_object()
        .expect("sites")
        .iter()
        .find(|(_, value)| value["lineage"].as_str() == Some(lineage.as_str()))
        .map(|(name, _)| name.clone())
        .expect("site name")
}

fn site_rank(site: &Site, data: &Value) -> (u64, u64, u64, u64, u64) {
    let value = data["sites"]
        .as_object()
        .expect("sites")
        .values()
        .find(|value| value["lineage"].as_str() == Some(site.target_lineage.as_str()))
        .expect("site rank");
    let location = value["location"].as_array().expect("site location");
    (
        value["moduleOrdinal"].as_u64().expect("module ordinal"),
        location[0].as_u64().expect("start line"),
        location[1].as_u64().expect("start column"),
        location[2].as_u64().expect("end line"),
        location[3].as_u64().expect("end column"),
    )
}

#[test]
fn every_applicable_mutation_selection_vector_folds_supplied_tuples() {
    let data: Value = serde_json::from_str(MUTATION_VECTORS).expect("mutation vectors");
    for case in data["selectionCases"].as_array().expect("selection cases") {
        let case_id = case["id"].as_str().expect("case ID");
        if case_id == "binding-order-normalized" {
            let make_bindings = |items: &Value| {
                items
                    .as_array()
                    .expect("bindings")
                    .iter()
                    .map(|item| Binding {
                        name: item["name"].as_str().expect("binding name").to_owned(),
                        term: match item["termRef"].as_str().expect("term ref") {
                            "a" => Term {
                                sort: "Address".to_owned(),
                                node: TermNode::Token {
                                    text: "1".to_owned(),
                                },
                            },
                            "v7" => Term {
                                sort: "Int".to_owned(),
                                node: TermNode::Token {
                                    text: "7".to_owned(),
                                },
                            },
                            other => panic!("unexpected binding term {other}"),
                        },
                    })
                    .collect::<Vec<_>>()
            };
            let alternatives = case["bindings"].as_array().expect("binding alternatives");
            assert_eq!(
                canonical_binding_digest(&make_bindings(&alternatives[0])),
                canonical_binding_digest(&make_bindings(&alternatives[1])),
                "{case_id}"
            );
        }
        let tuples = case["suppliedSiteTuples"]
            .as_array()
            .expect("site tuples")
            .iter()
            .map(|tuple| DiscoveryTuple {
                sites: tuple
                    .as_array()
                    .expect("site tuple")
                    .iter()
                    .map(|name| mutation_site(name.as_str().expect("site name"), &data))
                    .collect(),
                bindings: Vec::new(),
            })
            .collect::<Vec<_>>();
        let policy_name = case["policy"].as_str().expect("policy");
        let policy = match policy_name {
            "exact" => SelectionPolicy::Exact {
                expected_tuple_count: case["expectedTupleCount"].as_u64().expect("tuple count")
                    as usize,
                expected_tuple_arity: case["expectedTupleArity"].as_u64().expect("tuple arity")
                    as usize,
            },
            "each" => SelectionPolicy::Each,
            "tuple-each" => SelectionPolicy::TupleEach,
            "all-matches" => SelectionPolicy::AllMatches,
            other => panic!("unexpected policy {other}"),
        };
        let expected = &case["expected"];
        let joined =
            policy_name == "tuple-each" || tuples.iter().any(|tuple| tuple.sites.len() > 1);
        let tuple_symmetric = case
            .get("tupleSymmetric")
            .and_then(Value::as_bool)
            .unwrap_or(false);
        let discovery_complete = case
            .get("discoveryExhaustive")
            .and_then(Value::as_bool)
            .unwrap_or(true);
        let mut canonical_sites = tuples
            .iter()
            .flat_map(|tuple| tuple.sites.iter().cloned())
            .collect::<Vec<_>>();
        canonical_sites.sort_by_key(|site| site_rank(site, &data));
        canonical_sites.dedup_by(|left, right| left.site_id == right.site_id);
        let canonical_tuples = if joined {
            let mut canonical = tuples.clone();
            canonical.sort_by_key(|tuple| {
                tuple
                    .sites
                    .iter()
                    .map(|site| site_rank(site, &data))
                    .collect::<Vec<_>>()
            });
            canonical.dedup_by(|left, right| {
                left.sites
                    .iter()
                    .map(|site| &site.site_id)
                    .eq(right.sites.iter().map(|site| &site.site_id))
            });
            canonical
        } else {
            canonical_sites
                .iter()
                .cloned()
                .map(|site| DiscoveryTuple {
                    sites: vec![site],
                    bindings: Vec::new(),
                })
                .collect()
        };
        let registry_id = fixed_digest('9');
        let authority = DiscoveryAuthority {
            registry_id: registry_id.clone(),
            operator_id: "vector-operator".to_owned(),
            operator_version: 1,
            operator_digest: fixed_digest('8'),
            baseline_definition_digest: fixed_digest('a'),
            canonical_sites: canonical_sites.clone(),
            canonical_tuples,
            discovery_complete,
            joined_roles: joined.then(|| vec!["left".to_owned(), "right".to_owned()]),
            tuple_symmetric,
        };
        let evidence = if discovery_complete {
            DiscoveryEvidence::CompleteFinite {
                registry: ArtifactRef {
                    role: "mutation-site-registry".to_owned(),
                    digest: registry_id,
                },
            }
        } else {
            DiscoveryEvidence::Incomplete {
                registry: ArtifactRef {
                    role: "mutation-site-registry".to_owned(),
                    digest: registry_id,
                },
                failure: kink_pattern::CandidateFailureKind::IncompleteGeneration,
            }
        };
        let registry = DiscoveryRegistry {
            tuples,
            evidence,
            joined,
            tuple_symmetric,
        };
        let selection = select(
            &registry,
            &authority,
            policy,
            case["candidateCap"].as_u64().expect("cap") as usize,
        );
        if case_id == "duplicate-site-rejected" {
            assert_eq!(
                selection
                    .expect_err("duplicate registry must publish no generation")
                    .kind(),
                kink_pattern::CandidateFailureKind::DuplicateSite,
                "{case_id}"
            );
            continue;
        }
        let mut result = selection.unwrap_or_else(|error| panic!("{case_id}: {error}"));
        assert_eq!(
            result.completeness == kink_contracts::Completeness::CompleteFinite,
            expected["complete"].as_bool().expect("complete"),
            "{case_id}"
        );
        let expected_failure = expected
            .get("failure")
            .and_then(Value::as_str)
            .map(|value| match value {
                "cardinality-mismatch" => kink_pattern::CandidateFailureKind::CardinalityMismatch,
                "invalid-join" => kink_pattern::CandidateFailureKind::InvalidJoin,
                "incomplete-generation" => kink_pattern::CandidateFailureKind::IncompleteGeneration,
                other => panic!("unexpected candidate failure {other}"),
            });
        assert_eq!(result.failure, expected_failure, "{case_id}");
        assert_eq!(
            result.scored,
            expected
                .get("defaultScored")
                .and_then(Value::as_bool)
                .unwrap_or(expected_failure.is_none()),
            "{case_id}"
        );
        assert_eq!(result.native_conformance, NativeConformance::NotProven);
        if let Some(expected_tuples) = expected.get("candidateSiteTuples") {
            let actual = result
                .selected_origins
                .iter()
                .map(|origin| {
                    origin
                        .site_tuple
                        .iter()
                        .map(|site| site_name(site, &canonical_sites, &data))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let expected = expected_tuples
                .as_array()
                .expect("expected tuples")
                .iter()
                .map(|tuple| {
                    tuple
                        .as_array()
                        .expect("tuple")
                        .iter()
                        .map(|name| name.as_str().expect("name").to_owned())
                        .collect()
                })
                .collect::<Vec<Vec<String>>>();
            assert_eq!(actual, expected, "{case_id}");
        }
        if let Some(count) = expected
            .get("retainedOriginTupleCount")
            .and_then(Value::as_u64)
        {
            let retained = result
                .selected_origins
                .iter()
                .map(|origin| origin.discovery_tuples.len())
                .sum::<usize>();
            assert_eq!(retained, count as usize, "{case_id}");
        }
        if case_id == "identical-patch-dedup-retains-origins" {
            let patch_id = digest(&"1".repeat(64));
            let patches = result
                .selected_origins
                .iter()
                .cloned()
                .map(|origin| SuppliedPatch {
                    patch_id: patch_id.clone(),
                    origin,
                    edit_receipts: Vec::new(),
                })
                .collect();
            result = result
                .fold_patches("op", 1, &digest(&"a".repeat(64)), patches)
                .expect("patch fold");
            assert_eq!(
                result.candidates.len(),
                expected["candidateCount"]
                    .as_u64()
                    .expect("candidate count") as usize
            );
            assert_eq!(
                result.candidates[0].origins.len(),
                expected["retainedOriginTupleCount"]
                    .as_u64()
                    .expect("origin count") as usize
            );
        }
    }
}

#[test]
fn discovery_authority_and_edit_receipt_adversaries_publish_nothing() {
    let data: Value = serde_json::from_str(MUTATION_VECTORS).expect("mutation vectors");
    let write = mutation_site("write", &data);
    let load = mutation_site("load", &data);
    let canonical_tuples = vec![
        DiscoveryTuple {
            sites: vec![write.clone()],
            bindings: Vec::new(),
        },
        DiscoveryTuple {
            sites: vec![load.clone()],
            bindings: Vec::new(),
        },
    ];
    let registry_id = fixed_digest('9');
    let authority = DiscoveryAuthority {
        registry_id: registry_id.clone(),
        operator_id: "vector-operator".to_owned(),
        operator_version: 1,
        operator_digest: fixed_digest('8'),
        baseline_definition_digest: fixed_digest('a'),
        canonical_sites: vec![write.clone(), load.clone()],
        canonical_tuples: canonical_tuples.clone(),
        discovery_complete: true,
        joined_roles: None,
        tuple_symmetric: false,
    };
    let mut reversed = canonical_tuples.clone();
    reversed.reverse();
    let registry = DiscoveryRegistry {
        tuples: reversed,
        evidence: DiscoveryEvidence::CompleteFinite {
            registry: ArtifactRef {
                role: "mutation-site-registry".to_owned(),
                digest: registry_id.clone(),
            },
        },
        joined: false,
        tuple_symmetric: false,
    };
    let selected = select(&registry, &authority, SelectionPolicy::Each, 4)
        .expect("claimant tuple order is replaced by resolved canonical order");
    assert_eq!(
        selected
            .selected_origins
            .iter()
            .map(|origin| origin.site_tuple[0].clone())
            .collect::<Vec<_>>(),
        vec![write.site_id.clone(), load.site_id.clone()]
    );

    let mut stale_site = registry.clone();
    stale_site.tuples[0].sites[0].target_lineage = fixed_digest('6');
    assert_eq!(
        select(&stale_site, &authority, SelectionPolicy::Each, 4)
            .expect_err("stale site metadata")
            .kind(),
        kink_pattern::CandidateFailureKind::InvalidRegistry
    );
    let mut stale_registry = registry.clone();
    match &mut stale_registry.evidence {
        DiscoveryEvidence::CompleteFinite { registry }
        | DiscoveryEvidence::Incomplete { registry, .. } => registry.digest = fixed_digest('7'),
    }
    assert_eq!(
        select(&stale_registry, &authority, SelectionPolicy::Each, 4)
            .expect_err("stale registry identity")
            .kind(),
        kink_pattern::CandidateFailureKind::InvalidRegistry
    );
    let mut missing_member = registry.clone();
    missing_member.tuples.pop();
    assert_eq!(
        select(&missing_member, &authority, SelectionPolicy::Each, 4)
            .expect_err("missing canonical member")
            .kind(),
        kink_pattern::CandidateFailureKind::InvalidRegistry
    );
    let mut incomplete_authority = authority.clone();
    incomplete_authority.discovery_complete = false;
    assert_eq!(
        select(&registry, &incomplete_authority, SelectionPolicy::Each, 4)
            .expect_err("forged complete finite authority")
            .kind(),
        kink_pattern::CandidateFailureKind::InvalidRegistry
    );

    let joined_tuple = DiscoveryTuple {
        sites: vec![write.clone(), load.clone()],
        bindings: Vec::new(),
    };
    let operator_digest = fixed_digest('8');
    let template_digest = fixed_digest('7');
    let edit_id = fixed_digest('6');
    let mut patch = SuppliedPatch {
        patch_id: fixed_digest('5'),
        origin: PatchOrigin {
            site_tuple: vec![write.site_id.clone(), load.site_id.clone()],
            discovery_tuples: vec![joined_tuple],
        },
        edit_receipts: vec![EditOriginReceipt {
            edit_id: edit_id.clone(),
            operation: "replace-term".to_owned(),
            target_lineage: write.target_lineage.clone(),
            operator_id: "vector-operator".to_owned(),
            operator_version: 1,
            operator_digest: operator_digest.clone(),
            patch_template_digest: template_digest.clone(),
            template_role: "replacement".to_owned(),
            sources: vec![
                EditReceiptSource {
                    discovery_tuple_index: 0,
                    site_id: write.site_id.clone(),
                    selector_role: "left".to_owned(),
                    tuple_bindings: Vec::new(),
                },
                EditReceiptSource {
                    discovery_tuple_index: 0,
                    site_id: load.site_id.clone(),
                    selector_role: "right".to_owned(),
                    tuple_bindings: Vec::new(),
                },
            ],
        }],
    };
    let receipt_authority = ReceiptAuthority {
        operator_id: "vector-operator".to_owned(),
        operator_version: 1,
        operator_digest,
        patch_template_digest: template_digest,
    };
    let roles = [PatchTemplateRole {
        name: "replacement".to_owned(),
        operation: "replace-term".to_owned(),
        source_roles: vec!["left".to_owned(), "right".to_owned()],
    }];
    let selector_roles = ["left".to_owned(), "right".to_owned()];
    assert!(
        validate_edit_receipts(
            &patch,
            &receipt_authority,
            &roles,
            &selector_roles,
            std::slice::from_ref(&edit_id),
        )
        .is_ok()
    );
    patch.edit_receipts[0].sources.reverse();
    assert_eq!(
        validate_edit_receipts(
            &patch,
            &receipt_authority,
            &roles,
            &selector_roles,
            std::slice::from_ref(&edit_id),
        )
        .expect_err("reordered receipt sources")
        .kind(),
        kink_pattern::CandidateFailureKind::InvalidReceipt
    );
    patch.edit_receipts[0].sources.reverse();
    patch.edit_receipts[0].target_lineage = fixed_digest('4');
    assert_eq!(
        validate_edit_receipts(
            &patch,
            &receipt_authority,
            &roles,
            &selector_roles,
            &[edit_id],
        )
        .expect_err("cross-origin receipt target")
        .kind(),
        kink_pattern::CandidateFailureKind::InvalidReceipt
    );
}

#[test]
fn frozen_site_instance_candidate_and_mutant_identities_are_exact() {
    let data: Value = serde_json::from_str(MUTATION_VECTORS).expect("mutation vectors");
    let rows = data["idDerivation"].as_array().expect("ID rows");
    let site = &rows[0];
    let payload = &site["payload"];
    assert_eq!(
        derive_site_id(
            payload["operatorId"].as_str().expect("operator"),
            payload["operatorVersion"].as_u64().expect("version"),
            &digest(
                payload["baselineDefinitionDigest"]
                    .as_str()
                    .expect("baseline")
            ),
            &digest(payload["targetLineage"].as_str().expect("lineage")),
            payload["selectorRole"].as_str().expect("selector role"),
            semantic(&payload["termPath"]),
            &[],
        )
        .expect("site ID")
        .as_str(),
        site["expected"].as_str().expect("expected site")
    );
    let candidate = rows
        .iter()
        .find(|row| row["kind"] == "candidate")
        .expect("candidate row");
    let payload = &candidate["payload"];
    assert_eq!(
        derive_candidate_id(
            payload["operatorId"].as_str().expect("operator"),
            payload["operatorVersion"].as_u64().expect("version"),
            &digest(
                payload["baselineDefinitionDigest"]
                    .as_str()
                    .expect("baseline")
            ),
            &digest(payload["patchId"].as_str().expect("patch")),
        )
        .expect("candidate ID")
        .as_str(),
        candidate["expected"].as_str().expect("expected candidate")
    );
    let instance = rows
        .iter()
        .find(|row| row["kind"] == "instance")
        .expect("instance row");
    let payload = &instance["payload"];
    let site_id = digest(payload["siteTuple"][0].as_str().expect("instance site"));
    let tuple = DiscoveryTuple {
        sites: vec![Site {
            site_id: site_id.clone(),
            selector_role: "write".to_owned(),
            target_lineage: digest(&"b".repeat(64)),
            term_path: semantic(&serde_json::json!([{"kind": "field", "name": "body"}])),
            bindings: Vec::new(),
        }],
        bindings: Vec::new(),
    };
    let receipt = &payload["editReceipts"][0];
    let source = &receipt["sources"][0];
    let supplied = SuppliedPatch {
        patch_id: digest(payload["patchId"].as_str().expect("instance patch")),
        origin: PatchOrigin {
            site_tuple: vec![site_id.clone()],
            discovery_tuples: vec![tuple],
        },
        edit_receipts: vec![EditOriginReceipt {
            edit_id: digest(receipt["editId"].as_str().expect("receipt edit")),
            operation: "replace-term".to_owned(),
            target_lineage: digest(&"b".repeat(64)),
            operator_id: receipt["operator"]["id"]
                .as_str()
                .expect("receipt operator")
                .to_owned(),
            operator_version: receipt["operator"]["version"]
                .as_u64()
                .expect("receipt version"),
            operator_digest: digest(
                receipt["operator"]["digest"]
                    .as_str()
                    .expect("receipt operator digest"),
            ),
            patch_template_digest: digest(
                receipt["patchTemplateDigest"]
                    .as_str()
                    .expect("template digest"),
            ),
            template_role: receipt["templateRole"]
                .as_str()
                .expect("template role")
                .to_owned(),
            sources: vec![EditReceiptSource {
                discovery_tuple_index: source["discoveryTupleIndex"].as_u64().expect("tuple index")
                    as usize,
                site_id,
                selector_role: source["selectorRole"]
                    .as_str()
                    .expect("source role")
                    .to_owned(),
                tuple_bindings: Vec::new(),
            }],
        }],
    };
    assert_eq!(
        derive_instance_id(
            payload["operatorId"].as_str().expect("instance operator"),
            payload["operatorVersion"]
                .as_u64()
                .expect("instance version"),
            &digest(
                payload["baselineDefinitionDigest"]
                    .as_str()
                    .expect("instance baseline")
            ),
            SelectionPolicy::Exact {
                expected_tuple_count: 1,
                expected_tuple_arity: 1,
            },
            &supplied,
        )
        .expect("derived instance identity")
        .as_str(),
        instance["expected"].as_str().expect("expected instance")
    );
    let mutant = rows
        .iter()
        .find(|row| row["kind"] == "mutant")
        .expect("mutant row");
    let payload = &mutant["payload"];
    assert_eq!(
        derive_mutant_id(
            &digest(
                payload["baselineDefinitionDigest"]
                    .as_str()
                    .expect("baseline")
            ),
            &digest(payload["patchId"].as_str().expect("patch")),
        )
        .as_str(),
        mutant["expected"].as_str().expect("expected mutant")
    );
    let other_path = &rows[1];
    assert_ne!(
        site["expected"], other_path["expected"],
        "same lineage at another typed path must remain distinct"
    );
}
