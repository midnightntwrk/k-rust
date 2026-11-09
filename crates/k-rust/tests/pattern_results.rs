//! The facade hands a result's KORE either as JSON text (`Backend::execute_json` and the others,
//! which the bindings, the RPC server and the CLI hand out) or as a pattern
//! (`Backend::execute_kore` and the others); both are built from the same terms, and an output
//! holding patterns serializes with serde to the text.
//! Each fixture here runs both forms of every execution and search, or of a proof, on fresh
//! backends and compares their JSON, and checks that its own JSON shows what it is meant to: builtin
//! collections, observation events, effects, coverage with condition records, diagnostics,
//! cut-point and branch candidates, a branch leaf's remainder (with a solver; without one, the
//! indeterminate leaf's cause), implementation-chosen values, unsupported hooks, passed stops
//! and state matches.
//! Another fixture's JSON cannot show it in its place.
//! The run lists that need a compiled definition (contradicted claims, allowance refusals,
//! short-circuit readings, discarded events) are compared in the tests that build them
//! (`contradicted_claims.rs`, `short_circuit_readings.rs`, `undefined_step_coverage.rs`).

#[path = "support/pattern_results.rs"]
mod pattern_results;

use k_rust::backend::{
    Backend, BackendOptions, ConditionCollection, ExecuteRequest, PassedStopOutput, ProveRequest,
    ResultModalityOutput, SearchPatternRequest, SearchRequest, StateMatchRequest,
};
use k_rust::kore::{ast::Pattern, parser::parse_pattern};
use pattern_results::{
    executions_alike, leaf_shows, pattern_searches_alike, searches_alike, shows,
};
use serde_json::Value;

const MODALITIES: [ResultModalityOutput; 2] = [
    ResultModalityOutput::PathSet,
    ResultModalityOutput::StateSet,
];

/// A state holding a `List`, a `Map`, a `Set` and the map's keys as a list (`MAP.keys_list`,
/// whose order the definition leaves to the implementation), and a rule `finish` with a
/// condition on the state's first argument.
const COLLECTIONS: &str = r#"[]
    module MAIN
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        hooked-sort SortList{}
            [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
        hooked-sort SortSet{}
            [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
        hooked-sort SortMap{}
            [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
        sort SortState{} []
        hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
        hooked-symbol listItem{}(SortInt{}) : SortList{} [function{}(), total{}(), hook{}("LIST.element")]
        hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
            [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
        hooked-symbol setUnit{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
        hooked-symbol setItem{}(SortInt{}) : SortSet{} [function{}(), total{}(), hook{}("SET.element")]
        hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{}
            [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
        hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
        hooked-symbol mapItem{}(SortInt{}, SortInt{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
        hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
            [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
        hooked-symbol keys{}(SortMap{}) : SortList{} [function{}(), total{}(), hook{}("MAP.keys_list")]
        symbol state{}(SortInt{}, SortList{}, SortMap{}, SortSet{}, SortList{}) : SortState{} [constructor{}()]
        symbol done{}(SortList{}, SortMap{}, SortSet{}) : SortState{} [constructor{}()]
        axiom{} \rewrites{SortState{}}(
            \and{SortState{}}(
                state{}(X:SortInt{}, L:SortList{}, M:SortMap{}, S:SortSet{}, K:SortList{}),
                \equals{SortInt{}, SortState{}}(X:SortInt{}, \dv{SortInt{}}("0"))
            ),
            done{}(listConcat{}(L:SortList{}, K:SortList{}), M:SortMap{}, S:SortSet{})
        ) [label{}("finish")]
    endmodule []"#;

/// Two rules from `initial`, each logging a line (an effect) on its branch.
const EFFECTFUL_BRANCH: &str = r#"[]
    module MAIN
        sort SortString{} [hasDomainValues{}()]
        sort SortK{} []
        sort SortState{} []
        symbol initial{}() : SortState{} [constructor{}()]
        symbol left{}(SortK{}) : SortState{} [constructor{}()]
        symbol right{}(SortK{}) : SortState{} [constructor{}()]
        symbol merged{}() : SortState{} [constructor{}()]
        symbol dotk{}() : SortK{} [constructor{}()]
        hooked-symbol log{}(SortString{}) : SortK{}
            [function{}(), hook{}("IO.logString")]
        axiom{} \rewrites{SortState{}}(
            \and{SortState{}}(initial{}(), \top{SortState{}}()),
            left{}(log{}(\dv{SortString{}}("left")))
        ) [label{}("left")]
        axiom{} \rewrites{SortState{}}(
            \and{SortState{}}(initial{}(), \top{SortState{}}()),
            right{}(log{}(\dv{SortString{}}("right")))
        ) [label{}("right")]
        axiom{} \rewrites{SortState{}}(
            \and{SortState{}}(left{}(dotk{}()), \top{SortState{}}()), merged{}()
        ) [label{}("left-merged")]
    endmodule []"#;

/// A rule that applies to `wrap(X)` only where `X` is `zero`: with a solver, a symbolic
/// `wrap(X)` branches to `done` and leaves the rest of `X` as a remainder; without one, the
/// step is indeterminate and its leaf carries the cause.
const NARROWING: &str = r#"[]
    module MAIN
        sort SortS{} []
        symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
        symbol zero{}() : SortS{} [constructor{}()]
        symbol one{}() : SortS{} [constructor{}()]
        symbol done{}() : SortS{} [constructor{}()]
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(wrap{}(zero{}()), \top{SortS{}}()), done{}()
        ) [label{}("narrow")]
    endmodule []"#;

/// A function whose hook k-rust does not implement.
const UNSUPPORTED_HOOK: &str = r#"[]
    module MAIN
        sort SortState{} [hasDomainValues{}()]
        hooked-symbol missing{}(SortState{}) : SortState{}
            [function{}(), hook{}("TEST.missing")]
    endmodule []"#;

/// A claim that every path from `start` reaches `done`: one path is stuck at `stuck` and the
/// other counts for ever, so a bounded proof leaves a stuck leaf and leaves at its bound.
const REFUTED_CLAIM: &str = r#"[]
    module MAIN
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        sort SortS{} []
        symbol start{}() : SortS{} [constructor{}(), functional{}()]
        symbol stuck{}() : SortS{} [constructor{}(), functional{}()]
        symbol done{}() : SortS{} [constructor{}(), functional{}()]
        symbol count{}(SortInt{}) : SortS{} [constructor{}(), functional{}()]
        hooked-symbol add{}(SortInt{}, SortInt{}) : SortInt{}
            [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
        alias weakAlwaysFinally{S}(S) : S where weakAlwaysFinally{S}(@X:S) := @X:S []
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(start{}(), \top{SortS{}}()), \and{SortS{}}(stuck{}(), \top{SortS{}}())
        ) [label{}("to-stuck")]
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(start{}(), \top{SortS{}}()),
            \and{SortS{}}(count{}(\dv{SortInt{}}("0")), \top{SortS{}}())
        ) [label{}("to-count")]
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(count{}(I:SortInt{}), \top{SortS{}}()),
            \and{SortS{}}(count{}(add{}(I:SortInt{}, \dv{SortInt{}}("1"))), \top{SortS{}}())
        ) [label{}("count")]
        claim{} \implies{SortS{}}(
            \and{SortS{}}(\top{SortS{}}(), start{}()),
            weakAlwaysFinally{SortS{}}(\and{SortS{}}(done{}(), \top{SortS{}}()))
        ) [label{}("all-done")]
    endmodule []"#;

fn kore(text: &str) -> Pattern {
    parse_pattern(text).unwrap_or_else(|error| panic!("{text}: {error}"))
}

fn fresh(definition: &'static str) -> impl Fn() -> Backend {
    move || Backend::new(definition, "MAIN", BackendOptions::DEFAULT).unwrap()
}

/// The `Int` domain value `value`.
fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// `items` joined by right-nested applications of `concat`, the shape a sender writes and a
/// result holds.
fn chain(concat: &str, items: &[String]) -> String {
    let (last, rest) = items.split_last().unwrap();
    rest.iter().rev().fold(last.clone(), |chain, item| {
        format!("{concat}{{}}({item}, {chain})")
    })
}

fn collections_state() -> Pattern {
    let list = chain(
        "listConcat",
        &(1..=4)
            .map(|n| format!("listItem{{}}({})", int(n)))
            .collect::<Vec<_>>(),
    );
    let map = || {
        chain(
            "mapConcat",
            &(1..=4)
                .map(|n| format!("mapItem{{}}({}, {})", int(n), int(10 * n)))
                .collect::<Vec<_>>(),
        )
    };
    let set = chain(
        "setConcat",
        &(1..=4)
            .map(|n| format!("setItem{{}}({})", int(n)))
            .collect::<Vec<_>>(),
    );
    kore(&format!(
        "state{{}}({}, {list}, {}, {set}, keys{{}}({}))",
        int(0),
        map(),
        map()
    ))
}

/// Assert that `results`, the JSON of the fixture `fixture`, shows each of `keys` ([`shows`]).
fn assert_shows(fixture: &str, results: &[Value], keys: &[&str]) {
    for key in keys {
        assert!(
            shows(results, key),
            "{fixture}: {key}: {}",
            serde_json::to_string(results).unwrap()
        );
    }
}

/// Assert that `results`, the JSON of the fixture `fixture`, has a leaf whose `reason` is
/// `reason` and that shows `key` ([`leaf_shows`]).
fn assert_leaf_shows(fixture: &str, results: &[Value], reason: &str, key: &str) {
    assert!(
        leaf_shows(results, reason, key),
        "{fixture}: a {reason} leaf with {key}: {}",
        serde_json::to_string(results).unwrap()
    );
}

/// Assert that `results`, the JSON of the fixture `fixture`, holds the three builtin collections'
/// concatenations.
fn assert_collections(fixture: &str, results: &[Value]) {
    let text = serde_json::to_string(results).unwrap();
    for symbol in ["listConcat", "mapConcat", "setConcat"] {
        assert!(
            text.contains(&format!(r#""{symbol}""#)),
            "{fixture}: {symbol}: {text}"
        );
    }
}

#[test]
fn collections_coverage_and_state_matches_serialize_alike() {
    let conditions: ConditionCollection =
        serde_json::from_value(serde_json::json!({ "rules": ["finish"] })).unwrap();
    for modality in MODALITIES {
        let request = ExecuteRequest {
            result_modality: modality,
            collect_coverage: true,
            collect_offered: true,
            collect_counts: true,
            collect_conditions: Some(conditions.clone()),
            match_states: Some(StateMatchRequest::new(kore(
                "done{}(L:SortList{}, M:SortMap{}, S:SortSet{})",
            ))),
            ..ExecuteRequest::new(collections_state())
        };
        let run = executions_alike(fresh(COLLECTIONS), &request);
        let fixture = format!("the run of finish ({modality:?})");
        assert_collections(&fixture, &run);
        assert_shows(
            &fixture,
            &run,
            &[
                "coverage",
                "conditions",
                "implementationChosenValues",
                "stateMatches",
            ],
        );
        let stuck = ExecuteRequest {
            max_depth: Some(0),
            ..request
        };
        let run = executions_alike(fresh(COLLECTIONS), &stuck);
        let fixture = format!("the run stopped at depth 0 ({modality:?})");
        assert_collections(&fixture, &run);
        assert_leaf_shows(&fixture, &run, "depth-bound", "state");
        assert_shows(&fixture, &run, &["coverage", "implementationChosenValues"]);
    }
    let search = searches_alike(fresh(COLLECTIONS), &SearchRequest::new(collections_state()));
    assert_collections("the search", &search);
    assert_shows("the search", &search, &["implementationChosenValues"]);
    let pattern = pattern_searches_alike(
        fresh(COLLECTIONS),
        &SearchPatternRequest::new(
            collections_state(),
            kore("done{}(L:SortList{}, M:SortMap{}, S:SortSet{})"),
        ),
    );
    assert_collections("the pattern search", &pattern);
    assert_shows(
        "the pattern search",
        &pattern,
        &["implementationChosenValues", "matches"],
    );
}

#[test]
fn observations_and_effects_serialize_alike() {
    for modality in MODALITIES {
        let request = ExecuteRequest {
            result_modality: modality,
            ..ExecuteRequest::new(kore("initial{}()"))
        };
        let run = executions_alike(fresh(EFFECTFUL_BRANCH), &request);
        assert_shows(
            &format!("the run ({modality:?})"),
            &run,
            &["observations", "branch", "effects"],
        );
    }
    let search = searches_alike(
        fresh(EFFECTFUL_BRANCH),
        &SearchRequest::new(kore("initial{}()")),
    );
    assert_shows(
        "the search",
        &search,
        &["observations", "branch", "effects"],
    );
    let pattern = pattern_searches_alike(
        fresh(EFFECTFUL_BRANCH),
        &SearchPatternRequest::new(kore("initial{}()"), kore("X:SortState{}")),
    );
    assert_shows(
        "the pattern search",
        &pattern,
        &["observations", "branch", "effects", "matches"],
    );
}

#[test]
fn diagnostics_candidates_and_remainders_serialize_alike() {
    let budget = |state: &str| ExecuteRequest {
        max_simplification_iterations: 3,
        ..ExecuteRequest::new(kore(state))
    };
    let cut = executions_alike(
        fresh(include_str!("fixtures/execution-budget.kore")),
        &ExecuteRequest {
            cut_point_rules: vec!["to-g".into()],
            ..budget("start{}()")
        },
    );
    assert_leaf_shows("the cut point to-g", &cut, "cut-point", "candidates");
    assert_shows("the cut point to-g", &cut, &["diagnostics"]);
    let branch = executions_alike(
        fresh(include_str!("fixtures/execution-candidates.kore")),
        &ExecuteRequest {
            stop_at_branch: true,
            ..budget("start{}()")
        },
    );
    assert_leaf_shows("the stopped branch", &branch, "branch", "candidates");
    assert_shows("the stopped branch", &branch, &["diagnostics"]);
    let run = executions_alike(
        fresh(include_str!("fixtures/execution-candidates.kore")),
        &budget("start{}()"),
    );
    assert_shows("the run past the branch", &run, &["diagnostics"]);
    let narrowing = executions_alike(
        fresh(NARROWING),
        &ExecuteRequest {
            stop_at_branch: true,
            ..ExecuteRequest::new(kore("wrap{}(X:SortS{})"))
        },
    );
    if cfg!(feature = "z3-inference") {
        assert_leaf_shows("the narrowing step", &narrowing, "branch", "remainder");
    } else {
        assert_leaf_shows("the narrowing step", &narrowing, "indeterminate", "cause");
    }
    let unsupported = executions_alike(
        fresh(UNSUPPORTED_HOOK),
        &ExecuteRequest::new(kore(r#"missing{}(\dv{SortState{}}("x"))"#)),
    );
    assert_leaf_shows(
        "the unsupported hook",
        &unsupported,
        "unsupported-hook",
        "cause",
    );
    assert_shows("the unsupported hook", &unsupported, &["unsupportedHooks"]);

    let diagnostics = fresh(include_str!("fixtures/search-diagnostics.kore"));
    let search = searches_alike(
        &diagnostics,
        &SearchRequest {
            max_simplification_iterations: 3,
            ..SearchRequest::new(kore("start{}()"))
        },
    );
    assert_shows("the search", &search, &["diagnostics"]);
    let pattern = pattern_searches_alike(
        &diagnostics,
        &SearchPatternRequest {
            max_simplification_iterations: 3,
            ..SearchPatternRequest::new(
                kore("start{}()"),
                kore(
                    r#"\and{SortS{}}(X:SortS{}, \equals{SortS{}, SortS{}}(check{}(X:SortS{}), ok{}()))"#,
                ),
            )
        },
    );
    assert_shows("the pattern search", &pattern, &["diagnostics", "matches"]);
}

/// `prove_kore` serializes as the JSON text `prove_json` writes: a refuted proof's stuck leaf and
/// the leaves at its depth bound, each with its state.
/// A stop rule stops a run only as its state's one successor (docs/compatibility.md, "Passed
/// stops"). In `REFUTED_CLAIM`, `start` has two successors, `stuck` by `to-stuck` and `count(0)` by
/// `to-count`, so a terminal `to-stuck` stops nothing there and is listed at depth 0; `count` is
/// its state's one successor from `count(0)`, so it stops that path at depth 2 and is not listed.
/// Both facade routes write the list as `passedStops: [{rule, depth}]`, and a run without stop
/// rules writes none.
#[test]
fn passed_stops_reach_the_facade_alike() {
    let request = ExecuteRequest {
        terminal_rules: vec!["to-stuck".into(), "count".into()],
        ..ExecuteRequest::new(kore("start{}()"))
    };
    let mut backend = fresh(REFUTED_CLAIM)();
    let result = backend.execute_kore(request.clone()).unwrap();
    assert_eq!(
        result.passed_stops,
        [PassedStopOutput {
            rule: "to-stuck".into(),
            depth: 0,
        }],
        "{result:#?}"
    );
    let results = executions_alike(fresh(REFUTED_CLAIM), &request);
    for value in &results {
        assert_eq!(
            value["passedStops"],
            serde_json::json!([{ "rule": "to-stuck", "depth": 0 }]),
            "{value}"
        );
        let leaves = value["leaves"]
            .as_array()
            .unwrap()
            .iter()
            .map(|leaf| (leaf["reason"].clone(), leaf["depth"].clone()))
            .collect::<Vec<_>>();
        assert!(
            leaves.contains(&(serde_json::json!("terminal"), serde_json::json!(2))),
            "{value}"
        );
    }
    let free = executions_alike(
        fresh(REFUTED_CLAIM),
        &ExecuteRequest {
            max_depth: Some(3),
            ..ExecuteRequest::new(kore("start{}()"))
        },
    );
    assert!(!shows(&free, "passedStops"), "{free:?}");
}

#[test]
fn proofs_serialize_alike() {
    let fresh = fresh(REFUTED_CLAIM);
    let request = ProveRequest {
        max_depth: Some(3),
        max_counterexamples: 2,
        ..ProveRequest::default()
    };
    let expected = fresh().prove_json(request.clone()).unwrap();
    let actual = fresh().prove_kore(request).unwrap();
    assert_eq!(serde_json::to_string(&actual).unwrap(), expected);
    let states = actual
        .leaves
        .iter()
        .map(|leaf| leaf.state.to_string())
        .collect::<Vec<_>>();
    assert!(
        states.iter().any(|state| state.contains("stuck{}()"))
            && states.iter().any(|state| state.contains("count{}(")),
        "{states:?}"
    );
}
