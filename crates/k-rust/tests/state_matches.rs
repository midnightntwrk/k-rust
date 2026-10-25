//! State matches and committed transitions through the facade (docs/compatibility.md, "State
//! matches", "Committed transitions"): an execute request that sets `match_states` receives a
//! summary of the verdicts of every state the run reached against a pattern, and one that sets
//! `collect_committed` beside `collect_coverage` receives the rewrite rules whose successor the
//! run committed to. Neither changes any other field of the result.

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionResult, ResultModalityOutput,
        SearchPatternRequest, SearchTypeArg, StateMatchOutput, StateMatchRequest,
        StateMatchesOutput, UndecidedMatchReasonOutput,
    },
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{json, parser::parse_pattern},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

#[path = "support/shared.rs"]
mod shared;

const SOURCE: &str = include_str!("fixtures/state-matches/match.k");

/// The KORE of `SOURCE`, compiled once per process.
fn definition_kore() -> std::sync::Arc<String> {
    static KORE: shared::Shared<String> = shared::Shared::new();
    KORE.get(|| {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("match.k", SOURCE),
            "MATCH",
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .unwrap();
        compile_loaded_definition(&loaded, CompileOptions::default())
            .unwrap()
            .definition_kore
    })
}

fn backend() -> Backend {
    Backend::new(&definition_kore(), "MATCH", BackendOptions::default()).unwrap()
}

fn int(value: i64) -> String {
    format!("\\dv{{SortInt{{}}}}(\"{value}\")")
}

/// The initial configuration of `program` (`go(5)` is `("go", 5)`).
fn initial(program: (&str, i64)) -> String {
    let (head, argument) = program;
    format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortPgm{{}}, SortKItem{{}}}}(Lbl{head}{{}}({})), dotk{{}}())), Lbl'-LT-'out'-GT-'{{}}({}), Lbl'-LT-'generatedCounter'-GT-'{{}}({}))",
        int(argument),
        int(0),
        int(0)
    )
}

/// A configuration pattern: `k` in the `<k>` cell, `out` in `<out>`, any counter.
fn top(k: &str, out: &str) -> String {
    format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}({k}), Lbl'-LT-'out'-GT-'{{}}({out}), VarGC:SortGeneratedCounterCell{{}})"
    )
}

/// `<k> head(argument) ~> _ </k>` with any `<out>`; a `Pgm` head takes an injection.
fn head(head: &str, argument: i64, pgm: bool) -> String {
    let item = format!("Lbl{head}{{}}({})", int(argument));
    let item = if pgm {
        format!("inj{{SortPgm{{}}, SortKItem{{}}}}({item})")
    } else {
        item
    };
    top(
        &format!("kseq{{}}({item}, VarREST:SortK{{}})"),
        "VarO:SortInt{}",
    )
}

/// `<k> .K </k> <out> out </out>`.
fn done(out: i64) -> String {
    top("dotk{}()", &int(out))
}

/// `<k> .K </k> <out> O </out>` requires `O ==K keys_list(1 |-> 0 2 |-> 0)[0]`, a condition
/// whose value rests on the order in which `keys_list` lists the keys of a two-key map, which the
/// definition leaves open: k-rust lists them in execution mode, and leaves the listing
/// unevaluated in proof mode.
fn open_requires() -> String {
    let element = |key: i64| {
        format!(
            "Lbl'UndsPipe'-'-GT-Unds'{{}}(inj{{SortInt{{}}, SortKItem{{}}}}({}), inj{{SortInt{{}}, SortKItem{{}}}}({}))",
            int(key),
            int(0)
        )
    };
    format!(
        "\\and{{SortGeneratedTopCell{{}}}}({}, \\equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(Lbl'UndsEqlsEqls'K'Unds'{{}}(kseq{{}}(inj{{SortInt{{}}, SortKItem{{}}}}(VarO:SortInt{{}}), dotk{{}}()), kseq{{}}(LblList'Coln'get{{}}(Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map{{}}(Lbl'Unds'Map'Unds'{{}}({}, {})), {}), dotk{{}}())), \\dv{{SortBool{{}}}}(\"true\")))",
        top("dotk{}()", "VarO:SortInt{}"),
        element(1),
        element(2),
        int(0)
    )
}

fn request(program: (&str, i64), modality: ResultModalityOutput) -> ExecuteRequest {
    ExecuteRequest {
        result_modality: modality,
        max_depth: Some(50),
        ..ExecuteRequest::new(parse_pattern(&initial(program)).unwrap())
    }
}

fn matching(
    program: (&str, i64),
    modality: ResultModalityOutput,
    pattern: &str,
    proof_agreement: bool,
) -> ExecuteRequest {
    ExecuteRequest {
        match_states: Some(StateMatchRequest {
            pattern: parse_pattern(pattern).unwrap(),
            proof_agreement,
        }),
        ..request(program, modality)
    }
}

fn matches(result: &ExecutionResult) -> &StateMatchesOutput {
    result
        .state_matches
        .as_ref()
        .expect("the request matched states")
}

fn diagnostic_kinds(found: &StateMatchOutput) -> Vec<String> {
    found
        .diagnostics
        .iter()
        .map(|diagnostic| serde_json::to_value(diagnostic).unwrap()["kind"].to_string())
        .collect()
}

const PROGRAMS: [(&str, i64); 7] = [
    ("go", 5),
    ("mark", 5),
    ("pick", 0),
    ("pick", 1),
    ("undef", 0),
    ("loop", 3),
    ("loop", 0),
];

fn patterns() -> Vec<String> {
    vec![
        head("go", 5, true),
        head("c", 5, false),
        head("b", 5, false),
        head("f", 5, false),
        head("undef", 0, true),
        head("loop", 1, true),
        head("loop", 7, true),
        done(5),
        done(0),
        done(7),
    ]
}

const MODALITIES: [ResultModalityOutput; 2] = [
    ResultModalityOutput::StateSet,
    ResultModalityOutput::PathSet,
];

/// A `state-set` run matches each distinct state once: on `go(5)` it reaches four distinct
/// states (`go(5)`, `b(5)`, the end, `c(5)`) and merges the second arrival at the end; the
/// `path-set` run matches that end twice. A pattern nothing matches is refuted everywhere.
#[test]
fn a_state_set_run_matches_each_distinct_state_once() {
    let mut backend = backend();
    for (modality, expected) in [
        (ResultModalityOutput::StateSet, 4),
        (ResultModalityOutput::PathSet, 5),
    ] {
        let result = backend
            .execute(matching(("go", 5), modality, &head("c", 6, false), false))
            .unwrap();
        let found = matches(&result);
        assert_eq!(
            (found.matched, found.refuted),
            (expected, expected),
            "{modality:?}"
        );
        assert!(found.first_clean_reach.is_none() && found.first_dirty_reach.is_none());
        assert!(found.undecided.is_empty());
    }
    // A pattern of the end reaches it at depth 2, on a clean prefix, and matching stops there.
    let result = backend
        .execute(matching(
            ("go", 5),
            ResultModalityOutput::StateSet,
            &done(5),
            false,
        ))
        .unwrap();
    let reach = matches(&result).first_clean_reach.as_ref().unwrap();
    assert_eq!(reach.depth, 2);
    assert!(reach.diagnostics.is_empty());
    assert_eq!(matches(&result).matched, 3);
}

/// Whether some state of the run reaches `pattern` agrees with `search_pattern` over every
/// reachable state (`--search-all`): a search match with empty constraints exists exactly when
/// the state matches report a reach (clean or not), on every program and pattern of the
/// fixture, in both modalities; and a clean reach's state is one of the search's matched states.
/// The fixture's states are ground and ceil-free, so the verdicts' extra conditions (decided,
/// ceil-free) hold of every search match.
#[test]
fn state_matches_agree_with_search_pattern() {
    let mut backend = backend();
    for program in PROGRAMS {
        for pattern in patterns() {
            let search = backend
                .search_pattern(SearchPatternRequest {
                    search_type: SearchTypeArg::All,
                    max_depth: Some(50),
                    ..SearchPatternRequest::new(
                        parse_pattern(&initial(program)).unwrap(),
                        parse_pattern(&pattern).unwrap(),
                    )
                })
                .unwrap();
            let searched: Vec<String> = search
                .matches
                .iter()
                .filter(|found| found.constraints.is_empty())
                .map(|found| found.state.state.to_string())
                .collect();
            for modality in MODALITIES {
                let result = backend
                    .execute(matching(program, modality, &pattern, true))
                    .unwrap();
                let found = matches(&result);
                let reached =
                    found.first_clean_reach.is_some() || found.first_dirty_reach.is_some();
                assert_eq!(
                    reached,
                    !searched.is_empty(),
                    "{program:?} {modality:?} {pattern}: {found:?}"
                );
                assert!(found.undecided.is_empty(), "{program:?} {pattern}");
                if let Some(reach) = &found.first_clean_reach {
                    assert!(
                        searched.contains(&reach.state.to_string()),
                        "{program:?} {modality:?} {pattern}: {} is no searched state",
                        reach.state
                    );
                }
            }
        }
    }
}

/// Matching states and collecting committed transitions change no other field of the result:
/// the JSON text with both options, without `stateMatches` and `coverage.committed`, is the text
/// without them, on every program, in both modalities, with and without a work budget.
#[test]
fn matching_and_committed_change_no_other_field() {
    let mut backend = backend();
    for program in PROGRAMS {
        for modality in MODALITIES {
            for max_work in [None, Some(3)] {
                let plain = ExecuteRequest {
                    collect_coverage: true,
                    max_work,
                    ..request(program, modality)
                };
                let without: serde_json::Value =
                    serde_json::from_str(&backend.execute_json(plain.clone()).unwrap()).unwrap();
                for pattern in [done(5), head("loop", 1, true), open_requires()] {
                    let with = ExecuteRequest {
                        collect_committed: true,
                        match_states: Some(StateMatchRequest {
                            pattern: parse_pattern(&pattern).unwrap(),
                            proof_agreement: true,
                        }),
                        ..plain.clone()
                    };
                    let mut with: serde_json::Value =
                        serde_json::from_str(&backend.execute_json(with).unwrap()).unwrap();
                    assert!(with["stateMatches"].is_object());
                    assert!(with["coverage"]["committed"].is_array());
                    with.as_object_mut().unwrap().remove("stateMatches");
                    with["coverage"]
                        .as_object_mut()
                        .unwrap()
                        .remove("committed");
                    assert_eq!(with, without, "{program:?} {modality:?} {max_work:?}");
                }
                assert!(without.get("stateMatches").is_none());
                assert!(without["coverage"].get("committed").is_none());
            }
        }
    }
}

/// A clean arrival merged into a recorded reaching state whose prefix read an
/// implementation-chosen value is reported as the first clean reach, with its own prefix: on
/// `mark(5)` the `me`/`ed` branch, met first, reads one, and the `mf`/`fd` branch reaches the
/// same end at the same depth without one. Both modalities find the clean reach; the `state-set`
/// run finds it only through the merge.
#[test]
fn a_cleaner_merged_arrival_is_reported_as_the_clean_reach() {
    let mut backend = backend();
    for modality in MODALITIES {
        let result = backend
            .execute(matching(("mark", 5), modality, &done(5), false))
            .unwrap();
        let found = matches(&result);
        let dirty = found.first_dirty_reach.as_ref().expect("a dirty reach");
        assert_eq!(dirty.depth, 2);
        assert!(
            diagnostic_kinds(dirty).contains(&"\"implementation-chosen-value\"".to_owned()),
            "{dirty:?}"
        );
        let clean = found
            .first_clean_reach
            .as_ref()
            .unwrap_or_else(|| panic!("{modality:?}: no clean reach: {found:?}"));
        assert_eq!(clean.depth, 2);
        assert!(clean.diagnostics.is_empty(), "{clean:?}");
        assert_eq!(clean.state, dirty.state);
    }
}

/// A state whose verdict rests on a value the definition leaves to the implementation is
/// refuted in execution mode alone, and undecided under proof agreement, never refuted: the end
/// of `go(5)` against a `requires` that reads `keys_list` of a two-key map.
#[test]
fn a_verdict_only_execution_mode_gives_is_undecided_under_proof_agreement() {
    let mut backend = backend();
    let execution_only = backend
        .execute(matching(
            ("go", 5),
            ResultModalityOutput::StateSet,
            &open_requires(),
            false,
        ))
        .unwrap();
    let found = matches(&execution_only);
    assert_eq!((found.matched, found.refuted), (4, 4), "{found:?}");
    let agreed = backend
        .execute(matching(
            ("go", 5),
            ResultModalityOutput::StateSet,
            &open_requires(),
            true,
        ))
        .unwrap();
    let found = matches(&agreed);
    let undecided = found
        .undecided
        .iter()
        .find(|entry| entry.reason == UndecidedMatchReasonOutput::UndecidedMatch)
        .unwrap_or_else(|| panic!("no undecided match: {found:?}"));
    assert_eq!(undecided.first.depth, 2);
    assert_eq!(found.refuted + undecided.count, found.matched);
    assert!(found.first_clean_reach.is_none() && found.first_dirty_reach.is_none());
}

/// The configuration an undefined step is taken from is matched when it is reached, decided:
/// `undef(0)`'s only step divides by zero, its leaf is `trivial`, and its initial configuration
/// reaches a pattern of itself at depth 0. The undefined leaf itself is not matched.
#[test]
fn the_configuration_of_an_undefined_step_is_matched_decided() {
    let mut backend = backend();
    for modality in MODALITIES {
        let result = backend
            .execute(matching(
                ("undef", 0),
                modality,
                &head("undef", 0, true),
                false,
            ))
            .unwrap();
        assert_eq!(result.leaves.len(), 1);
        assert_eq!(
            serde_json::to_value(result.leaves[0].reason).unwrap(),
            "trivial"
        );
        let found = matches(&result);
        let reach = found.first_clean_reach.as_ref().expect("a clean reach");
        assert_eq!(reach.depth, 0);
        assert_eq!(found.matched, 1);
    }
}

/// `committed` holds the rules whose successor the run committed to: on `pick(0)` `bad`'s
/// successor divides by zero and is rolled back, so `bad` is in `applied` and not in
/// `committed`; on `go(5)` under `state-set` the `cd` successor is merged into the `bd` one, and
/// `cd` is committed. Without `collect_committed` there is no list, and asking without
/// `collect_coverage` is refused.
#[test]
fn committed_leaves_out_rolled_back_candidates_and_keeps_merged_ones() {
    let mut backend = backend();
    let catalog: Vec<(String, String)> = backend
        .rule_catalog(None)
        .unwrap()
        .into_iter()
        .filter_map(|rule| rule.label.map(|label| (label, rule.id)))
        .collect();
    let id = |label: &str| {
        catalog
            .iter()
            .find(|(name, _)| *name == format!("MATCH.{label}"))
            .unwrap_or_else(|| panic!("no rule {label}"))
            .1
            .clone()
    };
    let coverage = |backend: &mut Backend, program, modality| {
        backend
            .execute(ExecuteRequest {
                collect_coverage: true,
                collect_committed: true,
                ..request(program, modality)
            })
            .unwrap()
            .coverage
            .unwrap()
    };
    for modality in MODALITIES {
        let picked = coverage(&mut backend, ("pick", 0), modality);
        let committed = picked.committed.as_ref().unwrap();
        assert!(picked.applied.contains(&id("bad")), "{picked:?}");
        assert!(!committed.contains(&id("bad")), "{picked:?}");
        assert!(committed.contains(&id("good")), "{picked:?}");
        assert!(committed.iter().all(|entry| picked.applied.contains(entry)));
        let went = coverage(&mut backend, ("go", 5), modality);
        for label in ["ab", "ac", "bd", "cd"] {
            assert!(
                went.committed.as_ref().unwrap().contains(&id(label)),
                "{modality:?} {label}: {went:?}"
            );
        }
    }
    let plain = backend
        .execute(ExecuteRequest {
            collect_coverage: true,
            ..request(("go", 5), ResultModalityOutput::StateSet)
        })
        .unwrap();
    assert!(plain.coverage.unwrap().committed.is_none());
    let refused = backend
        .execute(ExecuteRequest {
            collect_committed: true,
            ..request(("go", 5), ResultModalityOutput::StateSet)
        })
        .unwrap_err();
    assert!(
        refused
            .to_string()
            .contains("collectCommitted requires collectCoverage")
    );
}

/// The wire spellings: `matchStates` with `proofAgreement`, and `collectCommitted`, are read,
/// and the result writes `stateMatches` and `coverage.committed`.
#[test]
fn the_wire_spells_the_options_in_camel_case() {
    let state = json::to_string(&parse_pattern(&initial(("go", 5))).unwrap()).unwrap();
    let pattern = json::to_string(&parse_pattern(&done(5)).unwrap()).unwrap();
    let text = format!(
        r#"{{"state":{state},"collectCoverage":true,"collectCommitted":true,"matchStates":{{"pattern":{pattern},"proofAgreement":true}}}}"#
    );
    let request: ExecuteRequest = serde_json::from_str(&text).unwrap();
    assert!(request.collect_committed);
    assert!(request.match_states.as_ref().unwrap().proof_agreement);
    let output: serde_json::Value =
        serde_json::from_str(&backend().execute_json(request).unwrap()).unwrap();
    assert_eq!(output["stateMatches"]["firstCleanReach"]["depth"], 2);
    assert_eq!(output["stateMatches"]["matched"], 3);
    assert!(output["coverage"]["committed"].is_array());
}
