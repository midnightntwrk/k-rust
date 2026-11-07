//! Report usability (flow F-13, README 6.4): named oracle slots, timings, leaf censuses in the
//! causes of stopped runs, no second run for a baseline this command saw stop on time, and the
//! rules no mutation targets.
//!
//! The soundness conditions pinned here: no timing or census value enters an evidence row, a
//! digest, a key or a lock (two cold runs give equal digests, keys and outcome records);
//! a timeout program is classified from this command's one live run, never comparable; and the
//! order of the programs in `FLOW.toml` changes which killer is found first and the cost, never a
//! status (every fixture list gives the same statuses with its programs in either order, warm
//! and cold).

mod flow_support;

use kink_campaign::{FinalResult, OracleOutcome, OracleSide, OracleValue, SideRun};
use kink_flow::{
    FlowManifest, MutationList,
    cli::{EXIT_UNASKED, results, results_status},
    outcomes::OUTCOMES_DIRECTORY,
    report::{KORE_CAP, slots_value},
    results::{CACHE_DIRECTORY, ResultsOptions},
    search::{REPORT_FILE, RunOptions, run},
};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

fn flow(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/flow")
        .join(name)
}

/// A fresh directory for one test, under the target's temporary directory.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-usability-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if name == CACHE_DIRECTORY {
            continue;
        }
        if entry.file_type().unwrap().is_dir() {
            copy_dir(&entry.path(), &to.join(&name));
        } else {
            fs::copy(entry.path(), to.join(&name)).unwrap();
        }
    }
}

/// A private copy of a testdata/flow fixture.
fn fixture(name: &str, test: &str) -> PathBuf {
    let dir = scratch(test).join(name);
    copy_dir(&flow(name), &dir);
    dir
}

fn search(manifest: &Path, mutations: &Path) -> Value {
    let flow = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    let (document, ok) = run(
        &flow,
        &list,
        &RunOptions {
            only: Vec::new(),
            cache: None,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
            schedule: kink_campaign::ScheduleMode::FirstKill,
            lock: None,
            locked: false,
        },
    );
    assert!(ok, "{document:#}");
    document
}

fn results_document(manifest: &Path, mutations: Option<PathBuf>) -> Value {
    let (document, code) = results(
        manifest,
        &ResultsOptions {
            verify: false,
            cache: None,
            mutations,
        },
    );
    // The command is asked and fails nothing its document does not show; which answer its
    // programs have (an `unknown` baseline is no answer, and which programs are unknown depends on
    // the profile) is each test's to pin.
    assert_ne!(code, EXIT_UNASKED, "{document:#}");
    assert_eq!(code, results_status(&document), "{document:#}");
    document
}

fn mutation<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["id"] == id)
        .unwrap_or_else(|| panic!("no mutation {id}"))
}

fn entry<'d>(document: &'d Value, id: &str, program: &str) -> &'d Value {
    mutation(document, id)["executed"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["program"] == program)
        .unwrap_or_else(|| panic!("{id} did not run {program}"))
}

fn cache_of(manifest: &Path) -> PathBuf {
    manifest.parent().unwrap().join(CACHE_DIRECTORY)
}

fn read_json(path: &Path) -> Value {
    serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap()
}

/// Every file under `dir`, by path relative to it, with its contents.
fn files(dir: &Path) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(next) = stack.pop() {
        let Ok(entries) = fs::read_dir(&next) else {
            continue;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else {
                let relative = path
                    .strip_prefix(dir)
                    .unwrap()
                    .to_string_lossy()
                    .into_owned();
                out.insert(relative, fs::read_to_string(&path).unwrap());
            }
        }
    }
    out
}

/// `(id, status)` of every mutation row.
fn statuses(document: &Value) -> Vec<(String, String)> {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|m| {
            (
                m["id"].as_str().unwrap().to_owned(),
                m["status"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

/// The document with every timing value removed (`wall_ms`, `baseline_ms`, `call_wall_ms`).
fn without_timings(value: &Value) -> Value {
    match value {
        Value::Object(map) => Value::Object(
            map.iter()
                .filter(|(key, _)| {
                    !matches!(key.as_str(), "wall_ms" | "baseline_ms" | "call_wall_ms")
                })
                .map(|(key, value)| (key.clone(), without_timings(value)))
                .collect(),
        ),
        Value::Array(items) => Value::Array(items.iter().map(without_timings).collect()),
        other => other.clone(),
    }
}

#[test]
fn final_configurations_are_capped_at_4000_characters() {
    let term = |value: String| k_rust::kore::ast::Pattern::DomainValue {
        sort: k_rust::kompile::initial_configuration::kore_sort("SortString"),
        value: value.into(),
    };
    let whole = |terms: Vec<k_rust::kore::ast::Pattern>| SideRun::Sides {
        sides: vec![
            OracleSide::Unknown,
            OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(
                terms.into_iter().collect(),
            ))),
        ],
    };
    let baseline = whole(vec![term("short".into())]);
    let mutant = whole(vec![term("x".repeat(KORE_CAP + 10)), term("y".into())]);
    let outcomes = [OracleOutcome::Agree, OracleOutcome::Distinguish];
    let killer = slots_value(
        &kink_flow::results::ORACLE_SLOTS,
        &outcomes,
        Some(&baseline),
        Some(&mutant),
        true,
        &Value::Null,
    );
    let sides = &killer["whole-term"]["sides"];
    assert_eq!(sides["baseline"], json!({"final_configurations": 1}));
    assert_eq!(sides["mutant"]["final_configurations"], 2);
    let kore = sides["mutant"]["kore"].as_array().unwrap();
    let long = kore
        .iter()
        .find(|k| k["truncated"] == true)
        .expect("the long term is cut");
    assert_eq!(long["text"].as_str().unwrap().chars().count(), KORE_CAP);
    let short = kore.iter().find(|k| k["truncated"] == false).unwrap();
    assert!(short["text"].as_str().unwrap().contains("\"y\""));
    // Only the killing program's entry carries the text.
    let other = slots_value(
        &kink_flow::results::ORACLE_SLOTS,
        &outcomes,
        Some(&baseline),
        Some(&mutant),
        false,
        &Value::Null,
    );
    assert_eq!(
        other["whole-term"]["sides"]["mutant"],
        json!({"final_configurations": 2})
    );
}

/// `the run did not finish ...; when the bound fired k-rust returned N leaves (...), the
/// deepest at depth D; those leaves had applied R of the T rules a run can observe`, or the
/// no-leaf form.
fn assert_census_cause(cause: &str, prefix: &str, rules: Option<(usize, usize)>) {
    assert!(cause.starts_with(prefix), "{cause}");
    let rest = &cause[prefix.len()..];
    // A baseline's timeout cause ends with why it is not cached (and how to bound it by work).
    let rest = rest
        .strip_suffix(kink_flow::results::TIMEOUT_BOUND_BY_WORK)
        .unwrap_or(rest);
    let rest = rest
        .strip_suffix(kink_flow::results::TIMEOUT_NOT_CACHED)
        .unwrap_or(rest);
    if rest.starts_with("k-rust returned no leaves") {
        return;
    }
    assert!(rest.starts_with("k-rust returned "), "{cause}");
    assert!(rest.contains(", the deepest at depth "), "{cause}");
    if let Some((reached, total)) = rules {
        assert!(
            rest.ends_with(&format!(
                "; those leaves had applied {reached} of the {total} rules a run can observe"
            )),
            "{cause}"
        );
    }
}

/// Every tier-1 record of a cache, by (context digest, mutation identity, program digest), as
/// its JSON text.
fn outcome_records(cache: &Path) -> BTreeMap<(String, String, String), String> {
    let mut out = BTreeMap::new();
    for text in files(&cache.join(OUTCOMES_DIRECTORY)).values() {
        let file: Value = serde_json::from_str(text).unwrap();
        let context = file["context_sha256"].as_str().unwrap();
        let identity = file["mutation_identity"].as_str().unwrap();
        for (program, record) in file["records"].as_object().unwrap() {
            out.insert(
                (context.to_owned(), identity.to_owned(), program.clone()),
                serde_json::to_string(record).unwrap(),
            );
        }
    }
    out
}

/// The undecided solver answers of a run document, k-rust's in a run (`smt_unknowns`) and kink's
/// in its judgement of the run (`decider_smt_unknowns`): its programs' baseline runs (every
/// program row carries both counts) and every executed entry of a live mutant run (an entry
/// carries each only when it is not zero).
fn undecided_answers(document: &Value) -> u64 {
    const COUNTS: [&str; 2] = ["smt_unknowns", "decider_smt_unknowns"];
    let programs = document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|row| {
            COUNTS.map(|count| {
                row[count]
                    .as_u64()
                    .unwrap_or_else(|| panic!("a program row's {count}"))
            })
        });
    let entries = document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|row| row["executed"].as_array().into_iter().flatten())
        .flat_map(|entry| COUNTS.map(|count| entry[count].as_u64().unwrap_or(0)));
    programs.chain(entries).sum()
}

/// The statuses of every mutation of a fixture list are the same with the programs of
/// `FLOW.toml` in corpus order and in reverse order, on the corpus-order run's result records
/// (outcomes forgotten) and cold (stop rule 1 of F-13: the order-independence premise of README
/// 6.4). Only the killers and the costs may differ.
///
/// F-13 review 1 minor 1 (flow F-16): the SET of tier-1 records a first-kill run writes depends
/// on the order (the programs after the first kill get none), but no record's content does: every
/// record a reversed run writes is byte-equal to the corpus-order run's record of the same
/// (mutation, program) when that run wrote one. Returns the documents and the number of such
/// shared records.
fn statuses_do_not_depend_on_the_order(
    name: &str,
    manifest: &str,
    mutations: &str,
) -> ([Value; 3], usize) {
    let slug = format!("{}-{manifest}-{mutations}", name.replace('/', "-"));
    // The corpus-order run is the cold run shared with the other tests of this binary
    // (`flow_support::after_cold`: `search` in corpus order).
    let corpus = scratch(&format!("order-corpus-{slug}")).join(name);
    let by_corpus = flow_support::after_cold(name, manifest, mutations, &corpus);
    let flow = corpus.join(manifest);
    let list = corpus.join(mutations);

    // The same result records with the programs reversed; outcomes and report forgotten.
    flow_support::reverse_programs(&flow);
    let cache = cache_of(&flow);
    let corpus_records = outcome_records(&cache);
    let _ = fs::remove_dir_all(cache.join(OUTCOMES_DIRECTORY));
    let _ = fs::remove_file(cache.join(REPORT_FILE));
    let reversed = search(&flow, &list);
    let programs = reversed["programs"].as_array().unwrap();
    assert_eq!(
        programs.iter().filter(|p| p["cached"] == false).count(),
        0,
        "reversing the programs keeps every record in use"
    );

    let measured = fixture(name, &format!("order-reversed-cold-{slug}"));
    flow_support::reverse_programs(&measured.join(manifest));
    let cold_reversed = search(&measured.join(manifest), &measured.join(mutations));

    assert_eq!(statuses(&reversed), statuses(&by_corpus), "{name} reversed");
    assert_eq!(
        statuses(&cold_reversed),
        statuses(&by_corpus),
        "{name} reversed cold"
    );
    // Under Z3 every solver query is resource-bounded, so an answer, decided or not, does not
    // depend on what a backend reused in search order asked before (src/search.rs, README `run`
    // step 3), and the statuses cannot depend on the order whatever the counts. Both counts are
    // reported, and no run of these fixtures takes an undecided answer, k-rust's or kink's.
    if cfg!(feature = "z3") {
        for document in [&by_corpus, &reversed, &cold_reversed] {
            assert_eq!(
                undecided_answers(document),
                0,
                "{name}: an undecided solver answer"
            );
        }
    }
    let mut shared = 0;
    for (label, records) in [
        ("reversed", outcome_records(&cache)),
        (
            "reversed cold",
            outcome_records(&cache_of(&measured.join(manifest))),
        ),
    ] {
        for (key, text) in &records {
            if let Some(corpus) = corpus_records.get(key) {
                assert_eq!(text, corpus, "{name} {label}: {key:?}");
                shared += 1;
            }
        }
    }
    // Each killer is a program that kills (a Distinguish of its own entry).
    for document in [&by_corpus, &reversed, &cold_reversed] {
        for row in document["mutations"].as_array().unwrap() {
            if let Some(killer) = row["killer"].as_str() {
                assert_eq!(
                    entry(document, row["id"].as_str().unwrap(), killer)["outcome"],
                    "distinguish"
                );
            }
        }
    }
    ([by_corpus, reversed, cold_reversed], shared)
}

mod heavy {
    use super::*;

    #[test]
    #[ignore = "heavy"]
    fn collection_statuses_do_not_depend_on_the_order() {
        for name in [
            "collections/cellmap",
            "collections/collenv",
            "collections/collimp",
            "collections/collstore",
        ] {
            statuses_do_not_depend_on_the_order(name, "FLOW.toml", "MUTATIONS.toml");
        }
    }

    #[test]
    #[ignore = "heavy"]
    fn register_statuses_do_not_depend_on_the_order() {
        statuses_do_not_depend_on_the_order("register", "FLOW.toml", "MUTATIONS.toml");
    }

    #[test]
    #[ignore = "heavy"]
    fn markdown_statuses_do_not_depend_on_the_order() {
        statuses_do_not_depend_on_the_order("markdown", "FLOW.toml", "MUTATIONS.toml");
    }

    #[test]
    #[ignore = "heavy"]
    fn twin_statuses_do_not_depend_on_the_order() {
        statuses_do_not_depend_on_the_order("twin", "FLOW.toml", "MUTATIONS.toml");
    }

    #[test]
    #[ignore = "heavy"]
    fn divide_statuses_do_not_depend_on_the_order() {
        statuses_do_not_depend_on_the_order("divide", "FLOW.toml", "MUTATIONS.toml");
    }

    #[test]
    #[ignore = "heavy"]
    fn map_store_statuses_do_not_depend_on_the_order() {
        statuses_do_not_depend_on_the_order("map-store", "FLOW.toml", "MUTATIONS.toml");
    }
}

mod kink_tier {
    use super::*;

    #[test]
    #[ignore = "kink"]
    fn calc_statuses_do_not_depend_on_the_order() {
        let ([by_corpus, reversed, _], shared) =
            statuses_do_not_depend_on_the_order("calc", "FLOW.toml", "MUTATIONS.toml");
        assert!(shared > 0, "the byte-equality check compared records");
        // The reversed manifest did reorder the search: inside each tier the survivor ran its
        // programs in reverse corpus order (corpus order: add, nested, sub, inline; add, nested
        // and inline reach the add rule).
        assert_eq!(
            mutation(&by_corpus, "add-swaps-operands")["calls"],
            json!([{"programs": ["add", "nested", "inline", "sub"], "status": "survived"}])
        );
        assert_eq!(
            mutation(&reversed, "add-swaps-operands")["calls"],
            json!([{"programs": ["inline", "nested", "add", "sub"], "status": "survived"}])
        );
    }

    #[test]
    #[ignore = "kink"]
    fn calc_status_list_statuses_do_not_depend_on_the_order() {
        statuses_do_not_depend_on_the_order("calc", "FLOW.toml", "MUTATIONS-statuses.toml");
    }

    #[test]
    #[ignore = "kink"]
    fn loop_timeout_statuses_do_not_depend_on_the_order() {
        statuses_do_not_depend_on_the_order("loop", "FLOW-search.toml", "MUTATIONS.toml");
    }

    #[test]
    #[ignore = "kink"]
    fn loop_depth_statuses_do_not_depend_on_the_order() {
        statuses_do_not_depend_on_the_order("loop", "FLOW-depth.toml", "MUTATIONS.toml");
    }

    #[test]
    #[ignore = "kink"]
    fn loop_cost_statuses_do_not_depend_on_the_order() {
        statuses_do_not_depend_on_the_order("loop", "FLOW-cost.toml", "MUTATIONS-cost.toml");
    }

    #[test]
    #[ignore = "kink"]
    fn a_timeout_is_classified_from_its_one_live_run_with_its_census() {
        // spin never ends: its baseline is class timeout, from the zero-mutant campaign's own run
        // (one live run per program, no diagnostic run), and its cause carries the census.
        let dir = fixture("loop", "timeout");
        let manifest = dir.join("FLOW-timeout.toml");
        let document = results_document(&manifest, None);
        let spin = &document["programs"][0];
        assert_eq!(spin["id"], "spin");
        assert_eq!(spin["class"], "timeout");
        assert!(spin["wall_ms"].as_u64().unwrap() >= 500, "{spin:#}");
        // The loop specification has five rules a run can observe (double is an equation); a
        // stopped spin run has applied the spin rule only.
        assert_census_cause(
            spin["cause"].as_str().unwrap(),
            "the run did not finish within time_ms = 500; when the bound fired ",
            Some((1, 5)),
        );
        assert_eq!(document["programs"][1]["class"], "comparable");
        assert_eq!(
            document["baseline_runs"],
            json!({"live": 2, "reused": 0, "diagnostic": 0})
        );
        // A session record never makes a program comparable, and a timeout is no record: it
        // depends on the host's load, so it is never written and the next command runs it again.
        let directory = cache_of(&manifest).join("results").join(
            document["spec"]["execution_digest"]["digest"]
                .as_str()
                .unwrap(),
        );
        assert!(
            !directory
                .join(format!("{}.json", spin["digest"].as_str().unwrap()))
                .exists()
        );
        assert_eq!(document["result_cache"]["enabled"], true);
        assert!(
            spin["not_cached"]
                .as_str()
                .is_some_and(|reason| reason.starts_with("timeout: ")),
            "{spin:#}"
        );
        let record = directory.join(format!(
            "{}.json",
            document["programs"][1]["digest"].as_str().unwrap()
        ));
        // Test-gate TG-F: the assertions of tests/results.rs
        // `a_non_terminating_program_is_class_timeout`, which ran the same command on the same
        // files. Neither program is from the cache; countdown's record names the bounds a stored
        // class depends on (not `time_ms`); the next run reuses it and runs spin again.
        let classes = |document: &Value| {
            document["programs"]
                .as_array()
                .unwrap()
                .iter()
                .map(|p| {
                    (
                        p["id"].as_str().unwrap().to_owned(),
                        p["class"].as_str().unwrap().to_owned(),
                        p["cached"].as_bool().unwrap(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let expected = |cached: bool| {
            vec![
                ("spin".to_owned(), "timeout".to_owned(), cached),
                ("countdown".to_owned(), "comparable".to_owned(), cached),
            ]
        };
        assert_eq!(classes(&document), expected(false));
        let record = read_json(&record);
        assert_eq!(record["class"], "comparable");
        assert!(record["key"]["budget"].get("time_ms").is_none());
        assert_eq!(record["key"]["budget"]["max_depth"], 1_000_000_000_u64);
        assert_eq!(
            classes(&results_document(&manifest, None)),
            vec![
                ("spin".to_owned(), "timeout".to_owned(), false),
                ("countdown".to_owned(), "comparable".to_owned(), true),
            ]
        );

        // An unknown baseline keeps its diagnostic run. Since kink27 R5-BYTES-ENDS a Bytes-keyed
        // map is comparable, so the unknown baseline is an overloaded list holding `opaque(1)`, a
        // total function's application no equation reduces (tests/results.rs
        // `an_overloaded_list_names_the_application_inside_it`).
        let dir = scratch("diagnostic");
        fs::write(
            dir.join("ovf.k"),
            r#"module OVF-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Exp  ::= Int | Id | opaque(Int) [function, total]
  syntax Ids  ::= List{Id,","}  [overload(Exps)]
  syntax Exps ::= List{Exp,","} [overload(Exps)]
  syntax Exps ::= Ids
  syntax Pgm  ::= "h" "(" Exps ")"
endmodule
module OVF
  imports OVF-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> h(Es) => .K </k> <s> _ => Es </s>
  rule opaque(0) => 0
endmodule
"#,
        )
        .unwrap();
        let opaque = dir.join("FLOW.toml");
        fs::write(
            &opaque,
            r#"[spec]
entry = "ovf.k"
main_module = "OVF"
syntax_module = "OVF-SYNTAX"
[[program]]
id = "opaque"
text = 'h(opaque(1), 2)'
"#,
        )
        .unwrap();
        let document = results_document(&opaque, None);
        assert_eq!(document["programs"][0]["class"], "unknown");
        assert_eq!(
            document["baseline_runs"],
            json!({"live": 1, "reused": 0, "diagnostic": 1})
        );
    }

    #[test]
    #[ignore = "kink"]
    fn an_exit_stop_kill_names_its_slot_and_both_sides() {
        // F-09's divzero, in small: the mutant's rule applies to 1 / 0 with an undefined result
        // where the baseline is stuck. An undefined step is no end (kink27 R1-UNDEF), so the mutant
        // has no end where the baseline has one (`normal` under the flow's all-normal classifier):
        // the exit stop distinguishes `["normal"]` from `[]`, and the whole final configuration 1
        // from 0. Before the ticket the exit stop read the mutant's class `undefined-step`, and the
        // whole term read the mutant's pre-step configuration, the baseline's stuck one, and agreed.
        let dir = fixture("divide", "exit-stop");
        let manifest = dir.join("FLOW.toml");
        let document = search(&manifest, &dir.join("MUTATIONS.toml"));
        let row = mutation(&document, "guard-dropped");
        assert_eq!(row["status"], "killed");
        assert_eq!(row["killer"], "by-zero");
        // Re-pin R0c-fix-3: version 5 adds each row's `inconsistent_pairs`; re-pin L2-2-fix-1:
        // version 6 adds each row's `typing_diagnostics`; packet CACHE-ID: version 7 adds the
        // document's `kink` identity; packet CACHE-ID-fix-1: version 8 adds its `kink_build`; re-pin
        // adoption A-1: version 9 adds `specification_diagnostics` and `smt_unknowns`; fz26
        // KINK-BASELINE-FINDINGS: version 10 adds `data`, a row's `findings` and `unable_to_kill`;
        // kink27 R5-WEAKENING: version 11 adds the status `unkillable` and a row's `weakening`;
        // CF-16: version 12 adds `difference` and `ends`; CF-02: version 13 adds `spec.exclusion`;
        // version 14 adds `result`, the compared cells; CF-03: version 15 adds
        // `short_circuit_readings`, the step that excluded a run; CF-23: version 16 adds
        // `schedule`, `matrix` and a row's `killed_by`; version 17 reads a row's `reaching` from
        // the compiled mutant; CF-40c2: version 18 names it `witnesses` and the status `invalid`
        // `not-admitted`; version 19 witnesses a rewrite rule edit that is not confined to its
        // right-hand side or ensures by `matched`; CF-21-U3: version 20 adds `stop`; CF-24f:
        // version 21 names each `difference`'s format; version 22 adds named cases and a case's
        // `expectation`; CF-33: version 23 adds `decider_smt_unknowns`; CF-33d: version 24 caches an unknown with its cause;
        // U8 stage 4b: version 25 names cells inside `?` and `*` cells in `result`.
        // Version 26 reads a left-hand side's aliases and adds `witnesses_global`; version 27 names
        // an open application of a stuck end and adds the reason `open-application`.
        assert_eq!(document["version"], 31);
        assert_eq!(row["typing_diagnostics"], json!([]));
        assert_eq!(
            entry(&document, "guard-dropped", "by-zero")["slots"],
            json!({
                "exit-stop": {
                    "outcome": "distinguish",
                    "sides": {"baseline": ["normal"], "mutant": []}
                },
                "whole-term": {
                    "outcome": "distinguish",
                    "sides": {
                        "baseline": {"final_configurations": 1},
                        "mutant": {"final_configurations": 0, "kore": []}
                    }
                }
            })
        );
        assert_eq!(
            entry(&document, "guard-dropped", "quotient")["slots"],
            json!({"exit-stop": {"outcome": "agree"}, "whole-term": {"outcome": "agree"}})
        );
    }

    #[test]
    #[ignore = "kink"]
    fn a_mutants_timeout_and_depth_stop_carry_the_census() {
        let dir = fixture("loop", "mutant-census");
        let mutations = dir.join("MUTATIONS.toml");
        let document = search(&dir.join("FLOW-search.toml"), &mutations);
        let countdown = entry(&document, "countdown-escapes", "countdown");
        assert_eq!(countdown["outcome"], "timeout");
        assert!(
            countdown["wall_ms"].as_u64().unwrap() >= 500,
            "{countdown:#}"
        );
        assert_census_cause(
            countdown["cause"].as_str().unwrap(),
            "the mutant's run did not end within time_ms = 500; when the bound fired ",
            None,
        );

        fs::remove_dir_all(dir.join(CACHE_DIRECTORY)).unwrap();
        let document = search(&dir.join("FLOW-depth.toml"), &mutations);
        let countdown = entry(&document, "countdown-escapes", "countdown");
        assert_eq!(countdown["outcome"], "unknown");
        let cause = countdown["cause"].as_str().unwrap();
        assert!(
            cause.ends_with(
                "; the mutant's run: k-rust returned 1 leaf (depth-bound 1), the deepest at depth 200"
            ),
            "{cause}"
        );
    }

    #[test]
    #[ignore = "kink"]
    fn a_whole_term_kill_shows_the_mutants_final_configurations_on_the_killer_only() {
        // The cold run, shared with the other tests of this binary (`flow_support::after_cold`).
        let dir = scratch("whole-term").join("calc");
        let document = flow_support::after_cold("calc", "FLOW.toml", "MUTATIONS.toml", &dir);
        let manifest = dir.join("FLOW.toml");
        // add-becomes-sub: `1 + 2` ends in -1 on the mutant, 3 on the baseline.
        let killer = entry(&document, "add-becomes-sub", "add");
        assert_eq!(killer["outcome"], "distinguish");
        assert_eq!(killer["slots"]["exit-stop"], json!({"outcome": "agree"}));
        let whole = &killer["slots"]["whole-term"];
        assert_eq!(whole["outcome"], "distinguish");
        assert_eq!(
            whole["sides"]["baseline"],
            json!({"final_configurations": 1})
        );
        assert_eq!(whole["sides"]["mutant"]["final_configurations"], 1);
        let kore = whole["sides"]["mutant"]["kore"].as_array().unwrap();
        assert_eq!(kore.len(), 1);
        assert_eq!(kore[0]["truncated"], false);
        let text = kore[0]["text"].as_str().unwrap();
        assert!(text.contains("\\dv{SortInt{}}(\"-1\")"), "{text}");
        assert!(!text.contains("\\dv{SortInt{}}(\"3\")"), "{text}");
        // CF-16: the kill's difference names the first differing cell and both values as K text,
        // and each end's computation head and class.
        let difference = &killer["difference"];
        assert_eq!(difference["outside"], "mutant", "{difference:#}");
        assert_eq!(
            difference["path"],
            json!(["<generatedTop>", "<k>"]),
            "{difference:#}"
        );
        for (side, value) in [("baseline", "3"), ("mutant", "-1")] {
            let printed = &difference[side]["value"];
            assert_eq!(printed["rendering"], "k", "{difference:#}");
            assert!(
                printed["text"].as_str().unwrap().starts_with(value),
                "{difference:#}"
            );
            assert_eq!(difference[side]["end"]["class"], "normal", "{difference:#}");
            assert_eq!(
                difference[side]["end"]["head"]["text"], value,
                "{difference:#}"
            );
        }
        // Every comparable program's row names its end's computation head and class.
        for program in document["programs"].as_array().unwrap() {
            if program["class"] == "comparable" {
                let ends = program["ends"].as_array().unwrap();
                assert!(!ends.is_empty(), "{program:#}");
                for end in ends {
                    assert_eq!(end["head"]["rendering"], "k", "{program:#}");
                    assert_eq!(end["class"], "normal", "{program:#}");
                }
            }
        }
        // A survivor's agreeing programs have no sides; an agreeing slot never has any.
        for entry in mutation(&document, "add-swaps-operands")["executed"]
            .as_array()
            .unwrap()
        {
            assert_eq!(
                entry["slots"],
                json!({"exit-stop": {"outcome": "agree"}, "whole-term": {"outcome": "agree"}}),
                "{entry:#}"
            );
        }

        // From the outcome cache the kill's evidence is the record's (CF-16): the same difference,
        // and the sides read from it.
        let warm = search(&manifest, &dir.join("MUTATIONS.toml"));
        let cached = entry(&warm, "add-becomes-sub", "add");
        assert_eq!(cached["cached"], true);
        assert_eq!(
            cached["slots"],
            json!({"exit-stop": {"outcome": "agree"},
            "whole-term": {"outcome": "distinguish", "sides": {
                "baseline": {"final_configurations": 1},
                "mutant": {"final_configurations": 1},
            }}})
        );
        assert_eq!(cached["difference"], *difference);
        assert_eq!(cached["wall_ms"], Value::Null);
    }

    #[test]
    #[ignore = "kink"]
    fn timings_are_recorded_outside_every_digest_key_and_record_digest() {
        // Two cold runs of the same files: the result records differ at most in wall_ms, the
        // outcome records are byte-identical, and the run documents differ only in timing fields.
        let one = fixture("calc", "timings-1");
        let two = fixture("calc", "timings-2");
        let mut documents = Vec::new();
        for dir in [&one, &two] {
            let document = search(&dir.join("FLOW.toml"), &dir.join("MUTATIONS.toml"));
            // Every row has a wall time per call; every live executed entry its own run's time and
            // the program's baseline run's.
            for row in document["mutations"].as_array().unwrap() {
                assert_eq!(
                    row["call_wall_ms"].as_array().unwrap().len(),
                    row["calls"].as_array().unwrap().len(),
                    "{row:#}"
                );
                assert!(
                    row["call_wall_ms"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .all(Value::is_u64)
                );
                for entry in row["executed"].as_array().unwrap() {
                    assert!(entry["wall_ms"].is_u64(), "{entry:#}");
                    assert!(entry["baseline_ms"].is_u64(), "{entry:#}");
                    // The result update ran every baseline live; the kill search reused them.
                    assert_eq!(entry["baseline_reused"], true, "{entry:#}");
                }
            }
            for program in document["programs"].as_array().unwrap() {
                assert!(program["wall_ms"].is_u64(), "{program:#}");
            }
            documents.push(document);
        }
        assert_eq!(
            without_timings(&documents[0]),
            without_timings(&documents[1])
        );
        let (records_one, records_two) = (
            files(&cache_of(&one.join("FLOW.toml")).join("results")),
            files(&cache_of(&two.join("FLOW.toml")).join("results")),
        );
        assert_eq!(
            records_one.keys().collect::<Vec<_>>(),
            records_two.keys().collect::<Vec<_>>()
        );
        for (path, text) in &records_one {
            let (a, b): (Value, Value) = (
                serde_json::from_str(text).unwrap(),
                serde_json::from_str(&records_two[path]).unwrap(),
            );
            assert!(a["wall_ms"].is_u64() && b["wall_ms"].is_u64());
            assert!(a["key"].get("wall_ms").is_none(), "{a:#}");
            assert_eq!(without_timings(&a), without_timings(&b), "{path}");
        }
        assert_eq!(
            files(&cache_of(&one.join("FLOW.toml")).join(OUTCOMES_DIRECTORY)),
            files(&cache_of(&two.join("FLOW.toml")).join(OUTCOMES_DIRECTORY))
        );
    }

    #[test]
    #[ignore = "kink"]
    fn results_and_the_report_list_the_rules_no_mutation_targets() {
        // The loop list targets only the countdown rule; the cost list only done.
        let dir = fixture("loop", "untargeted");
        let manifest = dir.join("FLOW.toml");
        let document = results_document(&manifest, Some(dir.join("MUTATIONS.toml")));
        let listed = |document: &Value| {
            document["untargeted_rules"]
                .as_array()
                .unwrap()
                .iter()
                .map(|rule| {
                    (
                        rule["label"].as_str().map(str::to_owned),
                        rule["start_line"].as_u64().unwrap(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let lines = |document: &Value| {
            listed(document)
                .into_iter()
                .map(|(_, line)| line)
                .collect::<Vec<_>>()
        };
        // double (an equation, unlabelled, line 19), spin, done, twice, unused.
        assert_eq!(lines(&document), [19, 20, 22, 23, 24]);
        let rules = document["untargeted_rules"].as_array().unwrap();
        assert_eq!(
            rules[0],
            json!({"module": "LOOP", "index": 2, "label": null, "file": "loop.k",
                   "start_line": 19, "end_line": 19, "address": {"file": "loop.k", "line": 19},
                   "text": "rule double(I) => I *Int 2"})
        );
        assert_eq!(rules[1]["address"], json!({"rule": "LOOP.spin"}));
        assert_eq!(
            rules[1]["text"],
            "rule [spin]: spin(I:Int) => spin(I +Int 1)"
        );
        // Without a list there is nothing to compare with.
        assert_eq!(
            results_document(&manifest, None)["untargeted_rules"],
            Value::Null
        );

        // The run document (the report) lists them for the whole list, `--only` or not.
        let run_document = search(&manifest, &dir.join("MUTATIONS.toml"));
        assert_eq!(
            run_document["untargeted_rules"],
            document["untargeted_rules"]
        );
        let both = dir.join("BOTH.toml");
        fs::write(
            &both,
            format!(
                "{}\n{}",
                fs::read_to_string(dir.join("MUTATIONS.toml")).unwrap(),
                fs::read_to_string(dir.join("MUTATIONS-cost.toml")).unwrap()
            ),
        )
        .unwrap();
        let flow = FlowManifest::read(&manifest).unwrap();
        let list = MutationList::read(&both).unwrap();
        let (only, ok) = run(
            &flow,
            &list,
            &RunOptions {
                only: vec!["countdown-escapes".into()],
                cache: None,
                compile_workers: None,
                memo: kink_flow::memo::MemoUse::On,
                schedule: kink_campaign::ScheduleMode::FirstKill,
                lock: None,
                locked: false,
            },
        );
        assert!(ok, "{only:#}");
        assert_eq!(only["mutations"].as_array().unwrap().len(), 1);
        assert_eq!(lines(&only), [19, 20, 23, 24]);
        // A mutation that does not resolve targets nothing.
        let invalid = dir.join("INVALID.toml");
        fs::write(
            &invalid,
            "[[mutation]]\nid = \"nowhere\"\nmisunderstanding = \"a test mutation\"\n\n  [[mutation.edit]]\n  rule = \"spin\"\n  \
             find = \"no such text\"\n  replace = \"x\"\n",
        )
        .unwrap();
        let document = results_document(&manifest, Some(invalid));
        assert_eq!(lines(&document), [19, 20, 21, 22, 23, 24]);
        let labels = listed(&document)
            .into_iter()
            .filter_map(|(label, _)| label)
            .collect::<BTreeSet<_>>();
        assert!(labels.contains("LOOP.countdown"));
    }

    /// kink27 R5-BYTES-ENDS: a Bytes value in an end is compared by its byte sequence, in a cell,
    /// a Map value and a List element. Two sequences kill; one sequence built by two routes (a
    /// literal and `BYTES.concat`) survives; a respelled literal (`b"\x41\x42"` for `b"AB"`)
    /// survives too. Its compiled definition is the baseline's except for the rule's `UNIQUE_ID`
    /// (and its location), and `equivalent_compilation` deliberately keeps `UNIQUE_ID`, which
    /// digests the sentence as printed with each token's source spelling; so the mutant is not
    /// `equivalent`, both ends are computed and compared, and they agree because both literals
    /// store one payload. The byte 0xe9 and the UTF-8 of `é` are distinct values: a Bytes payload
    /// has no second reading.
    /// Before, TV-01 refused every Bytes value, so no program was comparable and no row was killed
    /// or survived.
    #[test]
    #[ignore = "kink"]
    fn bytes_ends_are_compared_by_their_bytes() {
        let dir = scratch("bytes-ends");
        fs::write(
            dir.join("bytes-ends.k"),
            r#"module BYTES-ENDS-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= run(Int) [symbol(run)]
endmodule
module BYTES-ENDS
  imports BYTES-ENDS-SYNTAX
  imports INT
  imports BYTES
  imports MAP
  imports LIST
  configuration <k> $PGM:Prog </k> <out> b"" </out> <mem> .Map </mem> <log> .List </log>
  rule [cell]: <k> run(0) => .K ... </k> <out> _ => b"AB" </out>
  rule [map]:  <k> run(1) => .K ... </k> <mem> M => M[1 <- b"\xe9"] </mem>
  rule [list]: <k> run(2) => .K ... </k> <log> L => L ListItem(b"\x00\xff") </log>
endmodule
"#,
        )
        .unwrap();
        let manifest = dir.join("FLOW.toml");
        fs::write(
            &manifest,
            r#"[spec]
entry = "bytes-ends.k"
main_module = "BYTES-ENDS"
syntax_module = "BYTES-ENDS-SYNTAX"

[[program]]
id = "cell"
text = "run(0)"

[[program]]
id = "map"
text = "run(1)"

[[program]]
id = "list"
text = "run(2)"
"#,
        )
        .unwrap();
        let mutations = dir.join("MUTATIONS.toml");
        fs::write(
            &mutations,
            r#"[[mutation]]
id = "cell-other"
note = "two sequences in a cell"
  [[mutation.edit]]
  rule = "cell"
  find = 'b"AB"'
  replace = 'b"AC"'

[[mutation]]
id = "cell-concat"
note = "one sequence by two routes: a literal and BYTES.concat"
  [[mutation.edit]]
  rule = "cell"
  find = 'b"AB"'
  replace = 'b"A" +Bytes b"B"'

[[mutation]]
id = "cell-respell"
note = "one value, another spelling of its literal: compiles apart only in UNIQUE_ID, so it runs and its end agrees"
  [[mutation.edit]]
  rule = "cell"
  find = 'b"AB"'
  replace = 'b"\x41\x42"'

[[mutation]]
id = "map-utf8"
note = "a Map value: the byte 0xe9 against the UTF-8 of e-acute"
  [[mutation.edit]]
  rule = "map"
  find = 'b"\xe9"'
  replace = 'b"\xc3\xa9"'

[[mutation]]
id = "list-byte"
note = "a List element, NUL and high bytes"
  [[mutation.edit]]
  rule = "list"
  find = 'b"\x00\xff"'
  replace = 'b"\x00\xfe"'

[[mutation]]
id = "list-concat"
note = "one sequence by two routes in a List element"
  [[mutation.edit]]
  rule = "list"
  find = 'b"\x00\xff"'
  replace = 'b"\x00" +Bytes b"\xff"'
"#,
        )
        .unwrap();
        let document = search(&manifest, &mutations);
        let expected = [
            ("cell-other", "killed"),
            ("cell-concat", "survived"),
            // Not `equivalent`: the rule's UNIQUE_ID digests the literal's source spelling, so
            // the compiled definitions differ there only; the ends are compared and agree.
            ("cell-respell", "survived"),
            ("map-utf8", "killed"),
            ("list-byte", "killed"),
            ("list-concat", "survived"),
        ];
        assert_eq!(
            statuses(&document),
            expected
                .iter()
                .map(|(id, status)| ((*id).to_owned(), (*status).to_owned()))
                .collect::<Vec<_>>(),
            "{document:#}"
        );
        for (id, program) in [
            ("cell-other", "cell"),
            ("map-utf8", "map"),
            ("list-byte", "list"),
        ] {
            assert_eq!(mutation(&document, id)["killer"], program, "{id}");
        }
    }
}
