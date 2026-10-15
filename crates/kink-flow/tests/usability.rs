//! Report usability (flow F-13, README 6.4): named oracle slots, timings, leaf censuses in the
//! causes of stopped runs, no second run for a baseline this command saw stop on time, cheaper
//! killers first, and the rules no mutation targets.
//!
//! The soundness conditions pinned here: no timing or census value enters an evidence row, a
//! digest, a key or a hint (two cold runs give equal digests, keys, outcome records and hints);
//! a timeout program is classified from this command's one live run, never comparable; and the
//! program order changes which killer is found first and the cost, never a status (every fixture
//! list gives the same statuses under corpus order, under the measured cost order and under a
//! forged reversed cost order).

use kink_campaign::{FinalResult, OracleOutcome, OracleSide, OracleValue, SideRun};
use kink_flow::{
    FlowManifest, MutationList,
    cli::{EXIT_OK, results},
    hints::hints_path,
    outcomes::OUTCOMES_DIRECTORY,
    report::{KORE_CAP, slots_value},
    results::{CACHE_DIRECTORY, ResultsOptions},
    search::{ProgramOrder, REPORT_FILE, RunOptions, run},
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

fn search(manifest: &Path, mutations: &Path, order: ProgramOrder) -> Value {
    let flow = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    let (document, ok) = run(
        &flow,
        &list,
        &RunOptions {
            only: Vec::new(),
            cache: None,
            order,
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
    assert_eq!(code, EXIT_OK, "{document:#}");
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
fn an_exit_stop_kill_names_its_slot_and_both_sides() {
    // F-09's divzero, in small: the mutant's rule applies to 1 / 0 with an undefined result
    // where the baseline is stuck. The exit stop distinguishes (the baseline's terminal ends
    // normally under the flow's all-normal classifier, the mutant's is an undefined step); the
    // whole final configuration agrees, because an undefined step's terminal is its pre-step
    // configuration, the baseline's stuck one.
    let dir = fixture("divide", "exit-stop");
    let manifest = dir.join("FLOW.toml");
    let document = search(&manifest, &dir.join("MUTATIONS.toml"), ProgramOrder::Corpus);
    let row = mutation(&document, "guard-dropped");
    assert_eq!(row["status"], "killed");
    assert_eq!(row["killer"], "by-zero");
    assert_eq!(document["version"], 3);
    assert_eq!(
        entry(&document, "guard-dropped", "by-zero")["slots"],
        json!({
            "exit-stop": {
                "outcome": "distinguish",
                "sides": {"baseline": ["normal"], "mutant": ["undefined-step"]}
            },
            "whole-term": {"outcome": "agree"}
        })
    );
    assert_eq!(
        entry(&document, "guard-dropped", "quotient")["slots"],
        json!({"exit-stop": {"outcome": "agree"}, "whole-term": {"outcome": "agree"}})
    );
}

#[test]
fn a_whole_term_kill_shows_the_mutants_final_configurations_on_the_killer_only() {
    let dir = fixture("calc", "whole-term");
    let manifest = dir.join("FLOW.toml");
    let document = search(&manifest, &dir.join("MUTATIONS.toml"), ProgramOrder::Corpus);
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

    // From the outcome cache the kill has no evidence at hand: its slots carry no sides.
    let warm = search(&manifest, &dir.join("MUTATIONS.toml"), ProgramOrder::Corpus);
    let cached = entry(&warm, "add-becomes-sub", "add");
    assert_eq!(cached["cached"], true);
    assert_eq!(
        cached["slots"],
        json!({"exit-stop": {"outcome": "agree"},
               "whole-term": {"outcome": "distinguish", "sides": null}})
    );
    assert_eq!(cached["wall_ms"], Value::Null);
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
    let killer = slots_value(&outcomes, Some(&baseline), Some(&mutant), true);
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
    let other = slots_value(&outcomes, Some(&baseline), Some(&mutant), false);
    assert_eq!(
        other["whole-term"]["sides"]["mutant"],
        json!({"final_configurations": 2})
    );
}

#[test]
fn timings_are_recorded_outside_every_digest_key_record_digest_and_hint() {
    // Two cold runs of the same files (corpus order, so that nothing the clock decides can
    // differ): the result records differ at most in wall_ms, the outcome records and the
    // hints are byte-identical, and the run documents differ only in timing fields.
    let one = fixture("calc", "timings-1");
    let two = fixture("calc", "timings-2");
    let mut documents = Vec::new();
    for dir in [&one, &two] {
        let document = search(
            &dir.join("FLOW.toml"),
            &dir.join("MUTATIONS.toml"),
            ProgramOrder::Corpus,
        );
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
    assert_eq!(
        fs::read_to_string(hints_path(&cache_of(&one.join("FLOW.toml")))).unwrap(),
        fs::read_to_string(hints_path(&cache_of(&two.join("FLOW.toml")))).unwrap()
    );
}

/// `the run did not finish ...; when the bound fired k-rust returned N leaves (...), the
/// deepest at depth D; those leaves had applied R of the T rules a run can observe`, or the
/// no-leaf form.
fn assert_census_cause(cause: &str, prefix: &str, rules: Option<(usize, usize)>) {
    assert!(cause.starts_with(prefix), "{cause}");
    let rest = &cause[prefix.len()..];
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

#[test]
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
    // A session record never makes a program comparable: the record is a timeout record.
    let record = read_json(
        &cache_of(&manifest)
            .join("results")
            .join(document["spec"]["digest"].as_str().unwrap())
            .join(format!("{}.json", spin["digest"].as_str().unwrap())),
    );
    assert_eq!(record["class"], "timeout");
    assert!(record["baseline"].is_null() && record["run_sha256"].is_null());
    assert_eq!(record["cause"], spin["cause"]);

    // An unknown baseline (a Bytes-keyed map) keeps its diagnostic run.
    let bytes = fixture("bytes-map", "diagnostic").join("FLOW.toml");
    let document = results_document(&bytes, None);
    assert_eq!(document["programs"][0]["class"], "unknown");
    assert_eq!(
        document["baseline_runs"],
        json!({"live": 1, "reused": 0, "diagnostic": 1})
    );
}

#[test]
fn a_mutants_timeout_and_depth_stop_carry_the_census() {
    let dir = fixture("loop", "mutant-census");
    let mutations = dir.join("MUTATIONS.toml");
    let document = search(
        &dir.join("FLOW-search.toml"),
        &mutations,
        ProgramOrder::Corpus,
    );
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
    let document = search(
        &dir.join("FLOW-depth.toml"),
        &mutations,
        ProgramOrder::Corpus,
    );
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
fn the_cheaper_killer_is_found_and_hinted_first() {
    // slow and fast both reach the done rule and both kill done-returns-one; slow is first in
    // corpus order and takes many more steps.
    let cost = fixture("loop", "cost");
    let document = search(
        &cost.join("FLOW-cost.toml"),
        &cost.join("MUTATIONS-cost.toml"),
        ProgramOrder::Cost,
    );
    assert_eq!(document["order"], "cost");
    let wall = |id: &str| {
        document["programs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|p| p["id"] == id)
            .unwrap()["wall_ms"]
            .as_u64()
            .unwrap()
    };
    assert!(wall("slow") > wall("fast"), "{:#}", document["programs"]);
    let row = mutation(&document, "done-returns-one");
    assert_eq!(row["status"], "killed");
    assert_eq!(row["killer"], "fast");
    assert_eq!(
        row["calls"],
        json!([{"programs": ["fast", "slow"], "status": "killed"}])
    );
    let hints = read_json(&hints_path(&cache_of(&cost.join("FLOW-cost.toml"))));
    let hinted = hints["hints"]
        .as_object()
        .unwrap()
        .values()
        .map(|h| h["program_id"].as_str().unwrap().to_owned())
        .collect::<Vec<_>>();
    assert_eq!(hinted, ["fast"]);

    let corpus = fixture("loop", "corpus");
    let document = search(
        &corpus.join("FLOW-cost.toml"),
        &corpus.join("MUTATIONS-cost.toml"),
        ProgramOrder::Corpus,
    );
    assert_eq!(document["order"], "corpus");
    let row = mutation(&document, "done-returns-one");
    assert_eq!(row["status"], "killed");
    assert_eq!(row["killer"], "slow");
}

/// Rewrite every result record's `wall_ms` so that cost order is the reverse of corpus
/// order. `wall_ms` is outside the key, so every record stays in use.
fn reverse_costs(manifest: &Path, document: &Value) {
    let programs = document["programs"].as_array().unwrap();
    let directory = cache_of(manifest)
        .join("results")
        .join(document["spec"]["digest"].as_str().unwrap());
    for (index, program) in programs.iter().enumerate() {
        let Some(digest) = program["digest"].as_str() else {
            continue;
        };
        let path = directory.join(format!("{digest}.json"));
        let Ok(text) = fs::read_to_string(&path) else {
            continue;
        };
        let mut record: Value = serde_json::from_str(&text).unwrap();
        record["wall_ms"] = json!((programs.len() - index) * 1000);
        fs::write(&path, record.to_string()).unwrap();
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

/// The statuses of every mutation of a fixture list are the same under corpus order, under
/// the measured cost order and under a forged cost order that reverses corpus order inside
/// each tier (stop rule 1 of F-13: the order-independence premise of README 6.4). Only the
/// killers and the costs may differ.
///
/// F-13 review 1 minor 1 (flow F-16): under cost order the SET of tier-1 records written
/// depends on host timing (under FirstKill the programs after the first kill get none), but
/// no record's content does: every record a cost-order run writes (forged or measured costs)
/// is byte-equal to the corpus-order run's record of the same (mutation, program) when that
/// run wrote one. Returns the documents and the number of such shared records.
fn statuses_do_not_depend_on_the_order(
    name: &str,
    manifest: &str,
    mutations: &str,
) -> ([Value; 3], usize) {
    let slug = format!("{}-{manifest}-{mutations}", name.replace('/', "-"));
    let corpus = fixture(name, &format!("order-corpus-{slug}"));
    let flow = corpus.join(manifest);
    let list = corpus.join(mutations);
    let by_corpus = search(&flow, &list, ProgramOrder::Corpus);

    // The same result records with reversed costs; outcomes, hints and report forgotten.
    reverse_costs(&flow, &by_corpus);
    let cache = cache_of(&flow);
    let corpus_records = outcome_records(&cache);
    let _ = fs::remove_dir_all(cache.join(OUTCOMES_DIRECTORY));
    let _ = fs::remove_file(hints_path(&cache));
    let _ = fs::remove_file(cache.join(REPORT_FILE));
    let reversed = search(&flow, &list, ProgramOrder::Cost);
    assert_eq!(
        reversed["programs"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|p| p["cached"] == false)
            .count(),
        0,
        "the forged wall_ms keeps every record in use"
    );

    let measured = fixture(name, &format!("order-cost-{slug}"));
    let by_cost = search(
        &measured.join(manifest),
        &measured.join(mutations),
        ProgramOrder::Cost,
    );

    assert_eq!(statuses(&reversed), statuses(&by_corpus), "{name} reversed");
    assert_eq!(statuses(&by_cost), statuses(&by_corpus), "{name} cost");
    let mut shared = 0;
    for (label, records) in [
        ("reversed", outcome_records(&cache)),
        ("cost", outcome_records(&cache_of(&measured.join(manifest)))),
    ] {
        for (key, text) in &records {
            if let Some(corpus) = corpus_records.get(key) {
                assert_eq!(text, corpus, "{name} {label}: {key:?}");
                shared += 1;
            }
        }
    }
    // Each killer is a program that kills (a Distinguish of its own entry).
    for document in [&by_corpus, &reversed, &by_cost] {
        for row in document["mutations"].as_array().unwrap() {
            if let Some(killer) = row["killer"].as_str() {
                assert_eq!(
                    entry(document, row["id"].as_str().unwrap(), killer)["outcome"],
                    "distinguish"
                );
            }
        }
    }
    ([by_corpus, reversed, by_cost], shared)
}

#[test]
fn calc_statuses_do_not_depend_on_the_order() {
    let ([by_corpus, reversed, _], shared) =
        statuses_do_not_depend_on_the_order("calc", "FLOW.toml", "MUTATIONS.toml");
    assert!(shared > 0, "the byte-equality check compared records");
    // The forged costs did reorder the search: inside each tier the survivor ran its programs
    // in reverse corpus order (corpus order: add, nested, sub, inline; add, nested and inline
    // reach the add rule).
    assert_eq!(
        mutation(&by_corpus, "add-swaps-operands")["calls"],
        json!([{"programs": ["add", "nested", "inline", "sub"], "status": "survived"}])
    );
    assert_eq!(
        mutation(&reversed, "add-swaps-operands")["calls"],
        json!([{"programs": ["inline", "nested", "add", "sub"], "status": "survived"}])
    );
    assert_eq!(reversed["order"], "cost");
}

#[test]
fn calc_status_list_statuses_do_not_depend_on_the_order() {
    statuses_do_not_depend_on_the_order("calc", "FLOW.toml", "MUTATIONS-statuses.toml");
}

#[test]
fn register_statuses_do_not_depend_on_the_order() {
    statuses_do_not_depend_on_the_order("register", "FLOW.toml", "MUTATIONS.toml");
}

#[test]
fn loop_timeout_statuses_do_not_depend_on_the_order() {
    statuses_do_not_depend_on_the_order("loop", "FLOW-search.toml", "MUTATIONS.toml");
}

#[test]
fn loop_depth_statuses_do_not_depend_on_the_order() {
    statuses_do_not_depend_on_the_order("loop", "FLOW-depth.toml", "MUTATIONS.toml");
}

#[test]
fn loop_cost_statuses_do_not_depend_on_the_order() {
    statuses_do_not_depend_on_the_order("loop", "FLOW-cost.toml", "MUTATIONS-cost.toml");
}

#[test]
fn markdown_statuses_do_not_depend_on_the_order() {
    statuses_do_not_depend_on_the_order("markdown", "FLOW.toml", "MUTATIONS.toml");
}

#[test]
fn twin_statuses_do_not_depend_on_the_order() {
    statuses_do_not_depend_on_the_order("twin", "FLOW.toml", "MUTATIONS.toml");
}

#[test]
fn divide_statuses_do_not_depend_on_the_order() {
    statuses_do_not_depend_on_the_order("divide", "FLOW.toml", "MUTATIONS.toml");
}

#[test]
fn map_store_statuses_do_not_depend_on_the_order() {
    statuses_do_not_depend_on_the_order("map-store", "FLOW.toml", "MUTATIONS.toml");
}

#[test]
#[ignore = "milestone"]
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
    let run_document = search(&manifest, &dir.join("MUTATIONS.toml"), ProgramOrder::Corpus);
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
            order: ProgramOrder::Corpus,
        },
    );
    assert!(ok, "{only:#}");
    assert_eq!(only["mutations"].as_array().unwrap().len(), 1);
    assert_eq!(lines(&only), [19, 20, 23, 24]);
    // A mutation that does not resolve targets nothing.
    let invalid = dir.join("INVALID.toml");
    fs::write(
        &invalid,
        "[[mutation]]\nid = \"nowhere\"\n\n  [[mutation.edit]]\n  rule = \"spin\"\n  \
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
