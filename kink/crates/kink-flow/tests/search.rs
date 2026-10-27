//! The kill search with its killer cache and `kink-flow run` (flow F-05 deliverables 1-5).
//!
//! Every test pins statuses and killer ids. Each verdict is the status kink-campaign's
//! runner derives; the tests only read the run document, the killer hints file and the
//! result records. Since F-14 the killer cache is tier 2 of the outcome cache (`hints.json`,
//! keyed by the hint key); a test that pins the warm cost of a killer deletes tier 1
//! (`outcomes/`) first, so that the hint, not a cached outcome, decides the calls.

mod flow_support;

use kink_corpus::load_source;
use kink_flow::{
    FlowManifest, MutationList,
    admit::corpus_source,
    cli::{EXIT_CORPUS, EXIT_OK, EXIT_USAGE, results},
    digest::hint_key,
    hints::{HINTS_SCHEMA, hints_path},
    outcomes::OUTCOMES_DIRECTORY,
    resolve,
    results::{CACHE_DIRECTORY, ResultsOptions},
    search::{ProgramOrder, REPORT_FILE, RunOptions, run},
};
use kink_patch::Sha256Digest;
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

fn flow(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/flow")
        .join(name)
}

/// A fresh directory for one test, under the target's temporary directory.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-search-{}", std::process::id()))
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

fn append(path: &Path, text: &str) {
    let mut contents = fs::read_to_string(path).unwrap();
    contents.push_str(text);
    fs::write(path, contents).unwrap();
}

/// `kink-flow run` through the library, as the binary runs it.
fn search(manifest: &Path, mutations: &Path, only: &[&str]) -> (Value, bool) {
    let manifest = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    run(
        &manifest,
        &list,
        &RunOptions {
            only: only.iter().map(|id| (*id).to_owned()).collect(),
            cache: None,
            // F-05's corpus order, so that the pinned calls and killers do not depend on host
            // timing (F-13's cost order: tests/usability.rs).
            order: ProgramOrder::Corpus,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
        },
    )
}

/// `(id, status, killer, killer_from_cache)` of every mutation row.
fn verdicts(document: &Value) -> Vec<(String, String, Option<String>, bool)> {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|m| {
            (
                m["id"].as_str().unwrap().to_owned(),
                m["status"].as_str().unwrap().to_owned(),
                m["killer"].as_str().map(str::to_owned),
                m["killer_from_cache"].as_bool().unwrap(),
            )
        })
        .collect()
}

fn expect(
    rows: &[(&str, &str, Option<&str>, bool)],
) -> Vec<(String, String, Option<String>, bool)> {
    rows.iter()
        .map(|(id, status, killer, cached)| {
            (
                (*id).to_owned(),
                (*status).to_owned(),
                killer.map(str::to_owned),
                *cached,
            )
        })
        .collect()
}

fn mutation<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["id"] == id)
        .unwrap_or_else(|| panic!("no mutation {id}"))
}

/// The programs of each campaign call of a mutation.
fn calls(document: &Value, id: &str) -> Vec<Vec<String>> {
    mutation(document, id)["calls"]
        .as_array()
        .unwrap()
        .iter()
        .map(|call| {
            call["programs"]
                .as_array()
                .unwrap()
                .iter()
                .map(|p| p.as_str().unwrap().to_owned())
                .collect()
        })
        .collect()
}

/// `(program, outcome)` of every program the mutant ran on, in the runner's order.
fn executed(document: &Value, id: &str) -> Vec<(String, String)> {
    mutation(document, id)["executed"]
        .as_array()
        .unwrap()
        .iter()
        .map(|e| {
            (
                e["program"].as_str().unwrap().to_owned(),
                e["outcome"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

fn strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|s| (*s).to_owned()).collect()
}

fn pairs(items: &[(&str, &str)]) -> Vec<(String, String)> {
    items
        .iter()
        .map(|(a, b)| ((*a).to_owned(), (*b).to_owned()))
        .collect()
}

fn spec_digest(document: &Value) -> Sha256Digest {
    Sha256Digest::parse(document["spec"]["digest"].as_str().unwrap()).unwrap()
}

fn program_digest(document: &Value, id: &str) -> String {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["id"] == id)
        .unwrap()["digest"]
        .as_str()
        .unwrap()
        .to_owned()
}

fn cache_of(manifest: &Path) -> PathBuf {
    manifest.parent().unwrap().join(CACHE_DIRECTORY)
}

fn killers_file(manifest: &Path) -> PathBuf {
    hints_path(&cache_of(manifest))
}

/// Delete tier 1 of the outcome cache, so that the next run's calls come from the hints.
fn forget_outcomes(manifest: &Path) {
    let _ = fs::remove_dir_all(cache_of(manifest).join(OUTCOMES_DIRECTORY));
}

/// The hint key of mutation `id` of the manifest's `MUTATIONS.toml`.
fn hint_key_of(manifest: &Path, id: &str) -> String {
    let flow = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(&manifest.with_file_name("MUTATIONS.toml")).unwrap();
    let mutation = list.mutations.iter().find(|m| m.id == id).unwrap();
    let loaded = load_source(&corpus_source(&flow)).unwrap();
    let resolved = resolve(&flow, &loaded, mutation).unwrap();
    hint_key(mutation, &resolved).to_string()
}

/// The killer hints: hint key -> (mutation id, program id, program digest).
fn killers(manifest: &Path, _document: &Value) -> Vec<(String, String, String, String)> {
    let path = killers_file(manifest);
    let Ok(text) = fs::read_to_string(&path) else {
        return Vec::new();
    };
    let value: Value = serde_json::from_str(&text).unwrap();
    assert_eq!(value["schema"], HINTS_SCHEMA);
    value["hints"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(digest, entry)| {
            (
                digest.clone(),
                entry["mutation_id"].as_str().unwrap().to_owned(),
                entry["program_id"].as_str().unwrap().to_owned(),
                entry["program_digest"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

fn killer_of(manifest: &Path, document: &Value, id: &str) -> Option<(String, String)> {
    let key = hint_key_of(manifest, id);
    killers(manifest, document)
        .into_iter()
        .find(|(k, ..)| *k == key)
        .map(|(_, _, program, program_digest)| (program, program_digest))
}

/// Replace the killer hint of mutation `id` by hand.
fn set_killer(manifest: &Path, _document: &Value, id: &str, program: &str, program_digest: &str) {
    let path = killers_file(manifest);
    let mut value: Value = fs::read_to_string(&path)
        .ok()
        .map(|text| serde_json::from_str(&text).unwrap())
        .unwrap_or_else(|| json!({"schema": HINTS_SCHEMA, "version": 1, "hints": {}}));
    value["hints"][hint_key_of(manifest, id)] = json!({
        "mutation_id": id,
        "program_id": program,
        "program_digest": program_digest,
    });
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, serde_json::to_string_pretty(&value).unwrap()).unwrap();
}

fn record_path(manifest: &Path, document: &Value, program: &str) -> PathBuf {
    cache_of(manifest)
        .join("results")
        .join(spec_digest(document).to_string())
        .join(format!("{}.json", program_digest(document, program)))
}

/// Hand-edit program `program`'s cached run digest, as a stale record would have it.
fn corrupt_run_digest(manifest: &Path, document: &Value, program: &str) {
    let path = record_path(manifest, document, program);
    let mut record: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
    assert_eq!(record["class"], "comparable");
    record["run_sha256"] = json!("0".repeat(64));
    fs::write(&path, serde_json::to_string(&record).unwrap()).unwrap();
}

const CALC_VERDICTS: [(&str, &str, Option<&str>); 5] = [
    // 1 + 2 is 3 on the baseline and -1 on the mutant: the first program reaching add.
    ("add-becomes-sub", "killed", Some("add")),
    // 10 - 4 - 3 is 3 on the baseline and 1 on the mutant: the only program reaching sub.
    ("sub-off-by-one", "killed", Some("sub")),
    // (1 + 2) * 3 is 9 on the baseline and 6 on the mutant.
    ("mul-becomes-add", "killed", Some("nested")),
    // Without the mul rule, (1 + 2) * 3 is stuck at 3 * 3.
    ("no-mul", "killed", Some("nested")),
    // I2 +Int I1 equals I1 +Int I2 on every input: no program can tell.
    ("add-swaps-operands", "survived", None),
];

#[test]
fn the_runner_runs_the_mutant_in_the_chosen_order() {
    // The scheduling premise of README 5.6: under FirstKill and no coverage selection the
    // runner runs the mutant on Campaign.tests in the order given. The survivor runs on every
    // program, so its executed list is the whole order: the programs reaching the add rule
    // (add, nested, inline) in corpus order, then sub; the corpus order is add, nested, sub,
    // inline.
    let manifest = fixture("calc", "order").join("FLOW.toml");
    let (document, ok) = search(
        &manifest,
        &manifest.with_file_name("MUTATIONS.toml"),
        &["add-swaps-operands"],
    );
    assert!(ok);
    assert_eq!(
        verdicts(&document),
        expect(&[("add-swaps-operands", "survived", None, false)])
    );
    assert_eq!(
        executed(&document, "add-swaps-operands"),
        pairs(&[
            ("add", "agree"),
            ("nested", "agree"),
            ("inline", "agree"),
            ("sub", "agree"),
        ])
    );
    assert_eq!(
        calls(&document, "add-swaps-operands"),
        vec![strings(&["add", "nested", "inline", "sub"])]
    );
    // A survivor creates no entry: the cache file holds none.
    assert!(killers(&manifest, &document).is_empty());
}

/// Writes an inline flow fixture: the K file, a specification with `programs` (id, text), and a
/// mutation list with one edit per mutation (id, rule, find, replace).
fn inline_flow(
    name: &str,
    file: &str,
    text: &str,
    (main, syntax): (&str, &str),
    programs: &[(&str, &str)],
    mutations: &[(&str, &str, &str, &str)],
) -> PathBuf {
    let dir = scratch(name);
    fs::write(dir.join(file), text).unwrap();
    let mut flow = format!(
        "[spec]\nentry = \"{file}\"\nmain_module = \"{main}\"\nsyntax_module = \"{syntax}\"\n"
    );
    for (id, text) in programs {
        flow.push_str(&format!(
            "\n[[program]]\nid = \"{id}\"\ntext = \"{text}\"\n"
        ));
    }
    fs::write(dir.join("FLOW.toml"), flow).unwrap();
    let mut list = String::new();
    for (id, rule, find, replace) in mutations {
        list.push_str(&format!(
            "[[mutation]]\nid = \"{id}\"\n\n  [[mutation.edit]]\n  rule = \"{rule}\"\n  \
             find = \"{find}\"\n  replace = \"{replace}\"\n\n"
        ));
    }
    fs::write(dir.join("MUTATIONS.toml"), list).unwrap();
    dir
}

/// The labels of a row's typing diagnostics.
fn diagnosed(document: &Value, id: &str) -> Vec<Value> {
    mutation(document, id)["typing_diagnostics"]
        .as_array()
        .unwrap_or_else(|| panic!("{id}: {document:#}"))
        .iter()
        .map(|diagnostic| diagnostic["label"].clone())
        .collect()
}

mod kink_tier {
    use super::*;

    #[test]
    #[ignore = "kink"]
    fn the_binarys_run_command() {
        let binary = env!("CARGO_BIN_EXE_kink-flow");
        let dir = fixture("register", "binary");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let cache = scratch("binary-cache");
        // Re-pin R0c-fix-3 (R0c-fix-2 review major 3): corpus order, as the library-level tests use
        // (`search` above). Under the default cost order the killer is the first killing program by
        // measured baseline wall_ms, and store, increment and double each measure 1-3 ms on this
        // fixture, so a 1 ms jitter on a loaded host made increment the killer.
        let output = Command::new(binary)
            .arg("run")
            .arg(&manifest)
            .arg(&mutations)
            .args(["--only", "put-offset", "--order", "corpus", "--cache"])
            .arg(&cache)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(EXIT_OK)));
        let document: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(document["schema"], "kink-flow-run");
        assert_eq!(
            verdicts(&document),
            expect(&[("put-offset", "killed", Some("store"), false)])
        );
        assert!(cache.join(REPORT_FILE).is_file());
        assert!(hints_path(&cache).is_file());
        assert!(!dir.join(CACHE_DIRECTORY).exists());

        let bad = dir.join("BAD.toml");
        fs::write(&bad, "[[mutation]]\nid = \"m\"\nlabel = \"x\"\n").unwrap();
        for (args, code) in [
            (vec!["run"], EXIT_USAGE),
            (vec!["run", "FLOW.toml"], EXIT_USAGE),
            (
                vec!["run", "FLOW.toml", "MUTATIONS.toml", "--only"],
                EXIT_USAGE,
            ),
            (
                vec!["run", "FLOW.toml", "MUTATIONS.toml", "--only", "nope"],
                EXIT_USAGE,
            ),
            (
                vec!["run", "FLOW.toml", "MUTATIONS.toml", "--frobnicate"],
                EXIT_USAGE,
            ),
            (vec!["run", "FLOW.toml", "missing.toml"], EXIT_USAGE),
            (vec!["run", "FLOW.toml", "BAD.toml"], EXIT_CORPUS),
        ] {
            let output = Command::new(binary)
                .args(&args)
                .current_dir(&dir)
                .output()
                .unwrap();
            assert_eq!(output.status.code(), Some(i32::from(code)), "{args:?}");
            if code == EXIT_CORPUS {
                let document: Value = serde_json::from_slice(&output.stdout).unwrap();
                assert_eq!(document["mutation_list"]["outcome"], "refused");
            }
        }
    }

    #[test]
    #[ignore = "kink"]
    fn the_register_mutations_have_the_statuses_their_programs_imply() {
        let manifest = fixture("register", "register").join("FLOW.toml");
        let (document, ok) = search(&manifest, &manifest.with_file_name("MUTATIONS.toml"), &[]);
        assert!(ok, "{document:#}");
        assert_eq!(
            verdicts(&document),
            expect(&[
                // put(5) leaves 6 in <reg> instead of 5. The correlated get edit returns 6 - 1 =
                // 5 for every read, so a program that only compares values it reads back could
                // not tell; but the whole-term oracle sees the final <reg> cell, so the first
                // program reaching put (store) kills it.
                ("put-and-get-offset", "killed", Some("store"), false),
                // put alone: put(5) leaves 6 in <reg>.
                ("put-offset", "killed", Some("store"), false),
                // get alone: store never reads; increment's put(get + 1) stores 5 instead of 6.
                ("get-offset", "killed", Some("increment"), false),
                // Without seq, put(5); put(get + 1) is stuck at the first ';'.
                ("no-seq", "killed", Some("increment"), false),
            ])
        );
        // get-offset reaches the get rule through increment and double only, so store runs last.
        assert_eq!(
            mutation(&document, "get-offset")["reaching"],
            json!(["increment", "double"])
        );
        assert_eq!(
            calls(&document, "get-offset"),
            vec![strings(&["increment", "double", "store"])]
        );
        assert_eq!(
            killer_of(&manifest, &document, "put-and-get-offset")
                .unwrap()
                .0,
            "store"
        );
    }

    /// Re-pin L2-1-tail (review L2-1-1, D2): the first tier of O and the row's `reaching` are the
    /// programs whose coverage witnesses the edit. `by-zero` (`1 / 0`) matches the division rule
    /// and refutes its guard, so it reached the rule without firing it: it witnesses an edit of the
    /// `requires` (alone or with the right-hand side), never one of the right-hand side alone.
    #[test]
    #[ignore = "kink"]
    fn the_first_tier_is_the_programs_whose_coverage_witnesses_the_edit() {
        let dir = fixture("divide", "witness");
        let mutations = dir.join("MUTATIONS-witness.toml");
        fs::write(
            &mutations,
            r#"
[[mutation]]
id = "guard-dropped"
note = "requires"
  [[mutation.edit]]
  rule = "div"
  find = " requires I2 =/=Int 0"
  replace = ""

[[mutation]]
id = "operands-swapped"
note = "right-hand side"
  [[mutation.edit]]
  rule = "div"
  find = "I1 /Int I2"
  replace = "I2 /Int I1"

[[mutation]]
id = "both"
note = "requires and right-hand side"
  [[mutation.edit]]
  rule = "div"
  find = "I1 /Int I2 requires I2 =/=Int 0"
  replace = "I2 /Int I1 requires I1 =/=Int 0"
"#,
        )
        .unwrap();
        let (document, _) = search(&dir.join("FLOW.toml"), &mutations, &[]);
        for (id, reaching) in [
            ("guard-dropped", json!(["quotient", "by-zero"])),
            ("operands-swapped", json!(["quotient"])),
            ("both", json!(["quotient", "by-zero"])),
        ] {
            assert_eq!(mutation(&document, id)["reaching"], reaching, "{id}");
        }
        assert_eq!(
            verdicts(&document),
            expect(&[
                ("guard-dropped", "killed", Some("by-zero"), false),
                ("operands-swapped", "killed", Some("quotient"), false),
                ("both", "killed", Some("quotient"), false),
            ])
        );
    }

    #[test]
    #[ignore = "kink"]
    fn only_runs_the_named_mutations() {
        let manifest = fixture("register", "only").join("FLOW.toml");
        let (document, ok) = search(
            &manifest,
            &manifest.with_file_name("MUTATIONS.toml"),
            &["no-seq", "get-offset"],
        );
        assert!(ok);
        // File order, not --only order.
        assert_eq!(
            verdicts(&document),
            expect(&[
                ("get-offset", "killed", Some("increment"), false),
                ("no-seq", "killed", Some("increment"), false),
            ])
        );
        assert_eq!(killers(&manifest, &document).len(), 2);
    }

    /// L2-2 (decision 4; findings C-02, C-03 (a)): `TWICE` imports only `INT-SYNTAX`, so its own
    /// module's typing view lacks the `K` sequence order and types neither `twice` nor `first`;
    /// compilation types both in the main module's view and compiles. Until L2-2 kink-patch typed
    /// every edited rule in its own module, so both mutations were `invalid-mutation`
    /// (`patch-rejected`) although their mutants compile. Now compilation decides, and each mutant
    /// goes through claim removal, the compiled-effect diff and the consistency check before it
    /// runs: `second-steps` edits a rewrite rule (no claim to remove), `first-zero` edits the
    /// equation of the total function `first`, whose `total` claim the mutant loses. Both are
    /// killed by `go(1)`, whose baseline result is `done(1) ~> done(1) ~> done(1)`.
    #[test]
    #[ignore = "kink"]
    fn a_rule_typed_only_in_compilations_view_is_mutated_and_run() {
        let dir = scratch("module-view");
        fs::write(
            dir.join("modview.k"),
            "module MODVIEW-SYNTAX\n  imports INT-SYNTAX\n  syntax Pgm ::= go(Int)\nendmodule\n\n\
             module TWICE\n  imports INT-SYNTAX\n  syntax KItem ::= step(Int) | done(Int)\n  \
             syntax K ::= first(Int) [function, total]\n  \
             rule [twice]: step(X) => done(X) ~> done(X)\n  rule [first]: first(X) => done(X)\n\
             endmodule\n\n\
             module MODVIEW\n  imports MODVIEW-SYNTAX\n  imports TWICE\n  imports INT\n  \
             configuration <k> $PGM:Pgm </k>\n  rule [go]: go(X) => step(X) ~> first(X)\nendmodule\n",
        )
        .unwrap();
        fs::write(
            dir.join("FLOW.toml"),
            "[spec]\nentry = \"modview.k\"\nmain_module = \"MODVIEW\"\nsyntax_module = \"MODVIEW-SYNTAX\"\n\n\
             [[program]]\nid = \"one\"\ntext = \"go(1)\"\n",
        )
        .unwrap();
        fs::write(
            dir.join("MUTATIONS.toml"),
            "[[mutation]]\nid = \"second-steps\"\n\n  [[mutation.edit]]\n  rule = \"twice\"\n  \
             find = \"~> done(X)\"\n  replace = \"~> step(X)\"\n\n\
             [[mutation]]\nid = \"first-zero\"\n\n  [[mutation.edit]]\n  rule = \"first\"\n  \
             find = \"done(X)\"\n  replace = \"done(0)\"\n",
        )
        .unwrap();
        let (document, ok) = search(&dir.join("FLOW.toml"), &dir.join("MUTATIONS.toml"), &[]);
        assert!(ok, "{document:#}");
        assert_eq!(
            verdicts(&document),
            expect(&[
                ("second-steps", "killed", Some("one"), false),
                ("first-zero", "killed", Some("one"), false),
            ]),
            "{document:#}"
        );
        for id in ["second-steps", "first-zero"] {
            assert_eq!(
                mutation(&document, id)["inconsistent_pairs"],
                json!([]),
                "{id}"
            );
            assert_eq!(
                mutation(&document, id)["removed_claims"]["unsupported"],
                json!([]),
                "{id}"
            );
        }
        assert_eq!(
            mutation(&document, "second-steps")["removed_claims"]["removed"],
            json!([])
        );
        let removed = mutation(&document, "first-zero")["removed_claims"]["removed"]
            .as_array()
            .unwrap()
            .iter()
            .map(|claim| (claim["label"].clone(), claim["key"].clone()))
            .collect::<Vec<_>>();
        assert_eq!(removed, [(Value::Null, json!("total"))], "{document:#}");
    }

    /// Re-pin L2-2-fix-1 (review L2-2-review-1, minor 1; probe synout3): the syntax module, which the
    /// main module does not import, is loaded with its rules, outside the main module's import
    /// closure. Compilation never emits them, so an edit of one compiles equal to the baseline and is
    /// `equivalent` (`equivalent-compilation`), with no typing diagnostic (compilation's view says
    /// nothing outside the closure). An edit that does not parse is `edited-load-failed`. The main
    /// module's rule is a control.
    #[test]
    #[ignore = "kink"]
    fn a_syntax_module_rule_outside_the_main_closure_is_an_equivalent_mutation() {
        let dir = inline_flow(
            "typing-syntax-outside",
            "synout3.k",
            "module SYN3-CFG\n  imports INT\n  syntax Pgm ::= go(Int) [symbol(go)]\n  \
             syntax KItem ::= aux(Int) [symbol(aux)] | done(Int) [symbol(done)]\n  \
             syntax Int ::= sf(Int) [function, total, symbol(sf)]\n  \
             configuration <k> $PGM:Pgm </k>\n  rule [sfr]: sf(X) => X +Int 10\nendmodule\n\n\
             module SYN3-SYNTAX\n  imports SYN3-CFG\n  \
             rule [srule]: <k> aux(X) => done(X +Int 100) ... </k>\n  rule [sfr2]: sf(0) => 5\n\
             endmodule\n\nmodule SYN3\n  imports SYN3-CFG\n  rule [go]: go(X) => aux(sf(X))\n  \
             rule [mrule]: aux(X) => done(X +Int 1) [owise]\nendmodule\n",
            ("SYN3", "SYN3-SYNTAX"),
            &[("one", "go(1)"), ("zero", "go(0)")],
            &[
                ("srule-edit", "srule", "X +Int 100", "X +Int 200"),
                ("sfr2-edit", "sfr2", "=> 5", "=> 6"),
                ("srule-ill", "srule", "done(X +Int 100)", "done(true)"),
                ("mrule-edit", "mrule", "X +Int 1", "X +Int 2"),
            ],
        );
        let (document, ok) = search(&dir.join("FLOW.toml"), &dir.join("MUTATIONS.toml"), &[]);
        assert!(ok, "{document:#}");
        assert_eq!(
            verdicts(&document),
            expect(&[
                ("srule-edit", "equivalent", None, false),
                ("sfr2-edit", "equivalent", None, false),
                ("srule-ill", "invalid-mutation", None, false),
                ("mrule-edit", "killed", Some("one"), false),
            ]),
            "{document:#}"
        );
        for id in ["srule-edit", "sfr2-edit"] {
            let row = mutation(&document, id);
            assert_eq!(row["reason"], "equivalent-compilation", "{id}");
            assert_eq!(row["typing_diagnostics"], json!([]), "{id}");
        }
        assert_eq!(
            mutation(&document, "srule-ill")["reason"],
            "edited-load-failed"
        );
    }

    #[test]
    #[ignore = "kink"]
    fn programs_that_cannot_kill_are_never_run() {
        // A refused program fails the command but not the search; a timeout program is never
        // given to the runner.
        let manifest = fixture("calc", "refused").join("FLOW-bad-program.toml");
        let (document, ok) = search(
            &manifest,
            &manifest.with_file_name("MUTATIONS.toml"),
            &["add-becomes-sub"],
        );
        assert!(!ok);
        assert_eq!(
            verdicts(&document),
            expect(&[("add-becomes-sub", "killed", Some("add"), false)])
        );
        assert_eq!(
            calls(&document, "add-becomes-sub"),
            vec![strings(&["add", "sub"])]
        );

        let manifest = fixture("loop", "no-comparable").join("FLOW-timeout.toml");
        let text = fs::read_to_string(&manifest).unwrap().replace(
            "[[program]]\nid = \"countdown\"\nfile = \"programs/countdown.loop\"\n",
            "",
        );
        fs::write(&manifest, text).unwrap();
        let (document, ok) = search(&manifest, &manifest.with_file_name("MUTATIONS.toml"), &[]);
        assert!(!ok);
        assert_eq!(document["programs"][0]["class"], "timeout");
        assert_eq!(
            verdicts(&document),
            expect(&[("countdown-escapes", "error", None, false)])
        );
        assert_eq!(
            mutation(&document, "countdown-escapes")["reason"],
            json!("no-comparable-program")
        );
        assert_eq!(
            calls(&document, "countdown-escapes"),
            Vec::<Vec<String>>::new()
        );
    }

    /// Re-pin L2-2-fix-1 (review L2-2-review-1, minor 4; probe cellc): C-03 case (c), a local
    /// function whose equation has a variable in the body of a cell with children
    /// (`SentenceTypingError::CellCompletion`, k-rust's stated exception), run to a verdict. Both
    /// mutations were `patch-rejected` at 1ee9955; each compiles, removes no claim, passes the
    /// consistency check and is killed by `go` (final `barK(..)` against `fooK(..)`, and a stuck `go`
    /// against `fooK(..)`), with the CellCompletion message as its typing diagnostic.
    #[test]
    #[ignore = "kink"]
    fn a_cell_completion_shape_is_mutated_and_run_to_a_verdict() {
        let dir = inline_flow(
            "typing-cellc",
            "cellc.k",
            "module CELLC-SYNTAX\n  syntax KItem ::= \"go\" [symbol(go)]\nendmodule\n\n\
             module CELLC\n  imports CELLC-SYNTAX\n  imports INT\n  imports BOOL\n  \
             configuration <t>\n    <k> $PGM:K </k>\n    <accounts> <account multiplicity=\"*\" \
             type=\"Map\"> <id> 0 </id> <bal> 0 </bal> </account> </accounts>\n  </t>\n  \
             syntax KItem ::= \"stop\" | box(AccountsCell) | fooK(K) | barK(K)\n  \
             rule [completed]: <k> go => #fun(box(<accounts> B </accounts>) => fooK(B))\
             (box(<accounts> A </accounts>)) ... </k> <accounts> A </accounts>\n  \
             rule [plain]: <k> stop => .K ... </k>\nendmodule\n",
            ("CELLC", "CELLC-SYNTAX"),
            &[("go", "go")],
            &[
                ("lambda-body", "completed", "=> fooK(B)", "=> barK(B)"),
                (
                    "outer-requires",
                    "completed",
                    "</k> <accounts> A </accounts>",
                    "</k> <accounts> A </accounts> requires false",
                ),
            ],
        );
        let (document, ok) = search(&dir.join("FLOW.toml"), &dir.join("MUTATIONS.toml"), &[]);
        assert!(ok, "{document:#}");
        assert_eq!(
            verdicts(&document),
            expect(&[
                ("lambda-body", "killed", Some("go"), false),
                ("outer-requires", "killed", Some("go"), false),
            ]),
            "{document:#}"
        );
        for id in ["lambda-body", "outer-requires"] {
            assert_eq!(diagnosed(&document, id), [json!("CELLC.completed")], "{id}");
            let row = mutation(&document, id);
            assert!(
                row["typing_diagnostics"][0]["message"]
                    .as_str()
                    .unwrap()
                    .contains("local function"),
                "{id}: {row:#}"
            );
            assert_eq!(row["inconsistent_pairs"], json!([]), "{id}");
            assert_eq!(
                row["removed_claims"],
                json!({"removed": [], "unsupported": []}),
                "{id}"
            );
        }
    }

    #[test]
    #[ignore = "kink"]
    fn every_status_and_an_invalid_mutation_that_does_not_stop_the_others() {
        let manifest = fixture("calc", "statuses").join("FLOW.toml");
        let mutations = manifest.with_file_name("MUTATIONS-statuses.toml");
        let (document, ok) = search(&manifest, &mutations, &[]);
        assert!(ok, "{document:#}");
        assert_eq!(
            verdicts(&document),
            expect(&[
                ("no-such-rule", "invalid-mutation", None, false),
                ("add-becomes-sub", "killed", Some("add"), false),
                ("add-commutes", "survived", None, false),
                ("add-in-a-group", "equivalent", None, false),
                ("add-unbound", "invalid", None, false),
                ("add-ill-sorted", "invalid-mutation", None, false),
            ])
        );
        let reason = |id: &str| mutation(&document, id)["reason"].clone();
        assert_eq!(reason("no-such-rule"), json!("unknown-label"));
        assert_eq!(reason("add-ill-sorted"), json!("edited-load-failed"));
        assert_eq!(reason("add-in-a-group"), json!("equivalent-compilation"));
        assert_eq!(reason("add-unbound"), json!("rejected"));
        // A mutation that does not resolve is never compiled or run.
        for id in ["no-such-rule", "add-ill-sorted"] {
            assert_eq!(mutation(&document, id)["calls"], json!([]), "{id}");
            assert_eq!(mutation(&document, id)["digest"], Value::Null, "{id}");
        }
        // Equivalent and Invalid are mutant-scope statuses: the mutant runs on no program.
        for id in ["add-in-a-group", "add-unbound"] {
            assert_eq!(executed(&document, id), Vec::new(), "{id}");
            assert_eq!(calls(&document, id).len(), 1, "{id}");
        }
        assert_eq!(
            killers(&manifest, &document)
                .into_iter()
                .map(|(_, mutation, program, _)| (mutation, program))
                .collect::<Vec<_>>(),
            vec![("add-becomes-sub".to_owned(), "add".to_owned())]
        );
        assert_eq!(
            document["counts"],
            json!({"killed": 1, "survived": 1, "equivalent": 1, "invalid": 1, "timeout": 0,
                   "unknown": 0, "error": 0, "invalid-mutation": 2})
        );
    }

    /// Re-pin R0c-fix-3 deliverable 1 (`testdata/flow/overlap`): a mutation that makes two equations
    /// of one function apply to one input with different values is `invalid` with reason
    /// `inconsistent-mutant`, runs no program and writes no outcome record, and its row names the
    /// pair; a rewrite-rule edit changes no equation and runs (killed by `minus-one`: `0` against
    /// `-1`). A second cold run of the same list gives the same rows: the refusal is a function of
    /// the mutant, and no record of the refused mutation exists for tier 1 to read.
    #[test]
    #[ignore = "kink"]
    fn an_inconsistent_mutation_is_invalid_and_names_its_pair() {
        let dir = fixture("overlap", "inconsistent");
        let (document, ok) = search(&dir.join("FLOW.toml"), &dir.join("MUTATIONS.toml"), &[]);
        assert!(ok, "{document:#}");
        // Re-pin L2-2-fix-1: version 6 adds each row's `typing_diagnostics`; packet CACHE-ID:
        // version 7 adds the document's `kink` identity; packet CACHE-ID-fix-1: version 8 adds its
        // `kink_build`; re-pin adoption A-1: version 9 adds `specification_diagnostics` and
        // `smt_unknowns`; fz26 KINK-BASELINE-FINDINGS: version 10 adds `data`, a row's
        // `findings` and `unable_to_kill`.
        assert_eq!(document["version"], 10);
        // GUIDE-USABILITY 5 (KINK-R4 fix round): every kink-flow document names k-rust's build
        // identity, not the version alone.
        assert_eq!(document["k_rust_revision"], k_rust::build_identity());
        assert_eq!(
            verdicts(&document),
            expect(&[
                ("pos-widened", "invalid", None, false),
                ("sgn-plus-one", "killed", Some("minus-one"), false),
            ])
        );
        let refused = mutation(&document, "pos-widened");
        assert_eq!(refused["reason"], "inconsistent-mutant");
        assert_eq!(
            refused["calls"],
            json!([{"programs": ["minus-one"], "status": "invalid"}])
        );
        assert_eq!(refused["executed"], json!([]));
        let pairs = refused["inconsistent_pairs"].as_array().unwrap();
        assert_eq!(pairs.len(), 1, "{pairs:?}");
        let mut names = [
            pairs[0]["first"].as_str().unwrap(),
            pairs[0]["second"].as_str().unwrap(),
        ];
        names.sort_unstable();
        assert_eq!(names, ["OVERLAP.neg", "OVERLAP.pos"]);
        assert!(
            refused["action"]
                .as_str()
                .unwrap()
                .contains("inconsistent_pairs")
        );
        assert_eq!(
            mutation(&document, "sgn-plus-one")["inconsistent_pairs"],
            json!([])
        );
        // Under Z3 no record is written: tier 1 is off by design (search::tier1_refusal).
        let written = if cfg!(feature = "z3") { 0 } else { 1 };
        assert_eq!(document["outcome_cache"]["records_written"], written);

        let (again, ok) = search(&dir.join("FLOW.toml"), &dir.join("MUTATIONS.toml"), &[]);
        assert!(ok);
        assert_eq!(verdicts(&again)[0], verdicts(&document)[0]);
        assert_eq!(
            mutation(&again, "pos-widened")["inconsistent_pairs"],
            refused["inconsistent_pairs"]
        );
    }

    /// Re-pin L2-2-fix-1 (review L2-2-review-1, major defect; probes lub, lubbase and lubmain): no
    /// typing error makes a mutation `patch-rejected`. k-rust's typing view gives a `Sort` error (no
    /// unique least upper bound of `A` and `B`, since the main module adds a second common supersort
    /// `D`) on a rule `a(X) => b(X)` that compilation accepts. Each mutation compiles, goes through
    /// claim removal (nothing to remove: rewrite rules only), the compiled-effect diff and the
    /// consistency check, and runs, and `go(1)` kills it with a final configuration of another
    /// constructor; the error is the row's `typing_diagnostics`.
    /// - `lub-a-to-b` (imported module `LUBB`, edit `a2(X)` -> `b(X)`): killed at 1ee9955,
    ///   patch-rejected at L2-2, killed again.
    /// - `lubbase-b-arg` (imported module, baseline rule `a(X) => b(X)`, edit to `b(0)`): the same;
    ///   its control `a(X) => a2(X)` types.
    /// - `lubmain-a-to-b` (main module, edit `a2(X)` -> `b(X)`): patch-rejected at 1ee9955 and L2-2,
    ///   since both views refuse it; now compiled, run and killed.
    ///
    /// The controls have no diagnostic and are killed.
    #[test]
    #[ignore = "kink"]
    fn a_typing_error_compilation_accepts_is_a_diagnostic_and_the_mutant_runs() {
        let imported = |module: &str, rule: &str| {
            format!(
                "module {module}-SYNTAX\n  imports INT-SYNTAX\n  syntax Pgm ::= go(Int) [symbol(go)]\n\
                 endmodule\n\nmodule {module}B\n  imports INT-SYNTAX\n  \
                 syntax A ::= a(Int) [symbol(a)] | a2(Int) [symbol(a2)]\n  \
                 syntax B ::= b(Int) [symbol(b)]\n  syntax C ::= A | B\n  rule [ab]: {rule}\n\
                 endmodule\n\nmodule {module}\n  imports {module}-SYNTAX\n  imports {module}B\n  \
                 imports INT\n  syntax D ::= A | B\n  configuration <k> $PGM:Pgm </k>\n  \
                 rule [go]: go(X) => a(X)\nendmodule\n"
            )
        };
        let main = "module LUBM-SYNTAX\n  imports INT-SYNTAX\n  syntax Pgm ::= go(Int) [symbol(go)]\n\
                    endmodule\n\nmodule LUBM\n  imports LUBM-SYNTAX\n  imports INT\n  \
                    syntax A ::= a(Int) [symbol(a)] | a2(Int) [symbol(a2)]\n  \
                    syntax B ::= b(Int) [symbol(b)]\n  syntax C ::= A | B\n  syntax D ::= A | B\n  \
                    configuration <k> $PGM:Pgm </k>\n  rule [go]: go(X) => a(X)\n  \
                    rule [ab]: a(X) => a2(X)\nendmodule\n";
        // The last column names the rule whose typing error the row carried at 501f18b9 (re-pin
        // probe P-1: none now).
        for (name, text, modules, mutations, _label) in [
            (
                "lub",
                imported("LUB", "a(X) => a2(X)"),
                ("LUB", "LUB-SYNTAX"),
                [("a-to-b", "a2(X)", "b(X)"), ("control", "a2(X)", "a2(0)")],
                "LUBB.ab",
            ),
            (
                "lubbase",
                imported("LUBBASE", "a(X) => b(X)"),
                ("LUBBASE", "LUBBASE-SYNTAX"),
                [
                    ("b-arg", "b(X)", "b(0)"),
                    ("control", "=> b(X)", "=> a2(X)"),
                ],
                "LUBBASEB.ab",
            ),
            (
                "lubmain",
                main.to_owned(),
                ("LUBM", "LUBM-SYNTAX"),
                [("a-to-b", "a2(X)", "b(X)"), ("control", "a2(X)", "a2(0)")],
                "LUBM.ab",
            ),
        ] {
            let file = format!("{name}.k");
            let rows = mutations.map(|(id, find, replace)| (id, "ab", find, replace));
            let dir = inline_flow(
                &format!("typing-{name}"),
                &file,
                &text,
                modules,
                &[("one", "go(1)")],
                &rows,
            );
            let (document, ok) = search(&dir.join("FLOW.toml"), &dir.join("MUTATIONS.toml"), &[]);
            assert!(ok, "{name}: {document:#}");
            let [(edited, ..), (control, ..)] = mutations;
            assert_eq!(
                verdicts(&document),
                expect(&[
                    (edited, "killed", Some("one"), false),
                    (control, "killed", Some("one"), false),
                ]),
                "{name}: {document:#}"
            );
            // Re-pin probe P-1 (k-rust 58720d2e5; KINK-21/1, head e7b166360, merge 79fa4c823; k-rust's
            // draft answers-add3 section 2.4 "KINK-21/1"): the typing view now types a rule that
            // compilation wraps in the computation cell at `K`, as compilation does, so `a(X) => b(X)`
            // asks no least upper bound of `A` and `B` and has no typing error in any of the three
            // shapes. The verdicts above are unchanged; only the row's diagnostic is gone.
            assert_eq!(diagnosed(&document, edited), [] as [Value; 0], "{name}");
            assert_eq!(
                mutation(&document, edited)["typing_diagnostics"],
                json!([]),
                "{name}"
            );
            assert_eq!(diagnosed(&document, control), [] as [Value; 0], "{name}");
            for id in [edited, control] {
                let row = mutation(&document, id);
                assert_eq!(row["inconsistent_pairs"], json!([]), "{name} {id}");
                assert_eq!(
                    row["removed_claims"],
                    json!({"removed": [], "unsupported": []}),
                    "{name} {id}"
                );
            }
        }
    }

    #[test]
    #[ignore = "kink"]
    fn a_killed_mutation_caches_its_killer_and_a_second_run_runs_only_that_program() {
        // The cold run, shared with the other tests of this binary (`flow_support::after_cold`).
        let dir = scratch("warm").join("calc");
        let first = flow_support::after_cold("calc", "FLOW.toml", "MUTATIONS.toml", &dir);
        let manifest = dir.join("FLOW.toml");
        let mutations = manifest.with_file_name("MUTATIONS.toml");
        assert_eq!(
            verdicts(&first),
            CALC_VERDICTS
                .iter()
                .map(|(id, status, killer)| (
                    (*id).to_owned(),
                    (*status).to_owned(),
                    killer.map(str::to_owned),
                    false
                ))
                .collect::<Vec<_>>()
        );
        // Cold cache: one call over every comparable program, those reaching the edited rule
        // first; under FirstKill the mutant stops at its first kill.
        assert_eq!(
            calls(&first, "add-becomes-sub"),
            vec![strings(&["add", "nested", "inline", "sub"])]
        );
        assert_eq!(
            executed(&first, "add-becomes-sub"),
            pairs(&[("add", "distinguish")])
        );
        assert_eq!(
            mutation(&first, "add-becomes-sub")["reaching"],
            json!(["add", "nested", "inline"])
        );
        // The killer cache holds exactly the killed mutations, each with its first killing test
        // and that program's digest; the survivor has no entry.
        let mut entries = killers(&manifest, &first)
            .into_iter()
            .map(|(key, mutation, program, program_digest)| {
                assert_eq!(key, hint_key_of(&manifest, &mutation));
                assert_eq!(program_digest, self::program_digest(&first, &program));
                (mutation, program)
            })
            .collect::<Vec<_>>();
        entries.sort();
        assert_eq!(
            entries,
            vec![
                ("add-becomes-sub".to_owned(), "add".to_owned()),
                ("mul-becomes-add".to_owned(), "nested".to_owned()),
                ("no-mul".to_owned(), "nested".to_owned()),
                ("sub-off-by-one".to_owned(), "sub".to_owned()),
            ]
        );
        assert_eq!(killer_of(&manifest, &first, "add-swaps-operands"), None);
        // The report file is the document.
        let report: Value = serde_json::from_str(
            &fs::read_to_string(cache_of(&manifest).join(REPORT_FILE)).unwrap(),
        )
        .unwrap();
        assert_eq!(report, first);
        assert_eq!(
            first["counts"],
            json!({"killed": 4, "survived": 1, "equivalent": 0, "invalid": 0, "timeout": 0,
                   "unknown": 0, "error": 0, "invalid-mutation": 0})
        );

        // Warm cache: a killed mutation costs one campaign call over one program, whose baseline
        // and mutant run once each; the survivor is scanned again. (Tier 1 is deleted: with it,
        // a killed mutation and the survivor cost no call at all; tests/outcomes.rs.)
        forget_outcomes(&manifest);
        let (second, ok) = search(&manifest, &mutations, &[]);
        assert!(ok, "{second:#}");
        assert_eq!(
            verdicts(&second),
            CALC_VERDICTS
                .iter()
                .map(|(id, status, killer)| (
                    (*id).to_owned(),
                    (*status).to_owned(),
                    killer.map(str::to_owned),
                    killer.is_some()
                ))
                .collect::<Vec<_>>()
        );
        for (id, _, killer) in CALC_VERDICTS {
            if let Some(killer) = killer {
                assert_eq!(calls(&second, id), vec![strings(&[killer])], "{id}");
                assert_eq!(
                    executed(&second, id),
                    pairs(&[(killer, "distinguish")]),
                    "{id}"
                );
            }
        }
        assert_eq!(
            calls(&second, "add-swaps-operands"),
            vec![strings(&["add", "nested", "inline", "sub"])]
        );
        assert_eq!(killers(&manifest, &second), killers(&manifest, &first));
    }

    #[test]
    #[ignore = "kink"]
    fn a_timeout_is_never_cached_and_a_later_clean_kill_is() {
        let manifest = fixture("loop", "timeout").join("FLOW-search.toml");
        let mutations = manifest.with_file_name("MUTATIONS.toml");
        // countdown(3) never ends on the mutant (3 steps to 3); twice(4) does not reach the
        // countdown rule and agrees. The status is the runner's Timeout, and nothing is cached.
        let (first, ok) = search(&manifest, &mutations, &[]);
        assert!(ok, "{first:#}");
        assert_eq!(
            verdicts(&first),
            expect(&[("countdown-escapes", "timeout", None, false)])
        );
        assert_eq!(
            executed(&first, "countdown-escapes"),
            pairs(&[("countdown", "timeout"), ("twice", "agree")])
        );
        assert!(killers(&manifest, &first).is_empty());

        // A hand-made entry naming the program that times out: the cached call is a timeout, so
        // the entry is removed and the full call decides. Its status stays Timeout: a stale entry
        // never turns the verdict into the status of the other programs alone.
        let countdown = program_digest(&first, "countdown");
        set_killer(
            &manifest,
            &first,
            "countdown-escapes",
            "countdown",
            &countdown,
        );
        forget_outcomes(&manifest);
        let (stale, ok) = search(&manifest, &mutations, &[]);
        assert!(ok);
        assert_eq!(
            verdicts(&stale),
            expect(&[("countdown-escapes", "timeout", None, false)])
        );
        assert_eq!(
            calls(&stale, "countdown-escapes"),
            vec![strings(&["countdown"]), strings(&["countdown", "twice"])]
        );
        assert!(killers(&manifest, &stale).is_empty());

        // countdown(1) ends at countdown(-1) on the mutant and at 0 on the baseline. It runs
        // after the program that times out, and FirstKill folds the clean kill above the
        // timeout: Killed, with countdown-one cached.
        append(
            &manifest,
            "\n[[program]]\nid = \"countdown-one\"\ntext = \"countdown(1)\"\n",
        );
        forget_outcomes(&manifest);
        let (second, ok) = search(&manifest, &mutations, &[]);
        assert!(ok, "{second:#}");
        assert_eq!(
            verdicts(&second),
            expect(&[("countdown-escapes", "killed", Some("countdown-one"), false)])
        );
        assert_eq!(
            executed(&second, "countdown-escapes"),
            pairs(&[("countdown", "timeout"), ("countdown-one", "distinguish")])
        );
        assert_eq!(
            killer_of(&manifest, &second, "countdown-escapes")
                .unwrap()
                .0,
            "countdown-one"
        );
        forget_outcomes(&manifest);
        let (third, ok) = search(&manifest, &mutations, &[]);
        assert!(ok);
        assert_eq!(
            verdicts(&third),
            expect(&[("countdown-escapes", "killed", Some("countdown-one"), true)])
        );
        assert_eq!(
            calls(&third, "countdown-escapes"),
            vec![strings(&["countdown-one"])]
        );

        // A cached killer that times out never keeps its entry: the full call decides again.
        set_killer(
            &manifest,
            &third,
            "countdown-escapes",
            "countdown",
            &countdown,
        );
        forget_outcomes(&manifest);
        let (fourth, ok) = search(&manifest, &mutations, &[]);
        assert!(ok);
        assert_eq!(
            verdicts(&fourth),
            expect(&[("countdown-escapes", "killed", Some("countdown-one"), false)])
        );
        assert_eq!(
            calls(&fourth, "countdown-escapes"),
            vec![
                strings(&["countdown"]),
                strings(&["countdown", "countdown-one", "twice"])
            ]
        );
        assert_eq!(
            killer_of(&manifest, &fourth, "countdown-escapes")
                .unwrap()
                .0,
            "countdown-one"
        );
    }

    #[test]
    #[ignore = "kink"]
    fn a_baseline_mismatch_stops_the_run_without_a_verdict() {
        // Cold killer cache: the first call over every comparable program finds that add's
        // baseline run no longer has its cached run digest.
        let manifest = fixture("calc", "mismatch-cold").join("FLOW.toml");
        let mutations = manifest.with_file_name("MUTATIONS.toml");
        let (filled, status) = results(&manifest, &ResultsOptions::default());
        assert_eq!(status, EXIT_OK);
        let filled = json!({"spec": filled["spec"], "programs": filled["programs"]});
        corrupt_run_digest(&manifest, &filled, "add");
        let (document, ok) = search(&manifest, &mutations, &[]);
        assert!(!ok);
        assert_eq!(
            verdicts(&document),
            expect(&[("add-becomes-sub", "error", None, false)])
        );
        assert_eq!(
            mutation(&document, "add-becomes-sub")["reason"],
            json!("baseline-mismatch:add")
        );
        assert_eq!(
            document["stopped"],
            json!({"mutation": "add-becomes-sub", "reason": "baseline-mismatch:add"})
        );
        // Since F-14 the hints are written after a corpus error too (F-05 review 1 minor 3): the
        // file holds no hint.
        assert!(killers_file(&manifest).is_file());
        assert!(killers(&manifest, &filled).is_empty());

        // Warm killer cache: the one-program call over a cached killer checks its baseline too.
        // The mutations before it keep their verdicts; its entry is not touched.
        let manifest = fixture("calc", "mismatch-warm").join("FLOW.toml");
        let (warm, ok) = search(&manifest, &mutations, &[]);
        assert!(ok);
        let before = killers(&manifest, &warm);
        corrupt_run_digest(&manifest, &warm, "nested");
        forget_outcomes(&manifest);
        let (document, ok) = search(&manifest, &mutations, &[]);
        assert!(!ok);
        assert_eq!(
            verdicts(&document),
            expect(&[
                ("add-becomes-sub", "killed", Some("add"), true),
                ("sub-off-by-one", "killed", Some("sub"), true),
                ("mul-becomes-add", "error", None, false),
            ])
        );
        assert_eq!(
            mutation(&document, "mul-becomes-add")["reason"],
            json!("baseline-mismatch:nested")
        );
        assert_eq!(
            calls(&document, "mul-becomes-add"),
            vec![strings(&["nested"])]
        );
        assert_eq!(killers(&manifest, &document), before);
        let report: Value = serde_json::from_str(
            &fs::read_to_string(cache_of(&manifest).join(REPORT_FILE)).unwrap(),
        )
        .unwrap();
        assert_eq!(report, document);
    }

    #[test]
    #[ignore = "kink"]
    fn a_wrong_or_stale_killer_entry_changes_cost_but_never_the_verdict() {
        let manifest = fixture("calc", "stale").join("FLOW.toml");
        let mutations = manifest.with_file_name("MUTATIONS.toml");
        let only = ["add-becomes-sub", "add-swaps-operands"];
        let (first, _) = search(&manifest, &mutations, &only);
        assert_eq!(
            killer_of(&manifest, &first, "add-becomes-sub").unwrap().0,
            "add"
        );

        // An entry naming a comparable program that does not kill: one call over it alone, then
        // the entry is removed and the call a cold cache makes decides; the new killer replaces
        // the entry.
        let sub = program_digest(&first, "sub");
        set_killer(&manifest, &first, "add-becomes-sub", "sub", &sub);
        // An entry for the survivor naming a program that does not kill it.
        let add = program_digest(&first, "add");
        set_killer(&manifest, &first, "add-swaps-operands", "add", &add);
        forget_outcomes(&manifest);
        let (second, ok) = search(&manifest, &mutations, &only);
        assert!(ok, "{second:#}");
        assert_eq!(
            verdicts(&second),
            expect(&[
                ("add-becomes-sub", "killed", Some("add"), false),
                ("add-swaps-operands", "survived", None, false),
            ])
        );
        assert_eq!(
            calls(&second, "add-becomes-sub"),
            vec![
                strings(&["sub"]),
                strings(&["add", "nested", "inline", "sub"])
            ]
        );
        assert_eq!(
            executed(&second, "add-becomes-sub"),
            pairs(&[("sub", "agree"), ("add", "distinguish")])
        );
        assert_eq!(
            calls(&second, "add-swaps-operands"),
            vec![
                strings(&["add"]),
                strings(&["add", "nested", "inline", "sub"])
            ]
        );
        assert_eq!(
            killer_of(&manifest, &second, "add-becomes-sub"),
            Some(("add".to_owned(), add.clone()))
        );
        assert_eq!(killer_of(&manifest, &second, "add-swaps-operands"), None);

        // Entries naming a program that no longer exists, or a program whose digest changed, are
        // ignored and removed: the mutation is scanned as with a cold cache. Since F-14 a hint
        // names a program by its digest (a renamed program keeps its hint), so both entries name
        // a digest no program of the corpus has.
        let gone = "f".repeat(64);
        set_killer(&manifest, &first, "add-becomes-sub", "gone", &gone);
        forget_outcomes(&manifest);
        let (third, ok) = search(&manifest, &mutations, &["add-becomes-sub"]);
        assert!(ok);
        assert_eq!(
            verdicts(&third),
            expect(&[("add-becomes-sub", "killed", Some("add"), false)])
        );
        assert!(mutation(&third, "add-becomes-sub")["stale_killer"].is_string());
        assert_eq!(
            calls(&third, "add-becomes-sub"),
            vec![strings(&["add", "nested", "inline", "sub"])]
        );
        let changed = "1".repeat(64);
        set_killer(&manifest, &first, "add-becomes-sub", "add", &changed);
        forget_outcomes(&manifest);
        let (fourth, ok) = search(&manifest, &mutations, &["add-becomes-sub"]);
        assert!(ok);
        assert_eq!(
            verdicts(&fourth),
            expect(&[("add-becomes-sub", "killed", Some("add"), false)])
        );
        assert_eq!(
            calls(&fourth, "add-becomes-sub"),
            vec![strings(&["add", "nested", "inline", "sub"])]
        );
        assert_eq!(
            killer_of(&manifest, &fourth, "add-becomes-sub"),
            Some(("add".to_owned(), add))
        );

        // A killer cache file that does not parse is empty, and is replaced.
        fs::write(killers_file(&manifest), "{ not json").unwrap();
        forget_outcomes(&manifest);
        let (fifth, ok) = search(&manifest, &mutations, &["add-becomes-sub"]);
        assert!(ok);
        assert_eq!(
            verdicts(&fifth),
            expect(&[("add-becomes-sub", "killed", Some("add"), false)])
        );
        assert_eq!(
            killer_of(&manifest, &fifth, "add-becomes-sub").unwrap().0,
            "add"
        );
    }
}
