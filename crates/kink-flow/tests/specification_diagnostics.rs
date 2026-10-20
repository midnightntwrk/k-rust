//! Re-pin adoption A-1 (`draft/tasks/repin-58720d2e/ADOPTION.md` section 2.2, deliverable 3):
//! k-rust's contradicted-claim records are reported as specification diagnostics, on a program's
//! baseline in the results document and the run document (`programs`, from the result record),
//! and on a mutant in its row's executed entry. Each record excludes its run; none is evidence.

use kink_flow::{
    FlowManifest, MutationList,
    cli::{EXIT_OK, results},
    results::ResultsOptions,
    search::{ProgramOrder, RunOptions, run},
};
use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
};

/// `td` is declared total but divides by its argument, so the claim is false at 0. On `sib 0` the
/// candidate `val(td(0))` is undefined beside the defined `sibok`: the one leaf `done` is clean and
/// only k-rust's list holds the record (k-rust's own example). `ok X` uses no claim.
const SPEC: &str = r#"
module SPEC-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= "sib" Int [symbol(sib)]
                | "ok" Int [symbol(ok)]
                | val(Int) [symbol(val)]
                | "done" [symbol(done)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule
module SPEC
  imports SPEC-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int I
  rule [sibtd]: <k> sib X => val(td(X)) </k>
  rule [sibok]: <k> sib _ => done </k>
  rule [ok]: <k> ok X => val(X) </k>
endmodule
"#;

const FLOW: &str = r#"
[spec]
entry = "spec.k"
main_module = "SPEC"
syntax_module = "SPEC-SYNTAX"

[[program]]
id = "sib-0"
text = "sib 0"

[[program]]
id = "ok-1"
text = "ok 1"
"#;

/// The mutant keeps `td`'s `total` (its edit does not reach `td`) and on `ok 1` takes an undefined
/// step `val(td(0))` that names the contradicted claim.
const MUTATIONS: &str = r#"
[[mutation]]
id = "ok-through-td"

  [[mutation.edit]]
  rule = "ok"
  find = "val(X)"
  replace = "val(td(X -Int 1))"
"#;

fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-specification-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("spec.k"), SPEC).unwrap();
    fs::write(dir.join("FLOW.toml"), FLOW).unwrap();
    fs::write(dir.join("MUTATIONS.toml"), MUTATIONS).unwrap();
    dir
}

fn program<'a>(document: &'a Value, id: &str) -> &'a Value {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == id)
        .unwrap_or_else(|| panic!("no program {id}: {document:#}"))
}

/// The one record of `sib 0`'s baseline, as a specification diagnostic.
fn assert_sib_record(diagnostics: &Value, observing: &str) {
    let [record] = diagnostics.as_array().unwrap().as_slice() else {
        panic!("one record: {diagnostics:#}")
    };
    assert_eq!(record["claim"], "total");
    assert_eq!(record["k_label"], "td");
    assert_eq!(record["rule_label"], "SPEC.tdeq");
    assert_eq!(record["observing_rule_label"], observing);
    assert_eq!(record["ground"], true);
    assert_eq!(record["observed_in"], "run");
    assert!(
        record["says"]
            .as_str()
            .unwrap()
            .starts_with("the `total` claim of `td` is false at `"),
        "{record:#}"
    );
}

#[test]
fn records_are_reported_as_specification_diagnostics() {
    let dir = scratch("records");
    let manifest_path = dir.join("FLOW.toml");
    let (document, exit) = results(
        &manifest_path,
        &ResultsOptions {
            verify: false,
            cache: None,
            mutations: None,
        },
    );
    assert_eq!(exit, EXIT_OK, "{document:#}");
    // The baseline of `sib 0` is excluded by the record on its list alone, so the program is not
    // comparable, and its row names the record.
    let sib = program(&document, "sib-0");
    assert_eq!(sib["class"], "unknown", "{sib:#}");
    assert_sib_record(&sib["specification_diagnostics"], "SPEC.sibtd");
    assert_eq!(sib["smt_unknowns"], 0);
    let ok = program(&document, "ok-1");
    assert_eq!(ok["class"], "comparable", "{ok:#}");
    assert_eq!(ok["specification_diagnostics"], serde_json::json!([]));

    let manifest = FlowManifest::read(&manifest_path).unwrap();
    let list = MutationList::read(&dir.join("MUTATIONS.toml")).unwrap();
    let (document, _) = run(
        &manifest,
        &list,
        &RunOptions {
            only: Vec::new(),
            cache: None,
            order: ProgramOrder::Corpus,
            compile_workers: Some(1),
            memo: kink_flow::memo::MemoUse::On,
        },
    );
    assert_eq!(document["version"], 9);
    assert_sib_record(
        &program(&document, "sib-0")["specification_diagnostics"],
        "SPEC.sibtd",
    );
    let [row] = document["mutations"].as_array().unwrap().as_slice() else {
        panic!("one mutation: {document:#}")
    };
    assert_eq!(row["status"], "unknown", "{row:#}");
    let [entry] = row["executed"].as_array().unwrap().as_slice() else {
        panic!("one executed program: {row:#}")
    };
    assert_eq!(entry["program"], "ok-1");
    assert_eq!(entry["failure"], "contradicted-claim", "{entry:#}");
    let [record] = entry["specification_diagnostics"]
        .as_array()
        .unwrap()
        .as_slice()
    else {
        panic!("one record: {entry:#}")
    };
    assert_eq!(record["k_label"], "td");
    assert_eq!(record["observing_rule_label"], "SPEC.ok");
    assert_eq!(record["ground"], true);
}
