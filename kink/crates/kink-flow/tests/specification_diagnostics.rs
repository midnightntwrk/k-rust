//! Re-pin adoption A-1 (`draft/tasks/repin-58720d2e/ADOPTION.md` section 2.2, deliverable 3):
//! k-rust's contradicted-claim records are reported as specification diagnostics, on a program's
//! baseline in the results document and the run document (`programs`, from the result record),
//! and on a mutant in its row's executed entry. Each record excludes its run; none is evidence.
//! Re-pin adoption A-1b (review A-1-review-1 finding 1): the cause of a baseline excluded this
//! way names the exclusion and, for a contradicted claim, points at the row's specification
//! diagnostics, instead of a hint read from the leaves' shape.

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
/// only k-rust's list holds the record (k-rust's own example). `ok X` uses no claim. `tv 0` steps
/// to `val(td(0))` with no sibling: its one leaf is `Trivial` and names the contradicted claim.
const SPEC: &str = r#"
module SPEC-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= "sib" Int [symbol(sib)]
                | "ok" Int [symbol(ok)]
                | "tv" Int [symbol(tv)]
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
  rule [tv]: <k> tv X => val(td(X)) </k>
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

/// The leaf-shape hint `results` gives a refused baseline whose leaves all ended and that no
/// exclusion explains: never the cause of an excluded baseline.
const LEAF_SHAPE_HINT: &str = "a final configuration is not a value kink can compare";

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

mod kink_tier {
    use super::*;

    /// Review A-1-review-1 finding 1: an excluded baseline's cause says the exclusion, not that its
    /// final configuration is not comparable. `sib 0` (the record on k-rust's list alone, its one
    /// leaf the plain value `done`: the campaign refuses the baseline) and `tv 0` (a leaf contradiction:
    /// admitted, no sides) point at the specification diagnostics and say to fix the claim; `runh 1`
    /// (testdata/k/a1/refusals.k: an unsupported hook on the list alone, its leaf the value `val(2)`)
    /// names its own exclusion. Before A-1b each of the three gave the leaf-shape hint.
    #[test]
    #[ignore = "kink"]
    fn an_excluded_baseline_names_its_exclusion() {
        let dir = scratch("causes");
        fs::write(
            dir.join("FLOW.toml"),
            FLOW.replace(
                "id = \"ok-1\"\ntext = \"ok 1\"",
                "id = \"tv-0\"\ntext = \"tv 0\"",
            ),
        )
        .unwrap();
        let (document, exit) = results(
            &dir.join("FLOW.toml"),
            &ResultsOptions {
                verify: false,
                cache: None,
                mutations: None,
            },
        );
        assert_eq!(exit, EXIT_OK, "{document:#}");
        let sib = program(&document, "sib-0");
        assert_eq!(sib["class"], "unknown", "{sib:#}");
        let cause = sib["cause"].as_str().unwrap();
        assert!(
            cause.starts_with(
                "the campaign runner refused the baseline run (BaselineOracleFailed: the baseline run \
                 of test sib-0 is no evidence: contradicted-claim); the run is excluded \
                 (contradicted-claim): the run contradicts a trusted claim of the definition: k-rust \
                 lists a contradicted claim"
            ),
            "{cause}"
        );
        assert!(
            cause.contains("in this row's specification_diagnostics"),
            "{cause}"
        );
        assert!(cause.contains("fix the claim"), "{cause}");
        assert!(!cause.contains(LEAF_SHAPE_HINT), "{cause}");
        assert_sib_record(&sib["specification_diagnostics"], "SPEC.sibtd");

        let tv = program(&document, "tv-0");
        assert_eq!(tv["class"], "unknown", "{tv:#}");
        let cause = tv["cause"].as_str().unwrap();
        assert!(
            cause.starts_with(
                "the campaign runner gave the baseline run no sides: contradicted-claim; the run is \
                 excluded (contradicted-claim): the run contradicts a trusted claim of the definition"
            ),
            "{cause}"
        );
        assert!(cause.contains("specification_diagnostics"), "{cause}");
        assert!(cause.contains("fix the claim"), "{cause}");
        assert!(!cause.contains(LEAF_SHAPE_HINT), "{cause}");

        let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("kink-flow-specification-{}", std::process::id()))
            .join("unsupported");
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        fs::copy(
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/k/a1/refusals.k"),
            dir.join("refusals.k"),
        )
        .unwrap();
        fs::write(
            dir.join("FLOW.toml"),
            "[spec]\nentry = \"refusals.k\"\nmain_module = \"REFUSALS\"\n\
             syntax_module = \"REFUSALS-SYNTAX\"\n\n[[program]]\nid = \"runh-1\"\ntext = \"runh(1)\"\n",
        )
        .unwrap();
        let (document, exit) = results(
            &dir.join("FLOW.toml"),
            &ResultsOptions {
                verify: false,
                cache: None,
                mutations: None,
            },
        );
        assert_eq!(exit, EXIT_OK, "{document:#}");
        let runh = program(&document, "runh-1");
        assert_eq!(runh["class"], "unknown", "{runh:#}");
        let cause = runh["cause"].as_str().unwrap();
        assert!(
            cause.starts_with(
                "the campaign runner refused the baseline run (BaselineOracleFailed: the baseline run \
                 of test runh-1 is no evidence: unsupported-hook); the run is excluded \
                 (unsupported-hook): "
            ),
            "{cause}"
        );
        assert!(!cause.contains(LEAF_SHAPE_HINT), "{cause}");
        assert_eq!(runh["specification_diagnostics"], serde_json::json!([]));
    }

    #[test]
    #[ignore = "kink"]
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
        assert_eq!(document["version"], 10);
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
}
