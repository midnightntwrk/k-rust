//! `krs kink compare`: other implementations of a corpus's system, run on every program and
//! compared with the definition under each of their views (kink-flow `compare`).
//!
//! The fixture counts down: `count` with `n` in its cell adds `n` to `acc` and lowers `n` by one
//! while `n > 0` (the rule `tick`), and ends when `n` is 0 (the rule `done`, which empties the
//! computation). The corpus stops before the third `tick`, so a case of `n = 2` ends on its own
//! (`final`, `n = 0`, `acc = 3`) and one of `n = 5` at the stop (`stopped`, `n = 3`, `acc = 9`).
//! `Parity` is a view of `acc`.
//!
//! The implementations are one shell script, `fake.sh`, whose first argument says how it
//! answers: `equal` computes the end as the definition does, `different` adds 2 to `acc` (a
//! different end, of the same parity), `farther` adds 4 (the same, differing farther),
//! `wrong-end` swaps `stopped` and `final`,
//! `could-not-apply` declines every program, `omit` leaves `acc` out of its answer, `crash` exits
//! 3, `garbage` prints no JSON, and `sleep` never answers. Its second argument, when given, is a
//! file it appends each request to. It never states the computation cell `k`, which each
//! declaration omits.

#![cfg(feature = "kink")]

use std::fs;
use std::path::Path;
use std::process::Output;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value, json};

const PACKAGE: &str = "krs-cli-kink-compare";

const LIBRARY: &str = r##"use k::builtin::{Int, KSequence};
use k::{KItem, Term};

k::sorts! {
    Op: KItem;
}

#[k::constructors(sort = Op, result = k::KResult)]
pub enum Step {
    #[k::syntax("#count")]
    Count,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub n: Int,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(n: Int) -> Self {
        Self {
            k: k::k![Step::Count],
            n,
            acc: 0,
        }
    }
}

/// The parity of a sum, a view of `acc`.
#[k::function(total, internal)]
pub fn Parity(value: Term<Int>) -> Term<Int> {
    value % 2
}

k::rules! {
    for Machine;

    #[k::requires(n > 0)]
    tick: {
        k: [Step::Count, ..],
        n,
        acc,
    } => {
        n: n - 1,
        acc: acc + n,
    };

    #[k::requires(n <= 0)]
    done: {
        k: [Step::Count, ..],
        n,
    } => {
        k: [..],
    };
}
"##;

/// The fake implementation (module documentation).
const FAKE: &str = r#"#!/bin/sh
mode=$1
request=$(cat)
if [ -n "$2" ]; then printf '%s\n' "$request" >> "$2"; fi
n=$(printf '%s' "$request" | sed -n 's/.*"inputs":{"n":\(-\{0,1\}[0-9]*\)}.*/\1/p')
count=$(printf '%s' "$request" | sed -n 's/.*"stop":{"count":\([0-9]*\)}.*/\1/p')
case $mode in
  crash) echo "fake: crashed" >&2; exit 3;;
  garbage) echo "not json"; exit 0;;
  sleep) exec sleep 30;;
  could-not-apply) printf '{"end":"could-not-apply","reason":"the fake applies no program"}\n'; exit 0;;
esac
acc=0
ticks=0
end=final
while [ "$n" -gt 0 ]; do
  if [ -n "$count" ] && [ "$ticks" -eq $((count - 1)) ]; then end=stopped; break; fi
  acc=$((acc + n)); n=$((n - 1)); ticks=$((ticks + 1))
done
case $mode in
  different) acc=$((acc + 2));;
  farther) acc=$((acc + 4));;
  wrong-end) if [ "$end" = final ]; then end=stopped; else end=final; fi;;
esac
if [ "$mode" = omit ]; then
  printf '{"end":"%s","cells":{"n":%s}}\n' "$end" "$n"
else
  printf '{"end":"%s","cells":{"n":%s,"acc":%s}}\n' "$end" "$n" "$acc"
fi
"#;

/// One `[[implementation]]` running the fake in `mode`, given `given`, with `views`.
fn implementation(name: &str, mode: &str, given: &str, views: &str) -> String {
    format!(
        "[[implementation]]\nname = \"{name}\"\ncommand = [\"sh\", \"fake.sh\", \"{mode}\"]\n\
         given = \"{given}\"\nomits = [\"k\"]\nviews = {views}\n\n"
    )
}

/// The views most implementations are compared under: every stated cell (required), and
/// `acc`'s parity (reported).
const VIEWS: &str = "[{ name = \"whole\", required = true }, { name = \"parity\", views = { acc = \
                     \"Parity\" } }]";

/// The main corpus's implementations.
fn main_implementations() -> String {
    let mut text = String::new();
    for (name, mode) in [
        ("equal", "equal"),
        ("different", "different"),
        ("wrong-end", "wrong-end"),
        ("could-not-apply", "could-not-apply"),
        ("crash", "crash"),
        ("garbage", "garbage"),
        ("missing", "omit"),
    ] {
        text.push_str(&implementation(name, mode, "inputs", VIEWS));
    }
    // The same answers, with only the parity required.
    text.push_str(&implementation(
        "reported",
        "different",
        "inputs",
        "[{ name = \"whole\" }, { name = \"parity\", views = { acc = \"Parity\" }, required = true }]",
    ));
    // A view of a cell the implementation omits.
    text.push_str(&implementation(
        "omitted-view",
        "equal",
        "inputs",
        "[{ name = \"computation\", compare = [\"k\"] }, { name = \"whole\", required = true }]",
    ));
    // Given the start, and recording its requests.
    text.push_str(
        "[[implementation]]\nname = \"start\"\ncommand = [\"sh\", \"fake.sh\", \"equal\", \
         \"requests.log\"]\ngiven = \"start\"\nomits = [\"k\"]\nidentity = { file = \"fake.sh\" \
         }\nviews = [{ name = \"whole\", required = true }]\n\n",
    );
    // An answer the clock cancels.
    text.push_str(
        "[[implementation]]\nname = \"slow\"\ncommand = [\"sh\", \"fake.sh\", \"sleep\"]\ngiven = \
         \"inputs\"\nomits = [\"k\"]\ntime_ms = 1500\nviews = [{ name = \"whole\", required = true \
         }]\n\n",
    );
    text
}

/// The package with its corpora, and the fixture target `krs` builds in.
struct Package {
    directory: TempDir,
    target: SharedFixtureTarget,
}

impl Package {
    fn new() -> Self {
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let directory = temp_dir();
        let package = Self {
            directory,
            target: shared_fixture_target(),
        };
        package.write("src/lib.rs", LIBRARY);
        package.write(
            "Cargo.toml",
            &format!(
                "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"COMPARE\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
                serde_json::to_string(krs.to_str().unwrap()).unwrap(),
            ),
        );
        package.corpus(
            "kink",
            &main_implementations(),
            &[("a", 2), ("b", 5), ("z", 0)],
        );
        package
    }

    fn write(&self, relative: &str, contents: &str) {
        let path = self.directory.path().join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    /// A corpus at `corpus` with `implementations` and one case document per `(name, n)`. The
    /// clock never decides a run of the definition.
    fn corpus(&self, corpus: &str, implementations: &str, cases: &[(&str, i64)]) {
        self.write(
            &format!("{corpus}/FLOW.toml"),
            &format!(
                "[spec]\nkrs = {{ definition = \"main\" }}\n\n[budget]\ntime_ms = 600000\n\n\
                 [stop]\nbefore = [\"crate::tick\"]\ncount = 3\n\n[[program]]\ncases = \
                 \"cases/*/case.toml\"\n\n{implementations}"
            ),
        );
        self.write(&format!("{corpus}/fake.sh"), FAKE);
        for (name, n) in cases {
            self.case(corpus, name, *n);
        }
    }

    fn case(&self, corpus: &str, name: &str, n: i64) {
        self.write(
            &format!("{corpus}/cases/{name}/case.toml"),
            &format!("[inputs]\nn = {n}\n"),
        );
    }

    /// `krs kink compare ARGUMENTS` on the corpus `corpus`.
    fn compare(&self, corpus: &str, arguments: &[&str]) -> Output {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        process
            .current_dir(self.directory.path())
            .args(["kink", "compare"])
            .args(arguments)
            .args(["--package", PACKAGE, "--definition", "main"]);
        if corpus != "kink" {
            process.args(["--corpus", corpus]);
        }
        process.output().unwrap()
    }
}

fn json_of(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

#[track_caller]
fn assert_status(output: &Output, code: i32) {
    assert_eq!(
        output.status.code(),
        Some(code),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// The row of `implementation` on `program`.
fn row<'d>(document: &'d Value, implementation: &str, program: &str) -> &'d Value {
    document["rows"]
        .as_array()
        .unwrap_or_else(|| panic!("{document:#}"))
        .iter()
        .find(|row| row["implementation"] == implementation && row["program"] == program)
        .unwrap_or_else(|| panic!("no row of {implementation} on {program}: {document:#}"))
}

/// The verdict of `view` in `row`.
fn verdict<'r>(row: &'r Value, view: &str) -> &'r Value {
    row["views"]
        .as_array()
        .unwrap_or_else(|| panic!("{row:#}"))
        .iter()
        .find(|entry| entry["view"] == view)
        .unwrap_or_else(|| panic!("no view {view}: {row:#}"))
}

const PROGRAMS: [&str; 3] = [
    "cases/a/case.toml",
    "cases/b/case.toml",
    "cases/z/case.toml",
];

/// The `--only` arguments that select `names`.
fn only<'a>(names: &[&'a str]) -> Vec<&'a str> {
    names.iter().flat_map(|name| ["--only", name]).collect()
}

/// Each answering implementation's verdicts on every program, the words included.
fn assert_verdicts(document: &Value) {
    for program in PROGRAMS {
        let equal = row(document, "equal", program);
        assert_eq!(equal["failure"], Value::Null, "{equal:#}");
        assert_eq!(verdict(equal, "whole")["verdict"], "equal", "{equal:#}");
        assert_eq!(
            verdict(equal, "whole")["omitted"],
            json!(["k"]),
            "{equal:#}"
        );
        assert_eq!(verdict(equal, "parity")["verdict"], "equal", "{equal:#}");

        let different = row(document, "different", program);
        let whole = verdict(different, "whole");
        assert_eq!(whole["verdict"], "different", "{different:#}");
        assert!(
            whole["difference"].to_string().contains("acc"),
            "the first difference is at `acc`: {whole:#}"
        );
        assert_eq!(
            verdict(different, "parity")["verdict"],
            "equal",
            "{different:#}"
        );

        let declined = row(document, "could-not-apply", program);
        assert_eq!(declined["answer"]["end"], "could-not-apply", "{declined:#}");
        assert_eq!(verdict(declined, "whole")["verdict"], "could-not-apply");
        assert_eq!(
            verdict(declined, "whole")["detail"],
            "the fake applies no program"
        );

        let omitted = row(document, "omitted-view", program);
        let computation = verdict(omitted, "computation");
        assert_eq!(computation["verdict"], "not-compared", "{omitted:#}");
        assert_eq!(computation["reason"], "omitted", "{omitted:#}");
        assert_eq!(verdict(omitted, "whole")["verdict"], "equal", "{omitted:#}");

        assert_eq!(
            verdict(row(document, "start", program), "whole")["verdict"],
            "equal"
        );
    }
    // The words: `a` ends on its own, `b` at the stop.
    assert_eq!(
        row(document, "equal", PROGRAMS[0])["answer"]["end"],
        "final"
    );
    assert_eq!(
        row(document, "equal", PROGRAMS[1])["answer"]["end"],
        "stopped"
    );
    let swapped = verdict(row(document, "wrong-end", PROGRAMS[1]), "whole");
    assert_eq!(swapped["verdict"], "different", "{swapped:#}");
    assert_eq!(
        swapped["difference"],
        json!({"format": "kink-end/1", "at": "end", "definition": "stopped", "implementation": "final"})
    );
}

/// Failures of the implementation are no verdicts.
fn assert_failures(document: &Value) {
    let crash = row(document, "crash", PROGRAMS[0]);
    assert_eq!(crash["failure"]["kind"], "exit", "{crash:#}");
    assert_eq!(crash["failure"]["exit_code"], 3, "{crash:#}");
    assert!(
        crash["failure"]["stderr"]
            .as_str()
            .unwrap()
            .contains("fake: crashed")
    );
    assert_eq!(crash["views"], json!([]), "{crash:#}");
    let garbage = row(document, "garbage", PROGRAMS[0]);
    assert_eq!(garbage["failure"]["kind"], "malformed", "{garbage:#}");
    let missing = row(document, "missing", PROGRAMS[0]);
    assert_eq!(missing["failure"]["kind"], "malformed", "{missing:#}");
    assert!(
        missing["failure"]["detail"]
            .as_str()
            .unwrap()
            .contains("acc"),
        "the refusal names the unstated cell: {missing:#}"
    );
    let slow = row(document, "slow", PROGRAMS[0]);
    assert_eq!(slow["failure"]["kind"], "timeout", "{slow:#}");
}

/// The start's request: the program, its inputs as typed values, the stop's count and the
/// definition's start; and the identity's digest.
fn assert_start_request(package: &Package, document: &Value) {
    let requests = fs::read_to_string(package.directory.path().join("kink/requests.log")).unwrap();
    let request: Value = requests
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).unwrap())
        .find(|request| request["program"] == PROGRAMS[1])
        .unwrap();
    assert_eq!(request["protocol"], "kink-implementation/1");
    assert_eq!(request["inputs"], json!({"n": 5}), "{request:#}");
    assert_eq!(request["stop"], json!({"count": 3}), "{request:#}");
    assert_eq!(request["start"]["n"], 5, "{request:#}");
    assert_eq!(request["start"]["acc"], 0, "{request:#}");
    assert!(
        request["start"].get("k").is_some(),
        "the start states every cell: {request:#}"
    );
    let start = document["implementations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|implementation| implementation["name"] == "start")
        .unwrap();
    assert_eq!(start["identity"]["file"], "fake.sh");
    assert_eq!(
        start["identity"]["sha256"].as_str().map(str::len),
        Some(64),
        "{start:#}"
    );
}

/// Every verdict, every failure, and the exit policy: only a required view decides.
#[test]
fn each_implementation_is_compared_under_each_view() {
    let package = Package::new();
    let output = package.compare("kink", &[]);
    // `crash`, `garbage` and `missing` fail with a required view: the question is unasked.
    assert_status(&output, 2);
    let document = json_of(&output);
    assert_eq!(document["schema"], "kink-flow-compare", "{document:#}");
    assert_eq!(document["protocol"], "kink-implementation/1");
    assert_eq!(
        document["programs"].as_array().map(|programs| programs
            .iter()
            .map(|p| p["class"].clone())
            .collect::<Vec<_>>()),
        Some(vec![json!("comparable"); 3]),
        "{document:#}"
    );

    assert_verdicts(&document);
    assert_failures(&document);
    assert_start_request(&package, &document);

    // Only a required view decides the status.
    let answered = package.compare(
        "kink",
        &only(&[
            "equal",
            "reported",
            "could-not-apply",
            "omitted-view",
            "start",
        ]),
    );
    assert_status(&answered, 0);
    assert_status(&package.compare("kink", &only(&["different"])), 1);
    assert_status(&package.compare("kink", &only(&["slow"])), 3);

    // One line per verdict.
    let text = package.compare(
        "kink",
        &[&only(&["different"])[..], &["--output", "text"]].concat(),
    );
    assert_status(&text, 1);
    let text = String::from_utf8(text.stdout).unwrap();
    assert!(
        text.contains("different cases/a/case.toml whole (required): different")
            && text.contains("different cases/a/case.toml parity (reported): equal"),
        "{text}"
    );

    // An implementation the manifest does not declare.
    let unknown = package.compare("kink", &only(&["nope"]));
    assert_status(&unknown, 2);
    assert_eq!(
        json_of(&unknown)["refusal"]["reason"],
        "unknown-implementation"
    );
}

/// A case added to the corpus is compared with no other edit.
#[test]
fn a_new_case_is_compared_with_no_other_edit() {
    let package = Package::new();
    package.corpus(
        "corpora/grow",
        &implementation("equal", "equal", "inputs", VIEWS),
        &[("a", 2)],
    );
    let first = package.compare("corpora/grow", &[]);
    assert_status(&first, 0);
    assert_eq!(json_of(&first)["rows"].as_array().map(Vec::len), Some(1));
    package.case("corpora/grow", "c", 4);
    let second = package.compare("corpora/grow", &[]);
    assert_status(&second, 0);
    let document = json_of(&second);
    assert_eq!(
        document["rows"].as_array().map(Vec::len),
        Some(2),
        "{document:#}"
    );
    let added = row(&document, "equal", "cases/c/case.toml");
    assert_eq!(verdict(added, "whole")["verdict"], "equal", "{added:#}");
}

/// A declaration the definition refutes, or one that does not decode, is refused before any run.
#[test]
fn a_declaration_is_checked_before_any_run() {
    let package = Package::new();
    package.corpus(
        "corpora/unknown-cell",
        "[[implementation]]\nname = \"x\"\ncommand = [\"sh\", \"fake.sh\", \"equal\"]\ngiven = \
         \"inputs\"\nomits = [\"nope\"]\nviews = [{ name = \"whole\" }]\n",
        &[("a", 2)],
    );
    let output = package.compare("corpora/unknown-cell", &[]);
    assert_status(&output, 2);
    let refusal = &json_of(&output)["refusal"];
    assert_eq!(refusal["reason"], "declaration", "{refusal:#}");
    assert!(
        refusal["detail"]
            .as_str()
            .unwrap()
            .contains("`nope` is no cell"),
        "{refusal:#}"
    );

    package.corpus(
        "corpora/bad-given",
        "[[implementation]]\nname = \"x\"\ncommand = [\"sh\"]\ngiven = \"both\"\nviews = [{ name \
         = \"whole\" }]\n",
        &[("a", 2)],
    );
    let output = package.compare("corpora/bad-given", &[]);
    assert_status(&output, 2);
    let document = json_of(&output);
    assert!(
        document.to_string().contains("implementation[0].given"),
        "{document:#}"
    );
}

/// The implementations of the record's corpus: `logged` (no `identity`, recording each request it
/// is given in `logged.log`), `named` (given the start, with `identity`, recording in
/// `named.log`), both answering as the definition does, and `reported`, answering in
/// `reported` mode, whose `whole` view is reported and `parity` required. `logged` is cancelled
/// after `time_ms` when its mode is `sleep`.
fn record_implementations(logged: &str, reported: &str) -> String {
    format!(
        "[[implementation]]\nname = \"logged\"\ncommand = [\"sh\", \"fake.sh\", \"{logged}\", \
         \"logged.log\"]\ngiven = \"inputs\"\nomits = [\"k\"]\ntime_ms = 1500\nviews = \
         {VIEWS}\n\n[[implementation]]\nname = \"named\"\ncommand = [\"sh\", \"fake.sh\", \
         \"equal\", \"named.log\"]\ngiven = \"start\"\nomits = [\"k\"]\nidentity = {{ file = \
         \"fake.sh\" }}\nviews = [{{ name = \"whole\", required = true }}]\n\n{}",
        implementation(
            "reported",
            reported,
            "inputs",
            "[{ name = \"whole\" }, { name = \"parity\", views = { acc = \"Parity\" }, required = \
             true }]",
        )
    )
}

/// The record's other sections, as another command wrote them and a hand edited them.
const OTHER_SECTIONS: &str = "[run]\n# kept by hand\nversion = 25\nprofile = \"z3\"\n\n\
                              [[run.mutation]]\nid = \"m\"\nstatus = \"survived\"\n\n[coverage]\n\
                              version = 25\n\n[coverage.rules]\nopen = [\n]\n";

/// How many requests the log `name` of the corpus holds: one per run of its implementation.
fn runs(package: &Package, corpus: &str, name: &str) -> usize {
    fs::read_to_string(package.directory.path().join(corpus).join(name))
        .map_or(0, |log| log.lines().count())
}

/// The verdicts are the corpus record's `[compare]` section: `compare` writes it after the
/// other sections, keeping them byte for byte; `--locked` finds it current; an implementation
/// with `identity` is not run again for the same request, one without it always is; a reported
/// view whose first difference moves makes `--locked` exit 1; and a run the clock cancels under
/// `--locked` is not decided on this host (exit 3), leaving the rows as recorded.
#[test]
fn the_verdicts_are_the_corpus_records_compare_section() {
    let package = Package::new();
    let corpus = "corpora/record";
    package.corpus(
        corpus,
        &record_implementations("equal", "different"),
        &[("a", 2), ("b", 5)],
    );
    let record = package.directory.path().join(corpus).join("kink.lock");
    let other = format!("{}\n{OTHER_SECTIONS}", kink_flow::verdicts::record_header());
    fs::write(&record, &other).unwrap();

    // A write: the section follows the others, which are kept as they were.
    let first = package.compare(corpus, &[]);
    assert_status(&first, 0);
    let document = json_of(&first);
    assert_eq!(document["lock"]["status"], "created", "{document:#}");
    assert_eq!(document["lock"]["path"], "corpora/record/kink.lock");
    let written = fs::read_to_string(&record).unwrap();
    let section = written
        .strip_prefix(&format!("{other}\n"))
        .unwrap_or_else(|| panic!("the other sections are kept byte for byte:\n{written}"));
    assert!(section.starts_with("[compare]\n"), "{section}");
    assert!(
        section.contains("protocol = \"kink-implementation/1\"\n"),
        "{section}"
    );
    let rows = section
        .lines()
        .filter(|line| *line == "[[compare.verdict]]")
        .count();
    // `logged` and `reported` with two views, `named` with one, on two cases.
    assert_eq!(rows, 10, "{section}");
    let identity = document["implementations"][1]["identity"]["sha256"]
        .as_str()
        .unwrap();
    assert!(
        section.contains(&format!(
            "implementation = \"named\"\nprogram = \"cases/a/case.toml\"\nview = \
             \"whole\"\nrequired = true\nverdict = \"equal\"\nrequest_sha256 = \"{}\"\n\
             identity_sha256 = \"{identity}\"\n",
            row(&document, "named", "cases/a/case.toml")["request_sha256"]
                .as_str()
                .unwrap()
        )),
        "{section}"
    );
    assert!(
        section.contains(
            "implementation = \"reported\"\nprogram = \"cases/a/case.toml\"\nview = \
             \"whole\"\nrequired = false\nverdict = \"different\"\ndifference = '{"
        ),
        "the reported view's first difference is recorded: {section}"
    );
    assert_eq!(
        (
            runs(&package, corpus, "logged.log"),
            runs(&package, corpus, "named.log")
        ),
        (2, 2)
    );

    // `--locked` finds it current; `named` is answered from the cache, `logged` runs again.
    let locked = package.compare(corpus, &["--locked"]);
    assert_status(&locked, 0);
    let document = json_of(&locked);
    assert_eq!(document["lock"]["status"], "unchanged", "{document:#}");
    assert_eq!(fs::read_to_string(&record).unwrap(), written);
    assert_eq!(
        (
            runs(&package, corpus, "logged.log"),
            runs(&package, corpus, "named.log")
        ),
        (4, 2)
    );
    assert_eq!(row(&document, "named", "cases/b/case.toml")["cached"], true);
    assert_eq!(
        row(&document, "logged", "cases/b/case.toml")["cached"],
        false
    );

    let rewritten = assert_a_moved_difference_is_stale(&package, corpus, &other, &written);
    assert_a_cancelled_run_keeps_its_rows(&package, corpus, &rewritten);
}

/// A reported view whose first difference moved is a lock difference under `--locked`, which
/// writes nothing; a run without it rewrites the section, which is then current. The record's
/// text after the rewrite.
fn assert_a_moved_difference_is_stale(
    package: &Package,
    corpus: &str,
    other: &str,
    written: &str,
) -> String {
    let record = package.directory.path().join(corpus).join("kink.lock");
    package.write(
        &format!("{corpus}/FLOW.toml"),
        &fs::read_to_string(package.directory.path().join(corpus).join("FLOW.toml"))
            .unwrap()
            .replace("\"fake.sh\", \"different\"", "\"fake.sh\", \"farther\""),
    );
    let moved = package.compare(corpus, &["--locked"]);
    assert_status(&moved, 1);
    let document = json_of(&moved);
    assert_eq!(document["lock"]["status"], "stale", "{document:#}");
    assert_eq!(
        verdict(row(&document, "reported", "cases/a/case.toml"), "parity")["verdict"],
        "equal"
    );
    let stderr = String::from_utf8_lossy(&moved.stderr);
    assert!(
        stderr.contains("reported cases/a/case.toml whole: different: its first difference moved"),
        "{stderr}"
    );
    assert_eq!(fs::read_to_string(&record).unwrap(), written);
    // A run without `--locked` rewrites the section, and the record is current again.
    let rewrite = package.compare(corpus, &[]);
    assert_status(&rewrite, 0);
    assert_eq!(json_of(&rewrite)["lock"]["status"], "written");
    let rewritten = fs::read_to_string(&record).unwrap();
    assert!(rewritten.starts_with(&format!("{other}\n[compare]\n")));
    assert_ne!(rewritten, written);
    assert_status(&package.compare(corpus, &["--locked"]), 0);
    rewritten
}

/// The clock cancels `logged`: not decided on this host (3), and its rows stay as recorded
/// (`rewritten`), under `--locked` and without it; `--only` writes nothing, and `--output
/// verdicts` is the section the run would write.
fn assert_a_cancelled_run_keeps_its_rows(package: &Package, corpus: &str, rewritten: &str) {
    let record = package.directory.path().join(corpus).join("kink.lock");
    package.write(
        &format!("{corpus}/FLOW.toml"),
        &fs::read_to_string(package.directory.path().join(corpus).join("FLOW.toml"))
            .unwrap()
            .replace(
                "\"fake.sh\", \"equal\", \"logged.log\"",
                "\"fake.sh\", \"sleep\", \"logged.log\"",
            ),
    );
    for arguments in [&["--locked"][..], &[]] {
        let cancelled = package.compare(corpus, arguments);
        assert_status(&cancelled, 3);
        let document = json_of(&cancelled);
        let status = if arguments.is_empty() {
            "unchanged"
        } else {
            "undecided"
        };
        assert_eq!(document["lock"]["status"], status, "{document:#}");
        assert_eq!(
            document["lock"]["clock_stopped"][0],
            json!({"implementation": "logged", "program": "cases/a/case.toml", "run": "implementation"}),
            "{document:#}"
        );
        let stderr = String::from_utf8_lossy(&cancelled.stderr);
        assert!(
            stderr.contains("logged cases/a/case.toml: the clock (time_ms) cancelled"),
            "{stderr}"
        );
        assert_eq!(fs::read_to_string(&record).unwrap(), rewritten);
    }
    // `--only` writes nothing, and `--output verdicts` is the section the run would write.
    let only = package.compare(corpus, &["--only", "named", "--output", "verdicts"]);
    assert_status(&only, 0);
    let verdicts = String::from_utf8(only.stdout).unwrap();
    assert!(
        verdicts.starts_with(&kink_flow::verdicts::record_header()),
        "{verdicts}"
    );
    assert!(
        verdicts.contains("implementation = \"named\""),
        "{verdicts}"
    );
    assert!(
        !verdicts.contains("implementation = \"logged\""),
        "{verdicts}"
    );
    assert_eq!(fs::read_to_string(&record).unwrap(), rewritten);
}
