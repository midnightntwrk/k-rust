//! `krs kink` on a definition that declares ends (`#[k::end(finished)]`, `#[k::end(refused)]`):
//! each end of a baseline run where no rule applies has its declared class, a case's expectation
//! may state it, an end in no declared class is a finding of `coverage`, `compare` gives the
//! verdict `definition-refused` on a program the definition refuses, and the functions of the
//! ends are no obligation of `coverage`'s families. Also the record (`kink.lock`): it states the
//! definition's assumed totalities in each section it writes, and a change of them makes the
//! section stale.
//!
//! The fixture starts from `#start` and the input `n`: `n <= 0` goes to `halt` (declared
//! `finished` by `halted`), `n = 1` to `trap` (declared `refused` by `trapped`, whose reason is
//! `n`, under a condition `n > 0`), and `n >= 2` to `rest`, which no rule executes and no end
//! declares: a gap.

#![cfg(feature = "kink")]

use std::fs;
use std::path::Path;
use std::process::Output;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::Value;

const PACKAGE: &str = "krs-cli-kink-declared-ends";

const LIBRARY: &str = r##"use k::builtin::{Int, KSequence};
use k::{KItem, Term};

k::sorts! {
    Op: KItem;
}

#[k::constructors(sort = Op, result = k::KResult)]
pub enum Step {
    #[k::syntax("#start")]
    Start(),
    #[k::syntax("#halt")]
    Halt(),
    #[k::syntax("#trap")]
    Trap(),
    #[k::syntax("#rest")]
    Rest(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub n: Int,
}

impl Machine {
    #[k::init]
    pub fn init(n: Int) -> Self {
        Self {
            k: k::k![Step::Start()],
            n,
        }
    }
}

/// The program asked to stop.
#[k::end(finished)]
pub fn halted(
    k::cells! {
        k: k::configuration::KCell(Step::Halt(), ..),
        ..
    }: Machine,
) {
}

/// A trap is refused, with `n`.
#[k::end(refused)]
#[k::requires(n > 0)]
pub fn trapped(
    n: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Step::Trap(), ..),
        n: k::configuration::Cell(n),
        ..
    }: Machine,
) -> Term<Int> {
    n
}

/*ASSUMED*/

k::rules! {
    for Machine;
    use Step::*;

    #[k::requires(n <= 0)]
    halt: { k: [Start(), ..], n } => { k: [Halt(), ..] };

    #[k::requires(n > 0 && n < 2)]
    trap: { k: [Start(), ..], n } => { k: [Trap(), ..] };

    #[k::requires(n >= 2)]
    rest: { k: [Start(), ..], n } => { k: [Rest(), ..] };
}
"##;

/// A function total on the author's word, with `REASON` as its reason.
const ASSUMED: &str = r#"
#[k::function(total, internal, assumed = "REASON")]
pub fn Same(x: Term<Int>) -> Term<Int> {
    x
}
"#;

/// An implementation that ends every program on its own with the input `n` in `n`.
const FAKE: &str = r#"#!/bin/sh
request=$(cat)
n=$(printf '%s' "$request" | sed -n 's/.*"inputs":{"n":\(-\{0,1\}[0-9]*\)}.*/\1/p')
printf '{"end":"final","cells":{"n":%s}}\n' "$n"
"#;

/// The package with its corpus, and the fixture target `krs` builds in.
struct Package {
    directory: TempDir,
    target: SharedFixtureTarget,
}

impl Package {
    /// The package, with `assumed` as the reason of an assumed totality (none for `None`), and
    /// its corpus `kink` of `cases` (a name and the case document's text).
    fn new(assumed: Option<&str>, cases: &[(&str, &str)]) -> Self {
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let package = Self {
            directory: temp_dir(),
            target: shared_fixture_target(),
        };
        package.library(assumed);
        package.write(
            "Cargo.toml",
            &format!(
                "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"DECLARED-ENDS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
                serde_json::to_string(krs.to_str().unwrap()).unwrap(),
            ),
        );
        package.write(
            "kink/FLOW.toml",
            &format!(
                "[spec]\nkrs = {{ package = \"{PACKAGE}\", definition = \"main\" }}\n\n[budget]\ntime_ms = 600000\n\n\
                 [[program]]\ncases = \"cases/*.toml\"\n\n[[implementation]]\nname = \"fake\"\n\
                 command = [\"sh\", \"fake.sh\"]\ngiven = \"inputs\"\nomits = [\"k\"]\n\
                 views = [{{ name = \"whole\", required = true }}]\n"
            ),
        );
        package.write("kink/fake.sh", FAKE);
        for (name, text) in cases {
            package.write(&format!("kink/cases/{name}.toml"), text);
        }
        package
    }

    fn library(&self, assumed: Option<&str>) {
        let assumed = assumed.map_or_else(String::new, |reason| ASSUMED.replace("REASON", reason));
        self.write("src/lib.rs", &LIBRARY.replace("/*ASSUMED*/", &assumed));
    }

    fn write(&self, relative: &str, contents: &str) {
        let path = self.directory.path().join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn read(&self, relative: &str) -> String {
        fs::read_to_string(self.directory.path().join(relative)).unwrap()
    }

    /// `krs kink VERB ARGUMENTS` on the corpus.
    fn kink(&self, verb: &str, arguments: &[&str]) -> Output {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        process
            .current_dir(self.directory.path())
            .args(["kink", verb])
            .args(arguments)
            .args(["--package", PACKAGE, "--definition", "main"]);
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

/// The program row of `id`.
fn program<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["programs"]
        .as_array()
        .unwrap_or_else(|| panic!("{document:#}"))
        .iter()
        .find(|row| row["id"] == id)
        .unwrap_or_else(|| panic!("no program {id}: {document:#}"))
}

/// The cases of the main test: a finished end, a refused one stated in full, a gap the case does
/// not expect, and one it does.
const CASES: &[(&str, &str)] = &[
    (
        "halt",
        "[inputs]\nn = 0\n\n[expect]\nhalt = \"stuck\"\nclass = \"finished\"\ncompare = [\"n\"]\ncells = { n = 0 }\n",
    ),
    (
        "trap",
        "[inputs]\nn = 1\n\n[expect]\nhalt = \"stuck\"\nclass = \"refused\"\nend = \"crate::trapped\"\nreason = 1\ncompare = [\"n\"]\ncells = { n = 1 }\n",
    ),
    ("rest", "[inputs]\nn = 2\n"),
    (
        "gap",
        "[inputs]\nn = 3\n\n[expect]\nhalt = \"stuck\"\nclass = \"none\"\ncompare = [\"n\"]\ncells = { n = 3 }\n",
    ),
    (
        "wrong",
        "[inputs]\nn = 0\n\n[expect]\nhalt = \"stuck\"\nclass = \"refused\"\ncompare = [\"n\"]\ncells = { n = 0 }\n",
    ),
];

/// `coverage` reads each end's declared class from the definition's own end functions, an
/// expectation that states a class is met by the baseline's ends where they are of that class
/// (and unmet where not), an end in no declared class is a finding unless the case expects it,
/// and the functions of the ends are no obligation, so no flip is derived from them. `compare`
/// gives a program the definition refuses the verdict `definition-refused`, whatever the
/// implementation answered, with its reason, and exits 0 for it.
#[test]
fn declared_classes_are_read_stated_and_compared() {
    let package = Package::new(None, CASES);
    let output = package.kink("coverage", &[]);
    let document = json_of(&output);
    // The gap nobody expects is a finding, and so is the unmet expectation.
    assert_status(&output, 1);

    let halt = program(&document, "cases/halt.toml");
    assert_eq!(halt["ends"][0]["declared"], "finished", "{halt:#}");
    assert_eq!(halt["ends"][0]["declared_by"], "crate::halted", "{halt:#}");
    assert_eq!(halt["expectation"]["verdict"], "met", "{halt:#}");
    assert_eq!(halt.get("declared_end"), None, "{halt:#}");

    let trap = program(&document, "cases/trap.toml");
    assert_eq!(trap["ends"][0]["declared"], "refused", "{trap:#}");
    assert_eq!(trap["ends"][0]["declared_by"], "crate::trapped", "{trap:#}");
    assert_eq!(trap["ends"][0]["reason"], 1, "{trap:#}");
    assert_eq!(trap["ends"][0]["reason_text"], "1", "{trap:#}");
    assert_eq!(trap["expectation"]["verdict"], "met", "{trap:#}");
    assert_eq!(trap.get("declared_end"), None, "{trap:#}");

    let rest = program(&document, "cases/rest.toml");
    assert_eq!(rest["ends"][0]["declared"], "none", "{rest:#}");
    assert_eq!(rest["ends"][0].get("declared_by"), None, "{rest:#}");
    assert_eq!(
        rest["declared_end"]["finding"], "undeclared-end",
        "{rest:#}"
    );

    let gap = program(&document, "cases/gap.toml");
    assert_eq!(gap["ends"][0]["declared"], "none", "{gap:#}");
    assert_eq!(gap["expectation"]["verdict"], "met", "{gap:#}");
    assert_eq!(gap.get("declared_end"), None, "{gap:#}");

    let wrong = program(&document, "cases/wrong.toml");
    assert_eq!(wrong["expectation"]["verdict"], "unmet", "{wrong:#}");

    // The ends' functions are applied by no step: no obligation, and no flip of their guard.
    let rules = document["families"]["rules"]["items"]
        .as_array()
        .unwrap_or_else(|| panic!("{document:#}"));
    let declared = rules
        .iter()
        .filter(|rule| rule["status"] == "declared-end")
        .collect::<Vec<_>>();
    assert!(!declared.is_empty(), "{:#}", document["families"]["rules"]);
    assert!(
        rules
            .iter()
            .filter(|rule| rule["status"] == "unmatched")
            .all(|rule| !rule.to_string().contains("trapped")
                && !rule.to_string().contains("halted")),
        "{:#}",
        document["families"]["rules"]
    );
    let flips = &document["families"]["flips"];
    assert!(
        flips["not_generated"]
            .as_array()
            .into_iter()
            .flatten()
            .any(|flip| flip["reason"] == "declared-end"
                && flip["sentences"].to_string().contains("trapped")),
        "{flips:#}"
    );
    assert!(
        flips["items"]
            .as_array()
            .into_iter()
            .flatten()
            .all(|flip| !flip.to_string().contains("trapped")),
        "{flips:#}"
    );

    let output = package.kink("compare", &[]);
    let document = json_of(&output);
    assert_status(&output, 0);
    let row = |id: &str| {
        document["rows"]
            .as_array()
            .unwrap_or_else(|| panic!("{document:#}"))
            .iter()
            .find(|row| row["program"] == id)
            .unwrap_or_else(|| panic!("no row of {id}: {document:#}"))
            .clone()
    };
    let trap = row("cases/trap.toml");
    let view = &trap["views"][0];
    assert_eq!(view["verdict"], "definition-refused", "{trap:#}");
    assert_eq!(
        view["detail"],
        "the definition refuses the program, at its declared end `crate::trapped`: `1`",
        "{trap:#}"
    );
    assert_eq!(row("cases/halt.toml")["views"][0]["verdict"], "equal");
    assert_eq!(
        document["summary"]["verdicts"]["definition-refused"], 1,
        "{document:#}"
    );
}

/// The record states the definition's assumed totalities in each section it writes, as no
/// output does, and a change of them makes the section stale under `--locked`, naming the line
/// only; a definition with none writes no such table.
#[test]
fn the_record_states_the_assumed_totalities() {
    let cases: &[(&str, &str)] = &[("halt", "[inputs]\nn = 0\n")];
    let package = Package::new(None, cases);
    assert_status(&package.kink("coverage", &[]), 0);
    let without = package.read("kink/kink.lock");
    assert!(!without.contains("assumed_totals"), "{without}");

    package.library(Some("the first reason"));
    let output = package.kink("coverage", &[]);
    assert_status(&output, 0);
    let written = package.read("kink/kink.lock");
    assert!(
        written.contains("[coverage.assumed_totals]") && written.contains("= \"the first reason\""),
        "{written}"
    );
    // No output prints the list.
    assert!(
        !String::from_utf8_lossy(&output.stdout).contains("the first reason"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_status(&package.kink("coverage", &["--locked"]), 0);

    package.library(Some("another reason"));
    let output = package.kink("coverage", &["--locked"]);
    assert_status(&output, 1);
    let document = json_of(&output);
    assert_eq!(
        document["lock"]["status"], "stale",
        "{:#}",
        document["lock"]
    );
    assert_eq!(
        document["lock"]["difference"]["kind"], "assumed_totals",
        "{:#}",
        document["lock"]
    );
    // kink's own lines: the document and the record's notes (the compiler's diagnostics quote
    // the source, as they do of every attribute).
    let stderr = String::from_utf8_lossy(&output.stderr);
    let shown = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        stderr
            .lines()
            .filter(|line| line.starts_with("krs kink"))
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        !shown.contains("the first reason") && !shown.contains("another reason"),
        "{shown}"
    );
    // The lock is still the one written, until a command without --locked rewrites it.
    assert_eq!(package.read("kink/kink.lock"), written);
}
