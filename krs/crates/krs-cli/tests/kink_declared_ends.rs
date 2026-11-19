//! `krs kink` on a definition that declares ends (`#[k::end(finished)]`, `#[k::end(refused)]`):
//! each end of a baseline run where no rule applies has its declared class, a case's expectation
//! may state it, an end in no declared class is a finding of `coverage`, `compare` judges a
//! program the definition refuses at every end by acceptance, an acceptance view compares whether
//! each side accepts each program (and the refusal a `rejected` answer names), and the functions
//! of the ends are no obligation of `coverage`'s families. Also the record (`kink.lock`): it states the
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

/// The implementations, one script whose argument says how it answers: `final` ends every
/// program on its own with the input `n` in `n`; `rejects` does so for `n <= 0`, rejects `n = 1`
/// naming the definition's refusal (`crate::trapped`, reason 1) with a message, and rejects
/// `n >= 2` with a message alone; `wrong-reason` names the reason 2 for `n = 1`; `misnamed` names
/// the finished end `crate::halted` as its refusal for `n = 1`; `crash` exits 3.
const FAKE: &str = r#"#!/bin/sh
mode=${1:-final}
request=$(cat)
n=$(printf '%s' "$request" | sed -n 's/.*"inputs":{"n":\(-\{0,1\}[0-9]*\)}.*/\1/p')
if [ "$mode" = crash ]; then echo "fake: crashed" >&2; exit 3; fi
if [ "$mode" = final ] || [ "$n" -le 0 ]; then
  printf '{"end":"final","cells":{"n":%s}}\n' "$n"; exit 0
fi
case "$mode:$n" in
  rejects:1) printf '{"end":"rejected","message":"trap at %s","refused":{"end":"crate::trapped","reason":1}}\n' "$n";;
  wrong-reason:1) printf '{"end":"rejected","refused":{"end":"crate::trapped","reason":2}}\n';;
  misnamed:1) printf '{"end":"rejected","refused":{"end":"crate::halted"}}\n';;
  *) printf '{"end":"rejected","message":"no rule for %s"}\n' "$n";;
esac
"#;

/// The corpus's implementations ([`FAKE`]): `fake`, of the first protocol, compared on its end
/// (required); `accepting`, of the first protocol, on acceptance alone; `rejecting`, of the
/// third, on acceptance (required) and on its end (reported); `wrong-reason`, `misnamed` and
/// `crash`, of the third, on acceptance alone.
const IMPLEMENTATIONS: &str = "[[implementation]]\nname = \"fake\"\ncommand = [\"sh\", \"fake.sh\"]\n\
     given = \"inputs\"\nomits = [\"k\"]\nviews = [{ name = \"whole\", required = true }]\n\n\
     [[implementation]]\nname = \"accepting\"\ncommand = [\"sh\", \"fake.sh\", \"final\"]\n\
     given = \"inputs\"\nomits = [\"k\"]\nviews = [{ name = \"accepts\", kind = \"accepts\", \
     required = true }]\n\n\
     [[implementation]]\nname = \"rejecting\"\nprotocol = \"kink-implementation/3\"\n\
     command = [\"sh\", \"fake.sh\", \"rejects\"]\ngiven = \"inputs\"\nomits = [\"k\"]\n\
     views = [{ name = \"accepts\", kind = \"accepts\", required = true }, { name = \"whole\" }]\n\n\
     [[implementation]]\nname = \"wrong-reason\"\nprotocol = \"kink-implementation/3\"\n\
     command = [\"sh\", \"fake.sh\", \"wrong-reason\"]\ngiven = \"inputs\"\nomits = [\"k\"]\n\
     views = [{ name = \"accepts\", kind = \"accepts\", required = true }]\n\n\
     [[implementation]]\nname = \"misnamed\"\nprotocol = \"kink-implementation/3\"\n\
     command = [\"sh\", \"fake.sh\", \"misnamed\"]\ngiven = \"inputs\"\nomits = [\"k\"]\n\
     views = [{ name = \"accepts\", kind = \"accepts\", required = true }]\n\n\
     [[implementation]]\nname = \"crash\"\nprotocol = \"kink-implementation/3\"\n\
     command = [\"sh\", \"fake.sh\", \"crash\"]\ngiven = \"inputs\"\nomits = [\"k\"]\n\
     views = [{ name = \"accepts\", kind = \"accepts\", required = true }]\n";

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
                 [[program]]\ncases = \"cases/*.toml\"\n\n{IMPLEMENTATIONS}"
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
/// judges each program by acceptance where asked ([`assert_acceptance`]).
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

    assert_acceptance(&package);
}

/// A gap is no finding where an expectation the flow checks states `class = "none"`, the
/// expectation scoped to the flow's facet (`expect_for.main`) as well as `expect`; one scoped to
/// another facet is not read, so the gap it expects stays a finding.
#[test]
fn a_gap_expected_by_the_flow_s_scoped_expectation_is_no_finding() {
    let gap = |n: i64| {
        format!("halt = \"stuck\"\nclass = \"none\"\ncompare = [\"n\"]\ncells = {{ n = {n} }}\n")
    };
    let scoped = format!("[inputs]\nn = 3\n\n[expect_for.main]\n{}", gap(3));
    let both = format!(
        "[inputs]\nn = 5\n\n[expect]\nhalt = \"stuck\"\ncompare = [\"n\"]\ncells = {{ n = 5 }}\n\n[expect_for.main]\n{}",
        gap(5)
    );
    let foreign = format!("[inputs]\nn = 4\n\n[expect_for.other]\n{}", gap(4));
    let package = Package::new(
        None,
        &[("scoped", &scoped), ("both", &both), ("foreign", &foreign)],
    );
    let output = package.kink("coverage", &[]);
    let document = json_of(&output);
    // The gap only another facet's expectation expects is a finding.
    assert_status(&output, 1);

    let scoped = program(&document, "cases/scoped.toml");
    assert_eq!(scoped["ends"][0]["declared"], "none", "{scoped:#}");
    assert_eq!(scoped["expectation"]["verdict"], "met", "{scoped:#}");
    assert_eq!(scoped.get("declared_end"), None, "{scoped:#}");

    let both = program(&document, "cases/both.toml");
    assert_eq!(both["expectation"]["verdict"], "met", "{both:#}");
    assert_eq!(both.get("declared_end"), None, "{both:#}");

    let foreign = program(&document, "cases/foreign.toml");
    assert_eq!(foreign["ends"][0]["declared"], "none", "{foreign:#}");
    assert_eq!(foreign.get("expectation"), None, "{foreign:#}");
    assert_eq!(
        foreign["declared_end"]["finding"], "undeclared-end",
        "{foreign:#}"
    );
}

/// `compare` on the declared ends' corpus (projections PJ-02):
///
/// - an end view of a program the definition refuses at every end (`trap`) is judged by
///   acceptance: an implementation that ends it differs, one that rejects it is equal;
/// - an acceptance view: the definition accepts `halt` and `wrong` (a declared finished end) and
///   rejects `trap` (refused) and `rest` and `gap` (no declared end holds: a gap); an answer that
///   ends accepts, one that is `rejected` rejects;
/// - a rejection that names the definition's refusal is compared with it on the parts both
///   state, and recorded where it agrees; its message never is;
/// - a refusal that names no declared refused end makes the answer malformed;
/// - a crash is `different` on the acceptance view and keeps its failure (status 1, decided).
fn assert_acceptance(package: &Package) {
    let output = package.kink("compare", &[]);
    let document = json_of(&output);
    // `misnamed`'s malformed answer fails a required view.
    assert_status(&output, 2);
    assert_eq!(document["version"], 10, "{document:#}");
    let row = |implementation: &str, case: &str| {
        document["rows"]
            .as_array()
            .unwrap_or_else(|| panic!("{document:#}"))
            .iter()
            .find(|row| {
                row["implementation"] == implementation
                    && row["program"] == format!("cases/{case}.toml").as_str()
            })
            .unwrap_or_else(|| panic!("no row of {implementation} {case}: {document:#}"))
            .clone()
    };
    let view = |implementation: &str, case: &str, view: &str| {
        row(implementation, case)["views"]
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| entry["view"] == view)
            .unwrap_or_else(|| panic!("no view {view}: {:#}", row(implementation, case)))
            .clone()
    };
    let accepts = |definition: &str, implementation: &str| {
        serde_json::json!({"format": "kink-accepts/1", "definition": definition,
                           "implementation": implementation})
    };

    // The end view of a program the definition refuses at every end: no longer a pass.
    let trap = view("fake", "trap", "whole");
    assert_eq!(trap["verdict"], "different", "{trap:#}");
    assert_eq!(
        trap["difference"],
        accepts("rejects", "accepts"),
        "{trap:#}"
    );
    assert!(trap["distance"].is_null(), "{trap:#}");
    for case in ["halt", "rest", "gap", "wrong"] {
        assert_eq!(view("fake", case, "whole")["verdict"], "equal", "{case}");
    }

    for (case, verdict) in [
        ("halt", "equal"),
        ("trap", "different"),
        ("rest", "different"),
        ("gap", "different"),
        ("wrong", "equal"),
    ] {
        let entry = view("accepting", case, "accepts");
        assert_eq!(entry["verdict"], verdict, "{case}: {entry:#}");
        if verdict == "different" {
            assert_eq!(
                entry["difference"],
                accepts("rejects", "accepts"),
                "{entry:#}"
            );
        }
    }

    for case in ["halt", "trap", "rest", "gap", "wrong"] {
        let entry = view("rejecting", case, "accepts");
        assert_eq!(entry["verdict"], "equal", "{case}: {entry:#}");
    }
    let rejected = row("rejecting", "trap");
    assert_eq!(rejected["answer"]["end"], "rejected", "{rejected:#}");
    assert_eq!(rejected["answer"]["message"], "trap at 1", "{rejected:#}");
    assert_eq!(
        view("rejecting", "trap", "accepts")["refused"],
        serde_json::json!({"end": "crate::trapped", "reason": 1})
    );
    // Its end view: the trap is judged by acceptance, the gap compares words.
    assert_eq!(view("rejecting", "trap", "whole")["verdict"], "equal");
    let gap = view("rejecting", "gap", "whole");
    assert_eq!(gap["difference"]["format"], "kink-end/1", "{gap:#}");
    assert_eq!(gap["difference"]["implementation"], "rejected", "{gap:#}");

    let wrong = view("wrong-reason", "trap", "accepts");
    assert_eq!(wrong["verdict"], "different", "{wrong:#}");
    assert_eq!(wrong["difference"]["at"], "class", "{wrong:#}");
    assert!(wrong.get("refused").is_none_or(Value::is_null), "{wrong:#}");

    let misnamed = row("misnamed", "trap");
    assert_eq!(misnamed["failure"]["kind"], "malformed", "{misnamed:#}");
    assert!(
        misnamed["failure"]["detail"]
            .as_str()
            .unwrap()
            .contains("`refused`"),
        "{misnamed:#}"
    );

    let crash = row("crash", "trap");
    assert_eq!(crash["failure"]["kind"], "exit", "{crash:#}");
    assert_eq!(crash["failure"]["decided"], true, "{crash:#}");
    assert_eq!(
        crash["views"][0]["difference"],
        accepts("rejects", "crashed"),
        "{crash:#}"
    );

    assert_acceptance_record(package);
}

/// Each implementation's exit status alone, and the record of [`assert_acceptance`]'s run: the
/// agreed refusal is recorded, no message, and a crash's acceptance rows.
fn assert_acceptance_record(package: &Package) {
    for (implementation, status) in [
        ("rejecting", 0),
        ("accepting", 1),
        ("wrong-reason", 1),
        ("crash", 1),
        ("misnamed", 2),
    ] {
        let output = package.kink("compare", &["--only", implementation]);
        assert_status(&output, status);
    }

    let record = package.read("kink/kink.lock");
    assert!(
        record.contains(
            "implementation = \"rejecting\"\nprogram = \"cases/trap.toml\"\nview = \
             \"accepts\"\nrequired = true\nverdict = \"equal\"\n\
             refused = '{\"end\":\"crate::trapped\",\"reason\":1}'\n"
        ),
        "{record}"
    );
    assert!(
        !record.contains("trap at 1") && !record.contains("no rule for"),
        "{record}"
    );
    assert!(
        record.contains(
            "implementation = \"crash\"\nprogram = \"cases/trap.toml\"\nview = \"accepts\"\n\
             required = true\nverdict = \"different\"\n"
        ),
        "{record}"
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
