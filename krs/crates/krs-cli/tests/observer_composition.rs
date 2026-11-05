//! An observer is an ordinary package that depends on the compared definition's, composed from
//! its own dependency closure: it may compose a package outside the compared definition's closure,
//! its definition holds the compared one because it depends on it (whether or not its source names
//! anything of it), and when it cannot be compiled, `krs compare`, `krs run --case` and
//! `krs cases` print its diagnostics, saying what a view function must be where one is refused for
//! being program syntax.
//!
//! The workspace: the definition `fixtures/ends`; `helper`, a KRS package with a function over
//! builtin lists that the definition does not depend on; `observe`, which depends on both and whose
//! one-parameter view applies the helper's function, naming nothing of the definition; `tally`
//! and `observe-tally`, a second such helper and an observer that depends on it and not on
//! `helper`; and `broken`, an observer whose view is `pub` without `internal`, so program syntax
//! without a `syntax`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;
use std::sync::Mutex;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value, json};

const ENDS: &str = include_str!("fixtures/ends/src/lib.rs");
const PACKAGE: &str = "krs-cli-observer-ends-fixture";
const HELPER_PACKAGE: &str = "krs-cli-observer-helper-fixture";
const OBSERVER_PACKAGE: &str = "krs-cli-observer-observe-fixture";
const BROKEN_PACKAGE: &str = "krs-cli-observer-broken-fixture";
const TALLY_PACKAGE: &str = "krs-cli-observer-tally-fixture";
const TALLY_OBSERVER_PACKAGE: &str = "krs-cli-observer-observe-tally-fixture";

/// A second package of functions outside the definition's dependency closure.
const TALLY: &str = r"//! A count of event logs in hundreds, which no semantics depends on.

use k::Term;
use k::builtin::{Int, List};

/// A hundred per entry of a log.
#[k::function(total, internal)]
pub fn Hundreds(log: Term<List>) -> Term<Int> {
    log.len() * 100
}
";

/// An observer that depends on the definition and on `tally`, not on `helper`.
const TALLY_OBSERVER: &str = r"//! Views of the `ends` definition built from `tally`'s functions.

use k::Term;
use k::builtin::{Int, List};

/// The log's entries in hundreds.
#[k::function(total, internal)]
pub fn TallyView(log: Term<List>) -> Term<Int> {
    tally::Hundreds(log)
}
";

/// A package of functions outside the definition's dependency closure.
const HELPER: &str = r"//! Functions over event logs, which no semantics depends on.

use k::Term;
use k::builtin::{Int, List};

/// The number of entries of a log, plus `bonus`.
#[k::function(total, internal)]
pub fn Entries(log: Term<List>, bonus: Term<Int>) -> Term<Int> {
    log.len() + bonus
}
";

/// An observer that depends on the definition and on the helper, and whose view names only the
/// helper's function.
const OBSERVER: &str = r"//! Views of the `ends` definition built from the helper's functions alone.

use k::Term;
use k::builtin::{Int, List};

/// The helper's count of a log's entries, with a bonus of 10.
#[k::function(total, internal)]
pub fn HelperEntries(log: Term<List>) -> Term<Int> {
    helper::Entries(log, 10)
}
";

/// An observer whose view is program syntax (`pub`, not `internal`) without a `syntax`.
const BROKEN: &str = r"//! A view that is program syntax without a syntax.

use k::Term;
use k::builtin::{Int, List};

/// The number of entries of a log.
#[k::function(total)]
pub fn Exposed(log: Term<List>) -> Term<Int> {
    log.len()
}
";

/// The workspace, shared by this process's tests, which run `krs` on it one at a time.
struct Workspace {
    directory: TempDir,
    _target: SharedFixtureTarget,
    target: PathBuf,
    turn: Mutex<()>,
}

fn manifest(name: &str, namespace: &str, dependencies: &str) -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n"
    )
}

fn workspace() -> &'static Workspace {
    static WORKSPACE: std::sync::OnceLock<Workspace> = std::sync::OnceLock::new();
    WORKSPACE.get_or_init(|| {
        let target = shared_fixture_target();
        let directory = temp_dir();
        let root = directory.path();
        let ends = format!("ends = {{ package = \"{PACKAGE}\", path = \"../language\" }}\n");
        let helper = format!("helper = {{ package = \"{HELPER_PACKAGE}\", path = \"../helper\" }}\n");
        let tally = format!("tally = {{ package = \"{TALLY_PACKAGE}\", path = \"../tally\" }}\n");
        for (member, source, manifest) in [
            ("language", ENDS, manifest(PACKAGE, "ORG-KRS-CLI-OBSERVER", "")),
            (
                "helper",
                HELPER,
                manifest(HELPER_PACKAGE, "ORG-KRS-CLI-OBSERVER-HELPER", ""),
            ),
            (
                "observe",
                OBSERVER,
                manifest(
                    OBSERVER_PACKAGE,
                    "ORG-KRS-CLI-OBSERVER-OBSERVE",
                    &format!("{ends}{helper}"),
                ),
            ),
            (
                "tally",
                TALLY,
                manifest(TALLY_PACKAGE, "ORG-KRS-CLI-OBSERVER-TALLY", ""),
            ),
            (
                "observe-tally",
                TALLY_OBSERVER,
                manifest(
                    TALLY_OBSERVER_PACKAGE,
                    "ORG-KRS-CLI-OBSERVER-OBSERVE-TALLY",
                    &format!("{ends}{tally}"),
                ),
            ),
            (
                "broken",
                BROKEN,
                manifest(BROKEN_PACKAGE, "ORG-KRS-CLI-OBSERVER-BROKEN", &ends),
            ),
        ] {
            fs::create_dir_all(root.join(member).join("src")).unwrap();
            fs::write(root.join(member).join("src/lib.rs"), source).unwrap();
            fs::write(root.join(member).join("Cargo.toml"), manifest).unwrap();
        }
        fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"language\", \"helper\", \"observe\", \"tally\", \"observe-tally\", \"broken\"]\nresolver = \"3\"\n",
        )
        .unwrap();
        let workspace = Workspace {
            directory,
            target: target.path().to_path_buf(),
            _target: target,
            turn: Mutex::new(()),
        };
        workspace.write_cases();
        workspace
    })
}

impl Workspace {
    /// The definition's package directory, where `krs` runs and the documents are written.
    fn path(&self) -> PathBuf {
        self.directory.path().join("language")
    }

    fn write(&self, relative: &str, contents: impl AsRef<[u8]>) {
        fs::write(self.path().join(relative), contents).unwrap();
    }

    /// `cases.json`: the case `finish(3)` from a state whose bus holds one event, with no
    /// expectation (`plain`), expecting a bus of one other event under the helper's view in the
    /// observer (`helped`), under the tally observer's view (`tallied`), and under the broken
    /// observer's view (`broken`).
    fn write_cases(&self) {
        let inputs = json!({
            "pgm": {"Finish": {"value": 3}},
            "regs": {"A": 1},
            "f": {"Flags": {"zf": true, "cf": false}},
            "pc": 256,
            "bus": [{"Read": {"addr": 5}}],
            "memory": {"5": 6},
            "ime": true,
            "w": 9,
            "z": 4,
        });
        let expect = |views: Value, observer: &str| {
            json!({
                "halt": "stuck",
                "compare": ["bus"],
                "cells": {"bus": [{"Write": {"addr": 1, "value": 2}}]},
                "views": views,
                "observer": observer,
            })
        };
        let cases = json!({"case": [
            {"name": "plain", "inputs": inputs},
            {
                "name": "helped",
                "inputs": inputs,
                "expect": expect(json!({"bus": "HelperEntries"}), &observer()),
            },
            {
                "name": "tallied",
                "inputs": inputs,
                "expect": expect(json!({"bus": "TallyView"}), &format!("{TALLY_OBSERVER_PACKAGE}:main")),
            },
            {
                "name": "broken",
                "inputs": inputs,
                "expect": expect(json!({"bus": "Exposed"}), &format!("{BROKEN_PACKAGE}:main")),
            },
        ]});
        self.write("cases.json", cases.to_string());
        // Two ends of `finish(3)` whose buses differ in length.
        self.write(
            "end.json",
            json!({
                "halt": "stuck",
                "cells": {"bus": [{"Read": {"addr": 5}}]},
            })
            .to_string(),
        );
    }

    /// `krs VERB --package ends --definition main ARGUMENTS`, from the definition's package.
    fn krs(&self, verb: &str, arguments: &[&str]) -> Output {
        self.krs_with(verb, arguments, &[])
    }

    /// [`Self::krs`] with the environment variables `environment` set.
    fn krs_with(&self, verb: &str, arguments: &[&str], environment: &[(&str, &Path)]) -> Output {
        let _turn = self
            .turn
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut process = krs_command!();
        fixture_build_env(&mut process, &self.target);
        for (name, value) in environment {
            process.env(name, value);
        }
        process
            .current_dir(self.path())
            .arg(verb)
            .args(["--package", PACKAGE, "--definition", "main"])
            .args(arguments)
            .output()
            .unwrap()
    }
}

fn observer() -> String {
    format!("{OBSERVER_PACKAGE}:main")
}

fn helper_dependency() -> String {
    format!("{HELPER_PACKAGE}:main")
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// The observer composes the helper, which the definition's closure does not hold, named by
/// `--dependency`; its view names nothing of the definition, and its definition holds the
/// definition's because the observer depends on it.
#[test]
fn an_observer_composes_its_own_dependency_closure() {
    let workspace = workspace();
    let observer = observer();
    let helper = helper_dependency();
    let output = workspace.krs(
        "compare",
        &[
            "end.json",
            "cases.json#plain",
            "--compare",
            "bus",
            "--view",
            "bus=HelperEntries",
            "--observer",
            &observer,
            "--dependency",
            &helper,
        ],
    );
    // `end.json`'s bus is the input's one event; the run's, the same: equal under the view.
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    assert_eq!(
        stdout(&output),
        format!("krs compare: equal\n  views: `bus` = `HelperEntries`, in `{observer}`\n")
    );

    // An expectation of one other event is met under the view (both logs have one entry), in
    // `krs run --case` and in `krs cases`.
    let run = workspace.krs(
        "run",
        &[
            "--case",
            "cases.json",
            "--case-name",
            "helped",
            "--output",
            "none",
            "--dependency",
            &helper,
        ],
    );
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    let cases = workspace.krs(
        "cases",
        &[
            "cases.json",
            "--name",
            "helped",
            "--output",
            "json",
            "--dependency",
            &helper,
        ],
    );
    assert_eq!(cases.status.code(), Some(0), "{}", stderr(&cases));
    let record: Value = serde_json::from_str(stdout(&cases).lines().next().unwrap()).unwrap();
    assert_eq!(record["verdict"], "met", "{record}");
    assert_eq!(record["observer"], json!(observer), "{record}");

    // The viewed value is the helper's: a difference shows it.
    let moved = json!({
        "halt": "stuck",
        "cells": {"bus": [{"Read": {"addr": 5}}, {"Read": {"addr": 6}}]},
    });
    workspace.write("moved.json", moved.to_string());
    let output = workspace.krs(
        "compare",
        &[
            "moved.json",
            "end.json",
            "--compare",
            "bus",
            "--view",
            "bus=HelperEntries",
            "--observer",
            &observer,
            "--dependency",
            &helper,
            "--output",
            "json",
        ],
    );
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    let document: Value = serde_json::from_str(&stdout(&output)).unwrap();
    let difference = &document["difference"];
    assert_eq!(difference["left"]["value"]["document"], 12, "{difference}");
    assert_eq!(difference["right"]["value"]["document"], 11, "{difference}");
}

/// The helper's facet is composed only into the observer: without it the observer cannot collect
/// the helper's function, which the refusal says how to compose, and named for a command that
/// prepares no observer, it is refused.
#[test]
fn an_observer_dependency_is_named_and_composed_only_into_the_observer() {
    let workspace = workspace();
    let observer = observer();
    let helper = helper_dependency();
    // Without the helper's facet, the observer cannot collect the helper's function.
    let output = workspace.krs(
        "compare",
        &[
            "end.json",
            "cases.json#plain",
            "--compare",
            "bus",
            "--view",
            "bus=HelperEntries",
            "--observer",
            &observer,
        ],
    );
    assert_eq!(output.status.code(), Some(2), "{}", stdout(&output));
    let text = stderr(&output);
    assert!(text.contains("package-not-selected"), "{text}");
    assert!(
        text.contains(&format!("in the observer `{observer}`")),
        "{text}"
    );
    assert!(
        text.contains("name the package's facet with --dependency PACKAGE:DEFINITION"),
        "{text}"
    );

    // The helper's facet is outside the definition's closure, so a command that prepares no
    // observer refuses it, naming why.
    let output = workspace.krs(
        "compare",
        &[
            "end.json",
            "cases.json#plain",
            "--compare",
            "bus",
            "--dependency",
            &helper,
        ],
    );
    assert_eq!(output.status.code(), Some(2), "{}", stdout(&output));
    let text = stderr(&output);
    assert!(
        text.contains(&format!(
            "the dependency facet `{helper}` is not in root package `{PACKAGE}`'s resolved dependency closure, nor in that of an observer the command prepared"
        )),
        "{text}"
    );
    let output = workspace.krs("check", &["--dependency", &helper]);
    assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
    assert!(
        stderr(&output).contains(&format!(
            "selected package `{HELPER_PACKAGE}` is not in root package `{PACKAGE}`'s resolved dependency closure"
        )),
        "{}",
        stderr(&output)
    );
}

/// An observer that does not compile is refused with its diagnostics, each noting the observer,
/// rendered from its source; a view refused for being program syntax without a `syntax` says what
/// a view function must be. `krs compare`, `krs run --case` and `krs cases` all print them.
#[test]
fn an_observer_that_does_not_compile_prints_its_diagnostics() {
    let workspace = workspace();
    let broken = format!("{BROKEN_PACKAGE}:main");
    let said = |text: &str| {
        assert!(text.contains("missing-function-syntax"), "{text}");
        assert!(text.contains("pub fn Exposed"), "{text}");
        assert!(
            text.contains("if this function is a view (a function of one parameter that a comparison applies to a cell's value, never written in a program), mark it `internal`"),
            "{text}"
        );
        assert!(
            text.contains(&format!("in the observer `{broken}`")),
            "{text}"
        );
        assert!(!text.contains("structured diagnostic"), "{text}");
    };
    let output = workspace.krs(
        "compare",
        &[
            "end.json",
            "cases.json#plain",
            "--compare",
            "bus",
            "--view",
            "bus=Exposed",
            "--observer",
            &broken,
        ],
    );
    assert_eq!(output.status.code(), Some(2), "{}", stdout(&output));
    said(&stderr(&output));

    let run = workspace.krs(
        "run",
        &[
            "--case",
            "cases.json",
            "--case-name",
            "broken",
            "--output",
            "none",
        ],
    );
    assert_eq!(run.status.code(), Some(2), "{}", stdout(&run));
    said(&stderr(&run));

    let cases = workspace.krs("cases", &["cases.json", "--name", "broken"]);
    assert_eq!(cases.status.code(), Some(2), "{}", stderr(&cases));
    let text = stdout(&cases);
    assert!(text.starts_with("cases.json#broken: refused: "), "{text}");
    said(&text);
}

/// Each observer of a batch composes the extra facets its own closure holds: two observers that
/// need different packages run in one batch, and a facet that no observer the batch prepared
/// holds is reported as a warning once the verdicts are printed.
#[test]
fn each_observer_of_a_batch_composes_the_facets_its_closure_holds() {
    let workspace = workspace();
    let helper = helper_dependency();
    let tally = format!("{TALLY_PACKAGE}:main");
    let both = workspace.krs(
        "cases",
        &[
            "cases.json",
            "--name",
            "*ed",
            "--output",
            "json",
            "--dependency",
            &helper,
            "--dependency",
            &tally,
        ],
    );
    assert_eq!(both.status.code(), Some(0), "{}", stderr(&both));
    let records = stdout(&both)
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(records[0]["case"], "cases.json#helped", "{}", records[0]);
    assert_eq!(records[0]["verdict"], "met", "{}", records[0]);
    assert_eq!(records[1]["case"], "cases.json#tallied", "{}", records[1]);
    assert_eq!(records[1]["verdict"], "met", "{}", records[1]);
    assert!(
        !stderr(&both).contains("dependency facet"),
        "{}",
        stderr(&both)
    );

    let one = workspace.krs(
        "cases",
        &[
            "cases.json",
            "--name",
            "helped",
            "--dependency",
            &helper,
            "--dependency",
            &tally,
        ],
    );
    assert_eq!(one.status.code(), Some(0), "{}", stderr(&one));
    assert!(
        stderr(&one).contains(&format!(
            "the dependency facet `{tally}` is not in root package `{PACKAGE}`'s resolved dependency closure, nor in that of an observer the command prepared"
        )),
        "{}",
        stderr(&one)
    );
}

/// `krs search --case` evaluates the views in the observer the case names, as `krs run --case`
/// does; `krs run --case` refuses an outside facet when the case names no observer to compose
/// it; and the observer's own facet, given as a dependency too, counts as composed.
#[test]
fn search_and_run_of_a_case_compose_the_observer_and_judge_its_facets() {
    let workspace = workspace();
    let observer = observer();
    let helper = helper_dependency();
    let search = workspace.krs(
        "search",
        &[
            "--case",
            "cases.json",
            "--case-name",
            "helped",
            "--dependency",
            &helper,
        ],
    );
    assert_eq!(search.status.code(), Some(0), "{}", stderr(&search));
    let text = format!("{}{}", stdout(&search), stderr(&search));
    assert!(
        text.contains(&format!("views: `bus` = `HelperEntries`, in `{observer}`")),
        "{text}"
    );

    let run = workspace.krs(
        "run",
        &[
            "--case",
            "cases.json",
            "--case-name",
            "plain",
            "--output",
            "none",
            "--dependency",
            &helper,
        ],
    );
    assert_eq!(run.status.code(), Some(2), "{}", stdout(&run));
    assert!(
        stderr(&run).contains(&format!(
            "the dependency facet `{helper}` is not in root package `{PACKAGE}`'s resolved dependency closure, nor in that of an observer the command prepared"
        )),
        "{}",
        stderr(&run)
    );

    let output = workspace.krs(
        "compare",
        &[
            "end.json",
            "cases.json#plain",
            "--compare",
            "bus",
            "--view",
            "bus=HelperEntries",
            "--observer",
            &observer,
            "--dependency",
            &observer,
            "--dependency",
            &helper,
        ],
    );
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
}

/// A facet only the observer composes leaves the compared definition as it is: the compared
/// definition's compiled stage, whose key digests its Definition IR, is the one a run without
/// the facet stored, so the store holds that stage and the observer's, and no third.
#[test]
fn an_observer_facet_leaves_the_compared_definition_unchanged() {
    let workspace = workspace();
    let store = temp_dir();
    let environment = [("KRS_STAGE_CACHE_DIR", store.path())];
    let stages = || {
        fn count(directory: &Path) -> usize {
            fs::read_dir(directory).map_or(0, |entries| {
                entries
                    .flatten()
                    .map(|entry| {
                        let path = entry.path();
                        if path.is_dir() {
                            count(&path)
                        } else {
                            usize::from(
                                path.extension()
                                    .is_some_and(|extension| extension == "stage"),
                            )
                        }
                    })
                    .sum()
            })
        }
        count(store.path())
    };
    let run = workspace.krs_with(
        "run",
        &[
            "--case",
            "cases.json",
            "--case-name",
            "plain",
            "--output",
            "none",
        ],
        &environment,
    );
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    assert_eq!(stages(), 1);
    let observer = observer();
    let helper = helper_dependency();
    let output = workspace.krs_with(
        "compare",
        &[
            "end.json",
            "cases.json#plain",
            "--compare",
            "bus",
            "--view",
            "bus=HelperEntries",
            "--observer",
            &observer,
            "--dependency",
            &helper,
        ],
        &environment,
    );
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    assert_eq!(
        stages(),
        2,
        "the compared definition's stage was stored again"
    );
}

/// The FU-18 fixture's dependency, whose rule needs a configuration it does not declare.
const FU18_BASE: &str = r#"//! A dependency with rules but no configuration.

use k::KResult;
use k::builtin::{Int, int};

k::sorts! {
Exp;
Value: Exp + KResult;
impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Double))]
#[rustfmt::skip]
pub enum ExpSyntax {
#[k::syntax("double {value}")]
Double { value: Int },
}

k::rules! {
for Exp;
use ExpSyntax::*;

double: Double { value: v } => int::add(v, v);
}
"#;
/// The FU-18 fixture's configured package.
const FU18_LANG: &str = r"//! The configured package over `base`, whose rule needs this configuration.

use base::Exp;
use k::builtin::KSequence;

#[k::configuration]
pub struct Machine {
#[k::cell]
pub k: KSequence,
}

impl Machine {
#[k::init]
pub fn init(pgm: Exp) -> Self {
    Self { k: k::k![pgm] }
}
}
";
/// The FU-18 fixture's observer, naming nothing of the definition.
const FU18_OBS: &str = r"//! A view naming nothing of the definition.

use k::Term;
use k::builtin::{Int, List};

/// The entries of a list.
#[k::function(total, internal)]
pub fn Entries(log: Term<List>) -> Term<Int> {
log.len()
}
";

/// The FU-18 shape: a configured package (`ZZZ-LANG`) imports a dependency (`AAA-BASE`) whose
/// rules name its cells, so the dependency's module imports the configured module's
/// configuration module in the K, not the configured module. An observer that names nothing of
/// either still holds the configured module, whichever namespace sorts first.
#[test]
fn an_observer_holds_the_configured_module_of_an_fu18_composition() {
    let target = shared_fixture_target();
    let directory = temp_dir();
    let root = directory.path();
    for (member, name, namespace, source, dependencies) in [
        (
            "base",
            "krs-cli-fu18-base",
            "AAA-BASE",
            FU18_BASE,
            String::new(),
        ),
        (
            "lang",
            "krs-cli-fu18-lang",
            "ZZZ-LANG",
            FU18_LANG,
            "base = { package = \"krs-cli-fu18-base\", path = \"../base\" }\n".to_owned(),
        ),
        (
            "obs",
            "krs-cli-fu18-obs",
            "OBS",
            FU18_OBS,
            "lang = { package = \"krs-cli-fu18-lang\", path = \"../lang\" }\n".to_owned(),
        ),
    ] {
        fs::create_dir_all(root.join(member).join("src")).unwrap();
        fs::write(root.join(member).join("src/lib.rs"), source).unwrap();
        fs::write(
            root.join(member).join("Cargo.toml"),
            manifest(name, namespace, &dependencies),
        )
        .unwrap();
    }
    fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"base\", \"lang\", \"obs\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    let emitted = root.join("emitted");
    let mut process = krs_command!();
    fixture_build_env(&mut process, target.path());
    let output = process
        .current_dir(root.join("obs"))
        .args([
            "emit-k",
            "--package",
            "krs-cli-fu18-obs",
            "--definition",
            "main",
        ])
        .args(["--dependency", "krs-cli-fu18-lang:main"])
        .args(["--dependency", "krs-cli-fu18-base:main"])
        .arg("--output")
        .arg(&emitted)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    let definition = fs::read_to_string(emitted.join("definition.k")).unwrap();
    let observer = definition
        .split("\nmodule OBS\n")
        .nth(1)
        .and_then(|rest| rest.split("endmodule").next())
        .unwrap_or_else(|| panic!("no module OBS:\n{definition}"));
    assert!(observer.contains("  imports ZZZ-LANG\n"), "{definition}");
    // The dependency still imports the configuration's module, not the configured module.
    assert!(
        definition.contains("  imports ZZZ-LANG-CONFIGURATION\n"),
        "{definition}"
    );
}
