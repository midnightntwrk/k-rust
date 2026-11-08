//! `krs run`'s observations (`--observe FILE`, a case's `observe`, `--output observations`): the
//! declaration as a document states it, the `krs-observations/1` document a run prints, the
//! exit statuses, the usage errors, and `krs cases` and `krs search` of a case that declares
//! observations. The recording itself is krs-exec's (`tests/observation_core.rs`).
//!
//! The fixture (`fixtures/observations`) is a free-running machine: each step adds 1 to `n`, and
//! every third step (`emit`) appends `out(n)` to the `out` log. Its observer
//! (`fixtures/observations-observe`) depends on it and holds the views, components, filters and
//! element functions.

use std::fs;
use std::path::Path;
use std::sync::OnceLock;

use krs_exec::{ObservationSpec, Stutter};
use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value as Json, json};

const FIXTURE: &str = include_str!("fixtures/observations/src/lib.rs");
const PACKAGE: &str = "krs-observations-fixture";
const OBSERVER: &str = include_str!("fixtures/observations-observe/src/lib.rs");
const OBSERVER_PACKAGE: &str = "krs-observations-observe-fixture";

/// A package manifest of `name` in KRS namespace `namespace`, with `dependencies`.
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

/// The machine and its observer in one workspace, and the fixture target `krs` builds in.
struct Workspace {
    directory: TempDir,
    target: SharedFixtureTarget,
}

impl Workspace {
    fn new() -> Self {
        let directory = temp_dir();
        let root = directory.path();
        for (member, source, manifest) in [
            (
                "machine",
                FIXTURE,
                manifest(PACKAGE, "ORG-KRS-OBSERVATIONS", ""),
            ),
            (
                "observe",
                OBSERVER,
                manifest(
                    OBSERVER_PACKAGE,
                    "ORG-KRS-OBSERVATIONS-OBSERVE",
                    &format!("machine = {{ package = \"{PACKAGE}\", path = \"../machine\" }}\n"),
                ),
            ),
        ] {
            fs::create_dir_all(root.join(member).join("src")).unwrap();
            fs::write(root.join(member).join("src/lib.rs"), source).unwrap();
            fs::write(root.join(member).join("Cargo.toml"), manifest).unwrap();
        }
        fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"machine\", \"observe\"]\nresolver = \"3\"\n",
        )
        .unwrap();
        Self {
            directory,
            target: shared_fixture_target(),
        }
    }

    fn path(&self, name: &str) -> std::path::PathBuf {
        self.directory.path().join(name)
    }

    /// `krs VERB --package PACKAGE --definition main ARGUMENTS` from the machine's directory:
    /// the exit status, stdout and stderr.
    fn krs(&self, verb: &str, arguments: &[&str]) -> (Option<i32>, String, String) {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        let output = process
            .current_dir(self.path("machine"))
            .arg(verb)
            .args(["--package", PACKAGE, "--definition", "main"])
            .args(arguments)
            .output()
            .unwrap();
        let text = |bytes: &[u8]| String::from_utf8_lossy(bytes).into_owned();
        (
            output.status.code(),
            text(&output.stdout),
            text(&output.stderr),
        )
    }

    /// `krs run --input start=0 --input hole=0 ARGUMENTS --output observations`: the exit
    /// status, the document printed, and stderr.
    fn observe(&self, arguments: &[&str]) -> (Option<i32>, Json, String) {
        let mut all = vec!["--input", "start=0", "--input", "hole=0"];
        all.extend(arguments);
        all.extend(["--output", "observations"]);
        let (status, stdout, stderr) = self.krs("run", &all);
        assert_eq!(stdout.lines().count(), 1, "{stdout}{stderr}");
        let document = serde_json::from_str(&stdout).unwrap_or_else(|error| {
            panic!("{error}: {stdout}{stderr}");
        });
        (status, document, stderr)
    }

    /// Write `text` to the workspace file `name`; its path as text.
    fn write(&self, name: &str, text: &str) -> String {
        let path = self.path(name);
        fs::write(&path, text).unwrap();
        path.to_str().unwrap().to_owned()
    }
}

fn workspace() -> &'static Workspace {
    static WORKSPACE: OnceLock<Workspace> = OnceLock::new();
    WORKSPACE.get_or_init(Workspace::new)
}

/// The observer's facet, and the machine's, which the observer composes.
fn observer_arguments() -> [String; 2] {
    ["--dependency".to_owned(), format!("{PACKAGE}:main")]
}

/// The values of the channel `channel` of a document.
fn values(document: &Json, channel: usize) -> Vec<Json> {
    document["channels"][channel]["elements"]
        .as_array()
        .unwrap()
        .iter()
        .map(|element| element["value"].clone())
        .collect()
}

/// A class `name` sampling before both rules, by their KRS items, under `stutter`, reading
/// `cells`, with `extra` lines.
fn class(name: &str, stutter: &str, cells: &str, extra: &str) -> String {
    format!(
        "[[observe.point]]\nname = \"{name}\"\nbefore = [\"crate::tick\", \"crate::emit\"]\nstutter = \"{stutter}\"\ncells = [{cells}]\n{extra}"
    )
}

/// `--output observations` prints the one `krs-observations/1` document of the declaration
/// `--observe FILE` states: under `count` an element per point, under `collapse` one for the
/// bookkeeping `phase`, a log's items as they are appended; a depth bound leaves the channels
/// open and is yes (0), since it ends only what is known. `--output json` carries the summary.
#[test]
fn observations_of_a_free_running_run_to_its_depth() {
    let workspace = workspace();
    let declaration = workspace.write(
        "free.toml",
        &format!(
            "{}{}[[observe.log]]\nname = \"out\"\ncell = \"out\"\nat = [\"n\"]\n",
            class("n", "count", "\"n\"", ""),
            class("phase", "collapse", "\"phase\"", ""),
        ),
    );
    let (status, document, stderr) =
        workspace.observe(&["--depth", "9", "--observe", &declaration]);
    assert_eq!(status, Some(0), "{stderr}");
    assert_eq!(document["schema"], "krs-observations/1");
    assert_eq!(
        values(&document, 0),
        (0..9).map(|n| json!({"n": n})).collect::<Vec<_>>()
    );
    assert_eq!(values(&document, 1), [json!({"phase": 7})]);
    let out = |n: i64| json!({"Out": {"n": n}});
    assert_eq!(values(&document, 2), [out(2), out(5), out(8)]);
    let first = &document["channels"][0]["elements"][2];
    assert_eq!(
        first,
        &json!({"index": 2, "depth": 2, "rule": "crate::emit", "side": "before", "value": {"n": 2}})
    );
    for channel in document["channels"].as_array().unwrap() {
        assert_eq!(channel["closed"], Json::Null, "{channel}");
        let open = &channel["open"];
        assert_eq!(open["index"], channel["elements"].as_array().unwrap().len());
        assert!(
            open["reason"].as_str().unwrap().contains("depth-bound"),
            "{open}"
        );
    }
    assert_eq!(document["channels"][2]["kind"], "log");
    assert!(
        stderr.contains("krs run: depth-bound after 9 steps"),
        "{stderr}"
    );
    // The run document summarizes each channel.
    let (status, stdout, stderr) = workspace.krs(
        "run",
        &[
            "--input",
            "start=0",
            "--input",
            "hole=0",
            "--depth",
            "9",
            "--observe",
            &declaration,
            "--output",
            "json",
        ],
    );
    assert_eq!(status, Some(0), "{stderr}");
    let report: Json = serde_json::from_str(&stdout).unwrap();
    assert_eq!(report["schema"], "krs-exec/7");
    assert_eq!(
        report["run"]["observations"]["channels"][0],
        json!({"name": "n", "kind": "point", "elements": 9, "closed": null, "open": {"index": 9, "reason": document["channels"][0]["open"]["reason"]}})
    );
    // A JSON declaration states the same.
    let json_declaration = workspace.write(
        "free.json",
        r#"{"observe": {"point": [{"name": "n", "before": ["crate::tick", "crate::emit"], "stutter": "count", "cells": ["n"]}]}}"#,
    );
    let (status, again, stderr) =
        workspace.observe(&["--depth", "9", "--observe", &json_declaration]);
    assert_eq!(status, Some(0), "{stderr}");
    assert_eq!(again["channels"][0], document["channels"][0]);
}

/// A case's `observe` declares its run's observations, in an observer it names: a view, a
/// component of two cells and a filter, evaluated in the observer package; with no observer
/// named, a function of the run's own definition is evaluated in another copy of it. A
/// document of named cases gives its `observe` to every case that has none of its own.
#[test]
fn a_case_declares_its_observations_in_its_observer() {
    let workspace = workspace();
    let observed = class(
        "even",
        "count",
        "\"n\"",
        "views = { n = \"Twice\" }\ncomponents = [{ name = \"gap\", cells = [\"n\", \"phase\"], function = \"Gap\" }]\nwhen = { function = \"Even\", cells = [\"n\"] }\n",
    );
    let case = workspace.write(
        "observed.toml",
        &format!(
            "[inputs]\nstart = 0\nhole = 0\n[run]\ndepth = 6\n[observe]\nobserver = \"{OBSERVER_PACKAGE}:main\"\n{observed}"
        ),
    );
    let [dependency, facet] = observer_arguments();
    let (status, stdout, stderr) = workspace.krs(
        "run",
        &[
            "--case",
            &case,
            "--output",
            "observations",
            &dependency,
            &facet,
        ],
    );
    assert_eq!(status, Some(0), "{stderr}");
    let document: Json = serde_json::from_str(&stdout).unwrap();
    assert_eq!(
        values(&document, 0),
        [
            json!({"n": 0, "gap": -7}),
            json!({"n": 4, "gap": -5}),
            json!({"n": 8, "gap": -3}),
        ]
    );
    // `Natural`, the machine's own function, needs no observer named.
    let own = workspace.write(
        "own.toml",
        &class("n", "count", "\"n\"", "views = { n = \"Natural\" }\n"),
    );
    let (status, document, stderr) = workspace.observe(&["--depth", "3", "--observe", &own]);
    assert_eq!(status, Some(0), "{stderr}");
    assert_eq!(
        values(&document, 0),
        [json!({"n": 0}), json!({"n": 1}), json!({"n": 2})]
    );
    // A document of named cases: `a` takes the document's `observe`, `b` its own.
    let named = workspace.write(
        "named.toml",
        &format!(
            "{}[[case]]\nname = \"a\"\ninputs = {{ start = 0, hole = 0 }}\nrun = {{ depth = 2 }}\n[[case]]\nname = \"b\"\ninputs = {{ start = 0, hole = 0 }}\nrun = {{ depth = 2 }}\n[[case.observe.point]]\nname = \"phase\"\nbefore = [\"crate::tick\"]\nstutter = \"collapse\"\ncells = [\"phase\"]\n",
            class("n", "count", "\"n\"", "")
        ),
    );
    for (name, expected) in [
        ("a", vec![json!({"n": 0}), json!({"n": 1})]),
        ("b", vec![json!({"phase": 7})]),
    ] {
        let selected = format!("{named}#{name}");
        let (status, stdout, stderr) =
            workspace.krs("run", &["--case", &selected, "--output", "observations"]);
        assert_eq!(status, Some(0), "{stderr}");
        let document: Json = serde_json::from_str(&stdout).unwrap();
        assert_eq!(values(&document, 0), expected, "{name}");
    }
}

/// A log reads the items appended since its last read; a cell that does not only grow by
/// appending refuses the run (2) with the observation's diagnostic code.
#[test]
fn a_log_reads_appended_items_and_refuses_a_rewritten_one() {
    let workspace = workspace();
    let twins = workspace.write(
        "twins.toml",
        &format!(
            "[observe]\nobserver = \"{OBSERVER_PACKAGE}:main\"\n[[observe.log]]\nname = \"twins\"\ncell = \"out\"\nelement = \"Twin\"\n"
        ),
    );
    let [dependency, facet] = observer_arguments();
    let (status, document, stderr) =
        workspace.observe(&["--depth", "6", "--observe", &twins, &dependency, &facet]);
    assert_eq!(status, Some(0), "{stderr}");
    let out = |n: i64| json!({"Out": {"n": n}});
    assert_eq!(values(&document, 0), [out(2), out(2), out(5), out(5)]);
    let ring = workspace.write(
        "ring.toml",
        &format!(
            "{}[[observe.log]]\nname = \"ring\"\ncell = \"ring\"\nat = [\"steps\"]\n",
            class("steps", "count", "", "")
        ),
    );
    let (status, stdout, stderr) = workspace.krs(
        "run",
        &[
            "--input",
            "start=0",
            "--input",
            "hole=0",
            "--depth",
            "9",
            "--observe",
            &ring,
            "--output",
            "observations",
        ],
    );
    assert_eq!(status, Some(2), "{stderr}");
    assert!(stdout.is_empty(), "{stdout}");
    assert!(
        stderr.contains("error[krs::exec::observation]: the observation `ring` has no value"),
        "{stderr}"
    );
    assert!(stderr.contains("log-not-appended"), "{stderr}");
}

/// An element with no value refuses the run (2), naming the channel, the point's side and rule,
/// the steps and the component; whatever the output, since the observation sequence the run
/// declares does not exist.
#[test]
fn no_value_refuses_naming_arrival_rule_depth_cell() {
    let workspace = workspace();
    let small = workspace.write(
        "small.toml",
        &format!(
            "[observe]\nobserver = \"{OBSERVER_PACKAGE}:main\"\n{}",
            class(
                "small",
                "count",
                "",
                "components = [{ name = \"small\", cells = [\"n\"], function = \"Small\" }]\n"
            )
        ),
    );
    let [dependency, facet] = observer_arguments();
    for output in ["observations", "pretty"] {
        let (status, _, stderr) = workspace.krs(
            "run",
            &[
                "--input",
                "start=0",
                "--input",
                "hole=0",
                "--depth",
                "9",
                "--observe",
                &small,
                &dependency,
                &facet,
                "--output",
                output,
            ],
        );
        assert_eq!(status, Some(2), "{stderr}");
        assert!(
            stderr.contains(
                "error[krs::exec::observation]: the observation `small` has no value at the before point of `crate::tick` after 3 steps: the component `small`"
            ),
            "{stderr}"
        );
    }
}

/// An element whose evaluation spends `--view-budget` is undecided: the document carries its
/// reason in place of a value, and the status is no answer (3).
#[test]
fn undecided_is_inconclusive() {
    let workspace = workspace();
    let climbing = workspace.write(
        "climb.toml",
        &format!(
            "[observe]\nobserver = \"{OBSERVER_PACKAGE}:main\"\n{}",
            class(
                "climb",
                "count",
                "",
                "components = [{ name = \"climb\", cells = [\"n\"], function = \"Climb\" }]\n"
            )
        ),
    );
    let [dependency, facet] = observer_arguments();
    let (status, document, stderr) = workspace.observe(&[
        "--depth",
        "2",
        "--observe",
        &climbing,
        "--view-budget",
        "50",
        &dependency,
        &facet,
    ]);
    assert_eq!(status, Some(3), "{stderr}");
    let elements = document["channels"][0]["elements"].as_array().unwrap();
    assert_eq!(elements.len(), 2);
    for element in elements {
        assert!(element.get("value").is_none(), "{element}");
        assert!(element["undecided"].is_string(), "{element}");
    }
}

/// A run that ends at a stop closes its channels (`end`); with an expectation, the verdict and
/// the observations' status join as a batch's do: met and known is 0, unmet is 1.
#[test]
fn a_stop_closes_the_channels_and_an_expectation_joins_the_status() {
    let workspace = workspace();
    let case = |name: &str, n: i64| {
        workspace.write(
            name,
            &format!(
                "[inputs]\nstart = 0\nhole = 0\n[run]\nstop_before = [\"crate::emit\"]\n{}[expect]\nhalt = \"stopped\"\nrule = \"crate::emit\"\ncompare = [\"n\"]\ncells = {{ n = {n} }}\n",
                class("n", "count", "\"n\"", "")
            ),
        )
    };
    let met = case("met.toml", 2);
    let (status, stdout, stderr) =
        workspace.krs("run", &["--case", &met, "--output", "observations"]);
    assert_eq!(status, Some(0), "{stderr}");
    let document: Json = serde_json::from_str(&stdout).unwrap();
    assert_eq!(document["channels"][0]["closed"], "end");
    assert_eq!(document["channels"][0]["open"], Json::Null);
    assert_eq!(values(&document, 0), [json!({"n": 0}), json!({"n": 1})]);
    assert!(stderr.contains("krs run: expectation met"), "{stderr}");
    let unmet = case("unmet.toml", 3);
    let (status, _, stderr) = workspace.krs("run", &["--case", &unmet, "--output", "observations"]);
    assert_eq!(status, Some(1), "{stderr}");
}

/// A declaration the run cannot record is refused before the run (2), with the observation's
/// diagnostic code, naming the channel and the cause; a declaration that is no declaration is
/// refused naming its key: from `--observe FILE` with the observation's code, from a case
/// document with the case's.
#[test]
fn refusals() {
    let workspace = workspace();
    let run = |declaration: &str| {
        workspace.krs(
            "run",
            &[
                "--input",
                "start=0",
                "--input",
                "hole=0",
                "--depth",
                "2",
                "--observe",
                declaration,
            ],
        )
    };
    for (name, cells, expected) in [
        ("hidden.toml", "\"hidden\"", "hidden"),
        (
            "timer.toml",
            "\"timer\"",
            "is or is below the optional cell `timer`",
        ),
        ("group.toml", "\"cpu\"", "is a group cell"),
    ] {
        let declaration = workspace.write(name, &class("c", "count", cells, ""));
        let (status, _, stderr) = run(&declaration);
        assert_eq!(status, Some(2), "{stderr}");
        assert!(
            stderr.contains("error[krs::exec::observation]: the point class `c`"),
            "{stderr}"
        );
        assert!(stderr.contains(expected), "{expected}: {stderr}");
    }
    let declaration = workspace.write(
        "nostutter.toml",
        "[[observe.point]]\nname = \"c\"\nbefore = [\"crate::tick\"]\n",
    );
    let (status, _, stderr) = run(&declaration);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains("error[krs::exec::observation]: the observations `")
            && stderr.contains(
                "at `observe.point[0]`: a point class has a `stutter`, which has no default"
            ),
        "{stderr}"
    );
    let case = workspace.write(
        "badcase.toml",
        "[inputs]\nstart = 0\nhole = 0\n[[observe.point]]\nname = \"c\"\nstutter = \"twice\"\n",
    );
    let (status, _, stderr) = workspace.krs("run", &["--case", &case]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains("error[krs::exec::case]: case `")
            && stderr.contains("at `observe.point[0]`: `stutter` is `collapse`"),
        "{stderr}"
    );
}

/// Each refusal of a document that is no declaration names its key and its position.
#[test]
fn decode_refusals_name_their_key() {
    let refusal = |text: &str| ObservationSpec::from_toml(text).unwrap_err().to_string();
    let point =
        |extra: &str| format!("[[observe.point]]\nname = \"c\"\nstutter = \"count\"\n{extra}");
    for (text, expected) in [
        (
            "observe = 1\n".to_owned(),
            "at `observe`: `observe` is a table of `observer`, `point` and `log`",
        ),
        (
            "[observe]\nother = 1\n".to_owned(),
            "at `observe`: unknown key `other` in `observe`; it has the keys `observer`, `point` and `log`",
        ),
        (
            "[observe]\npoint = 1\n".to_owned(),
            "at `observe`: `point` is an array of point classes, each a table",
        ),
        (
            "[observe]\nobserver = \"p:d\"\n".to_owned(),
            "at `observe`: `observer` names the definition the declaration's functions are evaluated in, and it declares none",
        ),
        (
            "[observe]\nobserver = \"\"\n".to_owned(),
            "at `observe`: `observer` is the definition",
        ),
        (
            "[[observe.point]]\nstutter = \"count\"\n".to_owned(),
            "at `observe.point[0]`: a point class has a `name`",
        ),
        (
            "[[observe.point]]\nname = \"c\"\n".to_owned(),
            "at `observe.point[0]`: a point class has a `stutter`, which has no default",
        ),
        (
            point("stutter2 = 1\n"),
            "at `observe.point[0]`: unknown key `stutter2` in a point class",
        ),
        (
            point("before = \"crate::tick\"\n"),
            "at `observe.point[0]`: `before` is an array of rule names",
        ),
        (
            point("after = [1]\n"),
            "at `observe.point[0]`: `after` is an array of rule names",
        ),
        (
            point("cells = \"n\"\n"),
            "at `observe.point[0]`: `cells` is an array of leaf cells",
        ),
        (
            point("views = { n = 1 }\n"),
            "at `observe.point[0]`: `views` is a table of a function's path by cell",
        ),
        (
            point("components = [{ name = \"g\", cells = [\"n\"] }]\n"),
            "at `observe.point[0].components[0]`: a component is a table of `name`, `cells`",
        ),
        (
            point("when = { function = \"Even\" }\n"),
            "at `observe.point[0]`: `when` is a table of `function`",
        ),
        (
            "[[observe.log]]\nname = \"l\"\n".to_owned(),
            "at `observe.log[0]`: a log has a `cell`",
        ),
        (
            "[[observe.log]]\nname = \"l\"\ncell = \"out\"\nelement = 1\n".to_owned(),
            "at `observe.log[0]`: `element` is the path of a function `Item -> List<_>`",
        ),
        (
            "[[observe.log]]\nname = \"l\"\ncell = \"out\"\nat = \"steps\"\n".to_owned(),
            "at `observe.log[0]`: `at` is an array of the names of the point classes",
        ),
        (
            "[[observe.log]]\ncell = \"out\"\n".to_owned(),
            "at `observe.log[0]`: a log has a `name`",
        ),
        (
            "[run]\ndepth = 1\n".to_owned(),
            "unknown key `run`; an observation document is a table whose one key is `observe`",
        ),
    ] {
        let message = refusal(&text);
        assert!(
            message.starts_with(expected),
            "{expected:?} is not the start of {message:?}"
        );
    }
}

/// An empty declaration declares no channel; a whole one reads every key.
#[test]
fn a_declaration_reads_every_key() {
    assert!(
        ObservationSpec::from_toml("[observe]\n")
            .unwrap()
            .is_empty()
    );
    let spec = ObservationSpec::from_toml(&format!(
        "[observe]\nobserver = \"p:d\"\n{}[[observe.log]]\nname = \"l\"\ncell = \"out\"\nelement = \"Twin\"\nat = [\"c\"]\n",
        class("c", "collapse", "\"n\"", "after = [\"crate::emit\"]\nviews = { n = \"Twice\" }\ncomponents = [{ name = \"g\", cells = [\"n\", \"phase\"], function = \"Gap\" }]\nwhen = { function = \"Even\", cells = [\"n\"] }\n")
    ))
    .unwrap();
    assert_eq!(spec.observer.as_deref(), Some("p:d"));
    let class = &spec.points[0];
    assert_eq!(class.stutter, Stutter::Collapse);
    assert_eq!(class.before, ["crate::tick", "crate::emit"]);
    assert_eq!(class.after, ["crate::emit"]);
    assert_eq!(class.views["n"], "Twice");
    assert_eq!(class.components[0].cells, ["n", "phase"]);
    assert_eq!(class.when.as_ref().unwrap().function, "Even");
    assert_eq!(spec.logs[0].element.as_deref(), Some("Twin"));
    assert_eq!(spec.logs[0].at, ["c"]);
}

/// The usage errors: `--output observations` with nothing declared; `--observe` beside a case
/// that declares its own; an observation file of another extension; `--observe` with another
/// command; and `krs search` of a case that declares observations, which a search does not
/// record.
#[test]
fn usage_errors() {
    let workspace = workspace();
    let usage = |verb: &str, arguments: &[&str], expected: &str| {
        let (status, _, stderr) = workspace.krs(verb, arguments);
        assert_eq!(status, Some(2), "{stderr}");
        assert!(stderr.contains(expected), "{expected}: {stderr}");
    };
    usage(
        "run",
        &["--input", "start=0", "--output", "observations"],
        "--output observations prints the observations the run declares; declare them with --observe FILE",
    );
    let declared = workspace.write(
        "declared.toml",
        &format!(
            "[inputs]\nstart = 0\nhole = 0\n[run]\ndepth = 1\n{}",
            class("n", "count", "\"n\"", "")
        ),
    );
    let flag = workspace.write("flag.toml", &class("n", "count", "\"n\"", ""));
    usage(
        "run",
        &["--case", &declared, "--observe", &flag],
        "--observe and the `observe` of the case",
    );
    let bare = workspace.write("bare.toml", "[inputs]\nstart = 0\nhole = 0\n");
    usage(
        "run",
        &["--case", &bare, "--output", "observations"],
        "and the case `",
    );
    usage(
        "run",
        &["--observe", "declaration.yaml"],
        "--observe `declaration.yaml` has the extension `.yaml`; an observation file is `.toml` or `.json`",
    );
    usage(
        "search",
        &["--input", "start=0", "--observe", &flag],
        "--observe does not apply to krs search",
    );
    usage(
        "search",
        &["--case", &declared],
        "declares observations (`observe`), which krs search does not record",
    );
    usage(
        "run",
        &["--input", "start=0", "--output", "observation"],
        "unknown --output format `observation` for krs run",
    );
}

/// `krs cases` runs a case's observations as `krs run --case` does: a case whose observation
/// has no value is refused, and one whose observations are recorded is judged on its
/// expectation alone.
#[test]
fn cases_record_a_case_s_observations_as_run_does() {
    let workspace = workspace();
    let cases = workspace.write(
        "batch.toml",
        &format!(
            "[[case]]\nname = \"known\"\ninputs = {{ start = 0, hole = 0 }}\nrun = {{ stop_before = [\"crate::emit\"] }}\nexpect = {{ halt = \"stopped\", rule = \"crate::emit\", compare = [\"n\"], cells = {{ n = 2 }} }}\n{}[[case]]\nname = \"rewritten\"\ninputs = {{ start = 0, hole = 0 }}\nrun = {{ depth = 9 }}\n[[case.observe.point]]\nname = \"steps\"\nbefore = [\"crate::tick\", \"crate::emit\"]\nstutter = \"count\"\n[[case.observe.log]]\nname = \"ring\"\ncell = \"ring\"\nat = [\"steps\"]\n",
            "[[case.observe.point]]\nname = \"n\"\nbefore = [\"crate::tick\"]\nstutter = \"count\"\ncells = [\"n\"]\n"
        ),
    );
    let (status, stdout, stderr) = workspace.krs("cases", &[&cases, "--output", "json"]);
    assert_eq!(status, Some(2), "{stdout}{stderr}");
    let records = stdout
        .lines()
        .map(|line| serde_json::from_str::<Json>(line).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(records[0]["verdict"], "met", "{}", records[0]);
    assert_eq!(records[1]["verdict"], "refused", "{}", records[1]);
    assert!(
        records[1]["reason"]
            .as_str()
            .unwrap()
            .contains("the observation `ring` has no value"),
        "{}",
        records[1]
    );
    for (name, status) in [("known", 0), ("rewritten", 2)] {
        let selected = format!("{cases}#{name}");
        let (run, _, stderr) = workspace.krs("run", &["--case", &selected, "--output", "none"]);
        assert_eq!(run, Some(status), "{name}: {stderr}");
    }
}
