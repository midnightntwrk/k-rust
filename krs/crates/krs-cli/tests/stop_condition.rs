//! Stop conditions (`--stop-when`, a case's `run.stop_when`): a run ends at the `count`th arrival
//! at a stop rule whose stop state a named `Bool` function of named cells holds of, evaluated in
//! a fixed observer definition.
//!
//! The fixture (`fixtures/stop-condition`) is a free-running counter: `tick` adds 1 to `n` and 2
//! to `m`, from `n = start` and `m = 0`, so every step is an arrival at `tick`. Its observer
//! (`fixtures/stop-condition-observe`) depends on it and holds the conditions of two cells.

use std::fs;
use std::path::Path;
use std::sync::OnceLock;

use krs_exec::{
    CompiledStage, ConfigInputs, Halt, RunOptions, Semantics, State, StopCriterion, StopRules,
    StopWhen,
};
use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;
use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::Value as Json;

const FIXTURE: &str = include_str!("fixtures/stop-condition/src/lib.rs");
const PACKAGE: &str = "krs-stop-condition-fixture";
const OBSERVER: &str = include_str!("fixtures/stop-condition-observe/src/lib.rs");
const OBSERVER_PACKAGE: &str = "krs-stop-condition-observe-fixture";

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

/// The counter and its observer in one workspace, and the fixture target `krs` builds in.
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
                "counter",
                FIXTURE,
                manifest(PACKAGE, "ORG-KRS-STOP-CONDITION", ""),
            ),
            (
                "observe",
                OBSERVER,
                manifest(
                    OBSERVER_PACKAGE,
                    "ORG-KRS-STOP-CONDITION-OBSERVE",
                    &format!("counter = {{ package = \"{PACKAGE}\", path = \"../counter\" }}\n"),
                ),
            ),
        ] {
            fs::create_dir_all(root.join(member).join("src")).unwrap();
            fs::write(root.join(member).join("src/lib.rs"), source).unwrap();
            fs::write(root.join(member).join("Cargo.toml"), manifest).unwrap();
        }
        fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"counter\", \"observe\"]\nresolver = \"3\"\n",
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

    /// `krs VERB --package PACKAGE --definition main ARGUMENTS` from the counter's directory:
    /// the exit status, stdout and stderr.
    fn krs(&self, verb: &str, arguments: &[&str]) -> (Option<i32>, String, String) {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        let output = process
            .current_dir(self.path("counter"))
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

    /// `krs run` from `start`, the JSON report's `run`, with `arguments`.
    fn run_json(&self, start: i64, arguments: &[&str]) -> Json {
        let input = format!("start={start}");
        let mut all = vec!["--input", &input, "--output", "json"];
        all.extend(arguments);
        let (status, stdout, stderr) = self.krs("run", &all);
        assert!(matches!(status, Some(0 | 3)), "{stderr}");
        let report: Json = serde_json::from_str(&stdout).unwrap();
        assert_eq!(report["schema"], "krs-exec/5", "{report}");
        report["run"].clone()
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

/// The value of the cell `cell` in a JSON report's state: the token of the one argument of the
/// KAST application labelled `<cell>`.
fn cell(run: &Json, cell: &str) -> i64 {
    fn find(node: &Json, label: &str) -> Option<i64> {
        match node {
            Json::Object(object) => {
                if object.get("label").and_then(|label| label.get("name"))
                    == Some(&Json::from(label))
                {
                    return object["args"][0]["token"].as_str()?.parse().ok();
                }
                object.values().find_map(|value| find(value, label))
            }
            Json::Array(items) => items.iter().find_map(|item| find(item, label)),
            _ => None,
        }
    }
    find(&run["state"], &format!("<{cell}>")).unwrap_or_else(|| panic!("{}", run["state"]))
}

#[test]
fn stops_at_the_first_arrival_where_the_condition_holds() {
    let workspace = workspace();
    // Before `tick`: the stop states are n = 1, 2, 3; Third holds at the third.
    let run = workspace.run_json(1, &["--stop-before", "tick", "--stop-when", "n=Third"]);
    assert_eq!(run["halt"], "stopped");
    assert_eq!(run["steps"], 2);
    assert_eq!(cell(&run, "n"), 3);
    assert_eq!(run["stop"]["at"], "before");
    // After `tick`: the stop states are the successors n = 2, 3.
    let run = workspace.run_json(1, &["--stop-after", "tick", "--stop-when", "n=Third"]);
    assert_eq!(run["halt"], "stopped");
    assert_eq!(run["steps"], 2);
    assert_eq!(cell(&run, "n"), 3);
    // The status line names the condition and the arrivals.
    let (status, _, stderr) = workspace.krs(
        "run",
        &[
            "--input",
            "start=1",
            "--output",
            "none",
            "--stop-before",
            "tick",
            "--stop-when",
            "n=Third",
        ],
    );
    assert_eq!(status, Some(0), "{stderr}");
    assert!(
        stderr.contains(
            "krs run: stopped after 2 steps, before `crate::tick` (stop 1 of 1, where `Third` holds; 3 arrivals)"
        ),
        "{stderr}"
    );
}

#[test]
fn a_condition_of_two_cells() {
    let workspace = workspace();
    // m - n is -1, 0, 1, 2, 3, 4 at the stop states n = 1..6 before `tick`.
    let run = workspace.run_json(
        1,
        &[
            "--stop-before",
            "tick",
            "--stop-when",
            "n,m=Apart",
            "--observer",
            &format!("{OBSERVER_PACKAGE}:main"),
            "--dependency",
            &format!("{PACKAGE}:main"),
        ],
    );
    assert_eq!(run["halt"], "stopped", "{run}");
    assert_eq!(run["steps"], 5);
    assert_eq!((cell(&run, "n"), cell(&run, "m")), (6, 10));
    assert_eq!(run["arrivals"], 6);
}

#[test]
fn the_count_counts_arrivals_where_it_holds() {
    let workspace = workspace();
    // Third holds at n = 3 and n = 6: the second stop is after 5 steps.
    let run = workspace.run_json(
        1,
        &[
            "--stop-before",
            "tick",
            "--stop-when",
            "n=Third",
            "--stop-count",
            "2",
        ],
    );
    assert_eq!(run["steps"], 5);
    assert_eq!(cell(&run, "n"), 6);
    assert_eq!(run["stop"]["nth"], 2);
    assert_eq!(run["stops"], 2);
    assert_eq!(run["arrivals"], 6);
}

#[test]
fn the_report_counts_arrivals() {
    let workspace = workspace();
    let run = workspace.run_json(1, &["--stop-before", "tick", "--stop-when", "n=Third"]);
    assert_eq!(
        (run["stops"].clone(), run["arrivals"].clone()),
        (1.into(), 3.into())
    );
    // Without a condition every arrival is a stop, and no `arrivals` is reported.
    let run = workspace.run_json(1, &["--stop-before", "tick", "--stop-count", "3"]);
    assert_eq!(run["stops"], 3);
    assert_eq!(run.get("arrivals"), None);
}

#[test]
fn the_end_document_names_the_rule_and_reads_back_equal() {
    let workspace = workspace();
    let case = workspace.write(
        "third.toml",
        "[inputs]\nstart = 1\n[run]\nstop_before = [\"tick\"]\nstop_when = { function = \"Third\", cells = [\"n\"] }\n",
    );
    let (status, end, stderr) = workspace.krs("run", &["--case", &case, "--output", "end"]);
    assert_eq!(status, Some(0), "{stderr}");
    let document: Json = serde_json::from_str(&end).unwrap();
    assert_eq!(document["halt"], "stopped");
    assert_eq!(document["rule"], "crate::tick");
    let end = workspace.write("third-end.json", &end);
    let (status, stdout, stderr) = workspace.krs("compare", &[&case, &end]);
    assert_eq!(status, Some(0), "{stdout}{stderr}");
}

#[test]
fn a_depth_exhausted_first_is_inconclusive_under_an_expectation() {
    let workspace = workspace();
    let case = workspace.write(
        "shallow.toml",
        "[inputs]\nstart = 1\n[run]\ndepth = 1\nstop_before = [\"tick\"]\nstop_when = { function = \"Third\", cells = [\"n\"] }\n[expect]\nhalt = \"stopped\"\nrule = \"tick\"\ncompare = [\"n\"]\ncells = { n = 3 }\n",
    );
    let (status, _, stderr) = workspace.krs("run", &["--case", &case, "--output", "none"]);
    assert_eq!(status, Some(3), "{stderr}");
    assert!(stderr.contains("depth-bound"), "{stderr}");
}

#[test]
fn a_condition_without_value_refuses_naming_rule_depth_cell() {
    let workspace = workspace();
    // Natural has no value below 0: at the first arrival, n = -3.
    let (status, _, stderr) = workspace.krs(
        "run",
        &[
            "--input",
            "start=-3",
            "--stop-before",
            "tick",
            "--stop-when",
            "n=Natural",
            "--observer",
            &format!("{OBSERVER_PACKAGE}:main"),
            "--dependency",
            &format!("{PACKAGE}:main"),
        ],
    );
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains(
            "the stop condition has no value at the arrival at `crate::tick` after 0 steps"
        ),
        "{stderr}"
    );
    assert!(stderr.contains("`Natural` has no value"), "{stderr}");
}

/// A condition whose evaluation spends `--view-budget` leaves its arrival undecided: `krs run`
/// ends there, `stop-undecided` (3), naming the rule, the condition and why, which says that a
/// larger budget could decide it; `krs cases` records that halt and judges the case
/// inconclusive; and `krs compare`, of one pair and of `--pairs`, bounds each case side's
/// condition by the same budget and finds no end to compare.
#[test]
fn a_spent_budget_ends_stop_undecided() {
    let workspace = workspace();
    let observer = format!("{OBSERVER_PACKAGE}:main");
    let dependency = format!("{PACKAGE}:main");
    let budget = ["--view-budget", "100", "--dependency", &dependency];
    let mut flags = vec![
        "--input",
        "start=1",
        "--output",
        "json",
        "--stop-before",
        "tick",
        "--stop-when",
        "n=Climb",
        "--observer",
        &observer,
    ];
    flags.extend(budget);
    let (status, stdout, stderr) = workspace.krs("run", &flags);
    assert_eq!(status, Some(3), "{stderr}");
    let run = &serde_json::from_str::<Json>(&stdout).unwrap()["run"];
    assert_eq!(run["halt"], "stop-undecided", "{run}");
    assert_eq!(run["stop"], Json::Null, "{run}");
    assert_eq!(
        (run["stops"].clone(), run["arrivals"].clone()),
        (Json::Null, 1.into()),
        "{run}"
    );
    let undecided = &run["undecided"];
    assert_eq!(undecided["budget_spent"], true, "{run}");
    assert!(
        stderr.contains("a larger --view-budget can decide it"),
        "{stderr}"
    );
    assert_eq!(undecided["at"], "before", "{run}");
    assert_eq!(undecided["rule"]["item"], "crate::tick", "{run}");
    assert!(
        undecided["reason"]
            .as_str()
            .unwrap()
            .contains("it spent its budget of 100 polls"),
        "{run}"
    );
    assert!(
        stderr.contains(
            "krs run: stop-undecided after 0 steps, before `crate::tick`, undecided whether `Climb` holds (0 of 1 stops reached; 1 arrival): its evaluation stopped before it ended (it spent its budget of 100 polls)"
        ),
        "{stderr}"
    );

    let case = workspace.write(
        "climb.toml",
        &format!(
            "[inputs]\nstart = 1\n[run]\nstop_before = [\"tick\"]\nstop_when = {{ function = \"Climb\", cells = [\"n\"], observer = \"{observer}\" }}\n[expect]\nhalt = \"stopped\"\nrule = \"tick\"\ncompare = [\"n\"]\ncells = {{ n = 1 }}\n"
        ),
    );
    let mut arguments = vec![case.as_str(), "--output", "json"];
    arguments.extend(budget);
    let (status, stdout, stderr) = workspace.krs("cases", &arguments);
    assert_eq!(status, Some(3), "{stdout}{stderr}");
    let record: Json = serde_json::from_str(stdout.lines().next().unwrap()).unwrap();
    assert_eq!(record["schema"], "krs-cases/3", "{record}");
    assert_eq!(record["halt"], "stop-undecided", "{record}");
    assert_eq!(record["verdict"], "inconclusive", "{record}");
    // The record carries the run's stops, and its reason where and why it has no end, with the
    // remedy.
    assert_eq!(record["undecided"]["budget_spent"], true, "{record}");
    assert_eq!(record["stops"], 0, "{record}");
    assert!(
        record["reason"].as_str().unwrap().contains(
            "at the arrival before `crate::tick` after 0 steps, whether the stop condition holds is undecided"
        ) && record["reason"]
            .as_str()
            .unwrap()
            .contains("a larger budget of polls (`--view-budget`) can decide it"),
        "{record}"
    );

    // Each side is the case's run, under its condition and the budget: a run with no end.
    let mut arguments = vec![case.as_str(), case.as_str()];
    arguments.extend(budget);
    let (status, stdout, stderr) = workspace.krs("compare", &arguments);
    assert_eq!(status, Some(3), "{stdout}{stderr}");
    assert!(stdout.contains("stop-undecided"), "{stdout}{stderr}");
    assert!(stdout.contains("can decide it"), "{stdout}{stderr}");
    let pairs = workspace.write(
        "climb-pairs.toml",
        &format!("[[pair]]\nleft = {case:?}\nright = {case:?}\n"),
    );
    let mut arguments = vec!["--pairs", pairs.as_str()];
    arguments.extend(budget);
    let (status, stdout, stderr) = workspace.krs("compare", &arguments);
    assert_eq!(status, Some(3), "{stdout}{stderr}");
    assert!(stdout.contains("stop-undecided"), "{stdout}{stderr}");
}

/// A case whose `run` says where the run ends takes no stop flag beside it, `--stop-when`
/// included: the flags would change the case's question.
#[test]
fn a_case_with_its_own_stops_takes_no_stop_flag() {
    let workspace = workspace();
    let case = workspace.write(
        "own-stops.toml",
        "[inputs]\nstart = 1\n[run]\nstop_before = [\"tick\"]\n",
    );
    let (status, _, stderr) = workspace.krs(
        "run",
        &[
            "--case",
            &case,
            "--output",
            "none",
            "--stop-before",
            "tick",
            "--stop-when",
            "n=Third",
        ],
    );
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains("--stop-before, --stop-after, --stop-count and --stop-when, and the `run` stops of the case"),
        "{stderr}"
    );
}

#[test]
fn refusals() {
    let workspace = workspace();
    let refused = |when: &str, message: &str| {
        let (status, _, stderr) = workspace.krs(
            "run",
            &[
                "--input",
                "start=1",
                "--stop-before",
                "tick",
                "--stop-when",
                when,
            ],
        );
        assert_eq!(status, Some(2), "{when}: {stderr}");
        assert!(stderr.contains(message), "{when}: {stderr}");
    };
    refused("n=Nope", "the stop condition `Nope`");
    // A condition that does not resolve is refused under its own code.
    refused("n=Nope", "error[krs::exec::stop-condition]");
    refused(
        "n=Total",
        "takes 2 parameters, but the condition reads 1 cell",
    );
    refused("n,m=Total", "does not return Bool");
    refused("n=Set", "which does not admit the sort");
    refused("hidden=Third", "unobservable");
    refused("cpu=Third", "is a group cell");
    refused(
        "threads.thread.id=Third",
        "below the repeated cell `thread`",
    );
    refused("timer=Third", "below the optional cell `timer`");
    // The two-cell condition is the observer's: the counter's definition does not hold it.
    refused("n,m=Apart", "the stop condition `Apart`");
    // `krs compare` names the side and the case whose condition is refused, which the run's
    // own refusal cannot.
    let nope = workspace.write(
        "nope.toml",
        "[inputs]\nstart = 1\n[run]\nstop_before = [\"tick\"]\nstop_when = { function = \"Nope\", cells = [\"n\"] }\n",
    );
    let (status, stdout, stderr) = workspace.krs("compare", &[&nope, &nope]);
    assert_eq!(status, Some(2), "{stdout}{stderr}");
    assert!(
        stderr.contains("the left side, the case `")
            && stderr.contains("the stop condition `Nope`"),
        "{stderr}"
    );
    let (status, _, stderr) = workspace.krs("run", &["--stop-when", "n=Third"]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(stderr.contains("--stop-when needs --stop-before or --stop-after"));
    let (status, _, stderr) = workspace.krs("search", &["--stop-when", "n=Third"]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(stderr.contains("--stop-when does not apply to krs search"));
    let case = workspace.write(
        "no-rule.toml",
        "[inputs]\nstart = 1\n[run]\nstop_when = { function = \"Third\", cells = [\"n\"] }\n",
    );
    let (status, _, stderr) = workspace.krs("run", &["--case", &case]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains("`stop_when` needs `stop_before` or `stop_after`"),
        "{stderr}"
    );
    // Beside a case whose `run` names stops, a count or condition flag is refused for what is
    // wrong first: only one may say where the run ends. Beside a case that names none, it is
    // refused for having no rule.
    let ruled = workspace.write(
        "ruled.toml",
        "[inputs]\nstart = 1\n[run]\nstop_before = [\"tick\"]\n",
    );
    for flags in [&["--stop-when", "n=Third"][..], &["--stop-count", "2"][..]] {
        let mut arguments = vec!["--case", ruled.as_str()];
        arguments.extend(flags);
        let (status, _, stderr) = workspace.krs("run", &arguments);
        assert_eq!(status, Some(2), "{flags:?}: {stderr}");
        assert!(
            stderr.contains("both say where the run ends; a flag may not change a case's question"),
            "{flags:?}: {stderr}"
        );
    }
    let plain = workspace.write("plain.toml", "[inputs]\nstart = 1\n");
    let (status, _, stderr) = workspace.krs("run", &["--case", &plain, "--stop-count", "2"]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains("--stop-count needs --stop-before or --stop-after"),
        "{stderr}"
    );
    // A case's own `run` replaces its document's whole, so a count beside it names no rule.
    let named = workspace.write(
        "named.toml",
        "[run]\nstop_before = [\"tick\"]\n\n[[case]]\nname = \"third\"\n[case.inputs]\nstart = 1\n[case.run]\nstop_count = 3\n",
    );
    let (status, _, stderr) = workspace.krs("run", &["--case", &format!("{named}#third")]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains(
            "replaces the document's `run` whole, so it names none of the document's stop rules"
        ),
        "{stderr}"
    );
}

/// The counter's and the observer's Definition IR and compiled stages, built once.
fn compiled() -> &'static [(DefinitionIr, CompiledStage); 2] {
    static COMPILED: OnceLock<[(DefinitionIr, CompiledStage); 2]> = OnceLock::new();
    COMPILED.get_or_init(|| {
        let workspace = workspace();
        let emit = |member: &str, package: &str, extra: &[&str]| {
            let emitted = workspace.path(&format!("emitted-{package}"));
            let mut process = krs_command!();
            fixture_build_env(&mut process, workspace.target.path());
            let output = process
                .current_dir(workspace.path(member))
                .args([
                    "emit-k",
                    "--ir",
                    "--package",
                    package,
                    "--definition",
                    "main",
                ])
                .args(extra)
                .arg("--output")
                .arg(&emitted)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let definition: DefinitionIr =
                serde_json::from_slice(&fs::read(emitted.join("definition-ir.json")).unwrap())
                    .unwrap();
            let stage = CompiledStage::compile(&definition, &mut Timings::disabled()).unwrap();
            (definition, stage)
        };
        [
            emit("counter", PACKAGE, &[]),
            emit(
                "observe",
                OBSERVER_PACKAGE,
                &["--dependency", &format!("{PACKAGE}:main")],
            ),
        ]
    })
}

fn semantics((definition, stage): &(DefinitionIr, CompiledStage)) -> Semantics {
    Semantics::from_stage(definition, stage.clone(), None, &mut Timings::disabled()).unwrap()
}

/// The condition is evaluated in the observer package: the counter's own definition does not
/// declare `Apart`, and the run evaluates it in the observer definition it is given.
#[test]
fn evaluated_in_the_observer_package() {
    let [counter, observer] = compiled();
    on_worker_stack(|| evaluated_in(counter, observer));
}

fn evaluated_in(counter: &(DefinitionIr, CompiledStage), observer: &(DefinitionIr, CompiledStage)) {
    let mut subject = semantics(counter);
    let mut observer = semantics(observer);
    let when = StopWhen {
        function: "Apart".to_owned(),
        cells: vec!["n".to_owned(), "m".to_owned()],
        observer: Some(format!("{OBSERVER_PACKAGE}:main")),
    };
    assert!(subject.stop_condition(&subject, &when).is_err());
    assert!(subject.stop_condition(&observer, &when).is_ok());
    let state = start(&mut subject, 1);
    let options = RunOptions {
        stop: criterion(1, Some(when)),
        ..RunOptions::default()
    };
    let report = subject
        .run_observed(&state, options, Some(&mut observer))
        .unwrap();
    assert_eq!((report.halt, report.steps), (Halt::Stopped, 5));
    assert_eq!((report.stops, report.arrivals), (1, Some(6)));
}

fn start(semantics: &mut Semantics, start: i64) -> State {
    let text = start.to_string();
    semantics
        .configure(&ConfigInputs {
            variables: vec![("start".to_owned(), text.as_str().into())],
            ..ConfigInputs::default()
        })
        .unwrap()
}

/// Run `work` on a thread with the stack the run commands give their worker.
fn on_worker_stack(work: impl FnOnce() + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn_scoped(scope, work)
            .unwrap()
            .join()
            .unwrap();
    });
}

fn criterion(count: u64, when: Option<StopWhen>) -> StopCriterion {
    StopCriterion::Rules {
        rules: StopRules {
            before: vec!["tick".to_owned()],
            ..StopRules::default()
        },
        count: std::num::NonZeroU64::new(count).unwrap(),
        when,
    }
}

/// CF-22's invariant under a condition: a run to the Nth stop takes the steps of the runs to the
/// first stop resumed from each stop before it.
#[test]
fn pieces_sum_to_the_uncut_run() {
    let [counter, _] = compiled();
    on_worker_stack(|| pieces(counter));
}

fn pieces(counter: &(DefinitionIr, CompiledStage)) {
    let mut subject = semantics(counter);
    let mut twin = semantics(counter);
    let third = || StopWhen {
        function: "Third".to_owned(),
        cells: vec!["n".to_owned()],
        observer: None,
    };
    let state = start(&mut subject, 1);
    let uncut = subject
        .run_observed(
            &state,
            RunOptions {
                stop: criterion(3, Some(third())),
                ..RunOptions::default()
            },
            Some(&mut twin),
        )
        .unwrap();
    assert_eq!(
        (uncut.halt, uncut.steps, uncut.stops),
        (Halt::Stopped, 8, 3)
    );
    let mut from = state;
    let mut steps = 0;
    for _ in 0..3 {
        let piece = subject
            .run_observed(
                &from,
                RunOptions {
                    stop: criterion(1, Some(third())),
                    ..RunOptions::default()
                },
                Some(&mut twin),
            )
            .unwrap();
        assert_eq!(piece.halt, Halt::Stopped);
        steps += piece.steps;
        from = piece.resume();
    }
    assert_eq!(steps, uncut.steps);
}

/// `krs cases` and `krs compare` run a case under its condition as `krs run --case` does.
#[test]
fn cases_and_compare_agree_with_run_case() {
    let workspace = workspace();
    let case = workspace.write(
        "agree.toml",
        "[inputs]\nstart = 1\n[run]\nstop_before = [\"tick\"]\nstop_count = 2\nstop_when = { function = \"Third\", cells = [\"n\"] }\n[expect]\nhalt = \"stopped\"\nrule = \"tick\"\ncompare = [\"n\"]\ncells = { n = 6 }\n",
    );
    let (status, _, stderr) = workspace.krs("run", &["--case", &case, "--output", "none"]);
    assert_eq!(status, Some(0), "{stderr}");
    let (status, stdout, stderr) = workspace.krs("cases", &[&case, "--output", "json"]);
    assert_eq!(status, Some(0), "{stdout}{stderr}");
    let record: Json = serde_json::from_str(stdout.lines().next().unwrap()).unwrap();
    assert_eq!(record["schema"], "krs-cases/3");
    assert_eq!(record["verdict"], "met", "{record}");
    let (status, end, stderr) = workspace.krs("run", &["--case", &case, "--output", "end"]);
    assert_eq!(status, Some(0), "{stderr}");
    let end = workspace.write("agree-end.json", &end);
    let (status, stdout, stderr) = workspace.krs("compare", &["--expect", &case, &end]);
    assert_eq!(status, Some(0), "{stdout}{stderr}");
    let (status, stdout, stderr) = workspace.krs("compare", &[&case, &case]);
    assert_eq!(status, Some(0), "{stdout}{stderr}");
    // A condition with no value refuses the case.
    let refused = workspace.write(
        "refused.toml",
        &format!(
            "[inputs]\nstart = -3\n[run]\nstop_before = [\"tick\"]\nstop_when = {{ function = \"Natural\", cells = [\"n\"], observer = \"{OBSERVER_PACKAGE}:main\" }}\n[expect]\nhalt = \"stopped\"\ncompare = [\"n\"]\ncells = {{ n = 0 }}\n"
        ),
    );
    let dependency = format!("{PACKAGE}:main");
    let (status, stdout, stderr) = workspace.krs(
        "cases",
        &[&refused, "--output", "json", "--dependency", &dependency],
    );
    assert_eq!(status, Some(2), "{stdout}{stderr}");
    assert!(stdout.contains("\"verdict\":\"refused\""), "{stdout}");
    // One left undecided: [`a_spent_budget_ends_stop_undecided`].
}
