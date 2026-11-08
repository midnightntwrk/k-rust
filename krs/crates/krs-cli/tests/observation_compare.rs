//! `krs compare` over observations: a case side records the observations its `observe` declares,
//! an observation document (`krs-observations/1`) is a side of its own, and two sides are
//! compared on what both state, the observations by krs-exec's one comparison of records
//! (`compare_records`). The verdicts and their statuses, the refusals, `--pairs`, and a
//! comparison of ends alone, unchanged where no side states observations.
//!
//! The fixture is `tests/observations.rs`'s free-running machine (`fixtures/observations`): each
//! step adds 1 to `n`, and every third step (`emit`) appends `out(n)` to the `out` log. Its
//! observer (`fixtures/observations-observe`) holds the functions a declaration evaluates.

use std::fs;
use std::path::Path;
use std::sync::OnceLock;

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

    /// `krs VERB --package PACKAGE --definition main ARGUMENTS` from the machine's directory:
    /// the exit status, stdout and stderr.
    fn krs(&self, verb: &str, arguments: &[&str]) -> (Option<i32>, String, String) {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        let output = process
            .current_dir(self.directory.path().join("machine"))
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

    /// `krs compare ARGUMENTS --output json`: the exit status and the one document printed.
    fn compare_json(&self, arguments: &[&str]) -> (Option<i32>, Json) {
        let mut all = arguments.to_vec();
        all.extend(["--output", "json"]);
        let (status, stdout, stderr) = self.krs("compare", &all);
        let document = serde_json::from_str(&stdout).unwrap_or_else(|error| {
            panic!("{error}: {stdout}{stderr}");
        });
        (status, document)
    }

    /// Write `text` to the workspace file `name`; its path as text.
    fn write(&self, name: &str, text: &str) -> String {
        let path = self.directory.path().join(name);
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

/// The class `n`: the cell `n` at each step, under `count`.
const N: &str = "[[observe.point]]\nname = \"n\"\nbefore = [\"crate::tick\", \"crate::emit\"]\nstutter = \"count\"\ncells = [\"n\"]\n";

/// The log `out`, read at each step.
const OUT: &str = "[[observe.point]]\nname = \"steps\"\nbefore = [\"crate::tick\", \"crate::emit\"]\nstutter = \"count\"\n[[observe.log]]\nname = \"out\"\ncell = \"out\"\nat = [\"steps\"]\n";

/// A case document from `start`, its `run` table `run`, declaring `observe`.
fn case(workspace: &Workspace, name: &str, start: i64, run: &str, observe: &str) -> String {
    workspace.write(
        name,
        &format!("[inputs]\nstart = {start}\nhole = 0\n[run]\n{run}\n{observe}"),
    )
}

/// Two cases that declare the same observations and run alike agree: to both paths' end where a
/// stop closes the channels (equal, 0), and up to a horizon where their depth bound leaves the
/// channels open (equal up to a horizon, 0: the bound is the case's own, and ends only what is
/// known). Their ends are compared too, and agree.
#[test]
fn two_case_sides_that_agree() {
    let workspace = workspace();
    let stop = "stop_before = [\"crate::emit\"]";
    let left = case(workspace, "agree-left.toml", 0, stop, N);
    let right = case(workspace, "agree-right.toml", 0, stop, N);
    let (status, stdout, stderr) = workspace.krs("compare", &[&left, &right]);
    assert_eq!(status, Some(0), "{stdout}{stderr}");
    assert_eq!(
        stdout,
        "krs compare: equal\n  observation `n`: 2 elements agree, then both paths end\n"
    );
    let (status, document) = workspace.compare_json(&[&left, &right]);
    assert_eq!(status, Some(0));
    assert_eq!(
        document,
        json!({"schema": "krs-compare/1", "verdict": "equal", "observations": {"agree": [
            {"channel": "n", "through": 2, "left": "end", "right": "end"}
        ]}})
    );
    let left = case(workspace, "horizon-left.toml", 0, "depth = 4", N);
    let right = case(workspace, "horizon-right.toml", 0, "depth = 4", N);
    let (status, stdout, stderr) = workspace.krs("compare", &[&left, &right]);
    assert_eq!(status, Some(0), "{stdout}{stderr}");
    assert_eq!(
        stdout,
        "krs compare: equal up to a horizon\n  observation `n`: 4 elements agree, then both sides are open: the left side: the run ended `depth-bound`, which is no end of its path; the right side: the run ended `depth-bound`, which is no end of its path\n"
    );
}

/// Two cases whose observations differ are distinguished at the first decided difference (1),
/// which names the channel, the index, both elements and the path inside their values. The
/// observations are compared before the ends: where they agree, the ends still decide, so a
/// declared observation only adds distinctions.
#[test]
fn two_case_sides_that_differ_name_the_first_difference() {
    let workspace = workspace();
    let left = case(workspace, "differ-left.toml", 0, "depth = 4", N);
    let right = case(workspace, "differ-right.toml", 1, "depth = 4", N);
    let (status, stdout, stderr) = workspace.krs("compare", &[&left, &right]);
    assert_eq!(status, Some(1), "{stdout}{stderr}");
    assert_eq!(
        stdout,
        "krs compare: differs at the observation `n` element 0 at `n`\n  left:  {\"n\":0} (before `crate::tick`, after 0 steps)\n  right: {\"n\":1} (before `crate::tick`, after 0 steps)\n"
    );
    let (status, document) = workspace.compare_json(&[&left, &right]);
    assert_eq!(status, Some(1));
    assert_eq!(document["verdict"], "differs");
    assert_eq!(document.get("difference"), None, "{document}");
    assert_eq!(
        document["observations"],
        json!({"difference": {
            "channel": "n",
            "index": 0,
            "left": {"index": 0, "depth": 0, "rule": "crate::tick", "side": "before", "value": {"n": 0}},
            "right": {"index": 0, "depth": 0, "rule": "crate::tick", "side": "before", "value": {"n": 1}},
            "path": "n",
        }})
    );
    // The log of outputs abstracts when they happen: from 0 and from 1 the machine emits
    // out(2) then out(5), so the observations agree up to the horizon, and the ends differ.
    let left = case(workspace, "log-left.toml", 0, "depth = 6", OUT);
    let right = case(workspace, "log-right.toml", 1, "depth = 6", OUT);
    let (status, document) = workspace.compare_json(&[&left, &right, "--compare", "n"]);
    assert_eq!(status, Some(1), "{document}");
    assert_eq!(document["verdict"], "differs");
    assert_eq!(document["difference"]["cell"], "n", "{document}");
    let out = &document["observations"]["agree"][1];
    assert_eq!(out["channel"], "out");
    assert_eq!(out["through"], 2);
}

/// An observation document is a side: what `krs run --output observations` printed for one case
/// compares equal to that case's run, the ends left out since the document states none, and
/// differs from another case's, or from an edited copy at the path inside the edited value.
/// A document whose channels are not the other side's is refused (2), as are sides that state
/// nothing in common, and `--compare` where no ends are compared.
#[test]
fn a_document_side_against_a_case_side() {
    let workspace = workspace();
    let zero = case(workspace, "document-zero.toml", 0, "depth = 4", N);
    let one = case(workspace, "document-one.toml", 1, "depth = 4", N);
    let (status, printed, stderr) =
        workspace.krs("run", &["--case", &zero, "--output", "observations"]);
    assert_eq!(status, Some(0), "{stderr}");
    let document = workspace.write("zero-observations.json", &printed);
    let (status, verdict) = workspace.compare_json(&[&document, &zero]);
    assert_eq!(status, Some(0), "{verdict}");
    assert_eq!(verdict["verdict"], "equal");
    assert_eq!(verdict["observations"]["agree"][0]["through"], 4);
    let (status, verdict) = workspace.compare_json(&[&one, &document]);
    assert_eq!(status, Some(1), "{verdict}");
    assert_eq!(verdict["observations"]["difference"]["index"], 0);
    let mut edited: Json = serde_json::from_str(&printed).unwrap();
    edited["channels"][0]["elements"][2]["value"]["n"] = json!(7);
    let edited = workspace.write("edited-observations.json", &edited.to_string());
    let (status, verdict) = workspace.compare_json(&[&zero, &edited]);
    assert_eq!(status, Some(1), "{verdict}");
    let difference = &verdict["observations"]["difference"];
    assert_eq!(
        (difference["index"].clone(), difference["path"].clone()),
        (json!(2), json!("n"))
    );
    // Two documents compare without a run.
    let (status, verdict) = workspace.compare_json(&[&document, &edited]);
    assert_eq!(status, Some(1), "{verdict}");
    // Refusals.
    let out = case(workspace, "document-out.toml", 0, "depth = 4", OUT);
    let (status, _, stderr) = workspace.krs("compare", &[&document, &out]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains("error[krs::exec::observation]: the comparison: the left side's channels are `n` (point) and the right side's are `steps` (point), `out` (log); observations are compared under one declaration"),
        "{stderr}"
    );
    let bare = case(workspace, "document-bare.toml", 0, "depth = 4", "");
    let (status, _, stderr) = workspace.krs("compare", &[&document, &bare]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains("the left side, an observation document, states observations and no end, and the right side, a case, states an end and no observations (its case declares no `observe`): the two sides state nothing both can be compared on"),
        "{stderr}"
    );
    let (status, _, stderr) = workspace.krs("compare", &[&document, &zero, "--compare", "n"]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains("--compare and --view apply to the ends a comparison compares, and the left side, an observation document, states no end"),
        "{stderr}"
    );
    let (status, _, stderr) = workspace.krs("compare", &[&zero, &out]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains("declare different observations (`observe`)"),
        "{stderr}"
    );
    let broken = workspace.write(
        "broken-observations.json",
        r#"{"schema": "krs-observations/1", "channels": [{"name": "n", "kind": "point", "elements": [], "closed": null, "open": null}]}"#,
    );
    let (status, _, stderr) = workspace.krs("compare", &[&broken, &zero]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains("the observation document at `channels[0]`: a channel is closed (`closed`) or open (`open`)"),
        "{stderr}"
    );
    let expecting = case(
        workspace,
        "document-expecting.toml",
        0,
        "depth = 4",
        "[expect]\nhalt = \"depth-bound\"\n",
    );
    let (status, _, stderr) = workspace.krs("compare", &["--expect", &expecting, &document]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains("is an observation document, which states no end"),
        "{stderr}"
    );
}

/// An element whose evaluation spends `--view-budget` is unknown: where it comes before any
/// difference the comparison has no answer (3); a decided difference on another channel still
/// distinguishes the sides (1).
#[test]
fn an_undecided_element_is_inconclusive() {
    let workspace = workspace();
    let declaration = climb_declaration();
    let left = case(workspace, "climb-left.toml", 0, "depth = 2", &declaration);
    let right = case(workspace, "climb-right.toml", 0, "depth = 2", &declaration);
    let [dependency, facet] = observer_arguments();
    let arguments = |left: &str, right: &str| {
        vec![
            left.to_owned(),
            right.to_owned(),
            "--view-budget".to_owned(),
            "50".to_owned(),
            dependency.clone(),
            facet.clone(),
        ]
    };
    let same = arguments(&left, &right);
    let same = same.iter().map(String::as_str).collect::<Vec<_>>();
    let (status, stdout, stderr) = workspace.krs("compare", &same);
    assert_eq!(status, Some(3), "{stdout}{stderr}");
    assert!(
        stdout.starts_with(
            "krs compare: inconclusive: the observation `climb` element 0 is unknown on the left side: "
        ),
        "{stdout}"
    );
    let (status, verdict) = workspace.compare_json(&same);
    assert_eq!(status, Some(3));
    assert_eq!(verdict["verdict"], "inconclusive");
    let climb = &verdict["observations"]["agree"][1];
    assert_eq!(climb["uncompared"]["index"], 0, "{verdict}");
    assert_eq!(climb["uncompared"]["side"], "left", "{verdict}");
    let other = case(workspace, "climb-other.toml", 1, "depth = 2", &declaration);
    let differing = arguments(&left, &other);
    let differing = differing.iter().map(String::as_str).collect::<Vec<_>>();
    let (status, verdict) = workspace.compare_json(&differing);
    assert_eq!(status, Some(1), "{verdict}");
    assert_eq!(verdict["observations"]["difference"]["channel"], "n");
}

/// The declaration of [`an_undecided_element_is_inconclusive`]'s cases.
fn climb_declaration() -> String {
    format!(
        "[observe]\nobserver = \"{OBSERVER_PACKAGE}:main\"\n{N}[[observe.point]]\nname = \"climb\"\nbefore = [\"crate::tick\", \"crate::emit\"]\nstutter = \"count\"\ncomponents = [{{ name = \"climb\", cells = [\"n\"], function = \"Climb\" }}]\n"
    )
}

/// The case `ring`, whose log is rewritten rather than appended to: `krs run --case` refuses it
/// (its observation sequence does not exist).
fn ring(workspace: &Workspace) -> String {
    case(
        workspace,
        "ring.toml",
        0,
        "depth = 9",
        "[[observe.point]]\nname = \"steps\"\nbefore = [\"crate::tick\", \"crate::emit\"]\nstutter = \"count\"\n[[observe.log]]\nname = \"ring\"\ncell = \"ring\"\nat = [\"steps\"]\n",
    )
}

/// A case whose observations `krs run --case` and `krs cases` refuse is refused by `krs compare`
/// too (2), naming the side and the case, whatever the comparison reads of it: against an end
/// document, which compares ends alone, as against another case.
#[test]
fn a_refused_observation_case_is_refused_in_compare_too() {
    let workspace = workspace();
    let ring = ring(workspace);
    let (status, _, stderr) = workspace.krs("run", &["--case", &ring]);
    assert_eq!(status, Some(2), "{stderr}");
    let bare = case(workspace, "ring-bare.toml", 0, "depth = 9", "");
    let (status, end, stderr) = workspace.krs("run", &["--case", &bare, "--output", "end"]);
    assert_eq!(status, Some(0), "{stderr}");
    let end = workspace.write("ring-end.json", &end);
    for other in [&end, &ring] {
        let (status, _, stderr) = workspace.krs("compare", &[&ring, other]);
        assert_eq!(status, Some(2), "{stderr}");
        assert!(
            stderr.contains("error[krs::exec::observation]: the left side, the case `")
                && stderr.contains("the observation `ring` has no value"),
            "{stderr}"
        );
    }
}

/// `--pairs` compares each pair as `krs compare` compares it alone: observations agreeing,
/// differing, a document against a case, and a refused observation case, which refuses its
/// pair; the batch exits 2.
#[test]
fn pairs_compare_observations_as_a_single_comparison_does() {
    let workspace = workspace();
    let zero = case(workspace, "pairs-zero.toml", 0, "depth = 4", N);
    let again = case(workspace, "pairs-again.toml", 0, "depth = 4", N);
    let one = case(workspace, "pairs-one.toml", 1, "depth = 4", N);
    let (status, printed, stderr) =
        workspace.krs("run", &["--case", &zero, "--output", "observations"]);
    assert_eq!(status, Some(0), "{stderr}");
    let document = workspace.write("pairs-observations.json", &printed);
    let ring = ring(workspace);
    let pairs = workspace.write(
        "pairs.toml",
        &format!(
            "[[pair]]\nleft = \"{zero}\"\nright = \"{again}\"\n[[pair]]\nleft = \"{zero}\"\nright = \"{one}\"\n[[pair]]\nleft = \"{document}\"\nright = \"{again}\"\n[[pair]]\nleft = \"{ring}\"\nright = \"{ring}\"\n"
        ),
    );
    let (status, stdout, stderr) = workspace.krs(
        "compare",
        &["--pairs", &pairs, "--jobs", "2", "--output", "json"],
    );
    assert_eq!(status, Some(2), "{stdout}{stderr}");
    let records = stdout
        .lines()
        .map(|line| serde_json::from_str::<Json>(line).unwrap())
        .collect::<Vec<_>>();
    let verdicts = records[..4]
        .iter()
        .map(|record| record["verdict"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        verdicts,
        ["equal", "differs", "equal", "refused"],
        "{stdout}"
    );
    assert_eq!(records[1]["observations"]["difference"]["index"], 0);
    assert_eq!(records[2].get("difference"), None);
    assert!(
        records[3]["reason"]
            .as_str()
            .unwrap()
            .contains("the observation `ring` has no value"),
        "{}",
        records[3]
    );
    assert_eq!(
        records[4]["summary"],
        json!({"pairs": 4, "equal": 2, "differs": 1, "met": 0, "unmet": 0, "inconclusive": 0, "refused": 1})
    );
    // Each pair's verdict is the one `krs compare` gives it alone.
    let (_, alone) = workspace.compare_json(&[&zero, &one]);
    let mut paired = records[1].clone();
    paired.as_object_mut().unwrap().remove("pair");
    assert_eq!(paired, alone);
}

/// Where no side states observations the comparison is of ends alone, and its documents are
/// those of a comparison of ends; a case that declares observations against an end document
/// compares the ends, and says the observations are not compared.
#[test]
fn ends_only_compare_is_unchanged_without_observations() {
    let workspace = workspace();
    let left = case(workspace, "ends-left.toml", 0, "depth = 3", "");
    let right = case(workspace, "ends-right.toml", 0, "depth = 3", "");
    let (status, stdout, stderr) = workspace.krs("compare", &[&left, &right]);
    assert_eq!(status, Some(0), "{stderr}");
    assert_eq!(stdout, "krs compare: equal\n");
    let (status, document) = workspace.compare_json(&[&left, &right]);
    assert_eq!(status, Some(0));
    assert_eq!(
        document,
        json!({"schema": "krs-compare/1", "verdict": "equal"})
    );
    // An empty declaration declares no channel: ends alone.
    let empty = case(workspace, "ends-empty.toml", 0, "depth = 3", "[observe]\n");
    let (_, document) = workspace.compare_json(&[&left, &empty]);
    assert_eq!(
        document,
        json!({"schema": "krs-compare/1", "verdict": "equal"})
    );
    let (status, end, stderr) = workspace.krs("run", &["--case", &left, "--output", "end"]);
    assert_eq!(status, Some(0), "{stderr}");
    let end = workspace.write("ends-end.json", &end);
    let observed = case(workspace, "ends-observed.toml", 0, "depth = 3", N);
    let (status, stdout, stderr) = workspace.krs("compare", &[&observed, &end]);
    assert_eq!(status, Some(0), "{stderr}");
    assert_eq!(
        stdout,
        "krs compare: equal\n  observations not compared: the right side, an end document, states no observations\n"
    );
}
