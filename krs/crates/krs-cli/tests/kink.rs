//! `krs kink <verb>`: the corpus loop over a KRS package, with kink-flow as its engine.
//!
//! The main fixture is a copy of the introduction's story package (`docs-site/story/plus`) with
//! its corpus, `kink/FLOW.toml` and the story's four cases: the tool must report what the
//! story's pages claim, each rule named by its Rust item and position, and kill the story's
//! three edits written as K patches anchored by `plus_zero` and `plus_succ`. A small counter
//! definition, which has rewrite rules, gives `fuzz --matched` and a query witness rules to name;
//! `fixtures/inputs` gives a case of typed inputs. A definition of guarded transitions, a nondet
//! group, a branching function, a division in a condition and a claim helper gives the front
//! end's own mutation checks something to refuse, each checked against `krs check` of a Rust
//! source that emits the mutant.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;
use std::sync::{Arc, Mutex, Weak};

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::Value;

const STORY: &str = include_str!("../../../../docs-site/story/plus/src/lib.rs");
/// The story's corpus (`docs-site/story/plus/kink`), the one the introduction's pages show:
/// its manifest and four cases (story.toml `[[test]]`). The expectations below are what the
/// pages show for these programs, which the docs-site derives from its recorded outputs: the
/// coverage from `krs kink results` (story-kink-results), and the tests that catch each edit from
/// `krs kink run --full` (story-kink-run).
const STORY_FLOW: &str = include_str!("../../../../docs-site/story/plus/kink/FLOW.toml");
const STORY_CASES: [(&str, &str); 4] = [
    (
        "t1",
        include_str!("../../../../docs-site/story/plus/kink/cases/t1.nat"),
    ),
    (
        "t2",
        include_str!("../../../../docs-site/story/plus/kink/cases/t2.nat"),
    ),
    (
        "t3",
        include_str!("../../../../docs-site/story/plus/kink/cases/t3.nat"),
    ),
    (
        "t4",
        include_str!("../../../../docs-site/story/plus/kink/cases/t4.nat"),
    ),
];
const INPUTS: &str = include_str!("fixtures/inputs/src/lib.rs");

/// A definition with rewrite rules: `count(n)` steps down to `count(0)`, which stops.
const COUNTER: &str = r#"use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("count({value})")] Count { value: Int },
    #[k::syntax("done")] Done(),
}

#[k::rule]
#[k::requires(int::gt(value, 0))]
fn step(k::term![ExpSyntax::Count { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Count(int::sub(value, 1))
}

#[k::rule]
#[k::requires(int::le(value, 0))]
fn stop(k::term![ExpSyntax::Count { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Done()
}

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
"#;

/// The story's three edits (`docs-site/story/plus/kink/mutations/plus.toml`), the K patches the
/// introduction's mutation scenes make, each anchored by its Rust item and with the
/// misunderstanding the scenes quote.
const STORY_MUTATIONS: &str =
    include_str!("../../../../docs-site/story/plus/kink/mutations/plus.toml");

/// A package in a fresh directory, shared by the tests that overlap in this process: its
/// manifest path keys the collector's directory, so the tests that share it build it once, and
/// they run `krs` on it one at a time.
struct Project {
    package: &'static str,
    directory: TempDir,
    _target: SharedFixtureTarget,
    target: PathBuf,
    turn: Mutex<()>,
}

impl Project {
    fn new(package: &'static str, namespace: &str, files: &[(&str, &[u8])]) -> Self {
        let target = shared_fixture_target();
        let directory = temp_dir();
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        let project = Self {
            package,
            directory,
            target: target.path().to_path_buf(),
            _target: target,
            turn: Mutex::new(()),
        };
        project.write(
            "Cargo.toml",
            format!(
                "[package]\nname = \"{package}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
            ),
        );
        for (path, contents) in files {
            project.write(path, contents);
        }
        project
    }

    fn shared(slot: &'static Mutex<Weak<Self>>, build: impl FnOnce() -> Self) -> Arc<Self> {
        let mut slot = slot
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(project) = slot.upgrade() {
            return project;
        }
        let project = Arc::new(build());
        *slot = Arc::downgrade(&project);
        project
    }

    fn path(&self) -> &Path {
        self.directory.path()
    }

    fn write(&self, relative: &str, contents: impl AsRef<[u8]>) {
        let path = self.path().join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn read(&self, relative: &str) -> String {
        fs::read_to_string(self.path().join(relative)).unwrap()
    }

    /// `krs ARGUMENTS` with this package selected, from the package directory.
    fn krs(&self, arguments: &[&str]) -> Output {
        let _turn = self
            .turn
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut process = krs_command!();
        fixture_build_env(&mut process, &self.target);
        process.current_dir(self.path()).args(arguments).args([
            "--package",
            self.package,
            "--definition",
            "main",
        ]);
        process.output().unwrap()
    }

    /// `krs kink VERB ARGUMENTS`.
    fn kink(&self, verb: &str, arguments: &[&str]) -> Output {
        let mut all = vec!["kink", verb];
        all.extend_from_slice(arguments);
        self.krs(&all)
    }
}

/// The story package with its corpus, the files of `story_files`.
fn story_files() -> Vec<(String, Vec<u8>)> {
    let mut files = vec![
        ("src/lib.rs".to_owned(), STORY.as_bytes().to_vec()),
        ("kink/FLOW.toml".to_owned(), STORY_FLOW.as_bytes().to_vec()),
    ];
    for (id, text) in STORY_CASES {
        files.push((format!("kink/cases/{id}.nat"), text.as_bytes().to_vec()));
    }
    files
}

fn project_of(package: &'static str, namespace: &str, files: &[(String, Vec<u8>)]) -> Project {
    let files = files
        .iter()
        .map(|(path, bytes)| (path.as_str(), bytes.as_slice()))
        .collect::<Vec<_>>();
    Project::new(package, namespace, &files)
}

/// The story package shared by the tests that read it and edit only its corpus.
fn story() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, || project_of("story-plus", "NAT", &story_files()))
}

fn counter() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, || {
        project_of(
            "krs-cli-kink-counter",
            "COUNTER",
            &[
                ("src/lib.rs".to_owned(), COUNTER.as_bytes().to_vec()),
                (
                    "kink/FLOW.toml".to_owned(),
                    b"[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\nid = \"c3\"\nfile = \"cases/c3.cnt\"\n"
                        .to_vec(),
                ),
                ("kink/cases/c3.cnt".to_owned(), b"count(3)\n".to_vec()),
            ],
        )
    })
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn json(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
            stdout(output),
            stderr(output)
        )
    })
}

fn assert_status(output: &Output, code: i32) {
    assert_eq!(
        output.status.code(),
        Some(code),
        "stdout:\n{}\nstderr:\n{}",
        stdout(output),
        stderr(output)
    );
}

/// The 1-based line of the first line of `source` that contains `text`.
fn line_of(source: &str, text: &str) -> u64 {
    let index = source
        .lines()
        .position(|line| line.contains(text))
        .unwrap_or_else(|| panic!("{text:?} is not in the source"));
    u64::try_from(index).unwrap() + 1
}

/// The rule of a results document whose `krs.item` is `item`.
fn rule<'d>(document: &'d Value, item: &str) -> &'d Value {
    document["rules"]
        .as_array()
        .unwrap()
        .iter()
        .find(|rule| rule["krs"]["item"] == item)
        .unwrap_or_else(|| panic!("no rule names {item}: {:#}", document["rules"]))
}

fn strings(value: &Value) -> Vec<&str> {
    value
        .as_array()
        .unwrap_or_else(|| panic!("{value} is no array"))
        .iter()
        .map(|item| item.as_str().unwrap())
        .collect()
}

/// `results` reports each case's class and the rules it fires, each rule named by its Rust item
/// and position: the story's own coverage table.
#[test]
fn results_name_each_rule_by_its_rust_item_and_position() {
    let project = story();
    let output = project.kink("results", &[]);
    assert_status(&output, 0);
    let document = json(&output);
    assert_eq!(document["schema"], "kink-flow-results");
    assert!(
        matches!(
            document["definition"]["status"].as_str(),
            Some("written" | "unchanged")
        ),
        "{:#}",
        document["definition"]
    );
    assert_eq!(document["definition"]["path"], "kink/definition.k");
    for (item, function) in [
        ("plus_zero", "fn plus_zero("),
        ("plus_succ", "fn plus_succ("),
    ] {
        let krs = &rule(&document, item)["krs"];
        assert_eq!(krs["file"], "src/lib.rs", "{krs:#}");
        assert_eq!(krs["package"], "story-plus", "{krs:#}");
        assert_eq!(krs["kind"], "equation", "{krs:#}");
        assert_eq!(krs["claim_helper"], false, "{krs:#}");
        assert_eq!(krs["line"], line_of(STORY, function), "{krs:#}");
        assert!(krs["column"].as_u64().is_some(), "{krs:#}");
    }
    assert_eq!(
        strings(&rule(&document, "plus_zero")["fired_by"]),
        ["t1", "t2", "t3", "t4"]
    );
    assert_eq!(
        strings(&rule(&document, "plus_succ")["fired_by"]),
        ["t3", "t4"]
    );
    for program in document["programs"].as_array().unwrap() {
        assert_eq!(program["class"], "comparable", "{program:#}");
    }
    assert!(
        document.get("krs").is_none(),
        "every rule is named: {:#}",
        document["krs"]
    );

    // The verdicts rendering names the rules by the same items, as the docs-site's recorded
    // `story-kink-results` does.
    let output = project.kink("results", &["--output", "verdicts"]);
    assert_status(&output, 0);
    let verdicts = stdout(&output);
    // The story's rules are equations, each fired where it applies, and each case matches
    // exactly the rules it fires.
    for predicate in ["fired", "matched"] {
        let lines = verdicts
            .lines()
            .filter_map(|line| line.strip_prefix(predicate)?.strip_prefix(" = "))
            .collect::<Vec<_>>();
        assert_eq!(
            lines,
            [
                "[\"plus_zero\"]",
                "[\"plus_zero\"]",
                "[\"plus_succ\", \"plus_zero\"]",
                "[\"plus_succ\", \"plus_zero\"]",
            ],
            "{predicate}: {verdicts}"
        );
    }
}

/// `run` kills the story's three edits, written as K patches anchored by the Rust items, and a
/// full run finds exactly the killers the story's pages show (the docs-site takes them from its
/// recorded full run, story-kink-run).
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One story: its three patches, their kills and their pinned Rust locations."
)]
fn run_kills_the_story_edits() {
    let project = story();
    project.write("kink/mutations/plus.toml", STORY_MUTATIONS);
    let output = project.kink("run", &["--full"]);
    assert_status(&output, 0);
    let document = json(&output);
    let rows = document["mutations"].as_array().unwrap();
    let verdicts = rows
        .iter()
        .map(|row| {
            (
                row["id"].as_str().unwrap(),
                row["status"].as_str().unwrap(),
                strings(&row["killed_by"]),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        verdicts,
        [
            ("plus/a", "killed", vec!["t2", "t3", "t4"]),
            ("plus/b", "killed", vec!["t3", "t4"]),
            ("plus/c", "killed", vec!["t4"]),
        ],
        "{document:#}"
    );
    // `report` prints the stored run document as `run` printed it, named by the emission the
    // run judged; only the `definition` object is this command's.
    let output = project.kink("report", &[]);
    assert_status(&output, 0);
    let mut reported = json(&output);
    assert_eq!(reported["definition"]["status"], "unchanged");
    let mut printed = document.clone();
    reported.as_object_mut().unwrap().remove("definition");
    printed.as_object_mut().unwrap().remove("definition");
    assert_eq!(reported, printed);
    // `check` resolves the layout's mutations, runs nothing, and names each edited rule by its
    // item (a run row lists its edited rules only for a mutation that is not killed).
    let output = project.kink("check", &[]);
    assert_status(&output, 0);
    let check = json(&output);
    assert_eq!(check["schema"], "kink-flow-check");
    let named = check["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            let rules = row["rules"].as_array().unwrap();
            assert_eq!(rules.len(), 1, "{row:#}");
            (
                row["id"].as_str().unwrap(),
                rules[0]["krs"]["item"].as_str().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        named,
        [
            ("plus/a", "plus_zero"),
            ("plus/b", "plus_succ"),
            ("plus/c", "plus_succ")
        ],
        "{check:#}"
    );
    // The story's edits are each the emission of a Rust edit KRS admits: no finding, and each
    // edit named by the Rust bytes it changes.
    for row in check["mutations"].as_array().unwrap() {
        assert_eq!(row["outcome"], "ok", "{row:#}");
        assert_eq!(row["refusals"], serde_json::json!([]), "{row:#}");
        assert_eq!(row["warnings"], serde_json::json!([]), "{row:#}");
    }
    // The Rust each patch stands for is the whole construct its K edit replaces: the `n` that
    // plus_zero returns, the `NatSyntax::Succ(..)` call plus/b unwraps, and the `Plus(m, n)` call
    // plus/c replaces by `n`, each in the body of its function, the line after its signature.
    for (row, (label, item, function, text)) in check["mutations"].as_array().unwrap().iter().zip([
        ("nat--plus_zero", "plus_zero", "fn plus_zero(", "n"),
        (
            "nat--plus_succ",
            "plus_succ",
            "fn plus_succ(",
            "NatSyntax::Succ(Plus(m, n))",
        ),
        ("nat--plus_succ", "plus_succ", "fn plus_succ(", "Plus(m, n)"),
    ]) {
        let edits = row["krs"]["edits"].as_array().unwrap();
        assert_eq!(edits.len(), 1, "{row:#}");
        let edit = &edits[0];
        assert_eq!(edit["label"], label, "{edit:#}");
        assert_eq!(edit["item"], item, "{edit:#}");
        assert_eq!(edit["judged"], "authored", "{edit:#}");
        let rust = edit["rust"].as_array().unwrap();
        assert_eq!(rust.len(), 1, "{edit:#}");
        let line = line_of(STORY, function) + 1;
        let column = STORY
            .lines()
            .nth(usize::try_from(line).unwrap() - 1)
            .unwrap()
            .find(text)
            .unwrap()
            + 1;
        assert_eq!(rust[0]["file"], "src/lib.rs", "{edit:#}");
        assert_eq!(rust[0]["text"], text, "{edit:#}");
        assert_eq!(rust[0]["line"].as_u64(), Some(line), "{edit:#}");
        assert_eq!(rust[0]["end_line"].as_u64(), Some(line), "{edit:#}");
        assert_eq!(
            rust[0]["column"].as_u64(),
            Some(u64::try_from(column).unwrap()),
            "{edit:#}"
        );
        assert_eq!(
            rust[0]["end_column"].as_u64(),
            Some(u64::try_from(column + text.len()).unwrap()),
            "{edit:#}"
        );
    }
}

/// After an edit of the specification, the command builds the edited package once and runs
/// every patch whose anchored text the edit left unchanged, with no build of its own; a patch
/// whose anchored text changed is reported stale, naming the KRS item and the Rust position of
/// the rule its anchor names, and runs nothing.
#[test]
fn an_edit_of_the_specification_leaves_patches_running_or_stale() {
    // plus_succ is restated: `s(m) + n` is `m + s(n)`. The K it emits no longer holds the text
    // plus/b and plus/c replace; plus/a's anchor, plus_zero, is unchanged.
    let edited = STORY.replace("NatSyntax::Succ(Plus(m, n))", "Plus(m, NatSyntax::Succ(n))");
    assert_ne!(edited, STORY);
    let mut files = story_files();
    files[0].1 = edited.as_bytes().to_vec();
    files.push((
        "kink/mutations/plus.toml".to_owned(),
        STORY_MUTATIONS.as_bytes().to_vec(),
    ));
    let project = project_of("story-plus-respec", "NAT", &files);
    let timings = project.path().join("timings.json");
    let output = project.kink("run", &["--full", "--timings", timings.to_str().unwrap()]);
    // A mutation that does not resolve makes the run fail, after every other mutation ran.
    assert_status(&output, 1);
    let document = json(&output);
    assert_eq!(document["definition"]["status"], "written", "{document:#}");
    let rows = document["mutations"].as_array().unwrap();
    let statuses = rows
        .iter()
        .map(|row| (row["id"].as_str().unwrap(), row["status"].as_str().unwrap()))
        .collect::<Vec<_>>();
    assert_eq!(
        statuses,
        [
            ("plus/a", "killed"),
            ("plus/b", "invalid-mutation"),
            ("plus/c", "invalid-mutation"),
        ],
        "{document:#}"
    );
    for row in &rows[1..] {
        assert_eq!(row["reason"], "find-not-found", "{row:#}");
        assert_eq!(row["edit"], 0, "{row:#}");
        let anchor = &row["anchor"];
        assert_eq!(anchor["label"], "nat--plus_succ", "{row:#}");
        assert_eq!(anchor["krs"]["item"], "plus_succ", "{row:#}");
        assert_eq!(anchor["krs"]["file"], "src/lib.rs", "{row:#}");
        assert_eq!(
            anchor["krs"]["line"],
            line_of(&edited, "fn plus_succ("),
            "{row:#}"
        );
    }
    // The command's one krs build is the edited package's own; the patches run on its K.
    let timings: Value = serde_json::from_str(&fs::read_to_string(&timings).unwrap()).unwrap();
    let runs = timings["spans"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|span| span["id"] == "collector.run")
        .count();
    assert_eq!(runs, 1, "{timings:#}");

    // `check` refuses the stale patches with the same rule, and resolves the other.
    let output = project.kink("check", &[]);
    assert_status(&output, 1);
    let check = json(&output);
    let outcomes = check["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row["outcome"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(outcomes, ["ok", "refused", "refused"], "{check:#}");
    for row in &check["mutations"].as_array().unwrap()[1..] {
        let refusal = &row["refusals"][0];
        assert_eq!(refusal["reason"], "find-not-found", "{row:#}");
        assert_eq!(refusal["rule"]["krs"]["item"], "plus_succ", "{row:#}");
        assert_eq!(
            refusal["rule"]["krs"]["line"],
            line_of(&edited, "fn plus_succ("),
            "{row:#}"
        );
    }
}

/// `query` and `fuzz` run through the front end and print kink-flow's documents, with the
/// rules they name named by their Rust items.
#[test]
fn query_and_fuzz_name_rules_by_their_items() {
    let project = counter();
    project.write(
        "kink/PATTERNS.toml",
        "[[pattern]]\nid = \"done\"\npattern = \"<k> done </k>\"\nprograms = [\"c3\"]\n",
    );
    let output = project.kink("query", &[]);
    assert_status(&output, 0);
    let document = json(&output);
    assert_eq!(document["schema"], "kink-flow-query", "{document:#}");
    let row = &document["rows"][0];
    assert_eq!(row["answer"], "hit", "{document:#}");
    let steps = row["witness"]["krs_rules"]
        .as_array()
        .unwrap_or_else(|| panic!("the witness names its steps: {row:#}"))
        .iter()
        .map(|step| step["item"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(steps, ["step", "step", "step", "stop"], "{row:#}");

    project.write(
        "kink/TEMPLATES.toml",
        "[[template]]\nid = \"count\"\nprogram = \"c3\"\n\n  [[template.hole]]\n  name = \"N\"\n  \
         sort = \"Int\"\n  find = \"3\"\n  literal = \"3\"\n  range = { min = 0, max = 4 }\n",
    );
    let output = project.kink(
        "fuzz",
        &["--template", "count", "--matched", "stop", "--cases", "4"],
    );
    let document = json(&output);
    assert_eq!(document["schema"], "kink-flow-fuzz", "{document:#}");
    assert_eq!(
        document["job"]["rule"]["krs"]["item"], "stop",
        "the rule job's target is named by its item: {document:#}"
    );
    assert_status(&output, 0);
}

/// `emit --check` is the gate: it fails when `kink/definition.k` differs from the emission and
/// writes nothing; `--locked` refuses a stale file; without it a command writes the file and
/// says so.
#[test]
fn a_stale_definition_is_written_or_refused() {
    let project = project_of("story-plus-edit", "NAT", &story_files());
    let check = project.kink("emit", &["--check"]);
    assert_status(&check, 1);
    assert_eq!(json(&check)["definition"]["status"], "stale");
    assert!(!project.path().join("kink/definition.k").exists());

    let emit = project.kink("emit", &[]);
    assert_status(&emit, 0);
    assert_eq!(json(&emit)["definition"]["status"], "written");
    assert_status(&project.kink("emit", &["--check"]), 0);
    let emitted = project.read("kink/definition.k");

    // Renaming plus_zero's variable changes the K.
    let edited = STORY
        .replace("Plus(NatSyntax::Zero(), n)", "Plus(NatSyntax::Zero(), rhs)")
        .replace("    n\n}", "    rhs\n}");
    assert_ne!(edited, STORY);
    project.write("src/lib.rs", &edited);
    let check = project.kink("emit", &["--check"]);
    assert_status(&check, 1);
    assert_eq!(json(&check)["definition"]["status"], "stale");
    assert_eq!(project.read("kink/definition.k"), emitted);

    let locked = project.kink("results", &["--locked"]);
    assert_status(&locked, 1);
    let document = json(&locked);
    assert_eq!(document["spec"]["stage"], "definition", "{document:#}");
    assert_eq!(
        document["spec"]["reason"], "definition-stale",
        "{document:#}"
    );
    assert!(
        document["spec"]["detail"]
            .as_str()
            .unwrap()
            .contains("krs kink emit --package story-plus-edit --definition main"),
        "{document:#}"
    );
    assert_eq!(project.read("kink/definition.k"), emitted);

    let results = project.kink("results", &[]);
    assert_status(&results, 0);
    let document = json(&results);
    assert_eq!(document["definition"]["status"], "written", "{document:#}");
    assert_ne!(project.read("kink/definition.k"), emitted);
    assert_status(&project.kink("emit", &["--check"]), 0);
    let again = project.kink("results", &["--locked"]);
    assert_status(&again, 0);
    assert_eq!(json(&again)["definition"]["status"], "unchanged");
}

/// A FLOW.toml is a K corpus or a KRS one; the krs front end refuses a K corpus naming
/// kink-flow, and a KRS corpus of another facet naming both, before it builds anything.
#[test]
fn the_front_end_refuses_another_front_ends_corpus() {
    let project = story();
    project.write(
        "corpora/k/FLOW.toml",
        "[spec]\nentry = \"plus.k\"\nmain_module = \"NAT\"\n",
    );
    let output = project.kink("check", &["--corpus", "corpora/k"]);
    assert_status(&output, 1);
    let document = json(&output);
    assert_eq!(document["spec"]["stage"], "manifest", "{document:#}");
    let detail = document["spec"]["detail"].as_str().unwrap();
    assert!(
        detail.starts_with("spec.entry: a K corpus") && detail.contains("kink-flow"),
        "{detail}"
    );

    project.write(
        "corpora/other/FLOW.toml",
        "[spec]\nkrs = { definition = \"other\" }\n",
    );
    let output = project.kink("results", &["--corpus", "corpora/other"]);
    assert_status(&output, 1);
    let document = json(&output);
    let detail = document["spec"]["detail"].as_str().unwrap();
    assert!(
        detail.starts_with("spec.krs.definition:")
            && detail.contains("`other`")
            && detail.contains("`main`"),
        "{detail}"
    );

    // A package krs refuses while selecting it is answered by krs's diagnostics and the verb's
    // document, refused at stage krs-build: with the corpus's layout (results), and without it
    // (query, whose PATTERNS.toml the corpus lacks).
    for (verb, schema) in [
        ("results", "kink-flow-results"),
        ("query", "kink-flow-query"),
    ] {
        let output = {
            let _turn = project
                .turn
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let mut process = krs_command!();
            fixture_build_env(&mut process, &project.target);
            process
                .current_dir(project.path())
                .args(["kink", verb, "--package", "nope", "--definition", "main"])
                .output()
                .unwrap()
        };
        assert_status(&output, 1);
        assert!(
            stderr(&output).contains("missing-package"),
            "{}",
            stderr(&output)
        );
        let document = json(&output);
        assert_eq!(document["schema"], schema, "{document:#}");
        assert_eq!(document["spec"]["stage"], "krs-build", "{document:#}");
        assert_eq!(document["spec"]["reason"], "krs-refused", "{document:#}");
    }
}

/// The K kink judges is the K `krs emit-k` writes: the in-process emission, `kink/definition.k`
/// and `emit-k`'s `definition.k` are the same bytes, and the rule table names the story's two
/// equations.
#[test]
fn the_emitted_definition_is_the_one_emit_k_writes() {
    let project = story();
    let output = project.krs(&["emit-k", "--output", "target/krs-k"]);
    assert_status(&output, 0);
    let emit_k = project.read("target/krs-k/definition.k");
    let emit = project.kink("emit", &[]);
    assert_status(&emit, 0);
    assert_eq!(project.read("kink/definition.k"), emit_k);

    let request = krs_cli::CommandRequest {
        command: krs_cli::Command::Check {
            backend: None,
            partition: false,
        },
        manifest_path: project.path().join("Cargo.toml"),
        root: krs_cli::FacetSelector {
            package: krs_cli::PackageSelector::Name("story-plus".into()),
            definition: "main".into(),
        },
        dependencies: Vec::new(),
        cfg: Vec::new(),
        registration: krs_cli::RegistrationMode::Inventory,
        no_reuse: true,
        message_format: krs_cli::MessageFormat::Human,
        profile: None,
    };
    let emitted = {
        let _turn = project
            .turn
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let collected = krs_cli::collect_descriptors(&request, Some(&project.target)).unwrap();
        collected.emit_k(collected.bundle.clone()).unwrap()
    };
    assert_eq!(emitted.definition, emit_k);
    let mut items = emitted
        .rules
        .iter()
        .map(|rule| {
            (
                rule.module.as_str(),
                rule.label.as_str(),
                rule.item.as_deref(),
                rule.file.as_deref(),
            )
        })
        .collect::<Vec<_>>();
    items.sort_unstable();
    assert_eq!(
        items,
        [
            (
                "NAT",
                "nat--plus_succ",
                Some("plus_succ"),
                Some("src/lib.rs")
            ),
            (
                "NAT",
                "nat--plus_zero",
                Some("plus_zero"),
                Some("src/lib.rs")
            ),
        ]
    );
    // Each rule is labelled as its K sentence is, under the `// KRS` line that names its item.
    for rule in &emitted.rules {
        let comment = format!(
            "// KRS story-plus/src/lib.rs: {}\n",
            rule.item.as_deref().unwrap()
        );
        let sentence = format!("[label({})]", rule.label);
        let at = emit_k.find(&comment).unwrap();
        assert!(emit_k[at..].lines().nth(1).unwrap().ends_with(&sentence));
    }
}

/// A case of typed inputs, a map from a data file and bytes from a binary file, is read by
/// KRS's encoding, admitted and reported; the case's digest follows what the files denote, so
/// reformatting the data file reuses its result and changing a value computes it again.
#[test]
fn a_case_of_typed_inputs_is_read_by_the_krs_encoding() {
    let project = project_of(
        "krs-cli-kink-inputs",
        "ORG-KRS-CLI-KINK-INPUTS",
        &[
            ("src/lib.rs".to_owned(), INPUTS.as_bytes().to_vec()),
            (
                "kink/FLOW.toml".to_owned(),
                b"[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\ncases = \"cases/*.toml\"\n"
                    .to_vec(),
            ),
            (
                "kink/cases/boot.toml".to_owned(),
                br#"[inputs]
memory = { "$data-file" = "data/memory.toml" }
rom = { "$file" = "data/boot.bin" }
pc = 256
entry = { Load = { addr = 2, len = 3 } }
"#
                .to_vec(),
            ),
            (
                "kink/cases/data/memory.toml".to_owned(),
                b"\"0x0100\" = 0\n\"0x0101\" = 195\n".to_vec(),
            ),
            (
                "kink/cases/data/boot.bin".to_owned(),
                (0..=255_u8).collect::<Vec<_>>(),
            ),
        ],
    );
    let program = |output: &Output| {
        assert_status(output, 0);
        let document = json(output);
        let program = document["programs"][0].clone();
        assert_eq!(program["id"], "cases/boot.toml", "{document:#}");
        assert_eq!(program["class"], "comparable", "{document:#}");
        program
    };
    let first_output = project.kink("results", &[]);
    // The result cache is off in the Z3 profile (kink-flow `result_store`), where only the
    // digests say what reruns.
    let cache_on = json(&first_output)["result_cache"]["enabled"] == true;
    let first = program(&first_output);
    // The same map, written otherwise.
    project.write(
        "kink/cases/data/memory.toml",
        "\"257\" = 195\n\"256\" = 0\n",
    );
    let reformatted = program(&project.kink("results", &[]));
    assert_eq!(reformatted["digest"], first["digest"]);
    assert_eq!(reformatted["cached"], cache_on, "{reformatted:#}");
    // Another map.
    project.write(
        "kink/cases/data/memory.toml",
        "\"0x0100\" = 1\n\"0x0101\" = 195\n",
    );
    let changed = program(&project.kink("results", &[]));
    assert_ne!(changed["digest"], first["digest"]);
    assert_eq!(changed["cached"], false, "{changed:#}");
}

/// The definition the front end's mutation checks judge (its module doc says what it holds).
const CHECKED: &str = include_str!("fixtures/kink-checks/src/lib.rs");

/// The corpus of [`CHECKED`]: one program for each of three heads.
const CHECKED_FLOW: &str = "[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\nid = \"s5\"\nfile = \"cases/s5.exp\"\n\n[[program]]\nid = \"o3\"\nfile = \"cases/o3.exp\"\n\n[[program]]\nid = \"h2\"\nfile = \"cases/h2.exp\"\n";

fn checked_files(library: &str) -> Vec<(String, Vec<u8>)> {
    vec![
        ("src/lib.rs".to_owned(), library.as_bytes().to_vec()),
        (
            "kink/FLOW.toml".to_owned(),
            CHECKED_FLOW.as_bytes().to_vec(),
        ),
        ("kink/cases/s5.exp".to_owned(), b"step(5)\n".to_vec()),
        ("kink/cases/o3.exp".to_owned(), b"other(3)\n".to_vec()),
        ("kink/cases/h2.exp".to_owned(), b"half(2)\n".to_vec()),
    ]
}

fn checked() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, || {
        project_of("krs-cli-kink-checked", "CHECKS", &checked_files(CHECKED))
    })
}

/// One mutation of one edit: `rule`'s `find` becomes `replace`.
fn mutation(id: &str, rule: &str, find: &str, replace: &str) -> String {
    format!(
        "[[mutation]]\nid = \"{id}\"\nmisunderstanding = \"{id}\"\n\n  [[mutation.edit]]\n  rule = \"{rule}\"\n  find = {}\n  replace = {}\n\n",
        serde_json::to_string(find).unwrap(),
        serde_json::to_string(replace).unwrap()
    )
}

/// The mutations the checks judge, by what they show.
fn checked_mutations() -> String {
    [
        // Two transitions at one priority that now apply to one configuration.
        mutation("overlap", "step_nonneg", "Value:Int >=Int 0", "Value:Int >=Int -1"),
        // An if/else condition edited in its own branch only, then in every branch it renders.
        mutation("branch-one", "clamp_1", "Value:Int <Int 0", "Value:Int <Int 5"),
        format!(
            "{}  [[mutation.edit]]\n  rule = \"clamp_2\"\n  find = \"Value:Int <Int 0\"\n  replace = \"Value:Int <Int 5\"\n\n  [[mutation.edit]]\n  rule = \"clamp_3\"\n  find = \"Value:Int <Int 0\"\n  replace = \"Value:Int <Int 5\"\n\n",
            mutation("branch-all", "clamp_1", "Value:Int <Int 0", "Value:Int <Int 5")
        ),
        // The nondet group: an edit that keeps the overlap, one that leaves a member stale, one
        // that makes it overlap a rule outside the group, and a deletion leaving one member.
        mutation("toss-keeps", "toss_heads", "done ( 1 )", "done ( 2 )"),
        mutation("toss-stale", "toss_heads", "toss ( Value:Int )", "go ( Value:Int )"),
        mutation("toss-other", "toss_heads", "toss ( Value:Int )", "other ( Value:Int )"),
        "[[mutation]]\nid = \"toss-single\"\nmisunderstanding = \"no tails\"\n\n  [[mutation.edit]]\n  rule = \"toss_tails\"\n  delete = true\n\n".to_owned(),
        // The definedness test of a division: removed alone, kept for an edited divisor, and
        // edited with it.
        mutation("test-only", "half", "(Value:Int =/=Int 0) andThenBool ", ""),
        mutation("divisor", "half", "10 /Int Value:Int", "10 /Int (Value:Int +Int 1)"),
        format!(
            "{}  [[mutation.edit]]\n  rule = \"half\"\n  find = \"(Value:Int =/=Int 0)\"\n  replace = \"((Value:Int +Int 1) =/=Int 0)\"\n\n",
            mutation("divisor-both", "half", "10 /Int Value:Int", "10 /Int (Value:Int +Int 1)")
        ),
        // Layout only, and a renaming at every occurrence: neither changes what the rule says.
        mutation("layout", "other", "done ( Value:Int )", "done (  Value:Int )"),
        mutation(
            "renamed",
            "other",
            "other ( Value:Int ) => done ( Value:Int )",
            "other ( V:Int ) => done ( V:Int )",
        ),
        // A label only: kink's own refusal, which the front end never sees.
        mutation(
            "label",
            "other",
            "label(checks--other)",
            "label(checks--other-renamed)",
        ),
        // An equation of a function only the claim applies.
        mutation("helper", "expected", "+Int 1", "+Int 2"),
        // A priority that orders two overlapping rules, removed: never judged with the
        // specification's priority.
        mutation("priority", "pick_first", "priority(40), ", ""),
    ]
    .concat()
}

/// The row of the mutation `id` of a check or run document.
fn row<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == id)
        .unwrap_or_else(|| panic!("no row {id}: {document:#}"))
}

/// The reasons of a check row's refusals, then of its warnings.
fn reasons(row: &Value) -> (Vec<&str>, Vec<&str>) {
    let of = |key: &str| {
        row[key]
            .as_array()
            .unwrap_or_else(|| panic!("{key} of {row:#}"))
            .iter()
            .map(|finding| finding["reason"].as_str().unwrap())
            .collect::<Vec<_>>()
    };
    (of("refusals"), of("warnings"))
}

/// `check` refuses, with KRS's own code and next step, each mutation whose Rust source KRS
/// refuses, and each edit KRS's emission does not follow; it accepts the rest, warns of a claim
/// helper and an edited construct left in its other renderings, and names each edit's Rust.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One check document, read for each kind of refusal it shows."
)]
fn check_refuses_what_krs_refuses_of_the_mutations_source() {
    let project = checked();
    // Each test of this shared project reads a list of its own.
    project.write("kink/check-mutations.toml", checked_mutations());
    let output = project.kink("check", &["--mutations", "kink/check-mutations.toml"]);
    assert_status(&output, 1);
    let document = json(&output);
    let expected: [(&str, &[&str], &[&str]); 15] = [
        ("overlap", &["krs::analysis::overlapping-rule-heads"], &[]),
        (
            "branch-one",
            &["krs::analysis::overlapping-match-arms"],
            &["partial-rendering"],
        ),
        ("branch-all", &[], &[]),
        ("toss-keeps", &[], &[]),
        ("toss-stale", &["krs::analysis::nondet-group"], &[]),
        (
            "toss-other",
            &["krs::analysis::overlapping-rule-heads"],
            &[],
        ),
        ("toss-single", &["krs::analysis::nondet-group"], &[]),
        ("test-only", &["generated-only"], &[]),
        ("divisor", &["derived-mismatch"], &[]),
        ("divisor-both", &[], &[]),
        // kink-flow's own refusal: the texts are equal up to formatting.
        ("layout", &["no-change"], &[]),
        ("renamed", &["no-change"], &[]),
        ("label", &["label-changed"], &[]),
        ("helper", &[], &["claim-helper"]),
        ("priority", &["not-judged"], &[]),
    ];
    for (id, refusals, warnings) in expected {
        let row = row(&document, id);
        assert_eq!(
            reasons(row),
            (refusals.to_vec(), warnings.to_vec()),
            "{id}: {row:#}"
        );
        assert_eq!(
            row["outcome"],
            if refusals.is_empty() { "ok" } else { "refused" },
            "{row:#}"
        );
    }
    // A mutation that does not resolve gets no KRS judgement: no finding and no `krs` value.
    assert_eq!(row(&document, "label")["krs"], Value::Null, "{document:#}");
    // The overlap names both rules and says no Rust edit of the edited construct avoids it.
    let overlap = &row(&document, "overlap")["refusals"][0];
    let detail = overlap["detail"].as_str().unwrap();
    for named in [
        "`checks--step_neg` (step_neg",
        "`checks--step_nonneg` (step_nonneg",
    ] {
        assert!(detail.contains(named), "{detail}");
    }
    assert!(
        detail.contains("no Rust edit of these constructs avoids the refusal by itself"),
        "{detail}"
    );
    assert!(
        overlap["next"]
            .as_str()
            .unwrap()
            .starts_with("KRS accepts these rules only if they cannot apply"),
        "{overlap:#}"
    );
    // The edited branch condition is rendered, negated, in the later branches: they are the
    // siblings, the one KRS names first.
    let branch = row(&document, "branch-one");
    let siblings = branch["krs"]["siblings"]
        .as_array()
        .unwrap()
        .iter()
        .map(|sibling| {
            (
                sibling["label"].as_str().unwrap(),
                sibling["named_by_krs"].as_bool().unwrap(),
                sibling["changed"].as_bool().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        siblings,
        [
            ("checks--clamp_3", true, false),
            ("checks--clamp_2", false, false)
        ],
        "{branch:#}"
    );
    // The generated-only refusal names the authored construct and its Rust.
    let generated = &row(&document, "test-only")["refusals"][0];
    let detail = generated["detail"].as_str().unwrap();
    assert!(
        detail.contains("a definedness test KRS inserts"),
        "{detail}"
    );
    let division = line_of(CHECKED, "10 / value");
    assert!(
        detail.contains(&format!("`10 /Int Value:Int` at src/lib.rs:{division}:")),
        "{detail}"
    );
    // The derived mismatch shows the test KRS derives.
    let derived = row(&document, "divisor")["refusals"][0]["detail"]
        .as_str()
        .unwrap()
        .to_owned();
    assert!(derived.contains("(Value:Int +Int 1) =/=Int 0"), "{derived}");
    // Each edit's Rust: the guard's literal, the deleted rule's item.
    let edit = &row(&document, "overlap")["krs"]["edits"][0];
    assert_eq!(edit["judged"], "authored", "{edit:#}");
    assert_eq!(edit["item"], "step_nonneg", "{edit:#}");
    assert_eq!(edit["rust"][0]["text"], "0", "{edit:#}");
    assert_eq!(
        edit["rust"][0]["line"].as_u64(),
        Some(line_of(CHECKED, "int::ge(value, 0)")),
        "{edit:#}"
    );
    let edit = &row(&document, "toss-single")["krs"]["edits"][0];
    assert_eq!(edit["judged"], "deleted", "{edit:#}");
    assert_eq!(
        edit["rust"][0]["line"].as_u64(),
        Some(line_of(CHECKED, "fn toss_tails")),
        "{edit:#}"
    );
    assert_eq!(
        row(&document, "test-only")["krs"]["edits"][0]["judged"],
        "inserted"
    );
}

/// `run` gives each mutation the front end refuses its first refusal, runs nothing for it, runs
/// the rest, and exits non-zero.
#[test]
fn run_refuses_what_check_refuses() {
    let project = checked();
    // `run` reads the layout's list; the check test of this shared project reads another.
    project.write(
        "kink/MUTATIONS.toml",
        [
            mutation(
                "overlap",
                "step_nonneg",
                "Value:Int >=Int 0",
                "Value:Int >=Int -1",
            ),
            mutation("toss-keeps", "toss_heads", "done ( 1 )", "done ( 2 )"),
            mutation("test-only", "half", "(Value:Int =/=Int 0) andThenBool ", ""),
            mutation(
                "layout",
                "other",
                "done ( Value:Int )",
                "done (  Value:Int )",
            ),
        ]
        .concat(),
    );
    let refused = [
        ("overlap", "krs::analysis::overlapping-rule-heads"),
        ("test-only", "generated-only"),
        ("layout", "no-change"),
    ];
    let output = project.kink("run", &["--full", "--cache", "kink/run-cache"]);
    assert_status(&output, 1);
    let document = json(&output);
    for (id, reason) in refused {
        let row = row(&document, id);
        assert_eq!(row["status"], "invalid-mutation", "{row:#}");
        assert_eq!(row["reason"], reason, "{row:#}");
    }
    // A refused mutation ran nothing, so it has no tier-1 record and no hint; the mutation
    // that ran has its records wherever tier 1 is on (not under the Z3 profile).
    let cached = cached_mutations(&project.path().join("kink/run-cache"));
    for (id, _) in refused {
        assert!(
            !cached.contains(id),
            "{id} has a record or a hint: {cached:?}"
        );
    }
    if !cfg!(feature = "z3-inference") {
        assert!(cached.contains("toss-keeps"), "{cached:?}");
    }
    let refused = row(&document, "overlap");
    assert!(
        refused["action"]
            .as_str()
            .unwrap()
            .contains("KRS accepts these rules only if they cannot apply"),
        "{refused:#}"
    );
    assert_ne!(
        row(&document, "toss-keeps")["status"],
        "invalid-mutation",
        "{document:#}"
    );
    // `--only` judges the mutations it runs, and refuses them as the whole list does.
    let output = project.kink("run", &["--only", "overlap", "--cache", "kink/only-cache"]);
    assert_status(&output, 1);
    let document = json(&output);
    let rows = document["mutations"].as_array().unwrap();
    assert_eq!(rows.len(), 1, "{document:#}");
    assert_eq!(rows[0]["status"], "invalid-mutation", "{document:#}");
    assert_eq!(
        rows[0]["reason"], "krs::analysis::overlapping-rule-heads",
        "{document:#}"
    );
}

/// The mutation ids the cache at `cache` holds an outcome file or a hint for.
fn cached_mutations(cache: &Path) -> std::collections::BTreeSet<String> {
    let mut ids = std::collections::BTreeSet::new();
    let mut directories = vec![cache.join("outcomes")];
    while let Some(directory) = directories.pop() {
        let Ok(entries) = fs::read_dir(&directory) else {
            continue;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                directories.push(path);
            } else if let Ok(text) = fs::read_to_string(&path)
                && let Ok(record) = serde_json::from_str::<Value>(&text)
                && let Some(id) = record["mutation_id"].as_str()
            {
                ids.insert(id.to_owned());
            }
        }
    }
    if let Ok(text) = fs::read_to_string(cache.join("hints.json")) {
        let hints: Value = serde_json::from_str(&text).unwrap();
        for hint in hints["hints"]
            .as_object()
            .into_iter()
            .flat_map(|map| map.values())
        {
            if let Some(id) = hint["mutation_id"].as_str() {
                ids.insert(id.to_owned());
            }
        }
    }
    ids
}

/// A `fuzz` kill job of a mutation the front end refuses is refused before any case, with the
/// front end's reason and next step.
#[test]
fn a_fuzz_kill_job_of_a_refused_mutation_runs_nothing() {
    let project = checked();
    project.write(
        "kink/fuzz-mutations.toml",
        [
            mutation(
                "overlap",
                "step_nonneg",
                "Value:Int >=Int 0",
                "Value:Int >=Int -1",
            ),
            mutation("toss-keeps", "toss_heads", "done ( 1 )", "done ( 2 )"),
        ]
        .concat(),
    );
    project.write(
        "kink/TEMPLATES.toml",
        "[[template]]\nid = \"step\"\nprogram = \"s5\"\n\n  [[template.hole]]\n  name = \"N\"\n  \
         sort = \"Int\"\n  find = \"5\"\n  literal = \"5\"\n  range = { min = 0, max = 9 }\n",
    );
    let output = project.kink(
        "fuzz",
        &[
            "--template",
            "step",
            "--kill",
            "overlap",
            "--mutations",
            "kink/fuzz-mutations.toml",
        ],
    );
    let document = json(&output);
    let job = &document["job"];
    assert_eq!(job["outcome"], "refused", "{document:#}");
    assert_eq!(job["status"], "invalid-mutation", "{document:#}");
    assert_eq!(
        job["reason"], "krs::analysis::overlapping-rule-heads",
        "{document:#}"
    );
    assert!(
        document["action"]
            .as_str()
            .unwrap()
            .contains("KRS accepts these rules only if they cannot apply"),
        "{document:#}"
    );
    assert!(!output.status.success(), "{document:#}");
}

/// The verdict of `krs check` on a Rust source that emits each refused mutant is the front
/// end's: the same code, or `overlapping-equations` where the front end says
/// `overlapping-match-arms`, since the source writing one branch's guard alone is three
/// equations; and on a source that emits an accepted mutant, none.
#[test]
fn a_refused_mutants_rust_source_is_refused_by_krs_check() {
    let sources = [
        (
            "overlap",
            CHECKED.replace("int::ge(value, 0)", "int::ge(value, -1)"),
            Some("krs::analysis::overlapping-rule-heads"),
        ),
        (
            "toss-stale",
            CHECKED.replace(
                "fn toss_heads(k::term![ExpSyntax::Toss { value }]",
                "fn toss_heads(k::term![ExpSyntax::Go { value }]",
            ),
            Some("krs::analysis::nondet-group"),
        ),
        (
            "toss-other",
            CHECKED.replace(
                "fn toss_heads(k::term![ExpSyntax::Toss { value }]",
                "fn toss_heads(k::term![ExpSyntax::Other { value }]",
            ),
            Some("krs::analysis::overlapping-rule-heads"),
        ),
        (
            "toss-single",
            CHECKED.replace(
                "#[k::rule(nondet = toss)]\nfn toss_tails(k::term![ExpSyntax::Toss { value }]: Term<Exp>) -> Term<Exp> {\n    ExpSyntax::Done(0)\n}\n",
                "",
            ),
            Some("krs::analysis::nondet-group"),
        ),
        (
            "branch-one",
            CHECKED.replace(
                "#[k::function(total, internal)]\npub fn Clamp(value: Term<Int>) -> Term<Int> {\n    if value < 0 { 0 } else if value > 255 { 255 } else { value }\n}",
                "#[k::function(total, sort = Int, syntax = \"clamp({value})\")]\npub struct Clamp {\n    pub value: Term<Int>,\n}\n\n#[k::requires(value < 5)]\n#[k::equation]\nfn clamp_1(k::term![Clamp(value)]: Term<Int>) -> Term<Int> {\n    0\n}\n\n#[k::requires(!(value < 0) && value > 255)]\n#[k::equation]\nfn clamp_2(k::term![Clamp(value)]: Term<Int>) -> Term<Int> {\n    255\n}\n\n#[k::requires(!(value < 0) && !(value > 255))]\n#[k::equation]\nfn clamp_3(k::term![Clamp(value)]: Term<Int>) -> Term<Int> {\n    value\n}",
            ),
            Some("krs::analysis::overlapping-equations"),
        ),
        (
            "branch-all",
            CHECKED.replace("if value < 0 {", "if value < 5 {"),
            None,
        ),
    ];
    for (id, source, code) in sources {
        assert_ne!(source, CHECKED, "{id}: the source is edited");
        let project = project_of(
            "krs-cli-kink-checked-source",
            "CHECKS",
            &checked_files(&source),
        );
        let output = project.krs(&["check"]);
        let stderr = stderr(&output);
        match code {
            Some(code) => {
                assert!(!output.status.success(), "{id}: {stderr}");
                assert!(stderr.contains(&format!("[{code}]")), "{id}: {stderr}");
            }
            None => assert!(output.status.success(), "{id}: {stderr}"),
        }
    }
}
