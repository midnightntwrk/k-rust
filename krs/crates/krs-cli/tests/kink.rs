//! `krs kink <verb>`: the corpus loop over a KRS package, with kink-flow as its engine.
//!
//! The main fixture is a copy of the introduction's story package (`docs-site/story/plus`) with
//! `kink/FLOW.toml` and the story's four programs as cases: the tool must report what the
//! story's pages claim, each rule named by its Rust item and position, and kill the story's
//! three edits written as K patches anchored by `plus_zero` and `plus_succ`. A small counter
//! definition, which has rewrite rules, gives `fuzz --reach` and a query witness rules to name;
//! `fixtures/inputs` gives a case of typed inputs.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;
use std::sync::{Arc, Mutex, Weak};

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::Value;

const STORY: &str = include_str!("../../../../docs-site/story/plus/src/lib.rs");
/// The story's four tests (story.toml `[[test]]`), written here rather than read from the
/// story's directory, whose layout is the docs-site's to change; the expectations below are
/// story.toml's for these programs.
const STORY_PROGRAMS: [(&str, &str); 4] = [
    ("t1", "plus(zero, zero)\n"),
    ("t2", "plus(zero, s(zero))\n"),
    ("t3", "plus(s(zero), s(zero))\n"),
    ("t4", "plus(s(s(zero)), s(zero))\n"),
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

/// The story's corpus manifest: the four programs as cases.
const STORY_FLOW: &str = r#"[spec]
krs = { definition = "main" }

[[program]]
id = "t1"
file = "cases/t1.nat"

[[program]]
id = "t2"
file = "cases/t2.nat"

[[program]]
id = "t3"
file = "cases/t3.nat"

[[program]]
id = "t4"
file = "cases/t4.nat"
"#;

/// The story's three edits (story.toml `a`, `b`, `c`) as K patches of the emitted rules,
/// anchored by the Rust item names, each with the story's `why` as its misunderstanding.
const STORY_MUTATIONS: &str = r#"[[mutation]]
id = "a"
misunderstanding = "forgets what the base case returns"

  [[mutation.edit]]
  rule = "plus_zero"
  find = "=> N:Nat"
  replace = "=> zero"

[[mutation]]
id = "b"
misunderstanding = "loses one at every step"

  [[mutation.edit]]
  rule = "plus_succ"
  find = "=> s ( plus ( M:Nat , N:Nat ) )"
  replace = "=> plus ( M:Nat , N:Nat )"

[[mutation]]
id = "c"
misunderstanding = "stops recursing after one step"

  [[mutation.edit]]
  rule = "plus_succ"
  find = "=> s ( plus ( M:Nat , N:Nat ) )"
  replace = "=> s ( N:Nat )"
"#;

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
    for (id, text) in STORY_PROGRAMS {
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

    // The verdicts rendering names the rules by the same items: story.toml's `rules`.
    let output = project.kink("results", &["--output", "verdicts"]);
    assert_status(&output, 0);
    let verdicts = stdout(&output);
    let fired = verdicts
        .lines()
        .filter(|line| line.starts_with("fired = "))
        .collect::<Vec<_>>();
    assert_eq!(
        fired,
        [
            "fired = [\"plus_zero\"]",
            "fired = [\"plus_zero\"]",
            "fired = [\"plus_succ\", \"plus_zero\"]",
            "fired = [\"plus_succ\", \"plus_zero\"]",
        ],
        "{verdicts}"
    );
}

/// `run` kills the story's three edits, written as K patches anchored by the Rust items, and a
/// full run finds exactly the killers the story's pages show (story.toml `caught_by`).
#[test]
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
        &["--template", "count", "--reach", "stop", "--cases", "4"],
    );
    let document = json(&output);
    assert_eq!(document["schema"], "kink-flow-fuzz", "{document:#}");
    assert_eq!(
        document["job"]["rule"]["krs"]["item"], "stop",
        "the reach target is named by its item: {document:#}"
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
