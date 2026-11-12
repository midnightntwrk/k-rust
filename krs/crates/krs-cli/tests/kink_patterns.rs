//! `krs kink query` on a corpus whose patterns a KRS patterns package writes (FB-49 K2b,
//! `[[patterns]] krs = "PACKAGE"`).
//!
//! The fixture is a workspace of the specification `spec`, a machine whose statements write and
//! read values on a bus (a builtin `List` cell) and count steps in `pc`, and the patterns package
//! `pats`, which depends on it and writes three `k::patterns!` clauses: `written_then_read`, one
//! step with several list rests (`_ ListItem(write(A, V)) _ ListItem(read(A, V)) _`) claimed of
//! `p1`; `marked_read`, a chain with an `unless`, claimed of `p1`; and `read_without_mark`, a
//! chain with an `unless` the corpus is expected never to hit (`k::expect(no)`). The first test's
//! workspace also has `bad`, a patterns package whose binder has two sorts.
//!
//! Each clause is asked as the `[[pattern]]` a list would write for it, under the id the clause's
//! name gives, with its KRS source, and the document names each binding by the binder the clause
//! writes. The package is outside the definition's closure, so editing one clause keeps the
//! specification's digest and `definition.k`, and re-asks only that clause's pattern.

#![cfg(feature = "kink")]

use std::fs;
use std::path::Path;
use std::process::Output;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value, json};

/// The specification: a machine whose statements write and read values on the bus and count
/// steps in `pc`.
const SPEC: &str = r#"use k::KResult;
use k::builtin::{Int, KSequence, List};

k::sorts! {
    Stmt: k::KItem;
    Ev: KResult;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("wr ( {a} , {v} )")]
    Wr { a: Int, v: Int },
    #[k::syntax("rd ( {a} , {v} )")]
    Rd { a: Int, v: Int },
    #[k::syntax("mark")]
    Mark(),
    #[k::syntax("seq ( {first} , {second} )")]
    Seq { first: Stmt, second: Stmt },
}

#[k::constructors(sort = Ev, result = KResult)]
pub enum Event {
    #[k::syntax("write({a}, {v})")]
    Write { a: Int, v: Int },
    #[k::syntax("read({a}, {v})")]
    Read { a: Int, v: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell(name = "k")]
    pub k: KSequence,
    #[k::cell(name = "pc")]
    pub pc: Int,
    #[k::cell(name = "bus")]
    pub bus: List<Ev>,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] program: Stmt) -> Self {
        Self {
            k: k::k![program],
            pc: 0,
            bus: [],
        }
    }
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    seq: { k: [Seq { first: a, second: b }, ..] } => { k: [a, b, ..] };
    wr: { k: [Wr { a: addr, v: value }, ..], pc, bus: log } => { k: [..], pc: pc + 1, bus: [..log, Event::Write { a: addr, v: value }] };
    rd: { k: [Rd { a: addr, v: value }, ..], pc, bus: log } => { k: [..], pc: pc + 1, bus: [..log, Event::Read { a: addr, v: value }] };
    mark: { k: [Mark(), ..], pc } => { k: [..], pc: pc + 1 };
}
"#;

/// The patterns package's clauses (module documentation).
const PATTERNS: &str = r#"k::patterns! {
    for spec::Machine;
    use spec::Event::*;
    use spec::StmtSyntax::*;

    /// A value written, then read back, on the bus.
    #[k::cases("p1")]
    written_then_read: { bus: [.., Write(a, v), .., Read(a, v), ..] };

    /// A mark, then the first read of address 1.
    #[k::cases("p1")]
    marked_read: { k: [Mark(), ..] } => unless({ bus: [.., Read(1, _), ..] }) { bus: [.., Read(1, v), ..] };

    /// No program reads before it marks.
    #[k::expect(no)]
    read_without_mark: { pc: 0 } => unless({ k: [Mark(), ..] }) { bus: [.., Read(_, _), ..] };
}
"#;

/// A patterns package whose binder is an `Int` in one step and a `List` in the other.
const BAD: &str = r"k::patterns! {
    for spec::Machine;

    two_sorts: { pc: x } => { bus: x };
}
";

/// The corpus: two programs, each writing a value, marking, and reading.
const FLOW: &str = "[spec]\nkrs = { package = \"spec\", definition = \"main\" }\n\n[budget]\ntime_ms = 600000\n\n\
                    [[program]]\nid = \"p1\"\nfile = \"cases/p1.prog\"\n\n\
                    [[program]]\nid = \"p2\"\nfile = \"cases/p2.prog\"\n";

/// A workspace of `spec` with its corpus and the patterns packages `packages` (name, source),
/// each depending on `spec`, and the fixture target `krs` builds in.
struct Workspace {
    directory: TempDir,
    target: SharedFixtureTarget,
}

impl Workspace {
    fn new(packages: &[(&str, &str)]) -> Self {
        Self::of(
            SPEC,
            FLOW,
            &[
                ("p1", "seq(wr(1, 5), seq(mark, rd(1, 5)))\n"),
                ("p2", "seq(wr(2, 7), seq(mark, rd(2, 8)))\n"),
            ],
            packages,
        )
    }

    /// A workspace of the specification `spec` with the corpus `flow` over the programs
    /// `cases` (id, text) and the patterns packages `packages`.
    fn of(spec: &str, flow: &str, cases: &[(&str, &str)], packages: &[(&str, &str)]) -> Self {
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        let workspace = Self {
            directory: temp_dir(),
            target: shared_fixture_target(),
        };
        let manifest = |name: &str, dependencies: &str| {
            format!(
                "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-KINK-PATTERNS-{}\"\n\n[package.metadata.krs.definitions.main]\n",
                name.to_ascii_uppercase()
            )
        };
        workspace.write("spec/Cargo.toml", &manifest("spec", ""));
        workspace.write("spec/src/lib.rs", spec);
        workspace.write("spec/kink/FLOW.toml", flow);
        for (id, program) in cases {
            workspace.write(&format!("spec/kink/cases/{id}.prog"), program);
        }
        let mut members = vec!["\"spec\"".to_owned()];
        for (name, source) in packages {
            workspace.write(
                &format!("{name}/Cargo.toml"),
                &manifest(name, "spec = { path = \"../spec\" }\n"),
            );
            workspace.write(&format!("{name}/src/lib.rs"), source);
            members.push(format!("\"{name}\""));
        }
        workspace.write(
            "Cargo.toml",
            &format!(
                "[workspace]\nmembers = [{}]\nresolver = \"3\"\n",
                members.join(", ")
            ),
        );
        workspace
    }

    fn write(&self, relative: &str, contents: &str) {
        let path = self.directory.path().join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn read(&self, relative: &str) -> String {
        fs::read_to_string(self.directory.path().join(relative)).unwrap()
    }

    /// `krs kink VERB ARGUMENTS` on `spec`'s definition, from the workspace root.
    fn kink(&self, verb: &str, arguments: &[&str]) -> Output {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        process
            .current_dir(self.directory.path())
            .args(["kink", verb])
            .args(arguments)
            .args(["--package", "spec", "--definition", "main"])
            .env("NO_COLOR", "1");
        process.output().unwrap()
    }

    /// The corpus manifest declaring `entries` after the programs.
    fn declare(&self, entries: &str) {
        self.write("spec/kink/FLOW.toml", &format!("{FLOW}\n{entries}"));
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

/// The 1-based line of the first line of `source` holding `text`.
fn line_of(source: &str, text: &str) -> u64 {
    let index = source
        .lines()
        .position(|line| line.contains(text))
        .unwrap_or_else(|| panic!("no line holds {text:?}"));
    u64::try_from(index).unwrap() + 1
}

/// The entry of `patterns` of the pattern `id`.
fn pattern<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["patterns"]
        .as_array()
        .unwrap_or_else(|| panic!("{document:#}"))
        .iter()
        .find(|entry| entry["id"] == id)
        .unwrap_or_else(|| panic!("no pattern {id}: {document:#}"))
}

/// The row of `pattern` on `program`.
fn row<'d>(document: &'d Value, pattern: &str, program: &str) -> &'d Value {
    document["rows"]
        .as_array()
        .unwrap_or_else(|| panic!("{document:#}"))
        .iter()
        .find(|row| row["pattern"] == pattern && row["program"] == program)
        .unwrap_or_else(|| panic!("no row of {pattern} on {program}: {document:#}"))
}

/// The obligation of `pattern`.
fn obligation<'d>(document: &'d Value, pattern: &str) -> &'d Value {
    document["obligations"]
        .as_array()
        .unwrap_or_else(|| panic!("{document:#}"))
        .iter()
        .find(|obligation| obligation["id"] == pattern)
        .unwrap_or_else(|| panic!("no obligation of {pattern}: {document:#}"))
}

/// The `{krs_variable: variable}` pairs of a witness's bindings.
fn named_bindings(bindings: &Value) -> Vec<(Value, Value)> {
    bindings
        .as_array()
        .unwrap_or_else(|| panic!("bindings: {bindings:#}"))
        .iter()
        .map(|binding| (binding["krs_variable"].clone(), binding["variable"].clone()))
        .collect()
}

/// The package's clauses are asked as the corpus's patterns: under the ids their names give,
/// with their KRS sources, their claims and expectations checked, each binding named by its
/// binder, the obligations kept in `[query]`. An id a list and the package both give is refused
/// naming both; a package whose clauses do not emit refuses its entry with the reason, and is
/// built only by a command that asks the declared patterns.
#[test]
fn query_asks_the_clauses_of_a_krs_patterns_package() {
    let workspace = Workspace::new(&[("pats", PATTERNS), ("bad", BAD)]);
    workspace.declare("[[patterns]]\nkrs = \"pats\"\n");
    let output = workspace.kink("query", &[]);
    assert_status(&output, 0);
    let document = json_of(&output);

    let ids = document["patterns"]
        .as_array()
        .unwrap()
        .iter()
        .map(|entry| entry["id"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        ids,
        ["marked-read", "read-without-mark", "written-then-read"],
        "{document:#}"
    );
    let written = pattern(&document, "written-then-read");
    assert_eq!(
        written["source"],
        json!({
            "krs": "pats",
            "item": "pats::written_then_read",
            "file": "src/lib.rs",
            "line": line_of(PATTERNS, "written_then_read:"),
        }),
        "{written:#}"
    );
    // One step without `unless` is the single pattern a list's `pattern` gives, with its
    // several list rests.
    assert_eq!(
        written["pattern"],
        "<bus> _ ListItem(write ( A:Int , V:Int )) _ ListItem(read ( A:Int , V:Int )) _ </bus>",
        "{written:#}"
    );
    assert_eq!(
        written["krs_variables"],
        json!([
            {"k": "A", "krs": "a", "sort": "Int"},
            {"k": "V", "krs": "v", "sort": "Int"},
        ]),
        "{written:#}"
    );
    let hit = row(&document, "written-then-read", "p1");
    assert_eq!(
        (&hit["answer"], &hit["claim"]),
        (&json!("hit"), &json!("confirmed")),
        "{hit:#}"
    );
    assert_eq!(
        named_bindings(&hit["witness"]["bindings"]),
        [(json!("a"), json!("A")), (json!("v"), json!("V"))],
        "{hit:#}"
    );

    chains_and_expectations(&document);

    // The obligations are the corpus's own: `[query]` keeps them under the ids as written.
    assert_eq!(document["lock"]["status"], "created", "{document:#}");
    let lock = workspace.read("spec/kink/kink.lock");
    for id in ["written-then-read", "marked-read", "read-without-mark"] {
        assert!(lock.contains(&format!("id = \"{id}\"")), "{id}: {lock}");
    }

    refusals_and_laziness(&workspace);
}

/// The chains of [`query_asks_the_clauses_of_a_krs_patterns_package`]'s document: a chain with
/// an `unless`, and the claim `k::expect(no)`.
fn chains_and_expectations(document: &Value) {
    // A chain with an `unless`: its steps as the clause writes them, and its witness's
    // bindings named, at the top level and at the step that binds them.
    let marked = pattern(document, "marked-read");
    assert_eq!(
        marked["steps"]
            .as_array()
            .unwrap()
            .iter()
            .map(|step| (step["pattern"].clone(), step["unless"].clone()))
            .collect::<Vec<_>>(),
        [
            (json!("<k> mark ... </k>"), Value::Null),
            (
                json!("<bus> _ ListItem(read ( 1 , V:Int )) _ </bus>"),
                json!("<bus> _ ListItem(read ( 1 , _ )) _ </bus>")
            ),
        ],
        "{marked:#}"
    );
    let hit = row(document, "marked-read", "p1");
    assert_eq!(
        (&hit["answer"], &hit["claim"], &hit["route"]),
        (&json!("hit"), &json!("confirmed"), &json!("chain-run")),
        "{hit:#}"
    );
    assert_eq!(
        named_bindings(&hit["witness"]["bindings"]),
        [(json!("v"), json!("V"))],
        "{hit:#}"
    );
    assert_eq!(
        named_bindings(&hit["witness"]["steps"][1]["bindings"]),
        [(json!("v"), json!("V"))],
        "{hit:#}"
    );

    // `k::expect(no)`: no program reads before its mark.
    let open = obligation(document, "read-without-mark");
    assert_eq!(
        (
            &open["status"],
            &open["expect"],
            &open["expectation"]["verdict"]
        ),
        (&json!("open"), &json!("no"), &json!("met")),
        "{open:#}"
    );
    assert_eq!(
        pattern(document, "read-without-mark")["source"]["item"],
        "pats::read_without_mark"
    );
}

/// The rest of [`query_asks_the_clauses_of_a_krs_patterns_package`], on its workspace: the
/// refusals, and that only a command asking the declared patterns builds a package.
fn refusals_and_laziness(workspace: &Workspace) {
    // An id a list and the package both give is refused, naming both.
    workspace.write(
        "spec/kink/patterns/extra.toml",
        "[[pattern]]\nid = \"written-then-read\"\npattern = \"<pc> 3 </pc>\"\n",
    );
    workspace
        .declare("[[patterns]]\nfiles = \"patterns/*.toml\"\n\n[[patterns]]\nkrs = \"pats\"\n");
    let output = workspace.kink("query", &[]);
    assert_status(&output, 2);
    let document = json_of(&output);
    assert_eq!(
        document["pattern_list"]["detail"],
        format!(
            "pattern \"written-then-read\": duplicate pattern id: patterns/extra.toml pattern[0] \
             and KRS package \"pats\" item pats::written_then_read (src/lib.rs:{}) both give it",
            line_of(PATTERNS, "written_then_read:")
        ),
        "{document:#}"
    );

    // A package whose clauses do not emit refuses its entry with the reason.
    workspace.declare("[[patterns]]\nkrs = \"bad\"\n");
    let output = workspace.kink("query", &[]);
    assert_status(&output, 2);
    let document = json_of(&output);
    let detail = document["pattern_list"]["detail"].as_str().unwrap();
    assert!(
        detail.starts_with("patterns[0].krs: the KRS patterns package `bad` does not emit: "),
        "{document:#}"
    );
    assert!(
        detail.contains("`x` is `Int` in step 1 of `two_sorts`"),
        "{document:#}"
    );
    // So does a package the Cargo graph does not have.
    workspace.declare("[[patterns]]\nkrs = \"absent\"\n");
    let output = workspace.kink("query", &[]);
    assert_status(&output, 2);
    let detail = json_of(&output)["pattern_list"]["detail"]
        .as_str()
        .unwrap()
        .to_owned();
    assert!(
        detail
            .starts_with("patterns[0].krs: the KRS patterns package `absent` cannot be prepared: "),
        "{detail}"
    );
    assert!(
        detail.contains(
            "the package `absent` is not in the package graph Cargo resolves for --manifest-path"
        ),
        "{detail}"
    );

    // Only a command that asks the declared patterns builds the package: a query of a list,
    // and a verb that asks no pattern, answer as though the package were not there.
    workspace.declare("[[patterns]]\nkrs = \"bad\"\n");
    let output = workspace.kink("query", &["--patterns", "spec/kink/patterns/extra.toml"]);
    assert_status(&output, 0);
    assert_eq!(
        row(&json_of(&output), "written-then-read", "p1")["answer"],
        "hit"
    );
    assert_status(&workspace.kink("check", &[]), 0);
    assert_status(&workspace.kink("emit", &["--check"]), 0);
}

/// Editing one clause re-asks only its pattern: the package is outside the definition's
/// closure, so the specification's digest, `definition.k` and every other pattern's answers keep
/// their keys.
#[test]
fn editing_one_clause_re_asks_only_its_pattern() {
    let workspace = Workspace::new(&[("pats", PATTERNS)]);
    workspace.declare("[[patterns]]\nkrs = \"pats\"\n");
    let output = workspace.kink("query", &[]);
    assert_status(&output, 0);
    let first = json_of(&output);
    let definition = workspace.read("spec/kink/definition.k");

    workspace.write(
        "pats/src/lib.rs",
        &PATTERNS.replace(
            "unless({ bus: [.., Read(1, _), ..] })",
            "unless({ bus: [.., Read(3, _), ..] })",
        ),
    );
    let output = workspace.kink("query", &[]);
    assert_status(&output, 0);
    let second = json_of(&output);
    assert_eq!(second["spec"]["digest"], first["spec"]["digest"]);
    assert_eq!(second["definition"]["status"], "unchanged", "{second:#}");
    assert_eq!(workspace.read("spec/kink/definition.k"), definition);
    assert_ne!(
        pattern(&second, "marked-read")["digest"],
        pattern(&first, "marked-read")["digest"]
    );
    let rows = second["rows"].as_array().unwrap();
    assert!(!rows.is_empty(), "{second:#}");
    for row in rows {
        let edited = row["pattern"] == "marked-read";
        assert_eq!(row["cached"], json!(!edited), "{row:#}");
    }
    assert_eq!(row(&second, "marked-read", "p1")["answer"], "hit");
    assert_status(&workspace.kink("emit", &["--check"]), 0);
}

/// A package of vocabulary outside the specification's closure: a named constant, which a
/// sentence that names it holds as its value, and a function.
const HELPER: &str = r"use k::Term;
use k::builtin::Int;

/// The address the first program writes and reads.
#[k::constant]
pub const FIRST: Int = 1;

/// The successor.
#[k::function(total, internal)]
pub fn Bump(value: Term<Int>) -> Term<Int> {
    value + 1
}
";

/// A patterns package whose clause names the helper's constant, so that collecting the package
/// needs the helper's facet.
const HELPED_PATTERNS: &str = r#"k::patterns! {
    for spec::Machine;
    use spec::Event::*;

    /// The first address written, then read back, on the bus.
    #[k::cases("p1")]
    first_read_back: { bus: [.., Write(helper::FIRST, v), .., Read(helper::FIRST, v), ..] };
}
"#;

/// The clause of [`HELPED_PATTERNS`] with the constant's value written out, in a package that
/// needs no facet.
const PLAIN_PATTERNS: &str = r#"k::patterns! {
    for spec::Machine;
    use spec::Event::*;

    /// The first address written, then read back, on the bus.
    #[k::cases("p1")]
    first_read_back: { bus: [.., Write(1, v), .., Read(1, v), ..] };
}
"#;

/// A clause whose condition applies the helper's function, which the specification does not
/// hold.
const BUMPED_CLAUSE: &str = r"
    /// A write of the value whose successor is 6.
    #[k::requires(helper::Bump(v) == 6)]
    bumped: { bus: [.., Write(_, v), ..] };
}
";

/// OBSERVER-COMPOSITION: a patterns package that needs a facet outside the specification's
/// closure declares it in its own facet's table, and `krs kink query` composes it with no
/// `--dependency`. The addition reaches the package's composition alone: the specification's
/// digest, `definition.k`, the record and the pattern's digest and cached answers are those of
/// the corpus asked by a package that writes the constant's value out, and nothing of the
/// helper is in the emitted K. Without the declaration the entry is refused, naming the
/// package's key.
///
/// The addition gives the package's clauses names, and the specification nothing: a pattern is
/// asked of the specification's runs in the specification's own K. So a clause that applies a
/// function of the added facet emits and is then `invalid-pattern`, since the K it is asked in
/// has no such function, and the specification stays as it is.
#[test]
fn a_patterns_package_adds_the_facets_it_declares_and_leaves_the_definition_as_it_is() {
    let workspace = Workspace::new(&[("pats", PLAIN_PATTERNS), ("helper", HELPER)]);
    workspace.declare("[[patterns]]\nkrs = \"pats\"\n");
    let output = workspace.kink("query", &[]);
    assert_status(&output, 0);
    let alone = json_of(&output);
    let definition = workspace.read("spec/kink/definition.k");
    let lock = workspace.read("spec/kink/kink.lock");

    // The package now depends on the helper, names its constant, and declares its facet.
    let manifest = workspace.read("pats/Cargo.toml").replace(
        "spec = { path = \"../spec\" }\n",
        "spec = { path = \"../spec\" }\nhelper = { path = \"../helper\" }\n",
    );
    let declared = format!("{manifest}dependencies = [\"helper:main\"]\n");
    workspace.write("pats/Cargo.toml", &declared);
    workspace.write("pats/src/lib.rs", HELPED_PATTERNS);
    let output = workspace.kink("query", &[]);
    assert_status(&output, 0);
    let helped = json_of(&output);
    assert_eq!(helped["spec"]["digest"], alone["spec"]["digest"]);
    assert_eq!(helped["definition"]["status"], "unchanged", "{helped:#}");
    assert_eq!(workspace.read("spec/kink/definition.k"), definition);
    assert!(
        !definition.contains("ORG-KRS-KINK-PATTERNS-HELPER"),
        "{definition}"
    );
    assert_eq!(workspace.read("spec/kink/kink.lock"), lock);
    assert_eq!(
        pattern(&helped, "first-read-back")["digest"],
        pattern(&alone, "first-read-back")["digest"]
    );
    let hit = row(&helped, "first-read-back", "p1");
    assert_eq!(
        (&hit["answer"], &hit["cached"]),
        (&json!("hit"), &json!(true)),
        "{hit:#}"
    );
    assert_status(&workspace.kink("emit", &["--check"]), 0);

    // A clause that applies the added facet's function is asked in the specification's K,
    // which does not hold it.
    let clauses = HELPED_PATTERNS.trim_end().strip_suffix('}').unwrap();
    workspace.write("pats/src/lib.rs", &format!("{clauses}{BUMPED_CLAUSE}"));
    let output = workspace.kink("query", &[]);
    assert_status(&output, 2);
    let bumped = json_of(&output);
    assert_eq!(
        pattern(&bumped, "bumped")["outcome"],
        "invalid-pattern",
        "{bumped:#}"
    );
    assert_eq!(
        pattern(&bumped, "first-read-back")["outcome"],
        "valid",
        "{bumped:#}"
    );
    assert_eq!(bumped["spec"]["digest"], alone["spec"]["digest"]);
    assert_eq!(workspace.read("spec/kink/definition.k"), definition);
    workspace.write("pats/src/lib.rs", HELPED_PATTERNS);

    // Without the declaration the package cannot collect the helper's constant.
    workspace.write("pats/Cargo.toml", &manifest);
    let output = workspace.kink("query", &[]);
    assert_status(&output, 2);
    let document = json_of(&output);
    let detail = document["pattern_list"]["detail"].as_str().unwrap();
    assert!(detail.contains("package-not-selected"), "{detail}");
    assert!(
        detail.contains(
            "add `\"helper:main\"` to `package.metadata.krs.definitions.main.dependencies` in package `pats`'s Cargo.toml"
        ),
        "{detail}"
    );
    assert_eq!(workspace.read("spec/kink/definition.k"), definition);
}

/// A machine whose statements store values in a memory map and count steps in `pc`.
/// No sentence of it has a condition, so its module does not import `BOOL`: the connectives a
/// part's condition is joined with are the pattern's own vocabulary.
const MEMORY_SPEC: &str = r#"use k::KResult;
use k::builtin::{Int, KSequence, Map};

k::sorts! {
    Stmt: k::KItem;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("set ( {a} , {v} )")]
    Set { a: Int, v: Int },
    #[k::syntax("mark")]
    Mark(),
    #[k::syntax("seq ( {first} , {second} )")]
    Seq { first: Stmt, second: Stmt },
}

#[k::configuration]
pub struct Machine {
    #[k::cell(name = "k")]
    pub k: KSequence,
    #[k::cell(name = "pc")]
    pub pc: Int,
    #[k::cell(name = "memory")]
    pub memory: Map<Int, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] program: Stmt) -> Self {
        Self {
            k: k::k![program],
            pc: 0,
            memory: k::map![],
        }
    }
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    seq: { k: [Seq { first: a, second: b }, ..] } => { k: [a, b, ..] };
    set: { k: [Set { a: addr, v: value }, ..], pc, memory: m } => { k: [..], pc: pc + 1, memory: k::map![addr -> value, ..m] };
    mark: { k: [Mark(), ..], pc } => { k: [..], pc: pc + 1 };
}
"#;

/// Each question of key 9 written twice, with the lookup in the condition and with the map
/// pattern that binds the key's value: a step, a step whose lookup stands below `!`, and an
/// `unless` on the states between `pc` 0 and `pc` 2, plain and below `!`.
const MEMORY_PATTERNS: &str = r"k::patterns! {
    for spec::Machine;

    #[k::requires(memory[9] != 0)]
    lookup: { memory };

    #[k::requires(!(memory[9] == 0))]
    negated_lookup: { memory };

    #[k::requires(v != 0)]
    bound: { memory: { 9 -> v, .. } };

    kept: { pc: 0 } => unless({ memory }, requires(memory[9] == 0)) { pc: 2 };

    negated_kept: { pc: 0 } => unless({ memory }, requires(!(memory[9] != 0))) { pc: 2 };

    bound_kept: { pc: 0 } => unless({ memory: { 9 -> v, .. } }, requires(v == 0)) { pc: 2 };
}
";

/// The memory corpus: a program that never stores key 9, one that stores 5 there and one that
/// stores 0, each reaching `pc` 2 through one state at `pc` 1.
const MEMORY_FLOW: &str = "[spec]\nkrs = { package = \"spec\", definition = \"main\" }\n\n[budget]\ntime_ms = 600000\n\n\
                           [[program]]\nid = \"absent\"\nfile = \"cases/absent.prog\"\n\n\
                           [[program]]\nid = \"five\"\nfile = \"cases/five.prog\"\n\n\
                           [[program]]\nid = \"zero\"\nfile = \"cases/zero.prog\"\n\n\
                           [[patterns]]\nkrs = \"pats\"\n";

/// A part is the set of states at which its condition is true, and a lookup of a key the map
/// lacks has no value, so the condition is not true there, also where the lookup stands below
/// `!` (FB-63). A step does not match a state without the key; an `unless` does not exclude
/// one. The lookup spelling answers each program as the map pattern that binds the key's value
/// does.
#[test]
fn a_condition_with_no_value_is_not_true_of_a_state() {
    let workspace = Workspace::of(
        MEMORY_SPEC,
        MEMORY_FLOW,
        &[
            ("absent", "seq(mark, mark)\n"),
            ("five", "seq(set(9, 5), mark)\n"),
            ("zero", "seq(set(9, 0), mark)\n"),
        ],
        &[("pats", MEMORY_PATTERNS)],
    );
    // `--full` asks every program of every pattern, past its first hit.
    let output = workspace.kink("query", &["--full"]);
    assert_status(&output, 0);
    let document = json_of(&output);
    let answers = |id: &str| {
        ["absent", "five", "zero"].map(|program| row(&document, id, program)["answer"].clone())
    };

    // A step: only the program that stores a value other than 0 at the key hits.
    let step = [json!("no"), json!("hit"), json!("no")];
    assert_eq!(answers("bound"), step, "{document:#}");
    assert_eq!(answers("lookup"), step, "{document:#}");
    assert_eq!(answers("negated-lookup"), step, "{document:#}");

    // An `unless`: only the program whose state at `pc` 1 holds 0 at the key is excluded; the
    // one whose memory lacks the key is not, below `!` either.
    let unless = [json!("hit"), json!("hit"), json!("no")];
    assert_eq!(answers("bound-kept"), unless, "{document:#}");
    assert_eq!(answers("kept"), unless, "{document:#}");
    assert_eq!(answers("negated-kept"), unless, "{document:#}");

    // The lookup's tests stand before the conjunct that evaluates it, outside its `!`.
    assert_eq!(
        pattern(&document, "negated-lookup")["pattern"],
        "<memory> Memory:Map </memory> requires 9 in_keys(Memory:Map) andThenBool (isInt(Memory:Map [ 9 ]) andThenBool (notBool ({Memory:Map [ 9 ]}:>Int ==Int 0)))",
        "{document:#}"
    );
}

/// Patterns whose conditions name what no sentence of the memory specification does: the
/// connective the tests of one lookup are joined with, an author's `&&`, and an operation of
/// `STRING`, a module the specification's main module imports through no module.
const VOCABULARY_PATTERNS: &str = r#"k::patterns! {
    for spec::Machine;

    #[k::requires(memory[9] != 0)]
    lookup: { memory };

    #[k::requires(v != 0 && v != 1)]
    both: { memory: { 9 -> v, .. } };

    #[k::requires(memory.len() == 1)]
    sized: { memory };

    #[k::requires(k::builtin::string::length("ab") == pc)]
    text: { pc };
}
"#;

/// A pattern is a question about the specification's runs and no sentence of it, so the
/// operations its condition names are its own, whatever the specification's sentences import
/// (PATTERN-CONDITION-IMPORTS). A specification with no condition, whose module does not import
/// `BOOL`, answers a pattern whose condition holds one lookup, and one whose author joins two
/// tests; asking them leaves the specification as it is emitted alone. A pattern that names an
/// operation of a module the compiled definition does not hold is refused naming the module.
#[test]
fn a_condition_names_what_the_specification_does_not_import() {
    let workspace = Workspace::of(
        MEMORY_SPEC,
        MEMORY_FLOW,
        &[
            ("absent", "seq(mark, mark)\n"),
            ("five", "seq(set(9, 5), mark)\n"),
            ("zero", "seq(set(9, 0), mark)\n"),
        ],
        &[("pats", VOCABULARY_PATTERNS)],
    );
    let output = workspace.kink("query", &["--full"]);
    // The refused pattern is not asked.
    assert_status(&output, 2);
    let document = json_of(&output);
    let answers = |id: &str| {
        ["absent", "five", "zero"].map(|program| row(&document, id, program)["answer"].clone())
    };

    // The specification's module imports neither `BOOL` nor `STRING`, with the package asked
    // as without it: `definition.k` is what the specification alone emits.
    let definition = workspace.read("spec/kink/definition.k");
    for module in ["BOOL", "STRING"] {
        assert!(
            !definition
                .lines()
                .any(|line| line.trim() == format!("imports {module}")),
            "{definition}"
        );
    }
    assert_status(&workspace.kink("emit", &["--check"]), 0);

    for id in ["lookup", "both", "sized"] {
        assert_eq!(pattern(&document, id)["outcome"], "valid", "{document:#}");
    }
    assert_eq!(
        pattern(&document, "lookup")["pattern"],
        "<memory> Memory:Map </memory> requires 9 in_keys(Memory:Map) andThenBool (isInt(Memory:Map [ 9 ]) andThenBool ({Memory:Map [ 9 ]}:>Int =/=Int 0))",
        "{document:#}"
    );
    let stored = [json!("no"), json!("hit"), json!("no")];
    assert_eq!(answers("lookup"), stored, "{document:#}");
    assert_eq!(answers("both"), stored, "{document:#}");
    assert_eq!(
        answers("sized"),
        [json!("no"), json!("hit"), json!("hit")],
        "{document:#}"
    );

    let text = pattern(&document, "text");
    assert_eq!(text["outcome"], "invalid-pattern", "{document:#}");
    let detail = text["detail"].as_str().unwrap();
    assert!(
        detail.contains("the pattern imports STRING, which the specification's main module"),
        "{detail}"
    );
}
