//! The sort a binder gets, end to end: an existential or fresh binder has
//! exactly its declared sort in every rule form.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Id, Int, KSequence, List, Map, Set, list, map, set};
use k::{KItem, KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
    Exp;
    impl Exp for Int;
    Frame;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Skip, Seq, Op, Put, Pair))]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("seq ( {first} , {second} )")]
    Seq { first: Stmt, second: Stmt },
    #[k::syntax("op {code}")]
    Op { code: Int },
    #[k::syntax("put {name} {s}")]
    Put { name: Id, s: Stmt },
    #[k::syntax("pair ( {a} , {b} )")]
    Pair { a: Exp, b: Exp },
}

#[k::constructors(sort = Frame, result = KResult)]
#[k::precedence((Hold))]
pub enum FrameSyntax {
    #[k::syntax("hold ( {saved} )")]
    Hold { saved: KItem },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Value>,
    #[k::cell]
    pub stack: List<Value>,
    #[k::cell]
    pub queue: List,
    #[k::cell]
    pub acc: Int,
    #[k::cell]
    pub raw: Map,
    #[k::cell]
    pub raw2: Map,
    #[k::cell]
    pub bag: Set,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: map::empty(),
            stack: list::empty(),
            queue: list::empty(),
            acc: 0,
            raw: map::empty(),
            raw2: map::empty(),
            bag: set::empty(),
        }
    }
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is the preamble and `body`.
fn package(root: &Path, name: &str, body: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{PREAMBLE}{body}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-BINDERS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package's `main` definition.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let package = manifest
        .parent()
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())
        .unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main"])
        .args(extra)
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// Each diagnostic's headline and the source text its caret marks.
fn diagnostics(stderr: &str) -> Vec<(String, String)> {
    let lines = stderr.lines().collect::<Vec<_>>();
    let mut output = Vec::new();
    for (index, line) in lines.iter().enumerate() {
        if !(line.starts_with("error[") || line.starts_with("warning[")) {
            continue;
        }
        // `--> path`, ` |`, `N | source`, ` |   ^^^`.
        let marked = lines
            .get(index + 3)
            .zip(lines.get(index + 4))
            .and_then(|(source, carets)| {
                let source = source.split_once(" | ")?.1;
                let carets = carets.split_once(" | ")?.1;
                let start = carets.find('^')?;
                let width = carets[start..].chars().take_while(|c| *c == '^').count();
                source.get(start..start + width).map(str::to_owned)
            })
            .unwrap_or_default();
        output.push(((*line).to_owned(), marked));
    }
    output
}

/// Emits the package's K and returns `definition.k`.
fn emitted(target: &Path, manifest: &Path) -> String {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.k")).unwrap()
}

/// The rule's body lines in the emitted K, joined.
fn rule(definition: &str, label: &str) -> String {
    let start = definition
        .find(&format!("rule [{label}]:"))
        .unwrap_or_else(|| panic!("no rule {label}:\n{definition}"));
    definition[start..]
        .lines()
        .skip(1)
        .take_while(|line| {
            let line = line.trim();
            !line.is_empty()
                && !["rule", "//", "endmodule"]
                    .iter()
                    .any(|start| line.starts_with(start))
        })
        .map(str::trim)
        .collect::<Vec<_>>()
        .join(" ")
}

fn rules(body: &str) -> String {
    format!(
        "k::rules! {{\n    for Machine;\n    use StmtSyntax::*;\n    use FrameSyntax::*;\n\n    {body}\n}}\n"
    )
}

/// Asserts that `krs check` rejects each case with the expected first
/// diagnostic and caret.
fn assert_rejected(target: &Path, root: &Path, cases: &[(&str, String, String, &str)]) {
    for (name, source, headline, marked) in cases {
        let manifest = package(root, name, source);
        let (success, _, stderr) = krs(target, &manifest, "check", &["--backend", "haskell"]);
        assert!(!success, "{name}: krs check unexpectedly passed:\n{stderr}");
        assert_eq!(
            diagnostics(&stderr).first(),
            Some(&(headline.clone(), (*marked).to_owned())),
            "{name}:\n{stderr}"
        );
    }
}

/// An existential or fresh binder is a value of exactly its declared sort:
/// an occurrence whose position needs a sort the declared one is not below
/// is rejected in every rule form, at the declaration or, at a typed element
/// position, at the occurrence with the declared element type; one that fits
/// keeps its declared sort.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of rejected rules, each with its expected diagnostic."
)]
fn existential_and_fresh_binders_keep_their_declared_sort() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let incompatible = |name: &str, declared: &str, needed: &str| {
        format!(
            "error[krs::analysis::incompatible-binder]: binder `{name}` is declared `{declared}` but this occurrence needs `{needed}`"
        )
    };
    let stored = |term: &str, sort: &str, position: &str, element: &str| {
        format!(
            "error[krs::analysis::collection-element-sort]: `{term}` of sort {sort} is stored as {position}, and {sort} is not {element}"
        )
    };
    let env_value = "a value of the cell `env`, declared `Map<Id, Value>`";
    let cells_rule = |sort: &str| {
        format!(
            "#[k::rule]\n#[k::exists(v: {sort})]\npub fn probe(\n    k::cells! {{ k: k::configuration::KCell(StmtSyntax::Op(1), tail @ ..), state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(StmtSyntax::Op(v), ..tail), ..state }}\n}}\n"
        )
    };
    assert_rejected(
        target.path(),
        temporary.path(),
        &[
            (
                "unrelated",
                rules("#[k::exists(v: Stmt)]\n    probe: { k: [Op(1), ..] } => { k: [Op(v), ..] };"),
                incompatible("v", "Stmt", "Int"),
                "Stmt",
            ),
            (
                "wider",
                rules("#[k::exists(v: Value)]\n    probe: { k: [Op(1), ..] } => { k: [Op(v), ..] };"),
                incompatible("v", "Value", "Int"),
                "Value",
            ),
            (
                "map-value",
                rules(
                    "#[k::exists(v: Stmt)]\n    probe: { k: [Put(name, _), ..], env: e } => { k: [..], env: map::update(e, name, v) };",
                ),
                stored("v", "Stmt", env_value, "a Value"),
                "v",
            ),
            (
                "fresh-element",
                rules(
                    "#[k::fresh(n: Id)]\n    probe: { k: [Op(1), ..], stack: l } => { k: [..], stack: [n, ..l] };",
                ),
                stored(
                    "n",
                    "Id",
                    "an element of the cell `stack`, declared `List<Value>`",
                    "a Value",
                ),
                "n",
            ),
            (
                "claim",
                "k::claims! {\n    for Machine;\n    use StmtSyntax::*;\n\n    #[k::claim(all_paths)]\n    #[k::exists(v: Stmt)]\n    probe: { k: [Put(name, _)], env: e } => { k: [], env: map::update(e, name, v) };\n}\n".to_owned(),
                stored("v", "Stmt", env_value, "a Value"),
                "v",
            ),
            (
                "term-rule",
                "#[k::rule]\n#[k::exists(v: Stmt)]\npub fn probe(k::term![StmtSyntax::Op(1)]: Term<Stmt>) -> Term<Stmt> {\n    StmtSyntax::Op(v)\n}\n".to_owned(),
                incompatible("v", "Stmt", "Int"),
                "Stmt",
            ),
            (
                "cells-unrelated",
                cells_rule("Stmt"),
                incompatible("v", "Stmt", "Int"),
                "Stmt",
            ),
            (
                "cells-wider",
                cells_rule("Value"),
                incompatible("v", "Value", "Int"),
                "Value",
            ),
        ],
    );

    let manifest = package(
        temporary.path(),
        "fitting",
        &format!(
            "{}{}",
            rules(
                "#[k::exists(v: Int)]\n    narrow: { k: [Op(1), ..] } => { k: [Op(v), ..] };\n    #[k::exists(w: Int)]\n    store: { k: [Put(name, _), ..], env: e } => { k: [..], env: map::update(e, name, w) };\n    #[k::fresh(n: Int)]\n    push: { k: [Op(2), ..], stack: l } => { k: [..], stack: [n, ..l] };"
            ),
            cells_rule("Int")
                .replace("probe", "cells_probe")
                .replace("Op(1)", "Op(3)"),
        ),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &["--backend", "haskell"]);
    assert!(success, "{stderr}");
    let definition = emitted(target.path(), &manifest);
    expect_test::expect![[r#"
        [
            "<k> op 1 => op ?V:Int ... </k>",
            "<k> put Name:Id _ => .K ... </k> <env> E:Map => E:Map [ Name:Id <- ?W:Int ] </env>",
            "<k> op 2 => .K ... </k> <stack> L:List => ListItem(!N:Int) L:List </stack>",
        ]
    "#]]
    .assert_debug_eq(&[
        rule(&definition, "narrow"),
        rule(&definition, "store"),
        rule(&definition, "push"),
    ]);
}
