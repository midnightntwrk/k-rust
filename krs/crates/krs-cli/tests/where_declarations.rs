//! A given binder sort is a declaration in every form: `where s: S` on a
//! readable rule, table row, or claim, a rule fn's typed parameter, and a
//! `cells!` rule's binder list. The binder has exactly sort `S`, and every
//! occurrence, a typed map read included, must admit it; a wider, unrelated,
//! or disjoint declaration is an error whose help names the declaration that
//! fits.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Id, Int, KSequence, Map, map};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp;
    Stmt;
    Value: Stmt + Exp + KResult;
    impl Value for Int;
    Other;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Eval, Pair))]
pub enum ExpSyntax {
    #[k::syntax("eval ( {e} )")]
    Eval { e: Exp },
    #[k::syntax("pair ( {a} , {b} )")]
    Pair { a: Exp, b: Exp },
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Skip, Run, Hold, Load))]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("run ( {s} )")]
    Run { s: Stmt },
    #[k::syntax("hold ( {saved} )")]
    Hold { saved: KItem },
    #[k::syntax("load {n}")]
    Load { n: Id },
}

#[k::constructors(sort = Other, result = KResult)]
pub enum OtherSyntax {
    #[k::syntax("oth")]
    Oth(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Exp>,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: map::empty(),
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
    source_package(root, name, &format!("{PREAMBLE}{body}"))
}

/// Writes a one-package workspace whose library is `source`.
fn source_package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-WHERE\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The first diagnostic: its headline, the text its caret marks, and its
/// help lines.
fn first_diagnostic(stderr: &str) -> (String, String, Vec<String>) {
    let lines = stderr.lines().collect::<Vec<_>>();
    let index = lines
        .iter()
        .position(|line| line.starts_with("error["))
        .unwrap_or_else(|| panic!("no error:\n{stderr}"));
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
    let help = lines[index + 1..]
        .iter()
        .take_while(|line| !line.starts_with("error") && !line.starts_with("warning"))
        .filter_map(|line| line.trim().strip_prefix("= help: "))
        .map(str::to_owned)
        .collect();
    (lines[index].to_owned(), marked, help)
}

fn rules(body: &str) -> String {
    format!(
        "k::rules! {{\n    for Machine;\n    use ExpSyntax::*;\n    use StmtSyntax::*;\n    use OtherSyntax::*;\n\n    {body}\n}}\n"
    )
}

fn table(body: &str) -> String {
    format!("k::rules! {{\n    for Exp;\n    use ExpSyntax::*;\n\n    {body}\n}}\n")
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

/// The emitted lines that mention `pattern`, trimmed.
fn lines_with(definition: &str, pattern: &str) -> Vec<String> {
    definition
        .lines()
        .filter(|line| line.contains(pattern))
        .map(|line| line.trim().to_owned())
        .collect()
}

fn incompatible(declared: &str, needed: &str) -> String {
    format!(
        "error[krs::analysis::incompatible-binder]: binder `s` is declared `{declared}`, but an occurrence needs `{needed}`"
    )
}

/// A wider, unrelated, or disjoint declaration is rejected in every form, at
/// the declared sort, with the fitting declaration named.
#[test]
fn a_declaration_every_occurrence_does_not_admit_is_rejected() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let meet = "a `Stmt` that fits here is a `Value`: declare `s` as `Value`".to_owned();
    let cases = [
        (
            "unrelated",
            rules("r: { k: [Eval { e: s }, ..] } => { k: [s, ..] } where s: Stmt;"),
            incompatible("Stmt", "Exp"),
            "Stmt",
            vec![meet.clone()],
        ),
        (
            "unrelated-table",
            table("r: Eval { e: s } => s where s: Stmt;"),
            incompatible("Stmt", "Exp"),
            "Stmt",
            vec![meet.clone()],
        ),
        (
            "unrelated-result",
            rules("r: { k: [Eval { e: s }, ..] } => { k: [Run { s: s }, ..] } where s: Stmt;"),
            incompatible("Stmt", "Exp"),
            "Stmt",
            vec![meet.clone()],
        ),
        (
            "wider",
            rules("r: { k: [Eval { e: s }, ..] } => { k: [s, ..] } where s: KItem;"),
            incompatible("KItem", "Exp"),
            "KItem",
            vec![
                "this position admits only `Exp`: declare `s` as `Exp` or a sort below it".to_owned(),
            ],
        ),
        (
            "disjoint",
            rules("r: { k: [Eval { e: s }, ..] } => { k: [s, ..] } where s: Other;"),
            incompatible("Other", "Exp"),
            "Other",
            vec!["no term is both a `Other` and a `Exp`".to_owned()],
        ),
        (
            "claim",
            "k::claims! {\n    for Machine;\n    use ExpSyntax::*;\n\n    #[k::claim(all_paths)]\n    r: { k: [Eval { e: s }] } => { k: [s] } where s: Stmt;\n}\n".to_owned(),
            incompatible("Stmt", "Exp"),
            "Stmt",
            vec![meet.clone()],
        ),
        (
            "cells",
            "#[k::rule]\npub fn r(\n    s: Term<Stmt>,\n    k::cells! { k: k::configuration::KCell(ExpSyntax::Eval(s), tail @ ..), state @ .. }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(s, ..tail), ..state }\n}\n".to_owned(),
            incompatible("Stmt", "Exp"),
            "Stmt",
            vec![meet.clone()],
        ),
        (
            "map-overlapping",
            rules(
                "r: { k: [Load { n }, ..], env: { n -> v, .. } } => { k: [v, ..] } where n: Id, v: Stmt;",
            ),
            "error[krs::analysis::collection-element-sort]: `v` is read as a value of the cell `env`, declared `Map<Id, Exp>`, so `where v: Stmt` must name Exp or a sort below it; a value that is also a Stmt is a Value: write `where v: Value`".to_owned(),
            "Stmt",
            vec![],
        ),
        (
            "map-disjoint",
            rules(
                "r: { k: [Load { n }, ..], env: { n -> v, .. } } => { k: [v, ..] } where n: Id, v: Other;",
            ),
            "error[krs::analysis::collection-element-sort]: `v` is read as a value of the cell `env`, declared `Map<Id, Exp>`, but `where v: Other` asks for an Other, which no Exp is".to_owned(),
            "Other",
            vec![],
        ),
    ];
    for (name, source, headline, marked, rest) in cases {
        let manifest = package(temporary.path(), name, &source);
        let (success, _, stderr) =
            krs(target.path(), &manifest, "check", &["--backend", "haskell"]);
        assert!(!success, "{name}: krs check unexpectedly passed:\n{stderr}");
        assert_eq!(
            first_diagnostic(&stderr),
            (headline, marked.to_owned(), rest),
            "{name}:\n{stderr}"
        );
    }
}

/// A declaration at or below every occurrence emits exactly the declared
/// sort, and a binder without one is inferred as before; a `KItem`
/// occurrence admits every declaration. `krs expand` writes each `where` as
/// the `cells!` binder list, which declares the same sorts.
#[test]
fn a_declaration_every_occurrence_admits_emits_its_sort() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "fitting",
        &format!(
            "{}{}",
            rules(
                "narrow: { k: [Eval { e: s }, ..] } => { k: [s, ..] } where s: Int;\n    meet: { k: [Pair { a: s, b: Eval { e: _ } }, ..] } => { k: [s, ..] } where s: Value;\n    inferred: { k: [Pair { a: Eval { e: _ }, b: s }, ..] } => { k: [Run { s: s }, ..] };\n    held: { k: [Hold { saved: s }, ..] } => { k: [s, ..] } where s: Stmt;\n    read: { k: [Load { n }, ..], env: { n -> v, .. } } => { k: [v, ..] } where n: Id, v: Value;"
            ),
            "#[k::rule]\npub fn cells_run(\n    s: Term<Stmt>,\n    k::cells! { k: k::configuration::KCell(StmtSyntax::Run(s), tail @ ..), state @ .. }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(s, ..tail), ..state }\n}\n",
        ),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &["--backend", "haskell"]);
    assert!(success, "{stderr}");
    let definition = emitted(target.path(), &manifest);
    let rules = |definition: &str| {
        [
            lines_with(definition, "<k> eval"),
            lines_with(definition, "<k> pair ( S"),
            lines_with(definition, "<k> pair ( eval"),
            lines_with(definition, "<k> hold"),
            lines_with(definition, "<k> load"),
            lines_with(definition, "<k> run"),
        ]
    };
    expect_test::expect![[r#"
        [
            [
                "<k> eval ( S:Int ) => S:Int ... </k>",
            ],
            [
                "<k> pair ( S:Value , eval ( _ ) ) => S:Value ... </k>",
            ],
            [
                "<k> pair ( eval ( _ ) , S:Value ) => run ( S:Value ) ... </k>",
            ],
            [
                "<k> hold ( S:Stmt ) => S:Stmt ... </k>",
            ],
            [
                "<k> load N:Id => V:Value ... </k>",
            ],
            [
                "<k> run ( S:Stmt ) ~> Tail:K => S:Stmt ~> Tail:K </k>",
            ],
        ]
    "#]]
    .assert_debug_eq(&rules(&definition));

    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let reference = source_package(temporary.path(), "reference", &expanded);
    // The expansion frames the computation with `tail @ ..`, so compare the
    // sorted binders only.
    let binders = |rules: [Vec<String>; 6]| {
        rules.map(|lines| {
            lines
                .iter()
                .flat_map(|line| line.split_whitespace())
                .filter(|token| token.contains(':') && !token.starts_with("Tail:"))
                .map(str::to_owned)
                .collect::<Vec<_>>()
        })
    };
    assert_eq!(
        binders(rules(&emitted(target.path(), &reference))),
        binders(rules(&definition))
    );
}
