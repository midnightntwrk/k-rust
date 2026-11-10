//! The map from an author's Rust names to the emitted K names: every name rustc accepts either
//! becomes a K name that means what the Rust name means, distinct from every other name of its
//! K namespace, or is refused with an author code whose reason names both Rust names.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const LIBRARY: &str = r#"use k::KResult;
use k::builtin::{Int, KSequence, int};
use k::Term;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("wrap({s})")]
    Wrap { s: Stmt },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm], acc: 0 }
    }
}

#[k::function(total, internal)]
pub fn PickF(b: Term<Int>) -> Term<Int>;

k::equations! {
    for PickF;
    table: (b) => int::add(b, 1);
}

k::rules! {
    for Machine;
    use StmtSyntax::*;
    unwrap: { k: [Wrap { s }, ..], acc: v } => { k: [s, ..], acc: PickF(v) };
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace named `name`, in the directory `directory`, whose library is
/// `library`.
fn package(root: &Path, directory: &str, name: &str, library: &str) -> PathBuf {
    let directory = root.join(directory);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-NAME-MAP\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package `package`'s `main` definition.
fn krs(
    target: &Path,
    manifest: &Path,
    package: &str,
    command: &str,
    extra: &[&str],
) -> (bool, String, String) {
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

/// The emitted `definition.k` without its header line and the package-relative source comments,
/// which name the package.
fn emitted_k(target: &Path, manifest: &Path, package: &str, output: &Path) -> String {
    let (success, _, stderr) = krs(
        target,
        manifest,
        package,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.k"))
        .unwrap()
        .lines()
        .skip(1)
        .filter(|line| !line.trim_start().starts_with("// KRS "))
        .collect::<Vec<_>>()
        .join("\n")
}

/// A package whose name is a Rust keyword is a crate rustc names by the raw identifier
/// (`module_path!()` writes `r#let`), which is the identifier `let`: its items are the selected
/// target's, so it checks, and its K is the K of the same library under another name.
#[test]
fn a_package_named_by_a_keyword_is_its_crate() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let keyword = package(temporary.path(), "keyword", "let", LIBRARY);
    let plain = package(temporary.path(), "plain", "name_map_plain", LIBRARY);
    let (success, _, stderr) = krs(target.path(), &keyword, "let", "check", &[]);
    assert!(success, "{stderr}");
    assert_eq!(
        emitted_k(
            target.path(),
            &keyword,
            "let",
            &temporary.path().join("keyword-out")
        ),
        emitted_k(
            target.path(),
            &plain,
            "name_map_plain",
            &temporary.path().join("plain-out")
        ),
    );
}

/// A raw identifier is the identifier itself, so a table row written `r#table` is the row `table`
/// (its K is the plain row's), and one written `r#match` is the row `match`, labelled by it.
#[test]
fn a_raw_row_name_is_its_identifier() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let plain = package(temporary.path(), "plain", "name_map_rows", LIBRARY);
    let raw = package(
        temporary.path(),
        "raw",
        "name_map_rows",
        &LIBRARY.replace("table: (b)", "r#table: (b)"),
    );
    let keyword = package(
        temporary.path(),
        "keyword",
        "name_map_rows",
        &LIBRARY.replace("table: (b)", "r#match: (b)"),
    );
    let plain_k = emitted_k(
        target.path(),
        &plain,
        "name_map_rows",
        &temporary.path().join("plain-out"),
    );
    assert_eq!(
        emitted_k(
            target.path(),
            &raw,
            "name_map_rows",
            &temporary.path().join("raw-out")
        ),
        plain_k
    );
    let (success, _, stderr) = krs(target.path(), &keyword, "name_map_rows", "check", &[]);
    assert!(success, "{stderr}");
    let keyword_k = emitted_k(
        target.path(),
        &keyword,
        "name_map_rows",
        &temporary.path().join("keyword-out"),
    );
    assert_eq!(
        keyword_k,
        plain_k.replace(
            "[label(org_krs_name_map--table)]",
            "[label(org_krs_name_map--match)]"
        )
    );
}

/// `LIBRARY` with each `(from, to)` replaced and `extra` appended.
fn library(replacements: &[(&str, &str)], extra: &str) -> String {
    let mut source = LIBRARY.to_owned();
    for (from, to) in replacements {
        assert!(source.contains(from), "{from}");
        source = source.replacen(from, to, 1);
    }
    source + extra
}

/// The headline of `krs check`'s first error on a package of `library`, or `None` when the
/// package checks.
fn check_headline(target: &Path, root: &Path, directory: &str, library: &str) -> Option<String> {
    let name = format!("name_map_{}", directory.replace('-', "_"));
    let manifest = package(root, directory, &name, library);
    let (success, _, stderr) = krs(target, &manifest, &name, "check", &[]);
    (!success).then(|| {
        stderr
            .lines()
            .find(|line| line.starts_with("error"))
            .unwrap_or_else(|| panic!("no error:\n{stderr}"))
            .to_owned()
    })
}

/// A declared sort and a constructor of it, appended to `LIBRARY`.
fn sort(name: &str) -> String {
    format!(
        "\nk::sorts! {{\n    {name};\n}}\n\n#[k::constructors(sort = {name}, result = KResult)]\npub enum {name}Syntax {{\n    #[k::syntax(\"mark\")]\n    Mark(),\n}}\n"
    )
}

/// `LIBRARY` with a function `name`, which the rule `unwrap` reads in place of `PickF`.
fn function(name: &str) -> String {
    library(
        &[("acc: PickF(v)", &format!("acc: {name}(v)"))],
        &format!(
            "\n#[k::function(total, internal)]\npub fn {name}(b: Term<Int>) -> Term<Int> {{\n    int::add(b, 2)\n}}\n"
        ),
    )
}

/// A name K already gives a meaning is one thing in K, so an authored declaration that takes it
/// would add to K's thing instead of declaring its own: K's own sorts, the sorts K generates for
/// the definition's cells, a symbol of a builtin module the definition imports (the
/// conditional's `ite`; a configuration imports `MAP`), a cell K adds to every configuration,
/// and a terminal K reads as a sentence keyword (a function's name gives its terminal). Each is
/// refused at the declaration, naming both. A name of a module the definition does not import
/// (`bigEndianBytes` without bytes), a word K reads as a keyword only between sentences
/// (`requires`), a sort K does not declare (`KVariable`, whose K sort is `#KVariable`) and a
/// cell named by a keyword stay accepted.
#[test]
fn a_name_k_gives_a_meaning_is_refused_at_the_declaration() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let collision = "error[krs::analysis::symbol-name-collision]: ";
    let cases = [
        (
            "sort-kcell",
            library(&[], &sort("KCell")),
            Some(
                "sort `KCell` of ORG-KRS-NAME-MAP has the K name \"KCell\", which K generates as the sort of the cell `<k>`",
            ),
        ),
        (
            "sort-kbott",
            library(&[], &sort("KBott")),
            Some(
                "sort `KBott` of ORG-KRS-NAME-MAP has the K name \"KBott\", which K declares as a sort of its own",
            ),
        ),
        ("sort-kvariable", library(&[], &sort("KVariable")), None),
        (
            "cell-generated-top",
            library(
                &[
                    (
                        "pub acc: Int,",
                        "pub acc: Int,\n    #[k::cell(name = \"generatedTop\")]\n    pub top: Int,",
                    ),
                    ("acc: 0 }", "acc: 0, top: 0 }"),
                ],
                "",
            ),
            Some(
                "the cell `top` has the K name \"generatedTop\", which K adds as the top cell of every configuration",
            ),
        ),
        (
            "cell-rule",
            library(
                &[
                    (
                        "pub acc: Int,",
                        "pub acc: Int,\n    #[k::cell]\n    pub rule: Int,",
                    ),
                    ("acc: 0 }", "acc: 0, rule: 0 }"),
                ],
                "",
            ),
            None,
        ),
    ];
    let functions = [
        (
            "fn-ite",
            "Ite",
            Some(
                "production `Ite` of ORG-KRS-NAME-MAP has the K name \"ite\", which K's builtin module `K-EQUAL` declares as a symbol",
            ),
        ),
        (
            "fn-size-map",
            "SizeMap",
            Some(
                "production `SizeMap` of ORG-KRS-NAME-MAP has the K name \"sizeMap\", which K's builtin module `MAP` declares as a symbol",
            ),
        ),
        ("fn-big-endian-bytes", "BigEndianBytes", None),
        (
            "fn-rule",
            "Rule",
            Some(
                "production `Rule` of ORG-KRS-NAME-MAP has the K name \"rule\", which is a terminal K reads as a sentence keyword: K ends a sentence's text at a bare `rule`, so a rule or claim that applies the production would end there",
            ),
        ),
        ("fn-requires", "Requires", None),
    ];
    let cases = cases
        .into_iter()
        .chain(functions.map(|(directory, name, expected)| (directory, function(name), expected)));
    for (directory, source, expected) in cases {
        assert_eq!(
            check_headline(target.path(), temporary.path(), directory, &source),
            expected.map(|reason| format!("{collision}{reason}")),
            "{directory}"
        );
    }
}
