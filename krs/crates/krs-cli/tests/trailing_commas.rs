//! A trailing comma adds no element, so an authored package emits the same K
//! with and without one in every list, macro, and attribute argument list.
//! Each package is emitted twice, as authored and with trailing commas added,
//! under the same package name, and both `definition.k` and `spec.k` must be
//! byte-identical; `krs emit-k` compiles each package with rustc first, so
//! both the macros and the collector read every comma.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A package with a function shorthand, a readable claim, and its reference
/// fn; `$C` marks each place a trailing comma goes.
const CLAIMS: &str = r#"use k::builtin::{Bytes, Int, KSequence, bytes, int};
use k::{KResult, Term};

k::sorts! {
    Exp: k::KItem;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum Op {
    #[k::syntax("load")]
    Load(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub program: Bytes,
    #[k::cell]
    pub pc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm$C], program: bytes::empty(), pc: 0 }
    }
}

#[k::function(total, internal)]
pub fn Clamp(value: Term<Int>) -> Term<Int> {
    match value {
        0 => 0,
        #[k::label(clamp_rest$C)]
        _ => 1,
    }
}

k::rules! {
    for Machine;
    use Op::*;

    load: { k: [Load(), ..], program: p, pc: n } => { k: [..], pc: bytes::length(p) };
}

k::claims! {
    for Machine;
    use Op::*;

    #[k::claim(all_paths)]
    #[k::exists(left: Int)]
    #[k::ensures(int::eq(left, 2)$C)]
    loads: {
        k: [Load()],
        program: k::bytes!(b"\x60\x00"$C),
        pc: k::anonymous!(Int, "_Pc"$C),
    } => {
        k: [],
        program: k::bytes!(b"\x60\x00"$C),
        pc: left,
    };
}

#[k::claim(all_paths, label = "loads-reference")]
fn loads_reference(
    k::cells! {
        k: k::configuration::KCell(Op::Load()$C),
        program: k::configuration::Cell(k::bytes!(b"\x60\x00"$C)$C),
        pc: k::configuration::Cell(k::anonymous!(Int, "_Pc"$C)),
        state @ ..$C
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K$C),
        pc: k::configuration::Cell(2),
        ..state$C
    }
}
"#;

/// A package of a feature gate: its path under `tests/`, its K namespace,
/// and the trailing commas to add, as `(from, to)`.
type Package = (
    &'static str,
    &'static str,
    &'static [(&'static str, &'static str)],
);

/// Packages of the feature gates, each with the trailing commas to add:
/// every `from` must occur, and every occurrence becomes `to`.
const PACKAGES: &[Package] = &[
    (
        "rule-forms/packages/macros",
        "KRS-MACROS",
        &[
            ("impl Value for Int, Bool;", "impl Value for Int, Bool,;"),
            ("#[k::alias(recursive)]", "#[k::alias(recursive,)]"),
            ("#[k::desugar(recursive)]", "#[k::desugar(recursive,)]"),
            (
                "#[k::desugar(unbound_variables = [n, rest])]",
                "#[k::desugar(unbound_variables = [n, rest],)]",
            ),
            (
                "k::term![Sugar::Unless(c, s)]",
                "k::term![Sugar::Unless(c, s),]",
            ),
        ],
    ),
    (
        "builtin-domains/packages/sort-tests",
        "KRS-SORT-TESTS-FIXTURE",
        &[
            ("k::is!(Int, e)", "k::is!(Int, e,)"),
            (
                "#[k::requires(bool::or(k::is!(Int, x), k::is!(Bool, x)))]",
                "#[k::requires(bool::or(k::is!(Int, x,), k::is!(Bool, x)),)]",
            ),
            ("k::project!(Int, e)", "k::project!(Int, e,)"),
        ],
    ),
    (
        "configuration-cells/packages/threads",
        "KRS-THREADS",
        &[
            (r#"#[k::bracket("(", ")")]"#, r#"#[k::bracket("(", ")",)]"#),
            ("k: k::k![pgm],", "k: k::k![pgm,],"),
            ("where a: Int, b: Int;", "where a: Int, b: Int,;"),
            ("=> k::k![s1, s2];", "=> k::k![s1, s2,];"),
            ("tail0 @ ..]", "tail0 @ ..,]"),
            (
                "k::k![crate::StmtSyntax::Return(i), ..], .. }]",
                "k::k![crate::StmtSyntax::Return(i), ..,], .. },]",
            ),
            ("instances0 @ ..\n", "instances0 @ ..,\n"),
            ("state @ ..\n", "state @ ..,\n"),
            ("k::k![i, ..tail0]", "k::k![i, ..tail0,]"),
            ("..instances0 }", "..instances0, }"),
            ("..state\n", "..state,\n"),
        ],
    ),
    (
        "rule-forms/packages/local-rewrite",
        "KRS-LOCAL-REWRITE",
        &[
            (
                r#"#[k::format("{first}%n{second}")]"#,
                r#"#[k::format("{first}%n{second}",)]"#,
            ),
            ("k::rewrite!(name => value)", "k::rewrite!(name => value,)"),
            (
                "k::rewrite!(_ => value), ..]",
                "k::rewrite!(_ => value), ..,]",
            ),
        ],
    ),
    (
        "grammar-lexing/packages/tokens",
        "KRS-TOKENS",
        &[(r#"k::lexeme!(Name, "foo")"#, r#"k::lexeme!(Name, "foo",)"#)],
    ),
    (
        "patterns-functions/packages/matches",
        "KRS-MATCHES",
        &[
            (
                "k::matches!(e, ExpSyntax::Pair(x, x))",
                "k::matches!(e, ExpSyntax::Pair(x, x),)",
            ),
            (
                "#[k::requires(k::matches!(e, Pair(_, _)))]",
                "#[k::requires(k::matches!(e, Pair(_, _),),)]",
            ),
        ],
    ),
    (
        "grammar-lexing/packages/symbols",
        "KRS-SYMBOLS",
        &[(
            r#"#[k::symbol("symbols::Plus")]"#,
            r#"#[k::symbol("symbols::Plus",)]"#,
        )],
    ),
];

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace named `name` under `root`.
fn package(root: &Path, name: &str, namespace: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs emit-k` and returns `definition.k` and `spec.k`.
fn emit(target: &Path, manifest: &Path, name: &str) -> (String, String) {
    let output = manifest.with_file_name("emitted");
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let result = process
        .args(["emit-k", "--manifest-path"])
        .arg(manifest)
        .args(["--package", name, "--definition", "main", "--output"])
        .arg(&output)
        .env("NO_COLOR", "1")
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{name}: {}",
        String::from_utf8_lossy(&result.stderr)
    );
    let read = |file: &str| fs::read_to_string(output.join(file)).unwrap_or_default();
    (read("definition.k"), read("spec.k"))
}

fn assert_same_k(
    target: &Path,
    root: &Path,
    name: &str,
    namespace: &str,
    plain: &str,
    commas: &str,
) {
    assert_ne!(plain, commas, "{name}: no comma was added");
    let plain = emit(
        target,
        &package(&root.join("plain"), name, namespace, plain),
        name,
    );
    let commas = emit(
        target,
        &package(&root.join("commas"), name, namespace, commas),
        name,
    );
    assert!(!plain.0.is_empty(), "{name}: no definition.k");
    assert_eq!(plain.0, commas.0, "{name}: definition.k differs");
    assert_eq!(plain.1, commas.1, "{name}: spec.k differs");
}

#[test]
fn trailing_commas_leave_the_emitted_k_unchanged() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    assert_same_k(
        target.path(),
        temporary.path(),
        "commas_claims",
        "KRS-COMMAS",
        &CLAIMS.replace("$C", ""),
        &CLAIMS.replace("$C", ","),
    );
    let tests = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    for (path, namespace, replacements) in PACKAGES {
        let plain = fs::read_to_string(tests.join(path).join("src/lib.rs")).unwrap();
        let mut commas = plain.clone();
        for (from, to) in *replacements {
            assert!(commas.contains(from), "{path}: `{from}` does not occur");
            commas = commas.replace(from, to);
        }
        let name = format!(
            "commas_{}",
            path.rsplit('/').next().unwrap().replace('-', "_")
        );
        assert_same_k(
            target.path(),
            temporary.path(),
            &name,
            namespace,
            &plain,
            &commas,
        );
    }
}
