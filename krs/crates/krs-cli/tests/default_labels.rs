//! The default label of an unlabelled term or predicate rule spells its item's path,
//! `<namespace>--<module>--…--<item>`, and both routes give every sentence the same label.
//!
//! K qualifies a label by its module exactly when the sentence names it in brackets
//! (`rule [x]:`, `claim [x]:`, `context [x]:`) and keeps a `label(x)` attribute as written, so
//! the native route, which builds the sentences without K's text frontend, must follow the form
//! the emitted K writes. A default label that would coincide with another label is refused,
//! naming both owners, never renamed; and a label holds no source position, so an edit that only
//! moves Rust lines leaves the emitted K unchanged.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const NAMESPACE: &str = "ORG-KRS-LABELS";

const PREAMBLE: &str = r#"use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("go({value})")] Go { value: Int },
    #[k::syntax("halt")] Halt(),
    #[k::syntax("halted")] Halted(),
}

#[k::function(total, sort = Int, syntax = "h({value})")]
pub struct H {
    pub value: Term<Int>,
}

#[k::function(total, sort = Int, syntax = "g({value})")]
pub struct G {
    pub value: Term<Int>,
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

/// A term rule with an authored label.
#[k::rule(label = "go")]
fn go(k::term![ExpSyntax::Go { value }]: Term<Exp>) -> Term<Exp> {
    H(G(value))
}

/// A configuration rule, whose default label is its name with `_` written `-`.
k::rules! {
    for Exp;
    use ExpSyntax::*;

    halt: Halt() => Halted();
}

pub mod helpers {
    use super::G;
    use k::Term;
    use k::builtin::Int;

    /// An equation in a module: its default label holds the module.
    #[k::equation]
    fn g_any(k::term![G(x)]: Term<Int>) -> Term<Int> {
        x
    }
}
"#;

/// `h`'s equations: one with a default label, one with an authored label.
const EQUATIONS: &str = r#"
#[k::equation]
fn h_zero(k::term![H(0)]: Term<Int>) -> Term<Int> {
    1
}

#[k::equation(owise, label = "h-other")]
fn h_other(k::term![H(x)]: Term<Int>) -> Term<Int> {
    int::add(x, 1)
}
"#;

/// An authored label that spells another item's default label.
const COINCIDENT: &str = r#"
#[k::equation(label = "org_krs_labels--h_other")]
fn h_zero(k::term![H(0)]: Term<Int>) -> Term<Int> {
    1
}

#[k::equation(owise)]
fn h_other(k::term![H(x)]: Term<Int>) -> Term<Int> {
    int::add(x, 1)
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A one-package workspace named `labels` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"labels\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"{NAMESPACE}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    manifest
}

/// Runs `krs <command>` on the package's `main` definition: whether it passed, its stdout and
/// its stderr.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", "labels", "--definition", "main"])
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

/// `krs emit-k` into `directory`, and the emitted `definition.k`.
fn emit_k(target: &Path, manifest: &Path, directory: &str) -> String {
    let output = manifest.with_file_name(directory);
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.k")).unwrap()
}

/// The text route's KORE definition: the emitted `definition.k` compiled by k-rust's text
/// frontend, as `krust kcompile` compiles it.
fn text_route(definition: &str) -> String {
    use k_rust::builtin;
    use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
    use k_rust::outer::{LoadOptions, ResolvedSource, load_for_compilation};

    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    let syntax = format!("{NAMESPACE}-SYNTAX");
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("definition.k", definition.to_owned()),
        NAMESPACE,
        Some(syntax.as_str()),
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![builtin::embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust
                    .excluded_module_attribute()
                    .to_owned(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("the text route loads the definition: {error}\n{definition}"));
    compile_loaded_definition(&loaded, CompileOptions::default()).map_or_else(
        |error| {
            panic!(
                "the text route compiles the definition: {}\n{definition}",
                error
                    .diagnostics
                    .iter()
                    .map(|diagnostic| diagnostic.message.clone())
                    .collect::<Vec<_>>()
                    .join("\n")
            )
        },
        |compiled| compiled.definition_kore,
    )
}

/// The `label{}("..")` attribute values of a KORE definition that belong to the package: its
/// default labels, its qualified labels, and the authored `labels`.
fn package_labels(kore: &str, authored: &[&str]) -> BTreeSet<String> {
    let lowered = NAMESPACE.to_ascii_lowercase().replace('-', "_");
    kore.split("label{}(\"")
        .skip(1)
        .filter_map(|rest| rest.split('"').next())
        .filter(|label| {
            label.starts_with(&format!("{lowered}--"))
                || label.starts_with(&format!("{NAMESPACE}."))
                || authored.contains(label)
        })
        .map(str::to_owned)
        .collect()
}

/// Every unlabelled equation's label spells its item path, in the `label(..)` attribute; a
/// configuration rule keeps its bracketed name. The native route (`krs build`) and K's text
/// frontend over the emitted K give each of the package's sentences the same label, the
/// authored `go` and `h-other` included, which K leaves bare because they are attributes.
#[test]
fn default_labels_spell_the_item_path_and_both_routes_agree_on_every_label() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), EQUATIONS);
    let k = emit_k(target.path(), &manifest, "emitted");
    for written in [
        "[label(org_krs_labels--h_zero)]",
        "[label(org_krs_labels--helpers--g_any)]",
        "[owise, label(h-other)]",
        "[label(go)]",
        "rule [halt]:",
    ] {
        assert!(k.contains(written), "{written} is not in\n{k}");
    }
    assert!(!k.contains("krsRule_"), "{k}");

    let built = manifest.with_file_name("built");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "build",
        &["--output", built.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let native = fs::read_to_string(built.join("definition.kore")).unwrap();
    let text = text_route(&k);
    let authored = ["go", "h-other"];
    let expected = [
        "ORG-KRS-LABELS.halt",
        "go",
        "h-other",
        "org_krs_labels--h_zero",
        "org_krs_labels--helpers--g_any",
    ]
    .map(str::to_owned)
    .into_iter()
    .collect::<BTreeSet<_>>();
    assert_eq!(package_labels(&text, &authored), expected, "text route");
    assert_eq!(package_labels(&native, &authored), expected, "native route");
}

/// An authored label that spells another item's default label is refused with both owners
/// named, never renamed.
#[test]
fn a_default_label_that_meets_an_authored_label_is_refused_naming_both() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), COINCIDENT);
    let output = manifest.with_file_name("emitted");
    let (success, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(!success, "{stdout}\n{stderr}");
    assert!(
        stderr.contains("emitted label name collision for \"org_krs_labels--h_other\""),
        "{stderr}"
    );
    for owner in ["h_zero", "h_other", "the first owner of the name"] {
        assert!(stderr.contains(owner), "{owner} is not named in\n{stderr}");
    }
    assert!(!output.join("definition.k").exists());
}

/// A label holds no source position: blank lines inserted at the top of the Rust file, which
/// move every item, leave `definition.k` byte-identical.
#[test]
fn moving_rust_lines_leaves_the_emitted_definition_byte_identical() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), EQUATIONS);
    let before = emit_k(target.path(), &manifest, "before");
    let library = manifest.with_file_name("src").join("lib.rs");
    let source = fs::read_to_string(&library).unwrap();
    fs::write(&library, format!("\n\n\n{source}")).unwrap();
    let after = emit_k(target.path(), &manifest, "after");
    assert_eq!(before, after);
}
