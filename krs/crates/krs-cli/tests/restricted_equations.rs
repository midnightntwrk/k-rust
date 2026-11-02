//! `concrete` and `symbolic` on a function's equations, on every route.
//!
//! A restriction says when an equation is used, not what it states: an equation restricted to
//! ground arguments still holds on symbolic ones, where it is only not applied. So no equation of
//! the function may apply where the restriction skips it: an equation ordered after a `concrete`
//! one must be bare `concrete` too, and none may be ordered after a `symbolic` one. A restriction
//! on some binders only, or on some equations only, is accepted, and the native and the K text
//! route compile it.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Go))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("go({value})")] Go { value: Int },
}

#[k::function(total, sort = Int, syntax = "h({value})")]
pub struct H {
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

#[k::rule(label = "go")]
fn go(k::term![ExpSyntax::Go { value }]: Term<Exp>) -> Term<Exp> {
    H(value)
}
"#;

/// `h`'s equations, each bare `concrete`, and a claim over a symbolic argument, which needs `h`
/// evaluated where it is not ground.
const CONCRETE: &str = r#"
#[k::equation(concrete)]
fn h_zero(k::term![H(0)]: Term<Int>) -> Term<Int> {
    1
}

#[k::equation(owise, concrete)]
fn h_other(k::term![H(x)]: Term<Int>) -> Term<Int> {
    int::add(x, 1)
}

#[k::claim(all_paths, label = "go-symbolic")]
#[k::requires(int::gt(i, 0))]
pub fn go_symbolic(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Go(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(int::add(i, 1), ..tail), ..state }
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A one-package workspace named `restricted` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"restricted\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-RESTRICTED\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .args(["--package", "restricted", "--definition", "main"])
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

/// The text route's KORE definition: the emitted `definition.k` compiled by k-rust's text
/// frontend, as `krust kcompile` compiles it, or the frontend's diagnostics.
fn text_route(definition: &str) -> Result<String, String> {
    use k_rust::builtin;
    use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
    use k_rust::outer::{LoadOptions, ResolvedSource, load_for_compilation};

    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("definition.k", definition.to_owned()),
        "ORG-KRS-RESTRICTED",
        Some("ORG-KRS-RESTRICTED-SYNTAX"),
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
    .map_err(|error| format!("the text route loads the definition: {error}"))?;
    compile_loaded_definition(&loaded, CompileOptions::default())
        .map(|compiled| compiled.definition_kore)
        .map_err(|error| {
            error
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.message.clone())
                .collect::<Vec<_>>()
                .join("\n")
        })
}

/// Bare `concrete` on every equation of `h`, the `owise` one after the other included: both
/// routes compile it and honour it. A ground `go(5)` runs to 6, the claim over a symbolic `I`
/// is not proved, since `h(I)` is left as it is, and the K text route compiles the emitted K,
/// whose `concrete` it reads, and the same K with a listed `concrete(X)` on one equation only.
#[test]
fn bare_concrete_on_every_equation_is_compiled_and_honoured_on_both_routes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), CONCRETE);
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, "go(5)").unwrap();
    let (_, stdout, stderr) = krs(target.path(), &manifest, "run", &[file.to_str().unwrap()]);
    assert!(
        stdout
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
            .contains("<k> 6 ~> .K </k>"),
        "{stdout}\n{stderr}"
    );
    let (proved, stdout, stderr) = krs(target.path(), &manifest, "prove", &[]);
    assert!(!proved, "{stdout}\n{stderr}");
    assert!(
        stdout.contains("ORG-KRS-RESTRICTED-SPEC.go-symbolic: failed"),
        "{stdout}\n{stderr}"
    );

    let emitted = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", emitted.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    assert_eq!(restriction_requirements(&emitted), Vec::<String>::new());
    let k = fs::read_to_string(emitted.join("definition.k")).unwrap();
    assert!(k.contains("[owise, concrete, label("), "{k}");
    text_route(&k).unwrap_or_else(|error| panic!("{error}\n{k}"));
    let listed = k.replacen("[owise, concrete, label(", "[owise, concrete(X), label(", 1);
    text_route(&listed).unwrap_or_else(|error| panic!("{error}\n{listed}"));
}

/// `h`'s one equation restricted to a ground `x` by `concrete(x)`: `krs check` accepts it, a
/// ground `go(5)` runs to 6, and the claim over a symbolic `I` is not proved, since `h(I)` is
/// left as it is; the K text route compiles the emitted `concrete(X)`.
#[test]
fn a_listed_restriction_is_compiled_and_honoured_on_both_routes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let listed = CONCRETE
        .replacen(
            "#[k::equation(concrete)]\nfn h_zero(k::term![H(0)]: Term<Int>) -> Term<Int> {\n    1\n}\n",
            "",
            1,
        )
        .replacen("#[k::equation(owise, concrete)]", "#[k::equation(concrete(x))]", 1);
    assert!(
        listed.contains("concrete(x)") && !listed.contains("h_zero"),
        "{listed}"
    );
    let manifest = package(temporary.path(), &listed);
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, "go(5)").unwrap();
    let (_, stdout, stderr) = krs(target.path(), &manifest, "run", &[file.to_str().unwrap()]);
    assert!(
        stdout
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
            .contains("<k> 6 ~> .K </k>"),
        "{stdout}\n{stderr}"
    );
    let (proved, stdout, stderr) = krs(target.path(), &manifest, "prove", &[]);
    assert!(!proved, "{stdout}\n{stderr}");
    assert!(
        stdout.contains("ORG-KRS-RESTRICTED-SPEC.go-symbolic: failed"),
        "{stdout}\n{stderr}"
    );
    let emitted = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", emitted.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    // The Java frontend's routes take a restriction on an equation only bare and on every
    // equation of its function: the requirement names the function, and those routes refuse it.
    assert_eq!(restriction_requirements(&emitted), ["h"]);
    let k = fs::read_to_string(emitted.join("definition.k")).unwrap();
    assert!(k.contains("[concrete(X"), "{k}");
    text_route(&k).unwrap_or_else(|error| panic!("{error}\n{k}"));
}

/// The symbols of the `PartialEquationRestriction` requirements `symbols.json` in `emitted`
/// records.
fn restriction_requirements(emitted: &Path) -> Vec<String> {
    let symbols: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(emitted.join("symbols.json")).unwrap()).unwrap();
    symbols["capability_requirements"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|row| row["feature"] == "PartialEquationRestriction")
        .map(|row| row["symbol"].as_str().unwrap().to_owned())
        .collect()
}

/// `krs check`'s first error.
fn first_error(source: &str) -> String {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), source);
    let (success, stdout, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(!success, "{stdout}\n{stderr}");
    stderr
        .lines()
        .find(|line| line.starts_with("error"))
        .unwrap_or_else(|| panic!("{stderr}"))
        .to_owned()
}

/// An equation ordered after a restricted one, which would apply where the restriction skips
/// it, is refused at the restriction: after a `symbolic` one, whatever its own restriction; after
/// a `concrete` one, unless it is bare `concrete` (the verification-surface fixture
/// `restriction-equation-inconsistent`).
#[test]
fn a_restriction_another_equation_would_contradict_is_refused() {
    let symbolic = r"
#[k::equation(symbolic)]
fn h_zero(k::term![H(x)]: Term<Int>) -> Term<Int> {
    int::add(x, 1)
}

#[k::equation(owise, symbolic)]
fn h_other(k::term![H(x)]: Term<Int>) -> Term<Int> {
    x
}
";
    assert_eq!(
        first_error(symbolic),
        "error[krs::analysis::invalid-match-restriction]: equation `h_zero` is `symbolic`, so it is skipped where a binder it restricts is ground, though it still holds there; equation `h_other`, ordered after it (`owise`), applies wherever `h_zero` does not, so there it would give the function a value `h_zero` need not agree with: give the equations one order, or make `h_zero` a #[k::simplification]"
    );
}
