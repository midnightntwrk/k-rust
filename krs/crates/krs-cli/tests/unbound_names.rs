//! A bare snake-case name outside a pattern is a use of a binder (KRS's
//! spelling rule: binders are snake case, Rust items are not), so one that
//! nothing binds is `krs::expand::unbound-name` at the name, with the closest
//! name in scope as a suggestion, in every readable form, guard, equation,
//! rule fn body, and initializer term. A `PascalCase` name is a constructor
//! reference, which rustc resolves, as before.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"use k::KResult;
use k::builtin::{Int, KSequence, int};
use k::Term;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Skip, Tick, Tock, Wrap))]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("tick")]
    Tick(),
    #[k::syntax("tock")]
    Tock,
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
    pub fn init(pgm: Stmt, acc: Int) -> Self {
        Self { k: k::k![pgm], acc }
    }
}

#[k::function(total, internal)]
pub fn PickF(b: Term<Int>) -> Term<Int>;
"#;

/// One unbound name per sentence form, each in its own item.
const UNBOUND: &str = r"
k::rules! {
    for Machine;
    use StmtSyntax::*;
    result_cell: { k: [Skip(), ..], acc: _ } => { k: [..], acc: zz };
}

k::rules! {
    for Machine;
    use StmtSyntax::*;
    item: { k: [Tick(), ..], acc: value } => { k: [valeu, ..] };
}

k::rules! {
    for Machine;
    use StmtSyntax::*;
    #[k::requires(vv == zz)]
    guard: { k: [Skip(), Skip(), ..], acc: vv } => { k: [..] };
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;
    row: Wrap { s: Tick() } => Wrap { s: zz };
}

k::claims! {
    for Machine;
    use StmtSyntax::*;
    #[k::claim(all_paths)]
    claim: { k: [Skip()] } => { k: [zz] };
}

k::equations! {
    for PickF;
    table: (b) => bb;
}

#[k::equation]
fn body(k::term![PickF(b)]: Term<Int>) -> Term<Int> {
    bb
}

#[k::rule]
fn subject(k::term![StmtSyntax::Wrap { s }]: Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::Wrap { s: ss }
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is `library`.
fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-UNBOUND\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// `krs check`'s errors: each headline with the authored text its `-->`
/// location points at.
fn errors(target: &Path, manifest: &Path) -> Vec<String> {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    let source = fs::read_to_string(manifest.with_file_name("src/lib.rs")).unwrap();
    let lines = source.lines().collect::<Vec<_>>();
    let mut errors = Vec::new();
    let mut stderr_lines = stderr.lines();
    while let Some(line) = stderr_lines.next() {
        if !line.starts_with("error[") {
            continue;
        }
        let location = stderr_lines
            .next()
            .and_then(|next| next.trim_start().strip_prefix("--> "))
            .and_then(|path| path.split_once("src/lib.rs:"))
            .map(|(_, location)| location.split(':').collect::<Vec<_>>());
        let at = location.map_or_else(
            || "unlocated".to_owned(),
            |location| {
                let line: usize = location[0].parse().unwrap();
                let column: usize = location[1].parse().unwrap();
                let text = &lines[line - 1][column - 1..];
                let end = text
                    .find(|character: char| !(character.is_alphanumeric() || character == '_'))
                    .unwrap_or(text.len());
                format!("at `{}`", &text[..end])
            },
        );
        errors.push(format!("{line} {at}"));
    }
    errors
}

/// Every form that builds terms against a sentence's bindings reports an
/// unbound snake-case name at the name, suggesting a near name in scope.
#[test]
fn an_unbound_snake_case_name_is_a_krs_error_at_the_name() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "unbound", &format!("{PREAMBLE}{UNBOUND}"));
    expect_test::expect![[r#"
        [
            "error[krs::expand::unbound-name]: `zz` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one at `zz`",
            "error[krs::expand::unbound-name]: `valeu` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one; did you mean `value`? at `valeu`",
            "error[krs::expand::unbound-name]: `zz` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one at `zz`",
            "error[krs::expand::unbound-name]: `zz` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one at `zz`",
            "error[krs::expand::unbound-name]: `zz` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one at `zz`",
            "error[krs::expand::unbound-name]: `bb` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one; did you mean `b`? at `bb`",
            "error[krs::expand::unbound-name]: `bb` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one; did you mean `b`? at `bb`",
            "error[krs::expand::unbound-name]: `ss` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one; did you mean `s`? at `ss`",
        ]
    "#]]
    .assert_debug_eq(&errors(target.path(), &manifest));
}

/// A `PascalCase` name stays a constructor reference that rustc resolves,
/// with rustc's suggestion for a near variant, a bare unit variant still
/// emits its constructor, a `let` binder is in scope in its block, and a
/// `cells!` rule fn, whose binders are Rust parameters, stays rustc's.
#[test]
fn constructor_names_stay_with_rustc() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let unresolved = package(
        temporary.path(),
        "unresolved",
        &format!(
            r"{PREAMBLE}
k::rules! {{
    for Machine;
    use StmtSyntax::*;
    missing: {{ k: [Tick(), Tick(), ..] }} => {{ k: [Zz, ..] }};
}}

k::rules! {{
    for Machine;
    use StmtSyntax::*;
    misspelled: {{ k: [Tick(), Skip(), ..] }} => {{ k: [Tik(), ..] }};
}}

#[k::rule]
fn cells_rule(k::cells! {{ k: k::configuration::KCell(StmtSyntax::Skip(), tail @ ..), state @ .. }}: Machine) -> Machine {{
    k::cells! {{ k: k::configuration::KCell(zz, ..tail), ..state }}
}}
"
        ),
    );
    expect_test::expect![[r#"
        [
            "error[E0422]: cannot find struct, variant or union type `Zz` in this scope at `Zz`",
            "error[E0422]: cannot find struct, variant or union type `Tik` in this scope at `Tik`",
            "error[E0425]: cannot find type `zz` in this scope at `zz`",
        ]
    "#]]
    .assert_debug_eq(&errors(target.path(), &unresolved));
    let (_, _, stderr) = krs(target.path(), &unresolved, "check", &[]);
    assert!(
        stderr.contains("replace `Tik` with `Tick`"),
        "rustc's suggestion for a near variant stays:\n{stderr}"
    );
    let unit = package(
        temporary.path(),
        "unit",
        &format!(
            r"{PREAMBLE}
k::rules! {{
    for Machine;
    use StmtSyntax::*;
    tock: {{ k: [Skip(), Tick(), ..] }} => {{ k: [Tock, ..] }};
}}

k::rules! {{
    for Stmt;
    use StmtSyntax::*;
    unwrap: Wrap {{ s }} => Wrap {{ s: {{ let Wrap {{ s: inner }} = s; inner }} }};
}}
"
        ),
    );
    let (success, stdout, stderr) = krs(target.path(), &unit, "check", &[]);
    assert!(success, "{stdout}\n{stderr}");
}

/// An initializer's bare snake-case names are its parameters: a typo in a
/// `k!` item or a cell value is reported at the name.
#[test]
fn an_initializer_typo_is_a_krs_error_at_the_name() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let typo = |name: &str, initializer: &str| {
        let library = PREAMBLE.replace("Self { k: k::k![pgm], acc }", initializer);
        assert_ne!(library, PREAMBLE);
        errors(target.path(), &package(temporary.path(), name, &library))
    };
    let mut found = typo("item-typo", "Self { k: k::k![pgmm], acc }");
    found.extend(typo("cell-typo", "Self { k: k::k![pgm], acc: accc }"));
    expect_test::expect![[r#"
        [
            "error[krs::expand::unbound-name]: `pgmm` is not a parameter of this initializer: a bare snake-case name in an initializer term is one of its parameters; did you mean `pgm`? at `pgmm`",
            "error[krs::expand::unbound-name]: `accc` is not a parameter of this initializer: a bare snake-case name in an initializer term is one of its parameters; did you mean `acc`? at `accc`",
        ]
    "#]]
    .assert_debug_eq(&found);
}
