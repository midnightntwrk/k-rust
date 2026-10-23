//! `KItem` and `KResult` are part of every definition: a definition that
//! never declares a sort below them still has head and `cells!` rules,
//! `k::KItem` fields and binders, `k::is!(k::KResult, ..)`, strictness
//! results, and bare-collection elements typed `KItem`. Its K contains the
//! `KRS-FRAMEWORK` module only when the definition uses it.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const LIGHT: &str = r#"
use k::builtin::KSequence;

k::sorts! {
    Light;
}

#[k::constructors(sort = Light, result = KResult)]
#[k::precedence((Red, Green, Yellow))]
pub enum LightSyntax {
    #[k::syntax("red")]
    Red(),
    #[k::syntax("green")]
    Green(),
    #[k::syntax("yellow")]
    Yellow(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Light) -> Self {
        Self { k: k::k![pgm] }
    }
}
"#;

/// A table rule and a `cells!` rule, neither naming a framework sort.
const PLAIN_RULES: &str = r"
k::rules! {
    for Light;
    use LightSyntax::*;
    red_to_green: Red() => Green();
}

#[k::rule]
pub fn yellow_to_red(
    k::cells! { k: k::configuration::KCell(LightSyntax::Yellow(), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(LightSyntax::Red(), ..tail), ..state }
}
";

/// A rule whose only framework use is a variable inferred at `KItem`.
const ITEM_RULE: &str = r"
k::rules! {
    for Machine;
    use LightSyntax::*;
    drop_any: { k: [Yellow(), x, ..] } => { k: [..] };
}
";

/// Every place a declaration or a sentence names a framework sort, with no
/// sort declared below one.
const USES: &str = r#"
use k::Term;
use k::builtin::{Bool, Int, KSequence, List};

k::sorts! {
    Light;
    Exp;
    impl Exp for Int;
}

#[k::constructors(sort = Light, result = KResult)]
#[k::precedence((Red, Green, Hold, Peek))]
pub enum LightSyntax {
    #[k::syntax("red")]
    Red(),
    #[k::syntax("green")]
    Green(),
    #[k::syntax("hold ( {saved} )")]
    Hold { saved: k::KItem },
    #[k::syntax("peek ( {l} )")]
    Peek { l: List },
}

#[k::constructor(sort = Exp, syntax = "{lhs} + {rhs}")]
#[k::seqstrict(sequence = [lhs, rhs], result = k::KResult)]
pub struct Add {
    pub lhs: Term<dyn ExpSort>,
    pub rhs: Term<dyn ExpSort>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Light) -> Self {
        Self { k: k::k![pgm] }
    }
}

#[k::function(total, internal)]
pub fn Done(e: Term<Exp>) -> Term<Bool>;

#[k::equation]
fn done(k::term![Done(e)]: Term<Bool>) -> Term<Bool> {
    k::is!(k::KResult, e)
}

#[k::rule(owise)]
fn unhold(l: Term<k::KItem>, k::term![LightSyntax::Hold(l)]: Term<Light>) -> Term<Light> {
    LightSyntax::Green()
}

#[k::rule]
fn peek(k::term![LightSyntax::Peek([_x, ..])]: Term<Light>) -> Term<Light> {
    LightSyntax::Red()
}

k::rules! {
    for Light;
    use LightSyntax::*;
    hold_red: Hold { saved: Red() } => Red();
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is `source`.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-SORT-USE\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// Checks the package on every route and returns its `definition.k`.
fn checked_definition(target: &Path, manifest: &Path) -> String {
    let (success, _, stderr) = krs(target, manifest, "check", &["--backend", "haskell"]);
    assert!(success, "{stderr}");
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

/// The simplest rules compile without any sort declared below `KItem`, and a
/// definition that names no framework sort emits no framework module; a
/// program runs through both rules.
#[test]
fn a_definition_that_names_no_framework_sort_has_rules_and_no_framework_module() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "plain", &format!("{LIGHT}{PLAIN_RULES}"));
    let definition = checked_definition(target.path(), &manifest);
    assert!(!definition.contains("KRS-FRAMEWORK"), "{definition}");
    assert!(
        definition.contains("<k> red => green ... </k>"),
        "{definition}"
    );
    assert!(
        definition.contains("<k> yellow ~> Tail:K => red ~> Tail:K </k>"),
        "{definition}"
    );

    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "yellow").unwrap();
    let (_, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[program.to_str().unwrap()],
    );
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("<k> green ~> .K </k>"), "{stdout}\n{stderr}");
}

/// A rule variable inferred at `KItem` uses the framework without any
/// declaration importing it: the module is emitted, imported by nothing.
#[test]
fn a_rule_variable_at_k_item_keeps_the_framework_module() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "item-rule",
        &format!("{LIGHT}{ITEM_RULE}"),
    );
    let definition = checked_definition(target.path(), &manifest);
    assert!(
        definition.starts_with("module KRS-FRAMEWORK\n"),
        "{definition}"
    );
    assert!(
        !definition.contains("imports KRS-FRAMEWORK"),
        "{definition}"
    );
    assert!(
        definition.contains("<k> yellow ~> X:KItem => .K ... </k>"),
        "{definition}"
    );
}

/// `k::KItem` and `k::KResult` resolve wherever rustc resolves them, and a
/// module whose declarations name one imports the framework module.
#[test]
fn framework_sorts_resolve_without_a_declaration_below_them() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "uses", USES);
    let definition = checked_definition(target.path(), &manifest);
    for line in [
        "syntax Light ::= \"hold\" \"(\" KItem \")\"",
        "syntax Exp ::= Exp \"+\" Exp [symbol(add), seqstrict, result(KResult)]",
        "rule done ( E:Exp ) => isKResult(E:Exp)",
        "rule hold ( L:KItem ) => green",
        "rule peek ( ListItem(_X:KItem) _ ) => red",
        "<k> hold ( red ) => red ... </k>",
    ] {
        assert!(definition.contains(line), "{line}:\n{definition}");
    }
    let imports = definition
        .lines()
        .filter(|line| line.trim() == "imports KRS-FRAMEWORK")
        .count();
    assert_eq!(imports, 2, "{definition}");
}
