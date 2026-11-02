//! `krs expand` of a package whose readable forms are spread over several module files and
//! modules: each changed module file printed at its own path (`--output`), the printed package
//! checked, and its emitted K compared with the authored package's.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes the package `name` under `root`: its manifest, with `dependencies` as extra
/// `[dependencies]` lines and `workspace` as its own `[workspace]` table where set, and each of
/// `files` at its package-relative path. Returns the manifest.
fn write_package(
    root: &Path,
    name: &str,
    dependencies: &str,
    workspace: bool,
    files: &[(&str, &str)],
) -> PathBuf {
    let directory = root.join(name);
    for (path, text) in files {
        let path = directory.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    let workspace = if workspace {
        "\n[workspace]\nresolver = \"3\"\n"
    } else {
        ""
    };
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"WHOLE-{}\"\n\n[package.metadata.krs.definitions.main]\n{workspace}",
            krs_path(),
            name.to_ascii_uppercase()
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on `package`'s `main` definition.
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

/// Copies every file under `from` into `to`, keeping relative paths.
fn copy_tree(from: &Path, to: &Path) {
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let destination = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            fs::create_dir_all(&destination).unwrap();
            copy_tree(&entry.path(), &destination);
        } else {
            fs::copy(entry.path(), destination).unwrap();
        }
    }
}

/// The emitted `definition.k`, each `<k>` rewrite written with an explicit continuation
/// `A ~> T:K => B ~> T:K` read as `A => B ...`: a printed `cells!` rule names the continuation
/// its readable clause leaves implicit, and the two rules are the same rewrite.
fn emitted_definition(target: &Path, manifest: &Path, package: &str, extra: &[&str]) -> String {
    let output = manifest.with_file_name("emitted");
    let mut arguments = extra.to_vec();
    arguments.extend(["--output", output.to_str().unwrap()]);
    let (success, _, stderr) = krs(target, manifest, package, "emit-k", &arguments);
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.k"))
        .unwrap()
        .lines()
        .map(|line| {
            let words = line.split_whitespace().collect::<Vec<_>>();
            let tails = words
                .windows(3)
                .enumerate()
                .filter(|(_, window)| window[0] == "~>" && window[1].ends_with(":K"))
                .map(|(at, window)| (at, window[1], window[2]))
                .collect::<Vec<_>>();
            match tails.as_slice() {
                [(left, tail, "=>"), (right, other, "</k>")] if tail == other => {
                    let mut kept = words[..*left].to_vec();
                    kept.extend(&words[left + 2..*right]);
                    kept.extend(["...", "</k>"]);
                    kept.extend(&words[right + 3..]);
                    kept.join(" ")
                }
                _ => words.join(" "),
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// `krs expand --output` of `package` in `workspace`, the files it lists overlaid on a copy of
/// the workspace: the listed paths, the printed files by path, and the copy's manifest of
/// `package`. The copy must check, and emit the K the authored package emits.
fn round_trip(
    target: &Path,
    workspace: &Path,
    package: &str,
    extra: &[&str],
) -> (Vec<String>, Vec<(String, String)>, PathBuf) {
    let manifest = workspace.join(package).join("Cargo.toml");
    let output = workspace.with_file_name(format!("{package}-printed"));
    let mut arguments = extra.to_vec();
    arguments.extend(["--output", output.to_str().unwrap()]);
    let (success, listed, stderr) = krs(target, &manifest, package, "expand", &arguments);
    assert!(success, "{stderr}");
    let listed = listed.lines().map(str::to_owned).collect::<Vec<_>>();
    let copy = workspace.with_file_name(format!("{package}-copy"));
    fs::create_dir_all(&copy).unwrap();
    copy_tree(workspace, &copy);
    let printed = listed
        .iter()
        .map(|path| {
            let text = fs::read_to_string(output.join(path)).unwrap();
            fs::write(copy.join(package).join(path), &text).unwrap();
            (path.clone(), text)
        })
        .collect::<Vec<_>>();
    let copied = copy.join(package).join("Cargo.toml");
    let (success, _, stderr) = krs(target, &copied, package, "check", extra);
    let shown = printed
        .iter()
        .map(|(path, text)| format!("== {path}\n{text}"))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(success, "{shown}\n{stderr}");
    assert_eq!(
        emitted_definition(target, &copied, package, extra),
        emitted_definition(target, &manifest, package, extra),
        "{shown}"
    );
    (listed, printed, copied)
}

/// `text` without whitespace, since prettyplease breaks long lines anywhere.
fn collapsed(text: &str) -> String {
    text.split_whitespace().collect()
}

fn printed_file<'a>(printed: &'a [(String, String)], path: &str) -> &'a str {
    printed
        .iter()
        .find(|(listed, _)| listed == path)
        .map_or_else(|| panic!("{path} was not printed"), |(_, text)| text)
}

const DEPENDENCY: &str = r#"
pub mod sorts {
    use k::{KItem, KItemSort, Term};

    #[k::sort(alias = Common, parents = [KItem])]
    pub trait CommonSort: KItemSort {}
    pub type Common = Term<dyn CommonSort>;

    #[k::constructor(sort = Common, syntax = "same")]
    pub struct Same;
}
"#;

const ROOT: &str = r#"
//! A package whose readable forms are spread over module files and an inline module.

// The only path any file of the crate writes through the dependency's module `sorts`; the
// rule in `rules.rs` that needs that module's path writes none.
pub use semantic_dep::sorts;

pub mod ops;
pub mod rules;
pub mod syntax;
#[path = "cells/machine.rs"]
pub mod machine;
// Configured out: the file does not exist, and the module denotes nothing.
#[cfg(any())]
mod configured_out;

pub use syntax::ExpSyntax;

mod inline {
    k::rules! {
        for crate::syntax::Exp;
        use crate::ExpSyntax::*;

        unwrap: Wrap(v) => v;
    }
}
"#;

const OPS: &str = r#"
k::sorts! {
    Op;
}

#[k::constructors(sort = Op, result = k::KResult)]
pub enum OpSyntax {
    #[k::syntax("plus")]
    Plus(),
    #[k::syntax("minus")]
    Minus(),
}
"#;

const SYNTAX: &str = r#"
use k::KResult;
use k::builtin::Int;

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("wrap({value})")]
    Wrap { value: Exp },
    #[k::syntax("apply({op}, {lhs}, {rhs})")]
    #[k::strict]
    Apply { op: crate::ops::Op, lhs: Exp, rhs: Exp },
    #[k::syntax("hold({held})")]
    Hold { held: crate::sorts::Common },
}
"#;

const MACHINE: &str = r"
use k::builtin::KSequence;

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: crate::syntax::Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}
";

const RULES: &str = r"
use crate::machine::Machine;

pub mod arithmetic;

k::rules! {
    for Machine;
    use crate::syntax::ExpSyntax::*;

    unhold: { k: [Hold(held), ..] } => { k: [held, ..] };
}
";

const ARITHMETIC: &str = r"
use k::builtin::{Int, int};

k::rules! {
    for crate::syntax::Exp;
    use crate::ExpSyntax::*;
    use crate::ops::OpSyntax::*;

    plus : Apply(Plus(), lhs, rhs)  => int::add(lhs, rhs) where lhs: Int, rhs: Int;
    minus: Apply(Minus(), lhs, rhs) => int::sub(lhs, rhs) where lhs: Int, rhs: Int;
}
";

/// Rules in several module files (one under a `#[path]`, one a child of a module file) and an
/// inline module; a sort declared in one module and used as a field in another; references
/// through a block `use`, a re-export and a dependency crate; and a configured-out `mod`. Each
/// changed file is printed at its path, the printed package checks and emits the same K, and
/// expanding the printed package changes nothing.
#[test]
fn a_package_of_several_module_files_round_trips_through_its_printed_files() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let workspace = temporary.path().join("workspace");
    write_package(&workspace, "dep", "", false, &[("src/lib.rs", DEPENDENCY)]);
    let manifest = write_package(
        &workspace,
        "whole",
        "semantic_dep = { package = \"dep\", path = \"../dep\" }\n",
        false,
        &[
            ("src/lib.rs", ROOT),
            ("src/ops.rs", OPS),
            ("src/syntax.rs", SYNTAX),
            ("src/cells/machine.rs", MACHINE),
            ("src/rules.rs", RULES),
            ("src/rules/arithmetic.rs", ARITHMETIC),
        ],
    );
    fs::write(
        workspace.join("Cargo.toml"),
        "[workspace]\nmembers = [\"dep\", \"whole\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    let dependency = ["--dependency", "dep:main"];
    // stdout holds one file, and the expansion changes six.
    let (success, _, stderr) = krs(target.path(), &manifest, "whole", "expand", &dependency);
    assert!(!success);
    assert!(
        stderr.contains("krs expand changes 6 module files (src/cells/machine.rs, src/lib.rs, src/ops.rs, src/rules.rs, src/rules/arithmetic.rs, src/syntax.rs)")
            && stderr.contains("--output"),
        "{stderr}"
    );
    let (listed, printed, copied) = round_trip(target.path(), &workspace, "whole", &dependency);
    assert_eq!(
        listed,
        [
            "src/cells/machine.rs",
            "src/lib.rs",
            "src/ops.rs",
            "src/rules.rs",
            "src/rules/arithmetic.rs",
            "src/syntax.rs",
        ]
    );
    // A binder of the dependency's sort prints by its declaring path, which only `lib.rs` writes.
    assert!(
        collapsed(printed_file(&printed, "src/rules.rs"))
            .contains("held:::semantic_dep::sorts::Common,"),
        "{printed:?}"
    );
    // Fields of a sort of another module and of another crate print by their markers' paths.
    let syntax = collapsed(printed_file(&printed, "src/syntax.rs"));
    for field in [
        "op:k::Term<dyncrate::ops::OpSort>",
        "held:k::Term<dyn::semantic_dep::sorts::CommonSort>",
    ] {
        assert!(syntax.contains(field), "{syntax}");
    }
    // The inline module's clause prints in that module.
    let root = printed_file(&printed, "src/lib.rs");
    assert!(
        collapsed(root).contains("modinline{#[k::rule(label=\"unwrap\")]"),
        "{root}"
    );
    // The printed package is a fixpoint: no file of it changes, and stdout holds its crate root
    // (printed as a whole file always is, its `use` items allowed to be unused once more).
    let again = temporary.path().join("again");
    let (success, listed, stderr) = krs(
        target.path(),
        &copied,
        "whole",
        "expand",
        &[
            "--dependency",
            "dep:main",
            "--output",
            again.to_str().unwrap(),
        ],
    );
    assert!(success && listed.is_empty(), "{listed}\n{stderr}");
    assert_eq!(fs::read_dir(&again).unwrap().count(), 0);
    let (success, stdout, stderr) = krs(target.path(), &copied, "whole", "expand", &dependency);
    assert!(success, "{stderr}");
    assert_eq!(
        stdout.replace(
            "#[allow(unused_imports)]\n#[allow(unused_imports)]\n",
            "#[allow(unused_imports)]\n"
        ),
        root
    );
}

const VISIBLE_ROOT: &str = r"
use k::builtin::KSequence;

pub mod a;
pub mod b;

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: a::Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}
";

const VISIBLE_A: &str = r#"
use k::KResult;
use k::builtin::Int;

// A module private to `a`, whose items the rest of the crate names through `a`'s re-export.
mod secret;
pub use secret::{Op, OpSyntax};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("apply({op}, {lhs}, {rhs})")]
    Apply { op: secret::Op, lhs: Exp, rhs: Exp },
    #[k::syntax("swap({op})")]
    Swap { op: secret::Op },
    #[k::syntax("keep({op})")]
    Keep { op: secret::Op },
}

k::rules! {
    for crate::Machine;
    use ExpSyntax::*;

    swap: { k: [Swap(op), ..] } => { k: [op, ..] };
}
"#;

const VISIBLE_SECRET: &str = r#"
k::sorts! {
    Op;
}

#[k::constructors(sort = Op, result = k::KResult)]
pub enum OpSyntax {
    #[k::syntax("plus")]
    Plus(),
    #[k::syntax("minus")]
    Minus(),
}
"#;

const VISIBLE_B: &str = r"
use k::builtin::{Int, int};

k::rules! {
    for crate::a::Exp;
    use crate::a::ExpSyntax::*;

    plus: Apply(crate::a::OpSyntax::Plus(), lhs, rhs) => int::add(lhs, rhs) where lhs: Int, rhs: Int;
}
";

/// The `b` clause that takes a binder of the sort of `a`'s private module, `where` naming it
/// (`WHERE`) or not.
const KEEP: &str = r"
k::rules! {
    for crate::Machine;
    use crate::a::ExpSyntax::*;

    keep: { k: [Keep(op), ..] } => { k: [Swap(op), ..] }WHERE;
}
";

fn visibility_package(root: &Path, b: &str) -> PathBuf {
    write_package(
        root,
        "vis",
        "",
        true,
        &[
            ("src/lib.rs", VISIBLE_ROOT),
            ("src/a.rs", VISIBLE_A),
            ("src/a/secret.rs", VISIBLE_SECRET),
            ("src/b.rs", b),
        ],
    )
}

/// A module private to `a` (`a::secret`): an item of it prints by its `crate::` path where the
/// long form stands inside `a`, which sees the module, and elsewhere by the path the clause
/// writes to it (`crate::a::OpSyntax::Plus`, through `a`'s re-export).
#[test]
fn an_item_of_a_private_module_prints_by_its_path_where_visible_else_by_the_written_path() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let workspace = temporary.path().join("workspace");
    visibility_package(&workspace, VISIBLE_B);
    let (_, printed, _) = round_trip(target.path(), &workspace, "vis", &[]);
    let a = collapsed(printed_file(&printed, "src/a.rs"));
    assert!(a.contains("op:crate::a::secret::Op,"), "{a}");
    let b = collapsed(printed_file(&printed, "src/b.rs"));
    assert!(
        b.contains("crate::a::ExpSyntax::Apply(crate::a::OpSyntax::Plus(),lhs,rhs)"),
        "{b}"
    );
}

/// Where the long form stands outside `a` and the clause writes no path to the private module's
/// sort (a binder's), there is none it can print: refused, naming the module and the fix. A
/// `where` that names the sort by `a`'s re-export is such a path.
#[test]
fn an_item_of_a_private_module_with_no_path_the_clause_writes_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let workspace = temporary.path().join("workspace");
    let manifest = visibility_package(
        &workspace,
        &format!("{VISIBLE_B}{}", KEEP.replace("WHERE", "")),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "vis", "check", &[]);
    assert!(success, "{stderr}");
    let printed = temporary.path().join("printed");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "vis",
        "expand",
        &["--output", printed.to_str().unwrap()],
    );
    assert!(!success);
    assert!(
        stderr.contains("error[krs::reference::private-module]: cannot print a path to WHOLE-VIS::a::secret::Op (sort) in `crate::b`: a module on `crate::a::secret` is private to a module that does not contain `crate::b`"),
        "{stderr}"
    );
    fs::write(
        workspace.join("vis/src/b.rs"),
        format!(
            "{VISIBLE_B}{}",
            KEEP.replace("WHERE", " where op: crate::a::Op")
        ),
    )
    .unwrap();
    let (_, printed, _) = round_trip(target.path(), &workspace, "vis", &[]);
    let b = collapsed(printed_file(&printed, "src/b.rs"));
    assert!(b.contains("op:crate::a::Op,"), "{b}");
}

/// A descriptor from a file the crate's module tree does not read as a module (`include!`) has
/// no printed file to stand in: refused, naming the file.
#[test]
fn a_descriptor_from_a_file_no_module_declares_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let workspace = temporary.path().join("workspace");
    let manifest = visibility_package(&workspace, VISIBLE_B);
    let root = workspace.join("vis/src/lib.rs");
    fs::write(&root, format!("{VISIBLE_ROOT}\ninclude!(\"extra.rs\");\n")).unwrap();
    fs::write(
        workspace.join("vis/src/extra.rs"),
        KEEP.replace("WHERE", ""),
    )
    .unwrap();
    let (success, _, stderr) = krs(target.path(), &manifest, "vis", "expand", &[]);
    assert!(!success);
    assert!(
        stderr.contains("error[krs::reference::source-selection]: expand prints the crate's module files, and descriptors come from files its module tree does not reach as modules (such as a file `include!` reads): src/extra.rs"),
        "{stderr}"
    );
}
