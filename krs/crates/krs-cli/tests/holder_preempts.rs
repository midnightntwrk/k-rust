//! A holder's rule that pre-empts a cell group's rule (HOLDER-PREEMPTS-GROUP): `krs check` warns
//! where a rule of the definition that holds a group, at a priority more urgent than a rule the
//! group's package writes for it, can apply where that rule does
//! (`krs::analysis::holder-preempts-group`).
//! The group's rule then does not apply there in this definition, so the group's cells mean
//! something other than its package states.
//! It is a warning: the definition is accepted, and nothing emitted changes.
//!
//! The library `lib` declares the group `Core { k, acc }` and its rules; the package `small`
//! declares `Small { core: lib::Core, mem }` and writes its own rules.
//! Two rules the overlap check keeps apart by their guards are silent, as are two rules of one
//! package, a holder's rule after a group's, a group's rule before a holder's, and a definition
//! without priorities.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// The group and the program syntax; `rules` is appended.
const LIB: &str = r#"
use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Instr;
}

#[k::constructors(sort = Instr, result = KResult)]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("inc")] Inc(),
    #[k::syntax("dec")] Dec(),
    #[k::syntax("neg")] Neg(),
    #[k::syntax("reset")] Reset(),
    #[k::syntax("store ( {addr} )")] Store { addr: Int },
}

/// A core: its computation cell and an accumulator.
#[k::cell]
pub struct Core {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Int,
}
"#;

/// The holder's configuration; its rules are appended.
const SMALL: &str = r"
use k::builtin::{Int, Map, map};

#[k::configuration]
pub struct Small {
    #[k::cell(nested)]
    pub core: lib::Core,
    #[k::cell]
    pub mem: Map<Int, Int>,
}

impl Small {
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {
        Self {
            core: lib::Core { k: k::k![pgm], acc: 0 },
            mem: map::empty(),
        }
    }
}
";

/// The library's rules for `Core`, none with a priority.
const LIB_PLAIN: &str = r"
k::rules! {
    for Core;
    use Op::*;

    inc: { k: [Inc(), ..], acc } => { k: [..], acc: k::builtin::int::add(acc, 1) };
    dec: { k: [Dec(), ..], acc } => { k: [..], acc: k::builtin::int::sub(acc, 1) };
}
";

/// A holder's rule at priority 10 that applies wherever `inc` does, beside a rule of its own
/// that meets no rule of the group.
const SMALL_PREEMPTS: &str = r"
k::rules! {
    for Small;
    use lib::Op::*;

    #[k::rule(priority = 10)]
    double: { k: [Inc(), ..], acc } => { k: [..], acc: k::builtin::int::add(acc, 2) };
    store: { k: [Store { addr }, ..], acc, mem } => { k: [..], acc, mem: map::update(mem, addr, acc) };
}
";

/// The holder's rules without a priority, which meet no rule of the group.
const SMALL_PLAIN: &str = r"
k::rules! {
    for Small;
    use lib::Op::*;

    store: { k: [Store { addr }, ..], acc, mem } => { k: [..], acc, mem: map::update(mem, addr, acc) };
}
";

/// The library's rules for the silent cases: `inc` is guarded, `neg` is at priority 10, and
/// `reset_zero` at priority 10 pre-empts the library's own `reset`.
const LIB_SILENT: &str = r"
k::rules! {
    for Core;
    use Op::*;

    #[k::requires(k::builtin::int::lt(acc, 10))]
    inc: { k: [Inc(), ..], acc } => { k: [..], acc: k::builtin::int::add(acc, 1) };
    dec: { k: [Dec(), ..], acc } => { k: [..], acc: k::builtin::int::sub(acc, 1) };
    #[k::rule(priority = 10)]
    neg: { k: [Neg(), ..], acc } => { k: [..], acc: k::builtin::int::sub(0, acc) };
    #[k::rule(priority = 10)]
    reset_zero: { k: [Reset(), ..], acc: 0 } => { k: [..], acc: 0 };
    reset: { k: [Reset(), ..], acc: _ } => { k: [..], acc: 0 };
}
";

/// The holder's rules for the silent cases:
/// - `saturate`, at priority 10, is guarded apart from `inc` by the complementary conjunct;
/// - `dec_late`, at priority 60, is tried only where `dec` failed;
/// - `neg_late`, at the default priority, comes after the group's `neg` at priority 10;
/// - `store_zero`, at priority 10, pre-empts the holder's own `store`.
const SMALL_SILENT: &str = r"
k::rules! {
    for Small;
    use lib::Op::*;

    #[k::rule(priority = 10)]
    #[k::requires(k::builtin::int::ge(acc, 10))]
    saturate: { k: [Inc(), ..], acc } => { k: [..], acc };
    #[k::rule(priority = 60)]
    dec_late: { k: [Dec(), ..], acc: _ } => { k: [..], acc: 0 };
    neg_late: { k: [Neg(), ..], acc: _ } => { k: [..], acc: 0 };
    #[k::rule(priority = 10)]
    store_zero: { k: [Store { addr }, ..], acc: 0, mem } => { k: [..], acc: 0, mem: map::update(mem, addr, 0) };
    store: { k: [Store { addr }, ..], acc, mem } => { k: [..], acc, mem: map::update(mem, addr, acc) };
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

fn write_package(root: &Path, name: &str, source: &str, dependencies: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"HOLDER-PREEMPTS-{}\"\n\n[package.metadata.krs.definitions.main]\n",
            krs_path(),
            name.to_ascii_uppercase()
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// A workspace of `lib` (the group, plus `lib_rules`) and `small` (the configuration, plus
/// `small_rules`); the manifest of `small`.
fn workspace(root: &Path, lib_rules: &str, small_rules: &str) -> PathBuf {
    write_package(root, "lib", &format!("{LIB}{lib_rules}"), "");
    let manifest = write_package(
        root,
        "small",
        &format!("{SMALL}{small_rules}"),
        "lib = { path = \"../lib\" }\n",
    );
    fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"lib\", \"small\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    manifest
}

/// `krs check` of `small`'s `main` definition, composed with `lib`'s: whether it passed, and
/// each diagnostic's headline, the source line it points at, and its notes and help.
fn checked(target: &Path, manifest: &Path) -> (bool, Vec<String>) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args(["check", "--manifest-path"])
        .arg(manifest)
        .args(["--package", "small", "--definition", "main"])
        .args(["--dependency", "lib:main"])
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    let mut lines = Vec::new();
    let mut pointed = false;
    for line in stderr.lines() {
        let trimmed = line.trim_start();
        if line.starts_with("error") || line.starts_with("warning") {
            lines.push(line.to_owned());
            pointed = true;
        } else if pointed
            && let Some((number, source)) = line.split_once(" | ")
            && number.trim().parse::<usize>().is_ok()
        {
            lines.push(format!("at `{}`", source.trim()));
            pointed = false;
        } else if trimmed.starts_with("= note:") || trimmed.starts_with("= help:") {
            lines.push(trimmed.to_owned());
        }
    }
    (output.status.success(), lines)
}

/// A holder's rule at priority 10 whose pattern unifies with the group's `inc` and which has no
/// guard is warned, at the holder's rule, naming both rules, the group and its package.
/// The definition is accepted, and the holder's rule that meets no rule of the group is silent.
#[test]
fn a_holder_rule_that_preempts_an_overlapping_group_rule_is_warned() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = workspace(temporary.path(), LIB_PLAIN, SMALL_PREEMPTS);
    let (passed, lines) = checked(target.path(), &manifest);
    assert!(passed, "{lines:#?}");
    assert_eq!(
        lines,
        [
            "warning[krs::analysis::holder-preempts-group]: the rule `double` of package `small`, at priority 10, pre-empts the rule `inc` of the cell group `Core` of package `lib`, at the default priority 50: the two can apply to one configuration, and a rule is tried only where no rule of a more urgent priority applies, so in this definition `inc` does not apply where `double` does",
            "at `double: { k: [Inc(), ..], acc } => { k: [..], acc: k::builtin::int::add(acc, 2) };`",
            "= note: `lib`'s rules for `Core` are what its cells mean in every definition that holds it, so this definition holds `Core` with another meaning where `double` applies",
            "= help: to act beside the group without changing what it means, drop the priority and guard `double` so that it cannot apply where `inc` does; where this definition must decide such a state itself, ask the author of `lib` to leave the state to the holder, as an open item that `Core`'s rules produce and never consume",
        ]
        .map(str::to_owned),
    );
}

/// No warning where the holder's rule at priority 10 is guarded apart from the group's rule, for
/// a priority within one package (the library's `reset_zero` over its `reset`, the holder's
/// `store_zero` over its `store`), for a holder's rule after the group's rule, and for a group's
/// rule before the holder's.
#[test]
fn a_holder_rule_guarded_apart_or_after_the_group_or_a_priority_within_one_package_is_silent() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = workspace(temporary.path(), LIB_SILENT, SMALL_SILENT);
    let (passed, lines) = checked(target.path(), &manifest);
    assert!(passed, "{lines:#?}");
    assert_eq!(lines, Vec::<String>::new());
}

/// No warning for a definition whose rules have no priority.
#[test]
fn a_definition_without_priorities_is_silent() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = workspace(temporary.path(), LIB_PLAIN, SMALL_PLAIN);
    let (passed, lines) = checked(target.path(), &manifest);
    assert!(passed, "{lines:#?}");
    assert_eq!(lines, Vec::<String>::new());
}
