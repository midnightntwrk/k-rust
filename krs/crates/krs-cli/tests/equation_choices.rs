//! One equation over a map or set pattern that selects an entry (`map![k -> _, ..]`,
//! `set::concat(set::item(x), rest)`) applies to a collection of two entries in two ways, one
//! per entry. Where the two ways give different results, the equation states that they are
//! equal, which is what two overlapping equations state: `krs::analysis::overlapping-equations`,
//! with the argument, the two choices and the two results. A result that reads neither the
//! entry nor the rest (the violation form), a fold whose ways agree, and a key the pattern looks
//! up are accepted, and `krs run` evaluates them.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const SOURCE: &str = r#"
use k::builtin::{Bool, Int, KSequence, Map, Set, map, set};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("check({e})")]
    Check { e: Int },
    #[k::syntax("count")]
    CountAll(),
    #[k::syntax("fetch({a})")]
    Fetch { a: Int },
}

/// Whether no key the memory holds lies below `rom_end`: the violation form, a guard on the
/// key whose result reads neither the key nor the rest, beside an `owise` equation.
#[k::function(total, internal)]
pub fn OutsideRom(memory: Term<Map<Int, Int>>, rom_end: Term<Int>) -> Term<Bool>;

#[k::requires(k < e)]
#[k::equation]
fn outside_rom_violated(k::term![OutsideRom(map![k -> _, ..], e)]: Term<Bool>) -> Term<Bool> {
    false
}

#[k::equation(owise)]
fn outside_rom_holds(k::term![OutsideRom(_, _)]: Term<Bool>) -> Term<Bool> {
    true
}

/// The number of elements: a fold whose ways agree, which the check does not decide and does
/// not report.
#[k::function(total, internal)]
pub fn Count(s: Term<Set>) -> Term<Int>;

k::equations! {
    for Count;
    more: (set::concat(set::item(_), rest)) => 1 + Count(rest);
    none: (set![]) => 0;
}

/// The value at a key the other argument gives: looked up, one way.
#[k::function(partial, internal)]
pub fn At(memory: Term<Map<Int, Int>>, address: Term<Int>) -> Term<Int>;

k::equations! {
    for At;
    at: (map![a -> v, ..], a) => v;
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub mem: Map<Int, Int>,
    #[k::cell]
    pub bag: Set,
    #[k::cell]
    pub out: Bool,
    #[k::cell]
    pub seen: Int,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            mem: map![1 -> 10, 2 -> 20],
            bag: set![1, 2, 3],
            out: false,
            seen: 0,
        }
    }
}

k::rules! {
    for Machine;
    use ExpSyntax::*;

    check: { k: [Check(e), ..], mem: m } => { k: [..], out: OutsideRom(m, e) };
    count: { k: [CountAll(), ..], bag: s } => { k: [..], seen: Count(s) };
    fetch: { k: [Fetch(a), ..], mem: m } => { k: [..], seen: At(m, a) };
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes the package `name` with `source`.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(
        directory.join("src/lib.rs"),
        format!("#![allow(unused_imports)]\n{source}"),
    )
    .unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CHOICES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// The content of the cell `name` after `krs run` of `program`.
fn run_cell(target: &Path, manifest: &Path, program: &str, name: &str) -> String {
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, program).unwrap();
    let (success, stdout, stderr) = krs(target, manifest, "run", &[file.to_str().unwrap()]);
    assert!(
        stdout.contains("<generatedTop>"),
        "`krs run {program}` failed ({success}):\n{stdout}\n{stderr}"
    );
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    let open = format!("<{name}> ");
    let start = flat
        .find(&open)
        .unwrap_or_else(|| panic!("no <{name}>:\n{stdout}"))
        + open.len();
    let end = start + flat[start..].find(&format!(" </{name}>")).unwrap();
    flat[start..end].to_owned()
}

/// The violation form tests every key with a guard and reads neither the key nor the rest, so
/// each way it applies gives `false`: `check(2)` finds the key 1 below 2, and `check(1)` finds
/// none. The count reads the rest, and every way agrees: three elements. The lookup reads the
/// value at the key its other argument gives. `krs check` reports none of them.
#[test]
fn the_violation_form_a_fold_and_a_lookup_are_functions_and_run() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "choices", SOURCE);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");
    assert!(
        !stderr.contains("overlapping-equations"),
        "an equation was reported:\n{stderr}"
    );
    let outcomes = [
        ("check(1)", "out"),
        ("check(2)", "out"),
        ("count", "seen"),
        ("fetch(2)", "seen"),
    ]
    .map(|(program, cell)| {
        format!(
            "{program} => {cell}: {}",
            run_cell(target.path(), &manifest, program, cell)
        )
    });
    expect_test::expect![[r#"
        [
            "check(1) => out: true",
            "check(2) => out: false",
            "count => seen: 3",
            "fetch(2) => seen: 20",
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}

/// `krs check` on [`SOURCE`] with `item` appended: the `error[..]` headline and its location
/// line, or `accepted`.
fn verdict(target: &Path, item: &str) -> String {
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "choices", &format!("{SOURCE}\n{item}"));
    let (success, _, stderr) = krs(target, &manifest, "check", &[]);
    if success {
        return "accepted".to_owned();
    }
    let mut lines = stderr
        .lines()
        .skip_while(|line| !line.starts_with("error["));
    let headline = lines
        .next()
        .unwrap_or_else(|| panic!("no error headline:\n{stderr}"));
    // The location within the package, whose directory is a fresh temporary one.
    let location = lines
        .find(|line| line.trim_start().starts_with("-->"))
        .and_then(|line| line.rsplit_once("/choices/"))
        .map_or("", |(_, tail)| tail);
    format!("{headline}\n{location}")
}

/// Equations whose ways give different results, each with the argument the check exhibits: a
/// projection of the key, of the value and of the rest, a set's element, a key below a
/// constructor, an `owise` equation after an equation that excludes the argument, a function
/// context's map cell and a branching body's arm. A projection whose ways are not shown to
/// differ is not reported: a guard on the key, an `owise` equation after one that may apply to
/// the argument, and a value of a sort the check writes no two values of.
#[test]
fn an_equation_whose_ways_give_different_results_is_an_overlap() {
    let target = shared_fixture_target();
    let cases = [
        (
            "key",
            "#[k::function(partial, internal)]\npub fn First(m: Term<Map<Int, Int>>) -> Term<Int>;\nk::equations! { for First; first: (map![k -> _, ..]) => k; }",
        ),
        (
            "value",
            "#[k::function(partial, internal)]\npub fn Any(m: Term<Map<Int, Int>>) -> Term<Int>;\nk::equations! { for Any; any: (map![_ -> v, ..]) => v; }",
        ),
        (
            "rest",
            "#[k::function(partial, internal)]\npub fn Drop(m: Term<Map<Int, Int>>) -> Term<Map<Int, Int>>;\nk::equations! { for Drop; drop: (map![_ -> _, rest @ ..]) => rest; }",
        ),
        (
            "set",
            "#[k::function(partial, internal)]\npub fn Pick(s: Term<Set>) -> Term<KItem>;\nk::equations! { for Pick; pick: (set::concat(set::item(x), _rest)) => x; }",
        ),
        (
            "nested",
            "#[k::constructors(sort = Exp, result = KResult)]\npub enum Wrapped {\n    #[k::syntax(\"wrap({m})\")]\n    Wrap { m: Map },\n    #[k::syntax(\"two({a}, {b})\")]\n    Two { a: KItem, b: KItem },\n}\n#[k::function(partial, internal)]\npub fn Unwrap(w: Term<Exp>) -> Term<Exp>;\nk::equations! { for Unwrap; unwrap: (Wrapped::Wrap(map![k -> v, ..])) => Wrapped::Two(k, v); }",
        ),
        (
            "owise",
            "#[k::function(total, internal)]\npub fn Front(m: Term<Map<Int, Int>>) -> Term<Int>;\nk::equations! { for Front; front_none: (map![]) => 0; #[k::equation(owise)] front_some: (map![k -> _, ..]) => k; }",
        ),
        (
            "context",
            "#[k::function(partial, internal)]\npub fn Low() -> Term<Int>;\n#[k::equation]\nfn low(key: Term<Int>, k::term![Low()]: Term<Int>, k::cells! { mem: k::configuration::Cell(map![key -> _, ..]), .. }: Machine) -> Term<Int> {\n    key\n}",
        ),
        (
            "arm",
            "#[k::function(total, internal)]\npub fn Found(m: Term<Map<Int, Int>>) -> Term<Int> {\n    match m {\n        map![k -> _, ..] => k,\n        _ => 0,\n    }\n}",
        ),
        (
            "guarded",
            "#[k::function(partial, internal)]\npub fn Low2(m: Term<Map<Int, Int>>) -> Term<Int>;\nk::equations! { for Low2; #[k::requires(k < 0)] low: (map![k -> _, ..]) => k; }",
        ),
        (
            "owise-after-undecided",
            "#[k::function(total, internal)]\npub fn Later(m: Term<Map<Int, Int>>) -> Term<Int>;\nk::equations! { for Later; later_five: (map![_ -> 5, ..]) => 5; #[k::equation(owise)] later_any: (map![k -> _, ..]) => k; later_none: (map![]) => 0; }",
        ),
        (
            "owise-after-other-key",
            "#[k::function(total, internal)]\npub fn Next(m: Term<Map<Int, Int>>) -> Term<Int>;\nk::equations! { for Next; next_two: (map![2 -> v, ..]) => v; #[k::equation(owise)] next_any: (map![k -> _, ..]) => k; next_none: (map![]) => 0; }",
        ),
        (
            "unwritten-value",
            "#[k::function(partial, internal)]\npub fn Val(m: Term<Map<Int, Exp>>) -> Term<Exp>;\nk::equations! { for Val; val: (map![_ -> v, ..]) => v; }",
        ),
    ]
    .map(|(name, item)| format!("{name}:\n{}", verdict(target.path(), item)));
    expect_test::expect![[r"
        key:
        error[krs::analysis::overlapping-equations]: equation `first` of `First` applies to `First(map![0 -> 0, 1 -> 1])` in two ways, choosing the entry at `0` or the entry at `1`, and gives it different results, `0` and `1`; an equation holds for every way its pattern matches, so the definition would state that these are equal. To test whether some entry or element has a property, guard the equation on it and give a result that reads neither it nor the rest, beside an `owise` equation for the other case (`#[k::requires(..)]` on `f(map![k -> _, ..]) => false`, and `f(_) => true` with `#[k::equation(owise)]`); to read the entry at a known key, bind the key elsewhere in the pattern, so that the entry is looked up (`f(map![k -> v, ..], k)`).
        src/lib.rs:94:36
        value:
        error[krs::analysis::overlapping-equations]: equation `any` of `Any` applies to `Any(map![0 -> 0, 1 -> 1])` in two ways, choosing the entry at `0` or the entry at `1`, and gives it different results, `0` and `1`; an equation holds for every way its pattern matches, so the definition would state that these are equal. To test whether some entry or element has a property, guard the equation on it and give a result that reads neither it nor the rest, beside an `owise` equation for the other case (`#[k::requires(..)]` on `f(map![k -> _, ..]) => false`, and `f(_) => true` with `#[k::equation(owise)]`); to read the entry at a known key, bind the key elsewhere in the pattern, so that the entry is looked up (`f(map![k -> v, ..], k)`).
        src/lib.rs:94:32
        rest:
        error[krs::analysis::overlapping-equations]: equation `drop` of `Drop` applies to `Drop(map![0 -> 0, 1 -> 1])` in two ways, choosing the entry at `0` or the entry at `1`, and gives it different results, `map![1 -> 1]` and `map![0 -> 0]`; an equation holds for every way its pattern matches, so the definition would state that these are equal. To test whether some entry or element has a property, guard the equation on it and give a result that reads neither it nor the rest, beside an `owise` equation for the other case (`#[k::requires(..)]` on `f(map![k -> _, ..]) => false`, and `f(_) => true` with `#[k::equation(owise)]`); to read the entry at a known key, bind the key elsewhere in the pattern, so that the entry is looked up (`f(map![k -> v, ..], k)`).
        src/lib.rs:94:34
        set:
        error[krs::analysis::overlapping-equations]: equation `pick` of `Pick` applies to `Pick(set![0, 1])` in two ways, choosing the element `0` or the element `1`, and gives it different results, `0` and `1`; an equation holds for every way its pattern matches, so the definition would state that these are equal. To test whether some entry or element has a property, guard the equation on it and give a result that reads neither it nor the rest, beside an `owise` equation for the other case (`#[k::requires(..)]` on `f(map![k -> _, ..]) => false`, and `f(_) => true` with `#[k::equation(owise)]`); to read the entry at a known key, bind the key elsewhere in the pattern, so that the entry is looked up (`f(map![k -> v, ..], k)`).
        src/lib.rs:94:34
        nested:
        error[krs::analysis::overlapping-equations]: equation `unwrap` of `Unwrap` applies to `Unwrap(Wrapped::Wrap(map![0 -> 0, 1 -> 1]))` in two ways, choosing the entry at `0` or the entry at `1`, and gives it different results, `Wrapped::Two(0, 0)` and `Wrapped::Two(1, 1)`; an equation holds for every way its pattern matches, so the definition would state that these are equal. To test whether some entry or element has a property, guard the equation on it and give a result that reads neither it nor the rest, beside an `owise` equation for the other case (`#[k::requires(..)]` on `f(map![k -> _, ..]) => false`, and `f(_) => true` with `#[k::equation(owise)]`); to read the entry at a known key, bind the key elsewhere in the pattern, so that the entry is looked up (`f(map![k -> v, ..], k)`).
        src/lib.rs:101:52
        owise:
        error[krs::analysis::overlapping-equations]: equation `front_some` of `Front` applies to `Front(map![0 -> 0, 1 -> 1])` in two ways, choosing the entry at `0` or the entry at `1`, and gives it different results, `0` and `1`; an equation holds for every way its pattern matches, so the definition would state that these are equal. To test whether some entry or element has a property, guard the equation on it and give a result that reads neither it nor the rest, beside an `owise` equation for the other case (`#[k::requires(..)]` on `f(map![k -> _, ..]) => false`, and `f(_) => true` with `#[k::equation(owise)]`); to read the entry at a known key, bind the key elsewhere in the pattern, so that the entry is looked up (`f(map![k -> v, ..], k)`).
        src/lib.rs:94:90
        context:
        error[krs::analysis::overlapping-equations]: equation `low` of `Low` applies to `Low()` where the cell `mem` holds `map![0 -> 0, 1 -> 1]` in two ways, choosing the entry at `0` or the entry at `1`, and gives it different results, `0` and `1`; an equation holds for every way its pattern matches, so the definition would state that these are equal. To test whether some entry or element has a property, guard the equation on it and give a result that reads neither it nor the rest, beside an `owise` equation for the other case (`#[k::requires(..)]` on `f(map![k -> _, ..]) => false`, and `f(_) => true` with `#[k::equation(owise)]`); to read the entry at a known key, bind the key elsewhere in the pattern, so that the entry is looked up (`f(map![k -> v, ..], k)`).
        src/lib.rs:95:97
        arm:
        error[krs::analysis::overlapping-equations]: equation `found_1` of `Found` applies to `Found(map![0 -> 0, 1 -> 1])` in two ways, choosing the entry at `0` or the entry at `1`, and gives it different results, `0` and `1`; an equation holds for every way its pattern matches, so the definition would state that these are equal. To test whether some entry or element has a property, guard the equation on it and give a result that reads neither it nor the rest, beside an `owise` equation for the other case (`#[k::requires(..)]` on `f(map![k -> _, ..]) => false`, and `f(_) => true` with `#[k::equation(owise)]`); to read the entry at a known key, bind the key elsewhere in the pattern, so that the entry is looked up (`f(map![k -> v, ..], k)`).
        src/lib.rs:95:9
        guarded:
        accepted
        owise-after-undecided:
        accepted
        owise-after-other-key:
        error[krs::analysis::overlapping-equations]: equation `next_any` of `Next` applies to `Next(map![0 -> 0, 1 -> 1])` in two ways, choosing the entry at `0` or the entry at `1`, and gives it different results, `0` and `1`; an equation holds for every way its pattern matches, so the definition would state that these are equal. To test whether some entry or element has a property, guard the equation on it and give a result that reads neither it nor the rest, beside an `owise` equation for the other case (`#[k::requires(..)]` on `f(map![k -> _, ..]) => false`, and `f(_) => true` with `#[k::equation(owise)]`); to read the entry at a known key, bind the key elsewhere in the pattern, so that the entry is looked up (`f(map![k -> v, ..], k)`).
        src/lib.rs:94:95
        unwritten-value:
        accepted"]].assert_eq(&cases.join("\n"));
}
