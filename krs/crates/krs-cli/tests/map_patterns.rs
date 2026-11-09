//! A map's entries matched where a term is: `map![k -> v, rest @ ..]`, `map![k -> v, ..]` and
//! `map![k -> v]` at a pattern position of sort `Map`, K's `(K |-> V) REST`. An equation walks a
//! `Map` parameter entry by entry (FB-39's `MemoryOutsideRom`), and `krs run` evaluates it on a
//! concrete two-entry map to `true` and to `false`; the emitted equation is pinned; `krs expand`
//! writes the construct back, and the expanded package emits the same K.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const SOURCE: &str = r#"
use k::builtin::{Bool, Int, KSequence, Map, map};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("check({e})")]
    Check { e: Int },
    #[k::syntax("load({m})")]
    Load { m: Map },
}

/// Whether `address` lies below `rom_end`, in ROM.
#[k::function(total, internal)]
pub fn InRom(rom_end: Term<Int>, address: Term<Int>) -> Term<Bool> {
    k::term![address < rom_end]
}

/// Whether no address the memory holds lies in ROM: one entry at a time.
#[k::function(total, internal)]
pub fn MemoryOutsideRom(memory: Term<Map>, rom_end: Term<Int>) -> Term<Bool>;

k::equations! {
    for MemoryOutsideRom;
    walk: (map![k -> _, rest @ ..], e) => !InRom(e, k) && MemoryOutsideRom(rest, e);
    done: (map![], _) => true;
}

/// The value at a key the other argument gives: the key is looked up.
#[k::function(partial, internal)]
pub fn At(memory: Term<Map>, address: Term<Int>) -> Term<Int>;

k::equations! {
    for At;
    at: (map![a -> v, ..], a) => v;
}

/// The value at a map's one entry, or 0.
#[k::function(total, internal)]
pub fn Only(memory: Term<Map>) -> Term<Int> {
    match memory {
        map![_ -> v] => v,
        _ => 0,
    }
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub mem: Map,
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
            out: false,
            seen: 0,
        }
    }
}

k::rules! {
    for Machine;
    use ExpSyntax::*;

    check: { k: [Check(e), ..], mem: m } => { k: [..], out: MemoryOutsideRom(m, e) };
    // A constructor's field matched by its entries: the value at key 1, the others left open.
    load: { k: [Load(map![1 -> v, ..]), ..] } => { k: [..], seen: v };
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
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-MAPPATTERNS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The emitted `.k` files of the package at `manifest`, by name.
fn emitted_k(target: &Path, manifest: &Path) -> Vec<(String, String)> {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let mut files = fs::read_dir(&output)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "k"))
        .map(|path| {
            (
                path.file_name().unwrap().to_string_lossy().into_owned(),
                fs::read_to_string(&path).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    files.sort();
    files
}

/// The lines of `files` that mention `needle`.
fn lines_with<'a>(files: &'a [(String, String)], needle: &str) -> Vec<&'a str> {
    files
        .iter()
        .flat_map(|(_, text)| text.lines())
        .filter(|line| line.contains(needle))
        .map(str::trim)
        .collect()
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

/// The equation walks the map one entry at a time: `(K |-> _) REST` matches an entry, any one,
/// and its rest, the map without it, and `.Map` ends the walk. On `1 |-> 10 2 |-> 20`, no
/// address lies below 0, and address 1 lies below 2.
#[test]
fn an_equation_walks_a_map_parameter_entry_by_entry() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "mappatterns", SOURCE);
    let k = emitted_k(target.path(), &manifest);
    expect_test::expect![[r#"
        [
            "<mem> 1 |-> 10 2 |-> 20 </mem>",
            "<k> load ( 1 |-> V:Int _ ) => .K ... </k>",
            "rule at ( A:Int |-> V:Int _ , A:Int ) => V:Int [label(org_krs_mappatterns--at)]",
            "rule only ( _ |-> V:Int ) => V:Int [label(org_krs_mappatterns--only_1)]",
            "rule memoryOutsideRom ( K:Int |-> _ Rest:Map , E:Int ) => (notBool inRom ( E:Int , K:Int )) andThenBool memoryOutsideRom ( Rest:Map , E:Int ) [label(org_krs_mappatterns--walk)]",
        ]
    "#]]
    .assert_debug_eq(&lines_with(&k, "|->"));
    let outcomes = ["check(0)", "check(2)"].map(|program| {
        format!(
            "{program} => out: {}",
            run_cell(target.path(), &manifest, program, "out")
        )
    });
    expect_test::expect![[r#"
        [
            "check(0) => out: true",
            "check(2) => out: false",
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}

/// The first `error[..]` headline of `krs check` on [`SOURCE`] with `item` appended.
fn check_error(target: &Path, item: &str) -> String {
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "mappatterns",
        &format!("{SOURCE}\n{item}"),
    );
    let (success, _, stderr) = krs(target, &manifest, "check", &[]);
    assert!(!success, "{item} was accepted");
    stderr
        .lines()
        .find(|line| line.starts_with("error["))
        .unwrap_or_else(|| panic!("no error headline:\n{stderr}"))
        .to_owned()
}

/// A map pattern names an entry: one that names none is the whole map, `_` or its name; its
/// rest comes last; two keys written as the same term never both match; and a literal written
/// over a base is the update, a function, which never matches an evaluated map.
#[test]
fn malformed_map_patterns_and_an_update_in_a_pattern_are_errors() {
    let target = shared_fixture_target();
    let row = |pattern: &str| {
        format!(
            "#[k::function(partial, internal)]\npub fn Bad(memory: Term<Map>) -> Term<Int>;\nk::equations! {{ for Bad; bad: ({pattern}) => 0; }}"
        )
    };
    let errors = [
        "map![..]",
        "map![rest @ ..]",
        "map![.., a -> 1]",
        "map![a -> 1, a -> 2, ..]",
        "map![a -> 1, ..memory]",
    ]
    .map(|pattern| check_error(target.path(), &row(pattern)));
    expect_test::expect![[r#"
        [
            "error[krs::syntax::invalid-expression-notation]: `map![..]` names no entry: it matches every map, which `_` says",
            "error[krs::syntax::invalid-expression-notation]: `map![rest @ ..]` names no entry: it is the whole map `rest`, so write `rest`",
            "error[krs::syntax::invalid-expression-notation]: the rest `rest @ ..` of a map pattern comes last: it is the map without the entries written before it",
            "error[krs::syntax::invalid-expression-notation]: a map pattern names one key twice; its entries are distinct entries of the map, so no map matches it",
            "error[krs::analysis::function-in-pattern]: the builtin function `k::builtin::map::update` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: a pattern reads a map's entries with `map![k -> v, ..]` (`{ k -> v, .. }` in a readable record), the map holding an entry at `k` and others, or match a variable here and relate it to the map in a guard (`requires`)",
        ]
    "#]].assert_debug_eq(&errors);
}

/// `krs expand` writes each map pattern as it is authored, and the expanded package emits the
/// same K.
#[test]
fn krs_expand_writes_map_patterns_back_to_the_same_k() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "mappatterns", SOURCE);
    let (success, stdout, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    assert!(
        stdout.contains("map![k -> _, rest @ ..]"),
        "the walk's pattern is not written back:\n{stdout}"
    );
    let expanded = package(temporary.path(), "expanded", "");
    fs::write(expanded.with_file_name("src").join("lib.rs"), &stdout).unwrap();
    let original = emitted_k(target.path(), &manifest);
    let rewritten = emitted_k(target.path(), &expanded);
    // The comments name the package and the items the K comes from.
    let strip = |files: Vec<(String, String)>| {
        files
            .into_iter()
            .map(|(_, text)| {
                text.lines()
                    .filter(|line| !line.trim_start().starts_with("//"))
                    .collect::<Vec<_>>()
                    .join("\n")
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(strip(original), strip(rewritten));
}
