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
    #[k::syntax("fetch({a})")]
    Fetch { a: Int },
    #[k::syntax("holds")]
    Holds(),
    #[k::syntax("exactly")]
    Exactly(),
    #[k::syntax("second")]
    Second(),
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

/// Whether the memory holds 20 at 2, beside any other entries.
#[k::function(total, internal)]
pub fn HoldsTwenty(memory: Term<Map>) -> Term<Bool> {
    k::matches!(memory, map![2 -> 20, ..])
}

/// Whether the memory is the one entry 20 at 2 and nothing else.
#[k::function(total, internal)]
pub fn IsTwenty(memory: Term<Map>) -> Term<Bool> {
    k::matches!(memory, map![2 -> 20])
}

/// The value at 2, read by a `let`.
#[k::function(partial, internal)]
pub fn AtTwo(memory: Term<Map>) -> Term<KItem> {
    let map![2 -> v, ..] = memory;
    v
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
    fetch: { k: [Fetch(a), ..], mem: m } => { k: [..], seen: At(m, a) };
    holds: { k: [Holds(), ..], mem: m } => { k: [..], out: HoldsTwenty(m) };
    exactly: { k: [Exactly(), ..], mem: m } => { k: [..], out: IsTwenty(m) };
    second: { k: [Second(), ..], mem: m } => { k: [AtTwo(m), ..] };
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
/// address lies below 0, and address 1 lies below 2. `At`'s key is the variable its other
/// argument binds, `A:Int |-> V:Int _` beside `A:Int`: the map is looked up at the key the
/// address gives, so `fetch(1)` reads 10 and `fetch(2)` reads 20. A local pattern matches a
/// value the rule computed, so `k::matches!` and `let` read a map pattern by its entries, with a
/// rest or without (K's `#let` and `:=K`): the memory holds 20 at 2 among others (`holds`), it
/// is not that one entry alone (`exactly`), and the `let` reads 20 at 2 (`second`).
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
            "rule atTwo ( Memory:Map ) => ( #let 2 |-> V:KItem _ = Memory:Map #in V:KItem ) [label(org_krs_mappatterns--at_two)]",
            "rule holdsTwenty ( Memory:Map ) => ( 2 |-> 20 _ :=K Memory:Map ) [label(org_krs_mappatterns--holds_twenty)]",
            "rule isTwenty ( Memory:Map ) => ( 2 |-> 20 :=K Memory:Map ) [label(org_krs_mappatterns--is_twenty)]",
            "rule only ( _ |-> V:Int ) => V:Int [label(org_krs_mappatterns--only_1)]",
            "rule memoryOutsideRom ( K:Int |-> _ Rest:Map , E:Int ) => (notBool inRom ( E:Int , K:Int )) andThenBool memoryOutsideRom ( Rest:Map , E:Int ) [label(org_krs_mappatterns--walk)]",
        ]
    "#]]
    .assert_debug_eq(&lines_with(&k, "|->"));
    let outcomes = [
        ("check(0)", "out"),
        ("check(2)", "out"),
        ("fetch(1)", "seen"),
        ("fetch(2)", "seen"),
        ("holds", "out"),
        ("exactly", "out"),
        ("second", "k"),
    ]
    .map(|(program, cell)| {
        format!(
            "{program} => {cell}: {}",
            run_cell(target.path(), &manifest, program, cell)
        )
    });
    expect_test::expect![[r#"
        [
            "check(0) => out: true",
            "check(2) => out: false",
            "fetch(1) => seen: 10",
            "fetch(2) => seen: 20",
            "holds => out: true",
            "exactly => out: false",
            "second => k: 20 ~> .K",
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}

/// The first `error[..]` headline of `krs check` on [`SOURCE`] with `item` appended.
fn check_error(target: &Path, item: &str) -> String {
    check_error_in(target, SOURCE, item)
}

/// The first `error[..]` headline of `krs check` on `source` with `item` appended.
fn check_error_in(target: &Path, source: &str, item: &str) -> String {
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "mappatterns",
        &format!("{source}\n{item}"),
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
/// over a base is the update, a function, which never matches an evaluated map. A literal
/// without a rest whose value computes (`a + 1`) is no map pattern but the map it builds, the
/// update, which a matched parameter refuses as before map patterns; with a rest it is a map
/// pattern, whose value is a pattern.
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
        "map![a -> a + 1]",
        "map![a -> a + 1, ..]",
    ]
    .map(|pattern| check_error(target.path(), &row(pattern)));
    expect_test::expect![[r#"
        [
            "error[krs::syntax::invalid-expression-notation]: `map![..]` names no entry: it matches every map, which `_` says",
            "error[krs::syntax::invalid-expression-notation]: `map![rest @ ..]` names no entry: it is the whole map `rest`, so write `rest`",
            "error[krs::syntax::invalid-expression-notation]: the rest `rest @ ..` of a map pattern comes last: it is the map without the entries written before it",
            "error[krs::syntax::invalid-expression-notation]: a map pattern names one key twice; its entries are distinct entries of the map, so no map matches it",
            "error[krs::analysis::function-in-pattern]: the builtin function `k::builtin::map::update` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: a pattern reads a map's entries with `map![k -> v, ..]` (`{ k -> v, .. }` in a readable record), the map holding an entry at `k` and others, or match a variable here and relate it to the map in a guard (`requires`)",
            "error[krs::analysis::function-in-pattern]: the builtin function `k::builtin::map::update` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: a pattern reads a map's entries with `map![k -> v, ..]` (`{ k -> v, .. }` in a readable record), the map holding an entry at `k` and others, or match a variable here and relate it to the map in a guard (`requires`)",
            "error[krs::syntax::invalid-expression-notation]: `+` is not a pattern: a pattern writes a builtin operation as its call, `int::add(..)`, `string::concat(..)`, or `float::add(..)`, where a pattern holds an application at all: in a simplification's or a claim's subject, or in a map's key or a set's element, which are looked up",
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

/// A Set collection, `pouch`, nested in each instance of a Map collection, `thread`, and a Set
/// collection, `bag`, below a group, `sacks`. [`NESTED_RULES`] holds the rules for `Thread`.
const NESTED: &str = r#"
use k::builtin::{Int, KSequence, Map, map};
use k::{KItem, KResult};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum Cmd {
    #[k::syntax("peek({n})")]
    Peek { n: Int },
}

#[k::cell]
pub struct Threads {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub thread: Thread,
}

#[k::cell]
pub struct Thread {
    #[k::cell]
    pub tid: Int,
    #[k::cell]
    pub hits: Int,
    #[k::cell(nested)]
    pub pouches: Pouches,
}

#[k::cell]
pub struct Pouches {
    #[k::cell(multiplicity = "*", cell_type = "Set", nested)]
    pub pouch: Pouch,
}

#[k::cell]
pub struct Pouch {
    #[k::cell]
    pub pk: Int,
    #[k::cell]
    pub pm: Map,
}

#[k::cell]
pub struct Sacks {
    #[k::cell(multiplicity = "*", cell_type = "Set", nested)]
    pub bag: Bag,
}

#[k::cell]
pub struct Bag {
    #[k::cell]
    pub key: Int,
    #[k::cell]
    pub m: Map,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub threads: Threads,
    #[k::cell(nested)]
    pub sacks: Sacks,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            threads: Threads {
                thread: Thread { tid: 0, hits: 0, pouches: Pouches { pouch: Pouch { pk: 0, pm: map![] } } },
            },
            sacks: Sacks { bag: Bag { key: 0, m: map![] } },
        }
    }
}

k::rules! {
    for Machine;
    use Cmd::*;

    peek: { k: [Peek(n), ..] } => { k: [..] };
}
"#;

/// Two rules for one `Thread`, each looking its `pouch` collection up by an instance: `inner`
/// writes the instance's map as a literal, `spelled` as the update `map::update` it denotes.
const NESTED_RULES: &str = r"
k::rules! {
    for Thread;

    inner: { tid: n, hits: 0, pouch: { Pouch { pk: n, pm: map![n -> 1] }, .. } } => { hits: 1 };
    spelled: { tid: n, hits: 5, pouch: { Pouch { pk: n + 7, pm: map::update(map::empty(), n, 1) }, .. } } => { hits: 2 };
}
";

/// A Set collection is a set of its instances, looked up by an instance the pattern computes,
/// so a rest-less map literal in a Set collection's instance is the map it builds, wherever
/// the collection is nested. A rule for the instance of another collection (`for Thread`)
/// names its nested Set collection `pouch` as its own cell: the literal `map![n -> 1]` is the
/// update a guard equates, the K `map::update` written out has and the literal had before map
/// patterns. Nothing else reaches a Set collection inside an instance or a group record: an
/// instance's child and a group record's child is a term, a map, a computation or a presence,
/// never a list of instances, so the instances written there are not Rust syntax, a single
/// value there is refused, and the nested collection named at the record's level is refused.
#[test]
fn a_map_literal_in_a_nested_set_collections_instance_is_the_map_it_builds() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "mappatterns",
        &format!("{NESTED}\n{NESTED_RULES}"),
    );
    let k = emitted_k(target.path(), &manifest);
    expect_test::expect![[r#"
        [
            "<pm> Krs_Instance0:Map </pm>",
            "requires Krs_Instance0:Map ==K .Map [ N:Int <- 1 ]",
            "<pk> Krs_Instance0:Int </pk>",
            "<pm> Krs_Instance1:Map </pm>",
            "requires (Krs_Instance0:Int ==K (N:Int +Int 7)) andThenBool (Krs_Instance1:Map ==K .Map [ N:Int <- 1 ])",
        ]
    "#]]
    .assert_debug_eq(&lines_with(&k, "Krs_Instance"));
    let errors = [
        "k::rules! { for Machine; use Cmd::*; bad: { k: [Peek(n), ..], thread: { Thread { tid: n, pouches: Pouches { pouch: { Pouch { pk: n, pm: map![n -> 1] }, .. } }, .. }, .. } } => { k: [..] }; }",
        "k::rules! { for Machine; use Cmd::*; bad: { k: [Peek(n), ..], thread: { Thread { tid: n, pouches: Pouches { pouch: Pouch { pk: n, pm: map![n -> 1] } }, .. }, .. } } => { k: [..] }; }",
        "k::rules! { for Machine; use Cmd::*; bad: { k: [Peek(n), ..], sacks: Sacks { bag: { Bag { key: n, m: map![n -> 1] }, .. } } } => { k: [..] }; }",
        "k::rules! { for Machine; use Cmd::*; bad: { k: [Peek(n), ..], pouch: { Pouch { pk: n, pm: map![n -> 1] }, .. } } => { k: [..] }; }",
    ]
    .map(|item| check_error_in(target.path(), NESTED, item));
    expect_test::expect![[r#"
        [
            "error[krs::syntax::rust-syntax]: expected one of: identifier, `::`, `<`, `_`, literal, `const`, `ref`, `mut`, `&`, parentheses, square brackets, `..`, `const`",
            "error[krs::analysis::collection-entry]: the cell `pouch` is a Set collection of `Pouch` instances (`multiplicity = \"*\"`), so its entry is a list of its instances, each an instance record, not one value: no single cell has the content a value would name; write its entry as its instances, `{ Pouch { .. }, .. }`",
            "error[krs::syntax::rust-syntax]: expected one of: identifier, `::`, `<`, `_`, literal, `const`, `ref`, `mut`, `&`, parentheses, square brackets, `..`, `const`",
            "error[krs::analysis::collection-entry]: the rule matches `pouch`, a cell of an instance of the Map collection cell `thread`, and `k`, a cell outside every instance: the rule would match the outer cell beside one instance, and a rule whose cells lie both inside an instance and outside every instance is not supported yet; match the instance through its holder's instance list in a rule for the configuration",
        ]
    "#]]
    .assert_debug_eq(&errors);
}

/// Local patterns over typed collections: a map of Ints and a list of Ints.
const TYPED: &str = r#"
use k::builtin::{Bool, Int, KSequence, List, Map, list, map};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("second")]
    Second(),
    #[k::syntax("front")]
    Front(),
    #[k::syntax("same")]
    Same(),
    #[k::syntax("twin")]
    Twin(),
}

/// The value at 2 of a map of Ints, read by a `let`: an Int.
#[k::function(partial, internal)]
pub fn ValueAtTwo(memory: Term<Map<Int, Int>>) -> Term<Int> {
    let map![2 -> v, ..] = memory;
    v
}

/// The first element of a list of Ints, read by a `let`: an Int.
#[k::function(partial, internal)]
pub fn First(stack: Term<List<Int>>) -> Term<Int> {
    let [x, ..] = stack;
    x
}

/// Whether the values at 2 and 3 are one value.
#[k::function(total, internal)]
pub fn SameAtTwoAndThree(memory: Term<Map<Int, Int>>) -> Term<Bool> {
    k::matches!(memory, map![2 -> v, 3 -> v, ..])
}

/// Whether the list starts with one element twice.
#[k::function(total, internal)]
pub fn StartsTwice(stack: Term<List<Int>>) -> Term<Bool> {
    k::matches!(stack, [x, x, ..])
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub mem: Map<Int, Int>,
    #[k::cell]
    pub stack: List<Int>,
    #[k::cell]
    pub seen: Int,
    #[k::cell]
    pub out: Bool,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            mem: map![1 -> 10, 2 -> 20, 3 -> 20],
            stack: list::concat(list::item(7), list::concat(list::item(7), list::item(8))),
            seen: 0,
            out: false,
        }
    }
}

k::rules! {
    for Machine;
    use ExpSyntax::*;

    second: { k: [Second(), ..], mem: m } => { k: [..], seen: ValueAtTwo(m) };
    front: { k: [Front(), ..], stack: s } => { k: [..], seen: First(s) };
    same: { k: [Same(), ..], mem: m } => { k: [..], out: SameAtTwoAndThree(m) };
    twin: { k: [Twin(), ..], stack: s } => { k: [..], out: StartsTwice(s) };
}
"#;

/// A local pattern matches the value the rule computed, so its binders range over that value's
/// parts: a `let` or a `k::matches!` pattern over a `Map<Int, Int>` or a `List<Int>` binds its
/// entries' values and its elements at `Int`, as the same pattern at a parameter of that type
/// does, and a `let` binder returned at `Int` is accepted.
#[test]
fn a_local_pattern_binds_the_parts_of_a_typed_collection_at_their_types() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "mappatterns", TYPED);
    let k = emitted_k(target.path(), &manifest);
    expect_test::expect![[r#"
        [
            "rule first ( Stack:List ) => ( #let ListItem(X:Int) _ = Stack:List #in X:Int ) [label(org_krs_mappatterns--first)]",
            "rule valueAtTwo ( Memory:Map ) => ( #let 2 |-> V:Int _ = Memory:Map #in V:Int ) [label(org_krs_mappatterns--value_at_two)]",
            "rule sameAtTwoAndThree ( Memory:Map ) => ( 2 |-> V:Int 3 |-> V:Int _ :=K Memory:Map ) [label(org_krs_mappatterns--same_at_two_and_three)]",
            "rule startsTwice ( Stack:List ) => ( ListItem(X:Int) ListItem(X:Int) _ :=K Stack:List ) [label(org_krs_mappatterns--starts_twice)]",
        ]
    "#]].assert_debug_eq(
        &[lines_with(&k, "#let"), lines_with(&k, ":=K")].concat(),
    );
    let outcomes = [
        ("second", "seen"),
        ("front", "seen"),
        ("same", "out"),
        ("twin", "out"),
    ]
    .map(|(program, cell)| {
        format!(
            "{program} => {cell}: {}",
            run_cell(target.path(), &manifest, program, cell)
        )
    });
    expect_test::expect![[r#"
        [
            "second => seen: 20",
            "front => seen: 7",
            "same => out: true",
            "twin => out: true",
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}
