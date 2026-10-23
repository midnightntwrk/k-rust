//! Typed collections end to end: a cell declared `Map<Id, Value>`,
//! `List<Value>`, `Set<Id>`, or `Map<Id, Set<Int>>` checks every term a rule,
//! claim, or initializer writes into it, through every write path, and the
//! emitted K, which erases element types, is the K of the same rules over
//! untyped cells.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Id, Int, KSequence, List, Map, Set, list, map, set};
use k::{KResult, Term};

k::sorts! {
    Stmt;
    Value: KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Skip, Put, PutI, Op, Hold))]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("put {name} {s}")]
    Put { name: Id, s: Stmt },
    #[k::syntax("puti {name} {n}")]
    PutI { name: Id, n: Int },
    #[k::syntax("op {code}")]
    Op { code: Int },
    #[k::syntax("hold {m}")]
    Hold { m: Map },
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub locals: Map<Id, Int>,
    #[k::cell]
    pub depth: Int,
}

#[k::cell]
pub struct Objs {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub obj: Obj,
}

#[k::cell]
pub struct Obj {
    #[k::cell]
    pub oid: Int,
    #[k::cell]
    pub slots: Map<Int, Value>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Value>,
    #[k::cell]
    pub stack: List<Value>,
    #[k::cell]
    pub seen: Set<Id>,
    #[k::cell]
    pub raw: Map,
    #[k::cell]
    pub nested: Map<Id, Set<Int>>,
    #[k::cell(nested)]
    pub frame: Frame,
    #[k::cell(nested)]
    pub objs: Objs,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: map::empty(),
            stack: list::empty(),
            seen: set::empty(),
            raw: map::empty(),
            nested: map::empty(),
            frame: Frame { locals: map::empty(), depth: 0 },
            objs: Objs { obj: Obj { oid: 0, slots: map::empty() } },
        }
    }
}

"#;

/// Every accepted way of writing into and reading from typed cells.
const ACCEPTED: &str = r"
k::rules! {
    for Machine;
    use StmtSyntax::*;

    store_int: { k: [Op(1), Put(name, _), ..], env: e } => { k: [..], env: map::update(e, name, 1) };
    forget: { k: [Op(2), Put(name, _), ..], env: e } => { k: [..], env: map::remove(e, name) };
    raw_store: { k: [Op(3), Put(name, s), ..], raw: r } => { k: [..], raw: map::update(r, name, s) };
    nested_store: { k: [Op(4), PutI(name, n), ..], nested: s } => { k: [..], nested: map::update(s, name, set::item(n)) };
    read_int: { k: [Op(5), Put(name, _), ..], env: { name -> v, .. } } => { k: [v, ..] } where v: Int;
    increment: { k: [Op(6), PutI(name, _), ..], frame: Frame { locals: m, .. } } => { k: [PutI(name, map::get(m, name) + 1), ..] };
    lookup: { k: [Op(7), Put(name, _), ..], env: e } => { k: [map::get(e, name), ..] };
    keys: { k: [Op(8), ..], env: e, seen: _ } => { k: [..], seen: map::keys(e) };
    widen: { k: [Op(9), ..], env: _, frame: Frame { locals: l, .. } } => { k: [..], env: l };
    untyped_cell: { k: [Op(11), ..], raw: r, env: _ } => { k: [..], env: r };
    stash: { k: [Op(12), Hold(m), ..], env: _ } => { k: [..], env: m };
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
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-TYPED\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// Each diagnostic's headline and the source text its caret marks.
fn diagnostics(stderr: &str) -> Vec<(String, String)> {
    let lines = stderr.lines().collect::<Vec<_>>();
    let mut output = Vec::new();
    for (index, line) in lines.iter().enumerate() {
        if !(line.starts_with("error[") || line.starts_with("warning[")) {
            continue;
        }
        // `--> path`, ` |`, `N | source`, ` |   ^^^`.
        let marked = lines
            .get(index + 3)
            .zip(lines.get(index + 4))
            .and_then(|(source, carets)| {
                let source = source.split_once(" | ")?.1;
                let carets = carets.split_once(" | ")?.1;
                let start = carets.find('^')?;
                let width = carets[start..].chars().take_while(|c| *c == '^').count();
                source.get(start..start + width).map(str::to_owned)
            })
            .unwrap_or_default();
        output.push(((*line).to_owned(), marked));
    }
    output
}

/// The rule's body lines in the emitted K, joined.
fn rule(definition: &str, label: &str) -> String {
    let start = definition
        .find(&format!("rule [{label}]:"))
        .unwrap_or_else(|| panic!("no rule {label}:\n{definition}"));
    definition[start..]
        .lines()
        .skip(1)
        .take_while(|line| !line.trim_start().starts_with("rule") && !line.trim().is_empty())
        .map(str::trim)
        .collect::<Vec<_>>()
        .join(" ")
}

/// Typed writes that fit, reads at their element sorts, and untyped writes
/// check; the untyped writes warn at the written term, and the K is the K of
/// untyped cells: element types are erased.
#[test]
fn typed_cells_accept_fitting_writes_and_warn_on_untyped_ones() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "accepted",
        &format!("{PREAMBLE}{ACCEPTED}"),
    );
    let (success, _, check_stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{check_stderr}");
    expect_test::expect![[r#"
        [
            (
                "warning[krs::analysis::untyped-collection]: `m` is matched where no element types are declared, so nothing checks the elements it writes to the cell `env`, declared `Map<Id, Value>`",
                "m",
            ),
            (
                "warning[krs::analysis::untyped-collection]: `r` is matched in the cell `raw`, declared `Map`, so nothing checks the elements it writes to the cell `env`, declared `Map<Id, Value>`",
                "r",
            ),
        ]
    "#]]
    .assert_debug_eq(&diagnostics(&check_stderr));

    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    expect_test::expect![[r#"
        [
            "<k> op 1 ~> put Name:Id _ => .K ... </k> <env> E:Map => E:Map [ Name:Id <- 1 ] </env>",
            "<k> op 4 ~> puti Name:Id N:Int => .K ... </k> <nested> S:Map => S:Map [ Name:Id <- SetItem(N:Int) ] </nested>",
            "<k> op 5 ~> put Name:Id _ => V:Int ... </k> <env> Name:Id |-> V:Int ... </env>",
            "<k> op 6 ~> puti Name:Id _ => puti Name:Id {M:Map [ Name:Id ]}:>Int +Int 1 ... </k> <frame> <locals> M:Map </locals> <depth> _ </depth> </frame>",
            "<k> op 7 ~> put Name:Id _ => {E:Map [ Name:Id ]}:>Value ... </k> <env> E:Map </env>",
        ]
    "#]]
    .assert_debug_eq(&[
        rule(&definition, "store-int"),
        rule(&definition, "nested-store"),
        rule(&definition, "read-int"),
        rule(&definition, "increment"),
        rule(&definition, "lookup"),
    ]);

    // The expanded reference rules check the same: they declare every
    // binder `k::Term<Map>`, and the cells give the types.
    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let reference = package(temporary.path(), "expanded", &expanded);
    let (success, _, reference_stderr) = krs(target.path(), &reference, "check", &[]);
    assert!(success, "{reference_stderr}");
    let headlines = |stderr: &str| {
        diagnostics(stderr)
            .into_iter()
            .map(|(headline, _)| headline)
            .collect::<Vec<_>>()
    };
    assert_eq!(headlines(&reference_stderr), headlines(&check_stderr));
}

fn rules(body: &str) -> String {
    format!("k::rules! {{\n    for Machine;\n    use StmtSyntax::*;\n\n    {body}\n}}\n")
}

/// Every write of an ill-sorted element, and every read that asks for a
/// sort the collection never holds, is rejected at the term, naming the
/// position and its declared type: through nested updates, empty bases,
/// lists, sets, group and instance children, nested collection arguments,
/// `cells!` rules, single-body rules, claims, and initializers.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of rejected rules, each with its expected diagnostic."
)]
fn ill_sorted_elements_are_rejected_at_the_term() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let stored = |term: &str, sort: &str, position: &str, element: &str| {
        format!(
            "error[krs::analysis::collection-element-sort]: `{term}` of sort {sort} is stored as {position}, and {sort} is not {element}"
        )
    };
    let env_value = "a value of the cell `env`, declared `Map<Id, Value>`";
    let cases = [
        (
            "direct",
            rules(
                "probe: { k: [Put(name, s), ..], env: e } => { k: [..], env: map::update(e, name, s) };",
            ),
            stored("s", "Stmt", env_value, "a Value"),
            "s",
        ),
        (
            "nested",
            rules(
                "probe: { k: [Put(name, s), ..], env: e } => { k: [..], env: map::update(map::update(e, name, 0), name, s) };",
            ),
            stored("s", "Stmt", env_value, "a Value"),
            "s",
        ),
        (
            "nested-constructor",
            rules(
                "probe: { k: [Put(name, _), ..], env: e } => { k: [..], env: map::update(map::update(e, name, 0), name, Skip()) };",
            ),
            stored("Skip(..)", "Stmt", env_value, "a Value"),
            "Skip",
        ),
        (
            "empty-base",
            rules(
                "probe: { k: [Put(name, s), ..], env: _ } => { k: [..], env: map::update(map::empty(), name, s) };",
            ),
            stored("s", "Stmt", env_value, "a Value"),
            "s",
        ),
        (
            "key",
            rules(
                "probe: { k: [Skip(), ..], env: e } => { k: [..], env: map::update(e, 5, 1) };",
            ),
            stored(
                "5",
                "Int",
                "a key of the cell `env`, declared `Map<Id, Value>`",
                "an Id",
            ),
            "5",
        ),
        (
            "list",
            rules(
                "probe: { k: [Put(_, s), ..], stack: l } => { k: [..], stack: list::concat(list::item(s), l) };",
            ),
            stored(
                "s",
                "Stmt",
                "an element of the cell `stack`, declared `List<Value>`",
                "a Value",
            ),
            "s",
        ),
        (
            "set",
            rules(
                "probe: { k: [Put(_, s), ..], seen: x } => { k: [..], seen: set::concat(set::item(s), x) };",
            ),
            stored(
                "s",
                "Stmt",
                "an element of the cell `seen`, declared `Set<Id>`",
                "an Id",
            ),
            "s",
        ),
        (
            "group-update",
            rules(
                "probe: { k: [Put(name, s), ..], frame: f @ Frame { locals: m, .. } } => { k: [..], frame: Frame { locals: map::update(m, name, s), ..f } };",
            ),
            stored(
                "s",
                "Stmt",
                "a value of the cell `locals`, declared `Map<Id, Int>`",
                "an Int",
            ),
            "s",
        ),
        (
            "instance",
            rules(
                "probe: { k: [Put(_, s), ..], obj: { o @ Obj { slots: m, .. }, .. } } => { k: [..], obj: { Obj { slots: map::update(m, 1, s), ..o }, .. } };",
            ),
            stored(
                "s",
                "Stmt",
                "a value of the cell `slots`, declared `Map<Int, Value>`",
                "a Value",
            ),
            "s",
        ),
        (
            "nested-argument",
            rules(
                "probe: { k: [Put(name, s), ..], nested: n } => { k: [..], nested: map::update(n, name, set::item(s)) };",
            ),
            stored(
                "s",
                "Stmt",
                "an element of a value of the cell `nested`, declared `Map<Id, Set<Int>>`",
                "an Int",
            ),
            "s",
        ),
        (
            "typed-flow",
            rules(
                "probe: { k: [Skip(), ..], env: e, frame: Frame { locals: _, depth: d } } => { k: [..], frame: Frame { locals: e, depth: d } };",
            ),
            "error[krs::analysis::collection-element-sort]: `e`, matched as the cell `env`, has type `Map<Id, Value>`, which does not fit the cell `locals`, declared `Map<Id, Int>`: Value is not an Int".to_owned(),
            "e",
        ),
        (
            "read-narrowing",
            rules(
                "probe: { k: [Put(name, _), ..], env: { name -> v, .. } } => { k: [..] } where v: Stmt;",
            ),
            "error[krs::analysis::collection-element-sort]: `v` is read as a value of the cell `env`, declared `Map<Id, Value>`, but `where v: Stmt` asks for a Stmt, which no Value is".to_owned(),
            "env",
        ),
        (
            "read-occurrence",
            rules(
                "probe: { k: [PutI(name, _), ..], env: { name -> v, .. } } => { k: [Put(name, v), ..] };",
            ),
            "error[krs::analysis::collection-element-sort]: `v` of sort Stmt is read as a value of the cell `env`, declared `Map<Id, Value>`, and Stmt is not a Value".to_owned(),
            "env",
        ),
        (
            "get",
            rules(
                "probe: { k: [Put(name, _), ..], env: e } => { k: [Put(name, map::get(e, name)), ..] };",
            ),
            "error[krs::analysis::collection-element-sort]: `map::get(..)` reads a value of the cell `env`, declared `Map<Id, Value>`, which is always a Value and never a Stmt".to_owned(),
            "map::get",
        ),
        (
            "contains",
            "k::rules! {\n    for Machine;\n    use StmtSyntax::*;\n\n    #[k::requires(set::contains(s, x))]\n    probe: { k: [Put(_, s), ..], seen: x } => { k: [..] };\n}\n".to_owned(),
            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt reads an element of the cell `seen`, declared `Set<Id>`, which is always an Id and never a Stmt".to_owned(),
            "s",
        ),
        (
            "cells-rule",
            "#[k::rule]\npub fn probe(\n    name: Term<Id>,\n    s: Term<Stmt>,\n    e: Term<Map>,\n    k::cells! { k: k::configuration::KCell(StmtSyntax::Put(name, s), tail @ ..), env: k::configuration::Cell(e), state @ .. }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(..tail), env: k::configuration::Cell(map::update(e, name, s)), ..state }\n}\n".to_owned(),
            stored("s", "Stmt", env_value, "a Value"),
            "s",
        ),
        (
            "single-body",
            "#[k::rule]\npub fn probe(\n    name: Term<Id>,\n    s: Term<Stmt>,\n    k::cells! { k: k::configuration::KCell(k::rewrite!(StmtSyntax::Put(name, s) => ()), ..), env: k::configuration::Cell(map![name -> k::rewrite!(_ => s), ..]), .. }: Machine,\n) {}\n".to_owned(),
            stored("s", "Stmt", env_value, "a Value"),
            "k::rewrite!(_ => s)",
        ),
        (
            "claim-left",
            "k::claims! {\n    for Machine;\n    use StmtSyntax::*;\n\n    #[k::claim(all_paths)]\n    probe: { k: [Put(name, s)], env: map::update(map::empty(), name, s) } => { k: [] };\n}\n".to_owned(),
            stored("s", "Stmt", env_value, "a Value"),
            "s",
        ),
    ];
    for (name, source, headline, marked) in cases {
        let manifest = package(temporary.path(), name, &format!("{PREAMBLE}{source}"));
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: krs check unexpectedly passed:\n{stderr}");
        assert_eq!(
            diagnostics(&stderr).first(),
            Some(&(headline, marked.to_owned())),
            "{name}:\n{stderr}"
        );
    }
    // An initializer's values are checked like a rule's results.
    for (name, from, to, headline, marked) in [
        (
            "initializer-map",
            "slots: map::empty() }",
            "slots: k::map![1 -> StmtSyntax::Skip()] }",
            stored(
                "Skip(..)",
                "Stmt",
                "a value of the cell `slots`, declared `Map<Int, Value>`",
                "a Value",
            ),
            "StmtSyntax::Skip",
        ),
        (
            "initializer-list",
            "stack: list::empty(),",
            "stack: list::item(StmtSyntax::Skip()),",
            stored(
                "Skip(..)",
                "Stmt",
                "an element of the cell `stack`, declared `List<Value>`",
                "a Value",
            ),
            "StmtSyntax::Skip",
        ),
        (
            "one-argument-map",
            "pub raw: Map,",
            "pub raw: Map<Id>,",
            "error[krs::analysis::collection-element-sort]: the cell `raw` is declared `Map<Id>`: a `Map` takes a key and a value type, `Map<K, V>`, or none, `Map`".to_owned(),
            "Map<Id>",
        ),
    ] {
        assert!(PREAMBLE.contains(from), "{name}");
        let manifest = package(temporary.path(), name, &PREAMBLE.replace(from, to));
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: krs check unexpectedly passed:\n{stderr}");
        assert_eq!(
            diagnostics(&stderr).first(),
            Some(&(headline, marked.to_owned())),
            "{name}:\n{stderr}"
        );
    }
}
