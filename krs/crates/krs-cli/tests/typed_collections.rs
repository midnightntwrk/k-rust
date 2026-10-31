//! Typed collections end to end: a cell declared `Map<Id, Value>`,
//! `List<Value>`, `Set<Id>`, or `Map<Id, Set<Int>>`, a constructor field, and
//! a function parameter or result check every term a rule, claim, equation,
//! or initializer writes into them, through every write path, and the
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
#[k::precedence((Skip, Put, PutI, Op, Hold, Keep))]
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
    #[k::syntax("keep {m}")]
    Keep { m: Map<Id, Value> },
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

/// Stores a statement in a map: its result declares no element types.
#[k::function(total, internal)]
pub fn Put3(m: Term<Map>, key: Term<Id>, value: Term<Stmt>) -> Term<Map> {
    map::update(m, key, value)
}

/// Stores an integer in a map of values: its signature states the types.
#[k::function(total, internal)]
pub fn Store(m: Term<Map<Id, Value>>, key: Term<Id>, value: Term<Int>) -> Term<Map<Id, Value>> {
    map::update(m, key, value)
}

/// Pushes an integer on a list of values, written in brackets.
#[k::function(total, internal)]
pub fn Push(l: Term<List<Value>>, v: Term<Int>) -> Term<List<Value>> {
    [v, ..l]
}

/// The keys of a map of sets of integers, read through a typed lookup.
#[k::function(total, internal, sort = Set<Int>, syntax = "members({sets}, {key})")]
pub struct Members {
    pub sets: Term<Map<Id, Set<Int>>>,
    pub key: Term<Id>,
}

#[k::equation]
fn members(k::term![Members(sets, key)]: Term<Set>) -> Term<Set> {
    set::union(map::get(sets, key), set::item(0))
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
    typed_function: { k: [Op(13), Put(name, _), ..], env: e } => { k: [..], env: Store(e, name, 5) };
    typed_stash: { k: [Op(14), ..], env: e } => { k: [Keep(e), ..] };
    typed_restore: { k: [Op(15), Keep(m), ..], env: _ } => { k: [..], env: m };
    typed_push: { k: [Op(17), ..], stack: l } => { k: [..], stack: Push(l, 1) };
    typed_nested: { k: [Op(16), Put(name, _), ..], nested: n } => { k: [..], nested: map::update(n, name, Members(n, name)) };
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

/// Typed writes that fit, reads at their element sorts, and typed function
/// results and constructor fields check without a diagnostic, and the K is
/// the K of untyped cells: element types are erased.
#[test]
fn typed_positions_accept_fitting_writes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "accepted",
        &format!("{PREAMBLE}{ACCEPTED}"),
    );
    let (success, _, check_stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{check_stderr}");
    assert_eq!(diagnostics(&check_stderr), [], "{check_stderr}");

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
            "<k> op 13 ~> put Name:Id _ => .K ... </k> <env> E:Map => store ( E:Map , Name:Id , 5 ) </env>",
            "<k> op 16 ~> put Name:Id _ => .K ... </k> <nested> N:Map => N:Map [ Name:Id <- members ( N:Map , Name:Id ) ] </nested>",
        ]
    "#]]
    .assert_debug_eq(&[
        rule(&definition, "store-int"),
        rule(&definition, "nested-store"),
        rule(&definition, "read-int"),
        rule(&definition, "increment"),
        rule(&definition, "lookup"),
        rule(&definition, "typed-function"),
        rule(&definition, "typed-nested"),
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

/// A key a pattern looks up, computed by a read of an untyped map: K's read
/// returns a `KItem`, which KRS projects to the sort the position needs, and no
/// native route reads a projection on a left side (finding NT-11-1). The
/// projection denotes the read where the read has that sort, so the sentence
/// requires that instead: at a typed map's key root the key is the read, as a
/// map holds it, with the guard `isId(read)` (S2 of NT-18's review); below a
/// function the projected read is the function's argument, which matching
/// would evaluate before the guard, so the application is a fresh name the
/// condition equates with it after `isSet(read)` holds (M2). An equation's
/// function context guards its keys in the equation's condition as a rule
/// does (M1): `k::project!(Int, n)` is the key `n` where `isInt(n)` holds; and
/// since the equation matches the context as written, a key that computes
/// there is a fresh name too (NT-18-2). `krs check` passes.
#[test]
fn a_key_computed_by_a_projected_read_is_guarded() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "typed-key",
        &format!(
            "{PREAMBLE}{}{}",
            concat!(
                "#[k::function(partial, sort = k::KItem, syntax = \"rd({n})\")]\n",
                "pub struct Rd {\n    pub n: Term<k::KItem>,\n}\n\n",
                "#[k::equation]\n",
                "fn rd(\n",
                "    n: Term<k::KItem>,\n",
                "    v: Term<k::KItem>,\n",
                "    k::term![Rd(n)]: Term<k::KItem>,\n",
                "    k::cells! { raw: k::configuration::Cell(k::map![k::project!(Int, n) -> v, ..]), .. }: Machine,\n",
                ") -> Term<k::KItem> {\n    v\n}\n\n",
                "#[k::function(partial, sort = k::KItem, syntax = \"rn({n})\")]\n",
                "pub struct Rn {\n    pub n: Term<k::KItem>,\n}\n\n",
                "#[k::equation]\n",
                "fn rn(\n",
                "    n: Term<k::KItem>,\n",
                "    v: Term<k::KItem>,\n",
                "    k::term![Rn(n)]: Term<k::KItem>,\n",
                "    k::cells! { raw: k::configuration::Cell(k::map![k::builtin::int::add(k::project!(Int, n), 1) -> v, ..]), .. }: Machine,\n",
                ") -> Term<k::KItem> {\n    v\n}\n\n",
            ),
            rules(concat!(
                "typed_key: { k: [Op(20), Hold(m), ..], env: { map::get(m, 1) -> v, .. } } => { k: [v, ..] };\n",
                "    sized_key: { k: [Op(21), Hold(m), ..], raw: { set::size(map::get(m, 1)) -> v, .. } } => { k: [v, ..] };",
            ))
        ),
    );
    let (success, _, check_stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{check_stderr}");
    assert_eq!(diagnostics(&check_stderr), [], "{check_stderr}");
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    // An equation, its label (a hash of the sentence) left out.
    let equation = |head: &str| {
        let text = definition
            .lines()
            .skip_while(|line| !line.contains(head))
            .take(3)
            .map(str::trim)
            .collect::<Vec<_>>()
            .join(" ");
        text.split(" [label(").next().unwrap_or_default().to_owned()
    };
    expect_test::expect![[r#"
        [
            "<k> op 20 ~> hold M:Map => V:Value ... </k> <env> (M:Map [ 1 ]) |-> V:Value ... </env> requires isId(M:Map [ 1 ])",
            "<k> op 21 ~> hold M:Map => V:KItem ... </k> <raw> Krs_Instance1:Int |-> V:KItem ... </raw> requires isSet(M:Map [ 1 ]) andThenBool (Krs_Instance1:Int ==K size({M:Map [ 1 ]}:>Set))",
            "rule [[ rd ( N:KItem ) => V:KItem ]] <raw> N:KItem |-> V:KItem ... </raw> requires isInt(N:KItem)",
            "rule [[ rn ( N:KItem ) => V:KItem ]] <raw> Krs_Instance1:Int |-> V:KItem ... </raw> requires isInt(N:KItem) andThenBool (Krs_Instance1:Int ==K ({N:KItem}:>Int +Int 1))",
        ]
    "#]]
    .assert_debug_eq(&[
        rule(&definition, "typed-key").trim_end_matches(" endmodule"),
        rule(&definition, "sized-key").trim_end_matches(" endmodule"),
        &equation("rule [[ rd"),
        &equation("rule [[ rn"),
    ]);
}

/// Every write of an ill-sorted element or of a collection whose element
/// types nothing declares, and every read that asks for a sort the
/// collection never holds, is rejected at the term, naming the position and
/// its declared type: through nested updates, empty bases, lists, sets,
/// group and instance children, nested collection arguments, constructor
/// fields, function parameters and results, equations, `cells!` rules,
/// single-body rules, claims, and initializers.
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
    let env = "the cell `env`, declared `Map<Id, Value>`";
    let untyped = |reason: &str, position: &str| {
        format!(
            "error[krs::analysis::untyped-collection]: {reason}, so nothing checks the elements it writes to {position}"
        )
    };
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
            "Stmt",
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
            // The binder list declares `s`, so the declaration is what the
            // value position refuses.
            "error[krs::analysis::incompatible-binder]: binder `s` is declared `Stmt`, but an occurrence needs `Value`".to_owned(),
            "Stmt",
        ),
        (
            "untyped-cell",
            rules("probe: { k: [Op(11), ..], raw: r, env: _ } => { k: [..], env: r };"),
            untyped("`r` is matched in the cell `raw`, declared `Map`", env),
            "r",
        ),
        (
            "untyped-field",
            rules("probe: { k: [Op(12), Hold(m), ..], env: _ } => { k: [..], env: m };"),
            untyped("`m` is matched in the field `m` of `Hold`, declared `Map`", env),
            "m",
        ),
        (
            "untyped-argument",
            rules(
                "probe: { k: [Put(name, _), ..], raw: r, env: _ } => { k: [..], env: Store(r, name, 1) };",
            ),
            untyped(
                "`r` is matched in the cell `raw`, declared `Map`",
                "the parameter `m` of `Store`, declared `Map<Id, Value>`",
            ),
            "r",
        ),
        (
            "typed-parameter",
            rules(
                "probe: { k: [Put(name, s), ..], env: e } => { k: [..], env: Store(map::update(e, name, s), name, 1) };",
            ),
            stored(
                "s",
                "Stmt",
                "a value of the parameter `m` of `Store`, declared `Map<Id, Value>`",
                "a Value",
            ),
            "s",
        ),
        (
            "bracket-parameter",
            rules(
                "probe: { k: [Put(_, s), ..], stack: l } => { k: [..], stack: Push([s, ..l], 1) };",
            ),
            stored(
                "s",
                "Stmt",
                "an element of the parameter `l` of `Push`, declared `List<Value>`",
                "a Value",
            ),
            "s",
        ),
        (
            "typed-field",
            rules(
                "probe: { k: [Put(name, s), ..], env: e } => { k: [Keep(map::update(e, name, s)), ..] };",
            ),
            stored(
                "s",
                "Stmt",
                "a value of the field `m` of `Keep`, declared `Map<Id, Value>`",
                "a Value",
            ),
            "s",
        ),
        (
            "typed-result",
            rules(
                "probe: { k: [Put(name, _), ..], seen: _, nested: n } => { k: [..], seen: Members(n, name) };",
            ),
            "error[krs::analysis::collection-element-sort]: `Members(..)` has type `Set<Int>`, which does not fit the cell `seen`, declared `Set<Id>`: Int is not an Id".to_owned(),
            "Members",
        ),
        (
            "keys-of-built",
            rules(
                "probe: { k: [Put(name, s), ..], seen: _ } => { k: [..], seen: map::keys(map::update(map::empty(), s, 1)) };",
            ),
            stored(
                "s",
                "Stmt",
                "a key of the map whose keys `map::keys(..)` writes to the cell `seen`, declared `Set<Id>`",
                "an Id",
            ),
            "s",
        ),
        (
            "from-built-list",
            rules(
                "probe: { k: [Put(name, s), ..], seen: _ } => { k: [..], seen: set::from_list([name, s]) };",
            ),
            stored(
                "s",
                "Stmt",
                "an element of the list whose elements `set::from_list(..)` writes to the cell `seen`, declared `Set<Id>`",
                "an Id",
            ),
            "s",
        ),
        (
            "keys-of-bare",
            rules("probe: { k: [Skip(), ..], seen: _, raw: r } => { k: [..], seen: map::keys(r) };"),
            untyped(
                "`map::keys(..)` reads a collection whose element types are not declared",
                "the cell `seen`, declared `Set<Id>`",
            ),
            "map::keys",
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
        (
            "function-equation",
            "key: Term<Id>, value: Term<Int>)",
            "key: Term<Id>, value: Term<Stmt>)",
            stored(
                "value",
                "Stmt",
                "a value of the result of `Store`, declared `Map<Id, Value>`",
                "a Value",
            ),
            "value",
        ),
        (
            "bracket-result",
            "l: Term<List<Value>>, v: Term<Int>)",
            "l: Term<List<Value>>, v: Term<Stmt>)",
            stored(
                "v",
                "Stmt",
                "an element of the result of `Push`, declared `List<Value>`",
                "a Value",
            ),
            "v",
        ),
        (
            "parameter-arity",
            "pub sets: Term<Map<Id, Set<Int>>>,",
            "pub sets: Term<Map<Id>>,",
            "error[krs::analysis::collection-element-sort]: the parameter `sets` of `Members` is declared `Map<Id>`: a `Map` takes a key and a value type, `Map<K, V>`, or none, `Map`".to_owned(),
            "Id",
        ),
        (
            "binder-declaration",
            "#[k::equation]\nfn members(k::term![Members(sets, key)]: Term<Set>) -> Term<Set> {",
            "#[k::equation]\nfn members(k::term![Members(sets, key)]: Term<Set<Int>>) -> Term<Set> {",
            "error[krs::syntax::parametric-collection-sort]: a binder's or term's sort names only the sort `Set`: a binder takes the types of its elements from the position that matches it, and a cell, a constructor field, or a function signature declares them; write `Set` without generic arguments".to_owned(),
            "Set",
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

/// A three-argument user function whose result is written into a map cell
/// is a term like any other, never a misread map update: its signature
/// decides, so an untyped result is rejected for being untyped, and a
/// typed one of the same shape (`Store`, in the accepted rules) fits.
#[test]
fn a_user_function_result_is_typed_by_its_signature() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "user-function",
        &format!(
            "{PREAMBLE}{}",
            rules(
                "probe: { k: [Put(name, s), ..], env: e } => { k: [..], env: Put3(e, name, s) };"
            )
        ),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(!success, "{stderr}");
    assert_eq!(
        diagnostics(&stderr),
        [(
            "error[krs::analysis::untyped-collection]: `Put3(..)` returns an untyped `Map`, so nothing checks the elements it writes to the cell `env`, declared `Map<Id, Value>`".to_owned(),
            "Put3".to_owned()
        )]
    );
}

/// A reading operation whose operand the sentence builds is checked
/// through: `map::keys(m)` at `Set<K>` checks `m` at `Map<K, KItem>`,
/// `set::from_list(l)` at `Set<T>` checks `l` at `List<T>`, and so on, the
/// discarded parts unconstrained, in readable rules, `cells!` rules, claims,
/// initializers, typed arguments, and typed function results; a binder
/// stored there narrows as at any element, and one only at a discarded part
/// is a `KItem`.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One package of built collections, with the K each emits."
)]
fn built_collections_are_checked_through_reading_operations() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let library = format!(
        "{}{}{}",
        PREAMBLE.replace(
            "stack: list::empty(),",
            "stack: set::to_list(set::item(1)),"
        ),
        rules(
            "keys: { k: [Op(1), Put(name, s), ..], seen: _ } => { k: [..], seen: map::keys(map::update(map::empty(), name, s)) };
    empty_keys: { k: [Op(2), ..], seen: _ } => { k: [..], seen: map::keys(map::empty()) };
    from_item: { k: [Op(3), Put(name, _), ..], seen: _ } => { k: [..], seen: set::from_list(list::item(name)) };
    from_brackets: { k: [Op(4), Put(name, _), ..], seen: _ } => { k: [..], seen: set::from_list([name, name]) };
    values: { k: [Op(5), Put(name, _), ..], stack: _ } => { k: [..], stack: map::values(map::update(map::empty(), name, 1)) };
    to_list: { k: [Op(6), ..], stack: _ } => { k: [..], stack: set::to_list(set::item(1)) };
    nested: { k: [Op(7), Put(name, _), ..], nested: n } => { k: [..], nested: map::update(n, name, map::keys(map::update(map::empty(), 0, Skip()))) };
    union: { k: [Op(8), Put(name, s), ..], seen: x } => { k: [..], seen: set::union(x, map::keys(map::update(map::empty(), name, s))) };
    counted: { k: [Op(9), Put(name, _), ..], raw: r } => { k: [..], raw: map::update(r, name, Count(set::from_list([name]))) };
    get_nested: { k: [Op(10), Put(name, _), ..], nested: n } => { k: [..], nested: map::update(n, name, map::get(map::update(map::empty(), 1, set::item(2)), 1)) };
    choose: { k: [Op(11), Put(name, _), ..], seen: _ } => { k: [..], seen: k::builtin::kequal::ite(true, map::keys(map::update(map::empty(), name, 0)), set::empty()) };
    narrow: { k: [Op(12), Put(name, _), ..], stack: [x, ..], nested: n } => { k: [..], nested: map::update(n, name, set::from_list([x])) };
    discarded: { k: [Op(13), Put(name, _), ..], raw: { name -> y, .. }, seen: _ } => { k: [..], seen: map::keys(map::update(map::empty(), name, y)) };"
        ),
        r"
/// The number of distinct identifiers.
#[k::function(total, internal)]
pub fn Count(xs: Term<Set<Id>>) -> Term<Int> {
    set::size(xs)
}

/// Two identifiers as a set.
#[k::function(total, internal)]
pub fn Both(a: Term<Id>, b: Term<Id>) -> Term<Set<Id>> {
    set::from_list([a, b])
}

#[k::rule]
pub fn cells_keys(
    name: Term<Id>,
    s: Term<Stmt>,
    k::cells! { k: k::configuration::KCell(StmtSyntax::Op(14), StmtSyntax::Put(name, s), tail @ ..), seen: k::configuration::Cell(_), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), seen: k::configuration::Cell(map::keys(map::update(map::empty(), name, s))), ..state }
}

k::claims! {
    for Machine;
    use StmtSyntax::*;

    #[k::claim(all_paths)]
    keys_claim: { k: [Op(1), Put(name, s)], seen: _ } => { k: [], seen: map::keys(map::update(map::empty(), name, s)) };
}
",
    );
    let manifest = package(temporary.path(), "built", &library);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");
    assert_eq!(diagnostics(&stderr), [], "{stderr}");
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
            "<k> op 1 ~> put Name:Id S:Stmt => .K ... </k> <seen> _ => keys(.Map [ Name:Id <- S:Stmt ]) </seen>",
            "<k> op 2 => .K ... </k> <seen> _ => keys(.Map) </seen>",
            "<k> op 3 ~> put Name:Id _ => .K ... </k> <seen> _ => List2Set(ListItem(Name:Id)) </seen>",
            "<k> op 4 ~> put Name:Id _ => .K ... </k> <seen> _ => List2Set(ListItem(Name:Id) ListItem(Name:Id)) </seen>",
            "<k> op 5 ~> put Name:Id _ => .K ... </k> <stack> _ => values(.Map [ Name:Id <- 1 ]) </stack> endmodule",
            "<k> op 6 => .K ... </k> <stack> _ => Set2List(SetItem(1)) </stack>",
            "<k> op 7 ~> put Name:Id _ => .K ... </k> <nested> N:Map => N:Map [ Name:Id <- keys(.Map [ 0 <- skip ]) ] </nested>",
            "<k> op 8 ~> put Name:Id S:Stmt => .K ... </k> <seen> X:Set => X:Set |Set keys(.Map [ Name:Id <- S:Stmt ]) </seen>",
            "<k> op 9 ~> put Name:Id _ => .K ... </k> <raw> R:Map => R:Map [ Name:Id <- count ( List2Set(ListItem(Name:Id)) ) ] </raw>",
            "<k> op 10 ~> put Name:Id _ => .K ... </k> <nested> N:Map => N:Map [ Name:Id <- {.Map [ 1 <- SetItem(2) ] [ 1 ]}:>Set ] </nested>",
            "<k> op 11 ~> put Name:Id _ => .K ... </k> <seen> _ => #if true #then keys(.Map [ Name:Id <- 0 ]) #else .Set #fi </seen>",
            "<k> op 12 ~> put Name:Id _ => .K ... </k> <stack> ListItem(X:Int) Krs_RestStack:List </stack> <nested> N:Map => N:Map [ Name:Id <- List2Set(ListItem(X:Int)) ] </nested>",
            "<k> op 13 ~> put Name:Id _ => .K ... </k> <raw> Name:Id |-> Y:KItem ... </raw> <seen> _ => keys(.Map [ Name:Id <- Y:KItem ]) </seen>",
            "<k> op 14 ~> put Name:Id S:Stmt ~> Tail:K => .K ~> Tail:K </k> <seen> _ => keys(.Map [ Name:Id <- S:Stmt ]) </seen>",
        ]
    "#]].assert_debug_eq(
        &[
            "keys",
            "empty-keys",
            "from-item",
            "from-brackets",
            "values",
            "to-list",
            "nested",
            "union",
            "counted",
            "get-nested",
            "choose",
            "narrow",
            "discarded",
            "cells_keys",
        ]
        .map(|label| rule(&definition, label)),
    );
    let both = definition
        .lines()
        .find(|line| line.contains("rule both"))
        .unwrap_or_else(|| panic!("{definition}"));
    assert!(
        both.contains("List2Set(ListItem(A:Id) ListItem(B:Id))"),
        "{both}"
    );
}

/// Every kind of term at a typed element position whose sort is not the
/// element sort is `collection-element-sort`, naming the term, its sort, and
/// the position: tokens, `k::anonymous!`, operator expressions, sort tests,
/// a literal rewrite side, and initializer values; a probe of any kind into
/// a typed collection must share a sort with its elements. Elsewhere a
/// mis-sorted term stays `invalid-term`, naming both sorts.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of rejected terms, each with its expected diagnostic."
)]
fn every_term_kind_at_an_element_position_names_the_position() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let stored = |term: &str, sort: &str, position: &str, element: &str| {
        format!(
            "error[krs::analysis::collection-element-sort]: `{term}` of sort {sort} is stored as {position}, and {sort} is not {element}"
        )
    };
    let read = |term: &str, sort: &str, position: &str, element: &str| {
        format!(
            "error[krs::analysis::collection-element-sort]: `{term}` of sort {sort} reads {position}, which is always {element} and never {}",
            if sort.starts_with(['A', 'E', 'I', 'O', 'U']) {
                format!("an {sort}")
            } else {
                format!("a {sort}")
            }
        )
    };
    let stack = "an element of the cell `stack`, declared `List<Value>`";
    let env_value = "a value of the cell `env`, declared `Map<Id, Value>`";
    let env_key = "a key of the cell `env`, declared `Map<Id, Value>`";
    let seen = "an element of the cell `seen`, declared `Set<Id>`";
    let probe = |head: &str, result: &str| {
        rules(&format!(
            "probe: {{ k: [{head}, ..], stack: l, env: e, seen: x }} => {{ k: [..], {result} }};"
        ))
    };
    let mut cases = vec![
        (
            "id-in-list",
            probe("Skip()", "stack: list::item(k::id!(\"$x\"))"),
            stored("k::id!(..)", "Id", stack, "a Value"),
            "\"$x\"",
        ),
        (
            "id-in-brackets",
            probe("Skip()", "stack: [k::id!(\"$x\"), ..l]"),
            stored("k::id!(..)", "Id", stack, "a Value"),
            "\"$x\"",
        ),
        (
            "bytes-in-set",
            probe("Skip()", "seen: set::item(k::bytes!(b\"a\"))"),
            stored("k::bytes!(..)", "Bytes", seen, "an Id"),
            "b\"a\"",
        ),
        (
            "bytes-as-value",
            probe("Put(name, _)", "env: map::update(e, name, k::bytes!(b\"ab\"))"),
            stored("k::bytes!(..)", "Bytes", env_value, "a Value"),
            "b\"ab\"",
        ),
        (
            "bytes-as-key",
            probe("Skip()", "env: map::update(e, k::bytes!(b\"k\"), 1)"),
            stored("k::bytes!(..)", "Bytes", env_key, "an Id"),
            "b\"k\"",
        ),
        (
            "concatenation",
            probe("Skip()", "stack: [\"a\" + \"b\", ..l]"),
            stored(".. + ..", "String", stack, "a Value"),
            "+",
        ),
        (
            "comparison",
            probe("Skip()", "stack: [1 == 2, ..l]"),
            stored(".. == ..", "Bool", stack, "a Value"),
            "==",
        ),
        (
            "projection",
            probe("Put(_, s)", "stack: [k::project!(Stmt, s), ..l]"),
            stored("k::project!(Stmt, ..)", "Stmt", stack, "a Value"),
            "k::project!(Stmt, s)",
        ),
        (
            "sort-test",
            probe("Put(_, s)", "stack: [k::is!(Stmt, s), ..l]"),
            stored("k::is!(Stmt, ..)", "Bool", stack, "a Value"),
            "k::is!(Stmt, s)",
        ),
        (
            "anonymous",
            "k::claims! {\n    for Machine;\n    use StmtSyntax::*;\n\n    #[k::claim(all_paths)]\n    probe: { k: [Put(name, _)], env: map::update(map::empty(), name, k::anonymous!(Stmt, \"_S\")) } => { k: [] };\n}\n".to_owned(),
            stored("k::anonymous!(..)", "Stmt", env_value, "a Value"),
            "\"_S\"",
        ),
        (
            "rewrite-side",
            "#[k::rule]\npub fn probe(\n    k::cells! { k: k::configuration::KCell(k::rewrite!(StmtSyntax::Skip() => ()), ..), env: k::configuration::Cell(map![k::id!(\"$x\") -> k::rewrite!(_ => true), ..]), .. }: Machine,\n) {}\n".to_owned(),
            stored("true", "Bool", env_value, "a Value"),
            "true",
        ),
        (
            "read-bytes",
            "k::rules! {\n    for Machine;\n    use StmtSyntax::*;\n\n    #[k::requires(set::contains(k::bytes!(b\"a\"), x))]\n    probe: { k: [Skip(), ..], seen: x } => { k: [..] };\n}\n".to_owned(),
            read("k::bytes!(..)", "Bytes", seen, "an Id"),
            "b\"a\"",
        ),
        (
            "remove-bytes",
            probe("Skip()", "env: map::remove(e, k::bytes!(b\"a\"))"),
            read("k::bytes!(..)", "Bytes", env_key, "an Id"),
            "b\"a\"",
        ),
        (
            "remove-sum",
            probe("Skip()", "env: map::remove(e, 1 + 2)"),
            read(".. + ..", "Int", env_key, "an Id"),
            "+",
        ),
        (
            "in-keys-comparison",
            "k::rules! {\n    for Machine;\n    use StmtSyntax::*;\n\n    #[k::requires(map::in_keys(1 == 2, e))]\n    probe: { k: [Skip(), ..], env: e } => { k: [..] };\n}\n".to_owned(),
            read(".. == ..", "Bool", env_key, "an Id"),
            "==",
        ),
        (
            "field",
            probe("Skip()", "k: [PutI(k::bytes!(b\"x\"), 1), ..]").replace("k: [..], k:", "k:"),
            "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-TYPED::probe (rule): builtin token `b\"\\x78\"` of sort Bytes is not admissible at sort Id".to_owned(),
            "b\"x\"",
        ),
    ];
    for (name, from, to, headline, marked) in [
        (
            "initializer-comparison",
            "stack: list::empty(),",
            "stack: list::item(1 == 2),",
            stored(".. == ..", "Bool", stack, "a Value"),
            "==",
        ),
        (
            "initializer-map-comparison",
            "slots: map::empty() }",
            "slots: k::map![1 -> 1 == 2] }",
            stored(
                ".. == ..",
                "Bool",
                "a value of the cell `slots`, declared `Map<Int, Value>`",
                "a Value",
            ),
            "==",
        ),
    ] {
        assert!(PREAMBLE.contains(from), "{name}");
        cases.push((
            name,
            format!("{}\n", PREAMBLE.replace(from, to)),
            headline,
            marked,
        ));
    }
    let mut mismatches = Vec::new();
    for (name, source, headline, marked) in cases {
        let library = if source.starts_with('\n') {
            source
        } else {
            format!("{PREAMBLE}{source}")
        };
        let manifest = package(temporary.path(), name, &library);
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        let first = diagnostics(&stderr).into_iter().next();
        if success || first != Some((headline, marked.to_owned())) {
            mismatches.push(format!("{name}: {first:?}\n{stderr}"));
        }
    }
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));

    // A probe of the element sort is found, whatever kind of term it is.
    let manifest = package(
        temporary.path(),
        "fitting-probes",
        &format!(
            "{PREAMBLE}{}",
            "k::rules! {\n    for Machine;\n    use StmtSyntax::*;\n\n    #[k::requires(set::contains(k::id!(\"$x\"), x))]\n    probe: { k: [Skip(), ..], seen: x, env: e } => { k: [..], env: map::remove(e, k::id!(\"$x\")) };\n}\n"
        ),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");
}

/// The initializer with `parameters` after `pgm`, and `fields` replacing the
/// `k`, `env`, and `stack` values.
fn initializer_with(parameters: &str, k: &str, env: &str, stack: &str) -> String {
    let source = PREAMBLE
        .replace(
            "pgm: Stmt) -> Self {",
            &format!("pgm: Stmt, {parameters}) -> Self {{"),
        )
        .replace(
            "            k: k::k![pgm],",
            &format!("            k: {k},"),
        )
        .replace(
            "            env: map::empty(),",
            &format!("            env: {env},"),
        )
        .replace(
            "            stack: list::empty(),",
            &format!("            stack: {stack},"),
        );
    assert!(source.contains(parameters) && source.contains(stack));
    source
}

/// A configuration variable is a binder of its `#[k::init]` parameter's
/// type, element types included, as a typed function's parameter is: every
/// place the initializer puts a typed-collection variable is a checked flow,
/// a bare-collection variable is an untyped source, and any other variable is
/// checked by sort inference. Execution checks each value against the same
/// type (`typed_configuration.rs`).
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "Two tables of initializers, each with its expected outcome."
)]
fn configuration_variables_are_binders_of_their_declared_types() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let accepted = [
        (
            "typed-concat",
            "xs: List<Value>",
            "k::k![pgm]",
            "map::empty()",
            "list::concat(xs, list::item(1))",
        ),
        (
            "covariant",
            "xs: List<Int>",
            "k::k![pgm]",
            "map::empty()",
            "list::concat(xs, list::item(1))",
        ),
        (
            "whole-content",
            "e: Map<Id, Value>",
            "k::k![pgm]",
            "e",
            "list::empty()",
        ),
        (
            "scalar",
            "x: Value",
            "k::k![pgm]",
            "map::empty()",
            "list::item(x)",
        ),
        (
            "typed-field",
            "m: Map<Id, Value>",
            "k::k![pgm, StmtSyntax::Keep(m)]",
            "map::empty()",
            "list::empty()",
        ),
    ];
    for (name, parameters, k, env, stack) in accepted {
        let manifest = package(
            temporary.path(),
            name,
            &initializer_with(parameters, k, env, stack),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(success, "{name}:\n{stderr}");
        assert_eq!(diagnostics(&stderr), [], "{name}:\n{stderr}");
    }
    let stack = "the cell `stack`, declared `List<Value>`";
    let rejected = [
        (
            "ill-typed-concat",
            "xs: List<Stmt>",
            "k::k![pgm]",
            "map::empty()",
            "list::concat(xs, list::item(1))",
            format!(
                "error[krs::analysis::collection-element-sort]: `xs`, the configuration variable `$XS`, has type `List<Stmt>`, which does not fit {stack}: Stmt is not a Value"
            ),
            "xs",
        ),
        (
            "bare-concat",
            "xs: List",
            "k::k![pgm]",
            "map::empty()",
            "list::concat(xs, list::item(1))",
            format!(
                "error[krs::analysis::untyped-collection]: `xs`, the configuration variable `$XS`, is declared `List`, so nothing checks the elements it writes to {stack}"
            ),
            "xs",
        ),
        (
            "update-all",
            "e: Map<Id, Stmt>",
            "k::k![pgm]",
            "map::update_all(map::empty(), e)",
            "list::empty()",
            "error[krs::analysis::collection-element-sort]: `e`, the configuration variable `$E`, has type `Map<Id, Stmt>`, which does not fit the cell `env`, declared `Map<Id, Value>`: Stmt is not a Value".to_owned(),
            "e",
        ),
        (
            "field",
            "m: Map<Id, Stmt>",
            "k::k![pgm, StmtSyntax::Keep(m)]",
            "map::empty()",
            "list::empty()",
            "error[krs::analysis::collection-element-sort]: `m`, the configuration variable `$M`, has type `Map<Id, Stmt>`, which does not fit the field `m` of `Keep`, declared `Map<Id, Value>`: Stmt is not a Value".to_owned(),
            "m",
        ),
        (
            "variable-arity",
            "xs: Map<Id>",
            "k::k![pgm]",
            "map::empty()",
            "list::empty()",
            "error[krs::analysis::collection-element-sort]: `xs`, the configuration variable `$XS`, is declared `Map<Id>`: a `Map` takes a key and a value type, `Map<K, V>`, or none, `Map`".to_owned(),
            "Map<Id>",
        ),
    ];
    for (name, parameters, k, env, stack, headline, marked) in rejected {
        let manifest = package(
            temporary.path(),
            name,
            &initializer_with(parameters, k, env, stack),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: krs check unexpectedly passed:\n{stderr}");
        assert_eq!(
            diagnostics(&stderr).first(),
            Some(&(headline, marked.to_owned())),
            "{name}:\n{stderr}"
        );
    }
}

/// A transition's `#[k::exists(m: Map)]` is a value the step introduces, any
/// map at all, so writing it into a typed position is an untyped source in
/// every rule form; a claim's existential stands for what the target state
/// holds, and a scalar existential is checked by sort inference. These
/// checks run on the Haskell route, since the default route refuses
/// existential rules first.
#[test]
fn transition_existentials_of_collection_sorts_are_untyped_sources() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cells_rule = r#"
#[k::rule(label = "probe")]
#[k::exists(m: Map)]
pub fn probe(
    k::cells! {
        k: k::configuration::KCell(crate::StmtSyntax::Op(1), tail @ ..),
        env: k::configuration::Cell(_),
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! { k: k::configuration::KCell(..tail), env: k::configuration::Cell(m), ..state }
}
"#;
    let env = "the cell `env`, declared `Map<Id, Value>`";
    let untyped = |name: &str, kind: &str, position: &str| {
        format!(
            "error[krs::analysis::untyped-collection]: `{name}` is an existential `{kind}`, an unknown {} whose elements nothing constrains, so nothing checks the elements it writes to {position}",
            kind.to_lowercase()
        )
    };
    let rejected = [
        (
            "readable",
            rules("#[k::exists(m: Map)]\n    probe: { k: [Op(1), ..], env: _ } => { k: [..], env: m };"),
            untyped("m", "Map", env),
        ),
        ("cells-rule", cells_rule.to_owned(), untyped("m", "Map", env)),
        (
            "term-rule",
            "k::rules! {\n    for Stmt;\n    use StmtSyntax::*;\n\n    #[k::exists(m: Map)]\n    probe: Op(1) => Keep(m);\n}\n".to_owned(),
            untyped("m", "Map", "the field `m` of `Keep`, declared `Map<Id, Value>`"),
        ),
        (
            "list-concat",
            rules("#[k::exists(m: List)]\n    probe: { k: [Op(1), ..], stack: l } => { k: [..], stack: list::concat(m, l) };"),
            untyped("m", "List", "the cell `stack`, declared `List<Value>`"),
        ),
    ];
    for (name, source, headline) in rejected {
        let manifest = package(temporary.path(), name, &format!("{PREAMBLE}{source}"));
        let (success, _, stderr) =
            krs(target.path(), &manifest, "check", &["--backend", "haskell"]);
        assert!(!success, "{name}: krs check unexpectedly passed:\n{stderr}");
        assert_eq!(
            diagnostics(&stderr).first().map(|(headline, _)| headline),
            Some(&headline),
            "{name}:\n{stderr}"
        );
    }
    let accepted = [
        (
            "untyped-cell",
            rules("#[k::exists(m: Map)]\n    probe: { k: [Op(1), ..], raw: _ } => { k: [..], raw: m };"),
        ),
        (
            "scalar",
            rules("#[k::exists(v: Value)]\n    probe: { k: [Put(name, _), ..], env: e } => { k: [..], env: map::update(e, name, v) };"),
        ),
        (
            "claim",
            "k::claims! {\n    for Machine;\n    use StmtSyntax::*;\n\n    #[k::claim(all_paths)]\n    #[k::exists(m: Map)]\n    probe: { k: [Op(1)], env: _ } => { k: [], env: m };\n}\n".to_owned(),
        ),
    ];
    for (name, source) in accepted {
        let manifest = package(temporary.path(), name, &format!("{PREAMBLE}{source}"));
        let (success, _, stderr) =
            krs(target.path(), &manifest, "check", &["--backend", "haskell"]);
        assert!(success, "{name}:\n{stderr}");
        assert_eq!(diagnostics(&stderr), [], "{name}:\n{stderr}");
    }
}

/// How configuration variables and rule existentials meet element
/// positions: a typed part of a nested collection checks a typed variable
/// by its type and rejects a bare variable or a collection existential as
/// untyped; a scalar existential and a collection existential stored as an
/// element are checked at the element sort, as any binder is; and reading
/// an element out of a bare-collection variable is a `KItem` that the
/// position projects, never a write of the untyped collection itself.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of sentences, each with its expected outcome."
)]
fn untyped_sources_meet_typed_element_positions() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let nested = |parameters: &str| {
        initializer_with(parameters, "k::k![pgm]", "map::empty()", "list::empty()").replace(
            "            nested: map::empty(),",
            "            nested: map::update(map::empty(), k::id!(\"$x\"), s),",
        )
    };
    let nested_value = "a value of the cell `nested`, declared `Map<Id, Set<Int>>`";
    let accepted = [
        ("typed-part", nested("s: Set<Int>")),
        (
            "bare-read",
            initializer_with(
                "xs: List",
                "k::k![pgm]",
                "map::empty()",
                "list::item(list::get(xs, 0))",
            ),
        ),
    ];
    for (name, source) in accepted {
        let manifest = package(temporary.path(), name, &source);
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(success, "{name}:\n{stderr}");
        assert_eq!(diagnostics(&stderr), [], "{name}:\n{stderr}");
    }
    // The read is projected to the element sort, so no non-Value reaches the cell.
    let manifest = temporary.path().join("bare-read/Cargo.toml");
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    assert!(
        fs::read_to_string(output.join("definition.k"))
            .unwrap()
            .contains("<stack> ListItem({$XS:List [ 0 ]}:>Value) </stack>")
    );
    let rejected = [
        (
            "ill-typed-part",
            nested("s: Set<Stmt>"),
            format!(
                "error[krs::analysis::collection-element-sort]: `s`, the configuration variable `$S`, has type `Set<Stmt>`, which does not fit {nested_value}: Stmt is not an Int"
            ),
            "s",
        ),
        (
            "bare-part",
            nested("s: Set"),
            format!(
                "error[krs::analysis::untyped-collection]: `s`, the configuration variable `$S`, is declared `Set`, so nothing checks the elements it writes to {nested_value}"
            ),
            "s",
        ),
        (
            "existential-part",
            format!(
                "{PREAMBLE}{}",
                rules(
                    "#[k::exists(s: Set)]\n    probe: { k: [Op(1), PutI(name, _), ..], nested: n } => { k: [..], nested: map::update(n, name, s) };"
                )
            ),
            format!(
                "error[krs::analysis::untyped-collection]: `s` is an existential `Set`, an unknown set whose elements nothing constrains, so nothing checks the elements it writes to {nested_value}"
            ),
            "s",
        ),
        (
            "existential-scalar",
            format!(
                "{PREAMBLE}{}",
                rules(
                    "#[k::exists(v: Stmt)]\n    probe: { k: [Put(name, _), ..], env: e } => { k: [..], env: map::update(e, name, v) };"
                )
            ),
            "error[krs::analysis::collection-element-sort]: `v` of sort Stmt is stored as a value of the cell `env`, declared `Map<Id, Value>`, and Stmt is not a Value".to_owned(),
            "v",
        ),
        (
            "existential-element",
            format!(
                "{PREAMBLE}{}",
                rules(
                    "#[k::exists(m: Map)]\n    probe: { k: [Op(1), ..], stack: l } => { k: [..], stack: [m, ..l] };"
                )
            ),
            "error[krs::analysis::collection-element-sort]: `m` of sort Map is stored as an element of the cell `stack`, declared `List<Value>`, and Map is not a Value".to_owned(),
            "m",
        ),
    ];
    for (name, source, headline, marked) in rejected {
        let manifest = package(temporary.path(), name, &source);
        let (success, _, stderr) =
            krs(target.path(), &manifest, "check", &["--backend", "haskell"]);
        assert!(!success, "{name}: krs check unexpectedly passed:\n{stderr}");
        assert_eq!(
            diagnostics(&stderr).first(),
            Some(&(headline, marked.to_owned())),
            "{name}:\n{stderr}"
        );
    }
}
