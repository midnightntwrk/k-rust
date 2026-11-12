//! Typed collections end to end: a cell declared `Map<Id, Value>`,
//! `List<Value>`, `Set<Id>`, or `Map<Id, Set<Int>>`, a constructor field, and
//! a function parameter or result check every term a rule, claim, equation,
//! or initializer writes into them, through every write path, and the
//! emitted K, which erases element types, is the K of the same rules over
//! untyped cells.

use std::fmt::Write as _;
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
#[k::function(partial, internal, sort = Set<Int>, syntax = "members({sets}, {key})")]
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
    let definition = krs_test_support::without_source_comments(
        &fs::read_to_string(output.join("definition.k")).unwrap(),
    );
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
/// requires that instead, with `isId(read)` at a typed map's key root (S2 of
/// NT-18's review) and `isSet(read)` below a function (M2). The read is a
/// lookup, which has a value only where the map holds the key and which
/// matching would evaluate before any guard, so the key is a fresh name the
/// condition equates with it after the key's presence and the read's sort are
/// tested (NT-37). An equation's
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
    let definition = krs_test_support::without_source_comments(
        &fs::read_to_string(output.join("definition.k")).unwrap(),
    );
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
            "<k> op 20 ~> hold M:Map => V:Value ... </k> <env> Krs_Instance1:KItem |-> V:Value ... </env> requires (1 in_keys(M:Map) andThenBool isId(M:Map [ 1 ])) andThenBool (Krs_Instance1:KItem ==K (M:Map [ 1 ]))",
            "<k> op 21 ~> hold M:Map => V:KItem ... </k> <raw> Krs_Instance1:Int |-> V:KItem ... </raw> requires (1 in_keys(M:Map) andThenBool isSet(M:Map [ 1 ])) andThenBool (Krs_Instance1:Int ==K size({M:Map [ 1 ]}:>Set))",
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
            // A local is the value it names, so it has that value's type at a typed position.
            "typed-local-flow",
            "#[k::function(total, internal)]\npub fn Narrow(e: Term<Map<Id, Value>>) -> Term<Map<Id, Int>> {\n    let named = e;\n    named\n}\n".to_owned(),
            "error[krs::analysis::collection-element-sort]: `named`, bound to the parameter `e` of `Narrow`, has type `Map<Id, Value>`, which does not fit the result of `Narrow`, declared `Map<Id, Int>`: Value is not an Int".to_owned(),
            "named",
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

/// A local names its value, so a collection whose elements nothing declares
/// is one through a local too: written at a typed position, the local is
/// refused as the value written there directly is, for a map and a list, a
/// local bound to the whole value and one bound to a part of it.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of direct and local forms, each with its expected diagnostic."
)]
fn an_untyped_value_keeps_its_verdict_through_a_local() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let function = |parameter: &str, result: &str, body: &str| {
        format!(
            "{PREAMBLE}#[k::function(total, internal)]\npub fn Narrow(x: Term<{parameter}>) -> Term<{result}> {{\n    {body}\n}}\n"
        )
    };
    let untyped = |reason: &str, position: &str| {
        format!(
            "error[krs::analysis::untyped-collection]: {reason}, so nothing checks the elements it writes to {position}"
        )
    };
    let map_result = "the result of `Narrow`, declared `Map<Id, Value>`";
    let list_result = "the result of `Narrow`, declared `List<Value>`";
    let parameter =
        |sort: &str| format!("`x` is matched in the parameter `x` of `Narrow`, declared `{sort}`");
    let cases = [
        (
            "map-direct",
            function("Map", "Map<Id, Value>", "x"),
            untyped(&parameter("Map"), map_result),
            "x",
        ),
        (
            "map-local",
            function("Map", "Map<Id, Value>", "let named = x;\n    named"),
            untyped(
                &format!("`named` is bound to `x`, and {}", parameter("Map")),
                map_result,
            ),
            "named",
        ),
        (
            "list-direct",
            function("List", "List<Value>", "x"),
            untyped(&parameter("List"), list_result),
            "x",
        ),
        (
            "list-local",
            function("List", "List<Value>", "let named = x;\n    named"),
            untyped(
                &format!("`named` is bound to `x`, and {}", parameter("List")),
                list_result,
            ),
            "named",
        ),
        (
            "rule-direct",
            format!(
                "{PREAMBLE}{}",
                rules("probe: { k: [Skip(), ..], raw: r, env: _ } => { k: [..], env: r };")
            ),
            untyped(
                "`r` is matched in the cell `raw`, declared `Map`",
                "the cell `env`, declared `Map<Id, Value>`",
            ),
            "r",
        ),
        (
            "rule-local",
            format!(
                "{PREAMBLE}{}",
                rules(
                    "probe: { k: [Skip(), ..], raw: r, env: _ } => { k: [..], env: { let named = r; named } };"
                )
            ),
            untyped(
                "`named` is bound to `r`, and `r` is matched in the cell `raw`, declared `Map`",
                "the cell `env`, declared `Map<Id, Value>`",
            ),
            "named",
        ),
        (
            "part-direct",
            function("List", "Map<Id, Value>", "list::get(x, 0)"),
            untyped(
                "`list::get(..)` reads a collection whose element types are not declared",
                map_result,
            ),
            "list::get",
        ),
        (
            "part-local",
            function("List", "Map<Id, Value>", "let [first, ..] = x;\n    first"),
            untyped(
                &format!(
                    "`first` is matched in a part of `x`, and {}",
                    parameter("List")
                ),
                map_result,
            ),
            "first",
        ),
        (
            "typed-part-direct",
            function("List<Map>", "Map<Id, Value>", "list::get(x, 0)"),
            untyped(
                "`list::get(..)`, read from the parameter `x` of `Narrow`, has type `Map`, which declares not every element type",
                map_result,
            ),
            "list::get",
        ),
        (
            "typed-part-local",
            function(
                "List<Map>",
                "Map<Id, Value>",
                "let [first, ..] = x;\n    first",
            ),
            untyped(
                "`first` is matched in an element of the parameter `x` of `Narrow`, declared `List<Map>`",
                map_result,
            ),
            "first",
        ),
    ];
    for (name, source, headline, marked) in cases {
        let manifest = package(temporary.path(), name, &source);
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: krs check unexpectedly passed:\n{stderr}");
        assert_eq!(
            diagnostics(&stderr).first(),
            Some(&(headline, marked.to_owned())),
            "{name}:\n{stderr}"
        );
    }
}

/// A projection `k::project!(S, t)` to the collection sort `S` that a typed `t`
/// already has denotes `t`'s value, so it has `t`'s type: written where `t` would
/// be, directly or through a local, it gets `t`'s verdict there, accepted where
/// `t` fits and refused with `t`'s element mistake, at `t`, where it does not. A
/// projection of a term that is no typed collection of that sort tests only the
/// sort, and stays untyped.
#[test]
fn a_projection_to_its_typed_operand_s_sort_has_its_type() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let function = |parameter: &str, result: &str, body: &str| {
        format!(
            "{PREAMBLE}#[k::function(total, internal)]\npub fn Narrow(x: Term<{parameter}>) -> Term<{result}> {{\n    {body}\n}}\n"
        )
    };
    let verdict = |name: &str, source: &str| {
        let manifest = package(temporary.path(), name, source);
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        if success {
            ("accepted".to_owned(), String::new())
        } else {
            diagnostics(&stderr)
                .into_iter()
                .next()
                .unwrap_or_else(|| (format!("no diagnostic: {stderr}"), String::new()))
        }
    };
    let collections = [
        (
            "Map",
            ("Map<Id, Int>", "Map<Id, Value>"),
            ("Map<Id, Value>", "Map<Id, Int>"),
        ),
        (
            "List",
            ("List<Int>", "List<Value>"),
            ("List<Value>", "List<Int>"),
        ),
        ("Set", ("Set<Int>", "Set<Int>"), ("Set<Value>", "Set<Int>")),
    ];
    for (sort, fits, breaks) in collections {
        for (case, (parameter, result)) in [("fits", fits), ("breaks", breaks)] {
            let name = format!("project-{}-{case}", sort.to_lowercase());
            for (form, around) in [("direct", "VALUE"), ("local", "{ let b = VALUE; b }")] {
                let plain = verdict(
                    &format!("{name}-{form}-x"),
                    &function(parameter, result, &around.replace("VALUE", "x")),
                );
                assert_eq!(plain.0 == "accepted", case == "fits", "{name}: {plain:?}");
                let body = around.replace("VALUE", &format!("k::project!({sort}, x)"));
                let projected = verdict(
                    &format!("{name}-{form}"),
                    &function(parameter, result, &body),
                );
                assert_eq!(projected, plain, "{name}: `{body}`");
            }
        }
    }
    // A projection of a `KItem`, and of a collection to another collection sort: only the sort.
    for (name, parameter, body) in [
        ("project-item", "k::KItem", "k::project!(Map, x)"),
        ("project-other-sort", "List<Int>", "k::project!(Map, x)"),
    ] {
        let (headline, marked) = verdict(name, &function(parameter, "Map<Id, Value>", body));
        assert!(
            headline.starts_with("error[krs::analysis::untyped-collection]: `k::project!(Map, ..)` is a projection, which tests only the sort"),
            "{name}: {headline}"
        );
        assert_eq!(marked, body, "{name}");
    }
}

/// A local names its value, so a collection the sentence builds keeps, through
/// a local, the typing it has where it is used: `let b = map::update(map::empty(),
/// name, s); b` at the cell `env` checks `s` against `env`'s values, as
/// `map::update(map::empty(), name, s)` written there does, and so for a List
/// and a Set, through a second local naming the first, and through a carrying
/// operation the local is an operand of. Each local form gets its direct form's
/// verdict: the well-typed ones are accepted, with the direct form's K under the
/// `#let`, and the ill-typed ones are refused with the same diagnostic at the
/// same term.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of spellings, each with its verdict."
)]
fn a_collection_the_sentence_builds_keeps_its_typing_through_a_local() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let forms = [
        ("map-ok", "env", "map::update(map::empty(), name, 1)"),
        ("map-bad", "env", "map::update(map::empty(), name, s)"),
        ("list-ok", "stack", "list::item(1)"),
        ("list-bad", "stack", "list::item(s)"),
        ("set-ok", "seen", "set::item(name)"),
        ("set-bad", "seen", "set::item(s)"),
        (
            "keys-bad",
            "seen",
            "map::keys(map::update(map::empty(), s, 1))",
        ),
    ];
    let mut outcomes = Vec::new();
    for (name, cell, value) in forms {
        let spellings = [
            ("direct", value.to_owned()),
            ("local", format!("{{ let b = {value}; b }}")),
            (
                "second-local",
                format!("{{ let b = {value}; let c = b; c }}"),
            ),
        ];
        let mut verdicts = Vec::new();
        for (spelling, written) in spellings {
            let library = format!(
                "{PREAMBLE}{}",
                rules(&format!(
                    "probe: {{ k: [Put(name, s), ..], {cell}: _ }} => {{ k: [..], {cell}: {written} }};"
                ))
            );
            let manifest = package(temporary.path(), &format!("{name}-{spelling}"), &library);
            let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
            let verdict = if success {
                let output = manifest.with_file_name("emitted");
                let (success, _, stderr) = krs(
                    target.path(),
                    &manifest,
                    "emit-k",
                    &["--output", output.to_str().unwrap()],
                );
                assert!(success, "{name}-{spelling}: {stderr}");
                let definition = krs_test_support::without_source_comments(
                    &fs::read_to_string(output.join("definition.k")).unwrap(),
                );
                format!("accepted: {}", rule(&definition, "probe"))
            } else {
                let (headline, marked) = diagnostics(&stderr)
                    .into_iter()
                    .next()
                    .unwrap_or_else(|| panic!("{name}-{spelling}: {stderr}"));
                format!("{headline} at `{marked}`")
            };
            verdicts.push((spelling, verdict));
        }
        outcomes.push((name, verdicts));
    }
    // A built value's carrying operation through a local: the local stands at the operand the
    // position types, `map::update(b, name, 2)` at `env`.
    let carried = format!(
        "{PREAMBLE}{}",
        rules(
            "probe: { k: [Put(name, s), ..], env: _ } => { k: [..], env: { let b = map::update(map::empty(), name, s); map::update(b, name, 2) } };"
        )
    );
    let manifest = package(temporary.path(), "carried", &carried);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(!success, "{stderr}");
    let carried = diagnostics(&stderr).into_iter().next();
    expect_test::expect![[r#"
        (
            [
                (
                    "map-ok",
                    [
                        (
                            "direct",
                            "accepted: <k> put Name:Id S:Stmt => .K ... </k> <env> _ => .Map [ Name:Id <- 1 ] </env> endmodule",
                        ),
                        (
                            "local",
                            "accepted: <k> put Name:Id S:Stmt => .K ... </k> <env> _ => ( #let B:Map = .Map [ Name:Id <- 1 ] #in B:Map ) </env> endmodule",
                        ),
                        (
                            "second-local",
                            "accepted: <k> put Name:Id S:Stmt => .K ... </k> <env> _ => ( #let B:Map = .Map [ Name:Id <- 1 ] #in ( #let C:Map = B:Map #in C:Map ) ) </env> endmodule",
                        ),
                    ],
                ),
                (
                    "map-bad",
                    [
                        (
                            "direct",
                            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as a value of the cell `env`, declared `Map<Id, Value>`, and Stmt is not a Value at `s`",
                        ),
                        (
                            "local",
                            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as a value of the cell `env`, declared `Map<Id, Value>`, and Stmt is not a Value at `s`",
                        ),
                        (
                            "second-local",
                            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as a value of the cell `env`, declared `Map<Id, Value>`, and Stmt is not a Value at `s`",
                        ),
                    ],
                ),
                (
                    "list-ok",
                    [
                        (
                            "direct",
                            "accepted: <k> put Name:Id S:Stmt => .K ... </k> <stack> _ => ListItem(1) </stack> endmodule",
                        ),
                        (
                            "local",
                            "accepted: <k> put Name:Id S:Stmt => .K ... </k> <stack> _ => ( #let B:List = ListItem(1) #in B:List ) </stack> endmodule",
                        ),
                        (
                            "second-local",
                            "accepted: <k> put Name:Id S:Stmt => .K ... </k> <stack> _ => ( #let B:List = ListItem(1) #in ( #let C:List = B:List #in C:List ) ) </stack> endmodule",
                        ),
                    ],
                ),
                (
                    "list-bad",
                    [
                        (
                            "direct",
                            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `stack`, declared `List<Value>`, and Stmt is not a Value at `s`",
                        ),
                        (
                            "local",
                            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `stack`, declared `List<Value>`, and Stmt is not a Value at `s`",
                        ),
                        (
                            "second-local",
                            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `stack`, declared `List<Value>`, and Stmt is not a Value at `s`",
                        ),
                    ],
                ),
                (
                    "set-ok",
                    [
                        (
                            "direct",
                            "accepted: <k> put Name:Id S:Stmt => .K ... </k> <seen> _ => SetItem(Name:Id) </seen> endmodule",
                        ),
                        (
                            "local",
                            "accepted: <k> put Name:Id S:Stmt => .K ... </k> <seen> _ => ( #let B:Set = SetItem(Name:Id) #in B:Set ) </seen> endmodule",
                        ),
                        (
                            "second-local",
                            "accepted: <k> put Name:Id S:Stmt => .K ... </k> <seen> _ => ( #let B:Set = SetItem(Name:Id) #in ( #let C:Set = B:Set #in C:Set ) ) </seen> endmodule",
                        ),
                    ],
                ),
                (
                    "set-bad",
                    [
                        (
                            "direct",
                            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `seen`, declared `Set<Id>`, and Stmt is not an Id at `s`",
                        ),
                        (
                            "local",
                            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `seen`, declared `Set<Id>`, and Stmt is not an Id at `s`",
                        ),
                        (
                            "second-local",
                            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `seen`, declared `Set<Id>`, and Stmt is not an Id at `s`",
                        ),
                    ],
                ),
                (
                    "keys-bad",
                    [
                        (
                            "direct",
                            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as a key of the map whose keys `map::keys(..)` writes to the cell `seen`, declared `Set<Id>`, and Stmt is not an Id at `s`",
                        ),
                        (
                            "local",
                            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as a key of the map whose keys `map::keys(..)` writes to the cell `seen`, declared `Set<Id>`, and Stmt is not an Id at `s`",
                        ),
                        (
                            "second-local",
                            "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as a key of the map whose keys `map::keys(..)` writes to the cell `seen`, declared `Set<Id>`, and Stmt is not an Id at `s`",
                        ),
                    ],
                ),
            ],
            Some(
                (
                    "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as a value of the cell `env`, declared `Map<Id, Value>`, and Stmt is not a Value",
                    "s",
                ),
            ),
        )
    "#]].assert_debug_eq(&(outcomes, carried));
}

/// `value` written through the forms that denote another term's value, each
/// at the position (no local) and as the value of one and of two locals: a
/// block's result, a block whose result names its own statement's local or
/// an outer statement's, nested blocks, an ascription (`sort`), and
/// parentheses, which group and are no term of their own. The first spelling
/// is `value` itself, the direct form.
fn through_blocks(value: &str, sort: &str) -> Vec<(String, String)> {
    let forms = [
        ("value", value.to_owned()),
        ("block", format!("{{ let n = 1; {value} }}")),
        ("named", format!("{{ let c = {value}; c }}")),
        (
            "outer",
            format!("{{ let c = {value}; {{ let n = 1; c }} }}"),
        ),
        (
            "nested",
            format!("{{ let m = 0; {{ let n = 1; {value} }} }}"),
        ),
        ("ascribed", format!("{{ let a: {sort} = {value}; a }}")),
    ];
    let mut spellings = Vec::new();
    for (form, written) in forms {
        // `named` at the position is `value` through one local, spelled already.
        if form != "named" {
            spellings.push((form.to_owned(), written.clone()));
        }
        spellings.push((
            format!("{form}-local"),
            format!("{{ let b = {written}; b }}"),
        ));
        spellings.push((
            format!("{form}-second-local"),
            format!("{{ let b = {written}; let d = b; d }}"),
        ));
    }
    spellings.push((
        "parens-block-local".to_owned(),
        format!("{{ let b = ({{ let n = 1; {value} }}); b }}"),
    ));
    spellings
}

/// Whether a refusal is the direct form's: the same diagnostic code, and the
/// same reason, which for a typed source names the local it flows through
/// and for an untyped source the locals it is bound through first.
fn same_refusal(direct: &str, through: &str) -> bool {
    let code = |headline: &str| headline.split_once("]:").map(|(code, _)| code.to_owned());
    let reason = direct.find(" has type ").map_or_else(
        || {
            direct
                .split_once("]: ")
                .map_or(direct, |(_, reason)| reason)
        },
        |at| &direct[at..],
    );
    code(direct) == code(through) && through.ends_with(reason)
}

/// Where a typed collection's value is read: in a cell (a collection the
/// sentence builds, `s: Stmt`) or as the parameter `x` of `Narrow` (typed or
/// untyped), with a value that fits the position and one that does not.
enum Source {
    Cell {
        cell: &'static str,
        fits: &'static str,
        breaks: &'static str,
    },
    Parameter {
        fits: (&'static str, &'static str),
        breaks: (&'static str, &'static str),
    },
}

/// A local names its value and a block's value is its result, so a value
/// written through blocks and locals is, where it is used, the term its
/// innermost result names, and has that term's verdict there: for a
/// collection the sentence builds (Built), a typed parameter (Typed) and an
/// untyped one (Untyped), at a list, a map and a set, every spelling of
/// [`through_blocks`] that does not fit is refused as the direct form is,
/// and every one that fits is accepted. The well-typed list cell's K is the
/// direct form's under the blocks' `#let`s, and the block-valued local runs
/// to the direct form's cell.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of sources and spellings, each with its verdict."
)]
fn a_value_through_blocks_and_locals_has_the_verdict_of_the_term_it_denotes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let narrow = |name: &str, (parameter, result): (&str, &str), written: &str| {
        format!(
            "#[k::function(total, internal)]\npub fn {name}(x: Term<{parameter}>) -> Term<{result}> {{\n    {written}\n}}\n"
        )
    };
    // Each source at every spelling, or at the direct form and the block-valued local only.
    let groups = [
        (
            "built-list",
            "List",
            true,
            Source::Cell {
                cell: "stack",
                fits: "[1, 2]",
                breaks: "[1, s]",
            },
        ),
        (
            "built-map",
            "Map",
            false,
            Source::Cell {
                cell: "env",
                fits: "map::update(map::empty(), name, 1)",
                breaks: "map::update(map::empty(), name, s)",
            },
        ),
        (
            "built-set",
            "Set",
            false,
            Source::Cell {
                cell: "seen",
                fits: "set::item(name)",
                breaks: "set::item(s)",
            },
        ),
        (
            "typed-map",
            "Map",
            true,
            Source::Parameter {
                fits: ("Map<Id, Int>", "Map<Id, Value>"),
                breaks: ("Map<Id, Value>", "Map<Id, Int>"),
            },
        ),
        (
            "typed-list",
            "List",
            false,
            Source::Parameter {
                fits: ("List<Int>", "List<Value>"),
                breaks: ("List<Value>", "List<Int>"),
            },
        ),
        (
            "typed-set",
            "Set",
            false,
            Source::Parameter {
                fits: ("Set<Int>", "Set<Int>"),
                breaks: ("Set<Value>", "Set<Int>"),
            },
        ),
        (
            "untyped-set",
            "Set",
            true,
            Source::Parameter {
                fits: ("Set", "Set"),
                breaks: ("Set", "Set<Id>"),
            },
        ),
        (
            "untyped-map",
            "Map",
            false,
            Source::Parameter {
                fits: ("Map", "Map"),
                breaks: ("Map", "Map<Id, Value>"),
            },
        ),
        (
            "untyped-list",
            "List",
            false,
            Source::Parameter {
                fits: ("List", "List"),
                breaks: ("List", "List<Value>"),
            },
        ),
    ];
    let mut refused = Vec::new();
    let mut kept = Vec::new();
    for (group, sort, every, source) in &groups {
        let (fits, breaks) = match source {
            Source::Cell { fits, breaks, .. } => (*fits, *breaks),
            Source::Parameter { .. } => ("x", "x"),
        };
        let chosen = |spellings: Vec<(String, String)>| {
            spellings
                .into_iter()
                .filter(|(spelling, _)| {
                    *every || ["value", "block-local"].contains(&spelling.as_str())
                })
                .collect::<Vec<_>>()
        };
        // Every spelling that does not fit, one package each: `check` reports the first refusal.
        let mut verdicts = Vec::new();
        let mut direct = None;
        for (spelling, written) in chosen(through_blocks(breaks, sort)) {
            let library = match source {
                Source::Cell { cell, .. } => rules(&format!(
                    "probe: {{ k: [Put(name, s), ..], {cell}: _ }} => {{ k: [..], {cell}: {written} }};"
                )),
                Source::Parameter { breaks, .. } => narrow("Narrow", *breaks, &written),
            };
            let manifest = package(
                temporary.path(),
                &format!("{group}-breaks-{spelling}"),
                &format!("{PREAMBLE}{library}"),
            );
            let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
            assert!(!success, "{group} {spelling}: accepted");
            let (headline, marked) = diagnostics(&stderr)
                .into_iter()
                .next()
                .unwrap_or_else(|| panic!("{group} {spelling}: {stderr}"));
            let direct = direct.get_or_insert_with(|| headline.clone());
            assert!(
                same_refusal(direct, &headline),
                "{group} {spelling}: {headline}, where the direct form is {direct}"
            );
            verdicts.push((spelling, marked));
        }
        refused.push((*group, direct.unwrap(), verdicts));
        // Every spelling that fits, one package for the group, one sentence each.
        let spellings = chosen(through_blocks(fits, sort));
        let library = match source {
            Source::Cell { cell, .. } => rules(
                &spellings
                    .iter()
                    .enumerate()
                    .map(|(index, (_, written))| {
                        format!(
                            "probe_{index}: {{ k: [PutI(name, {index}), ..], {cell}: _ }} => {{ k: [..], {cell}: {written} }};"
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n    "),
            ),
            Source::Parameter { fits, .. } => spellings
                .iter()
                .enumerate()
                .map(|(index, (_, written))| narrow(&format!("Narrow{index}"), *fits, written))
                .collect(),
        };
        let manifest = package(
            temporary.path(),
            &format!("{group}-fits"),
            &format!("{PREAMBLE}{library}"),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(success, "{group}: {stderr}");
        let Source::Cell { cell, .. } = source else {
            continue;
        };
        if !*every {
            continue;
        }
        let output = manifest.with_file_name("emitted");
        let (success, _, stderr) = krs(
            target.path(),
            &manifest,
            "emit-k",
            &["--output", output.to_str().unwrap()],
        );
        assert!(success, "{group}: {stderr}");
        let definition = krs_test_support::without_source_comments(
            &fs::read_to_string(output.join("definition.k")).unwrap(),
        );
        for (index, (spelling, _)) in spellings.iter().enumerate() {
            // A label's `_` is K's `-`.
            let k = rule(&definition, &format!("probe-{index}"));
            kept.push((spelling.clone(), k));
        }
        // The block-valued local runs to the direct form's cell.
        let index = spellings
            .iter()
            .position(|(spelling, _)| spelling == "block-local")
            .unwrap();
        let program = manifest.with_file_name("program.txt");
        fs::write(&program, format!("puti x {index}")).unwrap();
        let (success, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &[program.to_str().unwrap()],
        );
        assert!(success, "{stderr}");
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        let open = format!("<{cell}> ");
        let start = flat
            .find(&open)
            .unwrap_or_else(|| panic!("no <{cell}>:\n{stdout}"))
            + open.len();
        let end = start + flat[start..].find(&format!(" </{cell}>")).unwrap();
        kept.push(("block-local run".to_owned(), flat[start..end].to_owned()));
    }
    expect_test::expect![[r#"
        (
            [
                (
                    "built-list",
                    "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `stack`, declared `List<Value>`, and Stmt is not a Value",
                    [
                        (
                            "value",
                            "s",
                        ),
                        (
                            "value-local",
                            "s",
                        ),
                        (
                            "value-second-local",
                            "s",
                        ),
                        (
                            "block",
                            "s",
                        ),
                        (
                            "block-local",
                            "s",
                        ),
                        (
                            "block-second-local",
                            "s",
                        ),
                        (
                            "named-local",
                            "s",
                        ),
                        (
                            "named-second-local",
                            "s",
                        ),
                        (
                            "outer",
                            "s",
                        ),
                        (
                            "outer-local",
                            "s",
                        ),
                        (
                            "outer-second-local",
                            "s",
                        ),
                        (
                            "nested",
                            "s",
                        ),
                        (
                            "nested-local",
                            "s",
                        ),
                        (
                            "nested-second-local",
                            "s",
                        ),
                        (
                            "ascribed",
                            "s",
                        ),
                        (
                            "ascribed-local",
                            "s",
                        ),
                        (
                            "ascribed-second-local",
                            "s",
                        ),
                        (
                            "parens-block-local",
                            "s",
                        ),
                    ],
                ),
                (
                    "built-map",
                    "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as a value of the cell `env`, declared `Map<Id, Value>`, and Stmt is not a Value",
                    [
                        (
                            "value",
                            "s",
                        ),
                        (
                            "block-local",
                            "s",
                        ),
                    ],
                ),
                (
                    "built-set",
                    "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `seen`, declared `Set<Id>`, and Stmt is not an Id",
                    [
                        (
                            "value",
                            "s",
                        ),
                        (
                            "block-local",
                            "s",
                        ),
                    ],
                ),
                (
                    "typed-map",
                    "error[krs::analysis::collection-element-sort]: `x`, matched as the parameter `x` of `Narrow`, has type `Map<Id, Value>`, which does not fit the result of `Narrow`, declared `Map<Id, Int>`: Value is not an Int",
                    [
                        (
                            "value",
                            "x",
                        ),
                        (
                            "value-local",
                            "b",
                        ),
                        (
                            "value-second-local",
                            "d",
                        ),
                        (
                            "block",
                            "x",
                        ),
                        (
                            "block-local",
                            "b",
                        ),
                        (
                            "block-second-local",
                            "d",
                        ),
                        (
                            "named-local",
                            "b",
                        ),
                        (
                            "named-second-local",
                            "d",
                        ),
                        (
                            "outer",
                            "c",
                        ),
                        (
                            "outer-local",
                            "b",
                        ),
                        (
                            "outer-second-local",
                            "d",
                        ),
                        (
                            "nested",
                            "x",
                        ),
                        (
                            "nested-local",
                            "b",
                        ),
                        (
                            "nested-second-local",
                            "d",
                        ),
                        (
                            "ascribed",
                            "a",
                        ),
                        (
                            "ascribed-local",
                            "b",
                        ),
                        (
                            "ascribed-second-local",
                            "d",
                        ),
                        (
                            "parens-block-local",
                            "b",
                        ),
                    ],
                ),
                (
                    "typed-list",
                    "error[krs::analysis::collection-element-sort]: `x`, matched as the parameter `x` of `Narrow`, has type `List<Value>`, which does not fit the result of `Narrow`, declared `List<Int>`: Value is not an Int",
                    [
                        (
                            "value",
                            "x",
                        ),
                        (
                            "block-local",
                            "b",
                        ),
                    ],
                ),
                (
                    "typed-set",
                    "error[krs::analysis::collection-element-sort]: `x`, matched as the parameter `x` of `Narrow`, has type `Set<Value>`, which does not fit the result of `Narrow`, declared `Set<Int>`: Value is not an Int",
                    [
                        (
                            "value",
                            "x",
                        ),
                        (
                            "block-local",
                            "b",
                        ),
                    ],
                ),
                (
                    "untyped-set",
                    "error[krs::analysis::untyped-collection]: `x` is matched in the parameter `x` of `Narrow`, declared `Set`, so nothing checks the elements it writes to the result of `Narrow`, declared `Set<Id>`",
                    [
                        (
                            "value",
                            "x",
                        ),
                        (
                            "value-local",
                            "b",
                        ),
                        (
                            "value-second-local",
                            "d",
                        ),
                        (
                            "block",
                            "x",
                        ),
                        (
                            "block-local",
                            "b",
                        ),
                        (
                            "block-second-local",
                            "d",
                        ),
                        (
                            "named-local",
                            "b",
                        ),
                        (
                            "named-second-local",
                            "d",
                        ),
                        (
                            "outer",
                            "c",
                        ),
                        (
                            "outer-local",
                            "b",
                        ),
                        (
                            "outer-second-local",
                            "d",
                        ),
                        (
                            "nested",
                            "x",
                        ),
                        (
                            "nested-local",
                            "b",
                        ),
                        (
                            "nested-second-local",
                            "d",
                        ),
                        (
                            "ascribed",
                            "a",
                        ),
                        (
                            "ascribed-local",
                            "b",
                        ),
                        (
                            "ascribed-second-local",
                            "d",
                        ),
                        (
                            "parens-block-local",
                            "b",
                        ),
                    ],
                ),
                (
                    "untyped-map",
                    "error[krs::analysis::untyped-collection]: `x` is matched in the parameter `x` of `Narrow`, declared `Map`, so nothing checks the elements it writes to the result of `Narrow`, declared `Map<Id, Value>`",
                    [
                        (
                            "value",
                            "x",
                        ),
                        (
                            "block-local",
                            "b",
                        ),
                    ],
                ),
                (
                    "untyped-list",
                    "error[krs::analysis::untyped-collection]: `x` is matched in the parameter `x` of `Narrow`, declared `List`, so nothing checks the elements it writes to the result of `Narrow`, declared `List<Value>`",
                    [
                        (
                            "value",
                            "x",
                        ),
                        (
                            "block-local",
                            "b",
                        ),
                    ],
                ),
            ],
            [
                (
                    "value",
                    "<k> puti Name:Id 0 => .K ... </k> <stack> _ => ListItem(1) ListItem(2) </stack>",
                ),
                (
                    "value-local",
                    "<k> puti Name:Id 1 => .K ... </k> <stack> _ => ( #let B:List = ListItem(1) ListItem(2) #in B:List ) </stack>",
                ),
                (
                    "value-second-local",
                    "<k> puti Name:Id 2 => .K ... </k> <stack> _ => ( #let B:List = ListItem(1) ListItem(2) #in ( #let D:List = B:List #in D:List ) ) </stack>",
                ),
                (
                    "block",
                    "<k> puti Name:Id 3 => .K ... </k> <stack> _ => ( #let N:Int = 1 #in ListItem(1) ListItem(2) ) </stack>",
                ),
                (
                    "block-local",
                    "<k> puti Name:Id 4 => .K ... </k> <stack> _ => ( #let B:List = ( #let N:Int = 1 #in ListItem(1) ListItem(2) ) #in B:List ) </stack>",
                ),
                (
                    "block-second-local",
                    "<k> puti Name:Id 5 => .K ... </k> <stack> _ => ( #let B:List = ( #let N:Int = 1 #in ListItem(1) ListItem(2) ) #in ( #let D:List = B:List #in D:List ) ) </stack>",
                ),
                (
                    "named-local",
                    "<k> puti Name:Id 6 => .K ... </k> <stack> _ => ( #let B:List = ( #let C:List = ListItem(1) ListItem(2) #in C:List ) #in B:List ) </stack>",
                ),
                (
                    "named-second-local",
                    "<k> puti Name:Id 7 => .K ... </k> <stack> _ => ( #let B:List = ( #let C:List = ListItem(1) ListItem(2) #in C:List ) #in ( #let D:List = B:List #in D:List ) ) </stack>",
                ),
                (
                    "outer",
                    "<k> puti Name:Id 8 => .K ... </k> <stack> _ => ( #let C:List = ListItem(1) ListItem(2) #in ( #let N:Int = 1 #in C:List ) ) </stack>",
                ),
                (
                    "outer-local",
                    "<k> puti Name:Id 9 => .K ... </k> <stack> _ => ( #let B:List = ( #let C:List = ListItem(1) ListItem(2) #in ( #let N:Int = 1 #in C:List ) ) #in B:List ) </stack>",
                ),
                (
                    "outer-second-local",
                    "<k> puti Name:Id 10 => .K ... </k> <stack> _ => ( #let B:List = ( #let C:List = ListItem(1) ListItem(2) #in ( #let N:Int = 1 #in C:List ) ) #in ( #let D:List = B:List #in D:List ) ) </stack>",
                ),
                (
                    "nested",
                    "<k> puti Name:Id 11 => .K ... </k> <stack> _ => ( #let M:Int = 0 #in ( #let N:Int = 1 #in ListItem(1) ListItem(2) ) ) </stack>",
                ),
                (
                    "nested-local",
                    "<k> puti Name:Id 12 => .K ... </k> <stack> _ => ( #let B:List = ( #let M:Int = 0 #in ( #let N:Int = 1 #in ListItem(1) ListItem(2) ) ) #in B:List ) </stack>",
                ),
                (
                    "nested-second-local",
                    "<k> puti Name:Id 13 => .K ... </k> <stack> _ => ( #let B:List = ( #let M:Int = 0 #in ( #let N:Int = 1 #in ListItem(1) ListItem(2) ) ) #in ( #let D:List = B:List #in D:List ) ) </stack>",
                ),
                (
                    "ascribed",
                    "<k> puti Name:Id 14 => .K ... </k> <stack> _ => ( #let A:List = ListItem(1) ListItem(2) #in A:List ) </stack>",
                ),
                (
                    "ascribed-local",
                    "<k> puti Name:Id 15 => .K ... </k> <stack> _ => ( #let B:List = ( #let A:List = ListItem(1) ListItem(2) #in A:List ) #in B:List ) </stack>",
                ),
                (
                    "ascribed-second-local",
                    "<k> puti Name:Id 16 => .K ... </k> <stack> _ => ( #let B:List = ( #let A:List = ListItem(1) ListItem(2) #in A:List ) #in ( #let D:List = B:List #in D:List ) ) </stack>",
                ),
                (
                    "parens-block-local",
                    "<k> puti Name:Id 17 => .K ... </k> <stack> _ => ( #let B:List = ( #let N:Int = 1 #in ListItem(1) ListItem(2) ) #in B:List ) </stack> endmodule",
                ),
                (
                    "block-local run",
                    "ListItem ( 1 ) ListItem ( 2 )",
                ),
            ],
        )
    "#]].assert_debug_eq(&(refused, kept));
}

/// A block's result is read in the scope of the block's statements, so what a
/// block-valued local is follows the names those statements bind: a name that
/// shadows a parameter is the value it is bound to, a destructured name is a
/// part of its value, and an operation over a statement's local is an
/// operation over that local's value; a block that is an operand is the term
/// it denotes there too. And a collection the sentence builds stands wherever
/// a local whose value carries it stands, `let b = map::update(c, name, 2);`
/// through `c`, so it is checked there, through any number of such locals.
/// Each spelling has the direct form's verdict.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of spellings, each with its verdict."
)]
fn a_block_result_is_read_in_the_scope_of_its_statements() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let narrow = |parameters: &str, result: &str, body: &str| {
        format!(
            "{PREAMBLE}#[k::function(total, internal)]\npub fn Narrow({parameters}) -> Term<{result}> {{\n    {body}\n}}\n"
        )
    };
    let maps = "x: Term<List<Map<Id, Value>>>";
    let cases = [
        (
            "shadow",
            narrow(
                "x: Term<Map<Id, Value>>, y: Term<Map<Id, Int>>",
                "Map<Id, Int>",
                "{ let y = x; y }",
            ),
        ),
        (
            "shadow-local",
            narrow(
                "x: Term<Map<Id, Value>>, y: Term<Map<Id, Int>>",
                "Map<Id, Int>",
                "let b = { let y = x; y };\n    b",
            ),
        ),
        (
            "part",
            narrow(maps, "Map<Id, Int>", "{ let [first, ..] = x; first }"),
        ),
        (
            "part-local",
            narrow(
                maps,
                "Map<Id, Int>",
                "let b = { let [first, ..] = x; first };\n    b",
            ),
        ),
        (
            "part-second-local",
            narrow(
                maps,
                "Map<Id, Int>",
                "let b = { let [first, ..] = x; first };\n    let d = b;\n    d",
            ),
        ),
        ("read", narrow(maps, "Map<Id, Int>", "list::get(x, 0)")),
        (
            "read-in-block",
            narrow(maps, "Map<Id, Int>", "{ let y = x; list::get(y, 0) }"),
        ),
        (
            "read-in-block-local",
            narrow(
                maps,
                "Map<Id, Int>",
                "let b = { let y = x; list::get(y, 0) };\n    b",
            ),
        ),
        (
            "read-of-block",
            narrow(maps, "Map<Id, Int>", "list::get({ let n = 1; x }, 0)"),
        ),
        (
            "read-of-block-local",
            narrow(
                maps,
                "Map<Id, Int>",
                "let b = list::get({ let n = 1; x }, 0);\n    b",
            ),
        ),
        (
            "untyped-read",
            narrow("x: Term<List>", "Map<Id, Value>", "list::get(x, 0)"),
        ),
        (
            "untyped-read-in-block-local",
            narrow(
                "x: Term<List>",
                "Map<Id, Value>",
                "let b = { let y = x; list::get(y, 0) };\n    b",
            ),
        ),
        (
            "built-in-block",
            format!(
                "{PREAMBLE}{}",
                rules(
                    "probe: { k: [Put(name, s), ..], stack: _ } => { k: [..], stack: { let c = [1, s]; list::concat(c, []) } };"
                )
            ),
        ),
        (
            "built-through-operation",
            format!(
                "{PREAMBLE}{}",
                rules(
                    "probe: { k: [Put(name, s), ..], env: _ } => { k: [..], env: { let c = map::update(map::empty(), name, s); map::update(c, name, 2) } };"
                )
            ),
        ),
        (
            "built-through-operation-local",
            format!(
                "{PREAMBLE}{}",
                rules(
                    "probe: { k: [Put(name, s), ..], env: _ } => { k: [..], env: { let c = map::update(map::empty(), name, s); let b = map::update(c, name, 2); b } };"
                )
            ),
        ),
        (
            "built-through-two-operations-local",
            format!(
                "{PREAMBLE}{}",
                rules(
                    "probe: { k: [Put(name, s), ..], stack: _ } => { k: [..], stack: { let c = [1, s]; let e = list::concat(c, []); let b = list::concat(e, []); b } };"
                )
            ),
        ),
        (
            "built-in-block-local",
            format!(
                "{PREAMBLE}{}",
                rules(
                    "probe: { k: [Put(name, s), ..], stack: _ } => { k: [..], stack: { let b = { let c = [1, s]; list::concat(c, []) }; b } };"
                )
            ),
        ),
    ];
    let mut outcomes = Vec::new();
    for (name, library) in cases {
        let manifest = package(temporary.path(), &format!("scope-{name}"), &library);
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        let verdict = if success {
            "accepted".to_owned()
        } else {
            let (headline, marked) = diagnostics(&stderr)
                .into_iter()
                .next()
                .unwrap_or_else(|| panic!("{name}: {stderr}"));
            format!("{headline} at `{marked}`")
        };
        outcomes.push((name, verdict));
    }
    expect_test::expect![[r#"
        [
            (
                "shadow",
                "error[krs::analysis::collection-element-sort]: `y`, bound to the parameter `x` of `Narrow`, has type `Map<Id, Value>`, which does not fit the result of `Narrow`, declared `Map<Id, Int>`: Value is not an Int at `y`",
            ),
            (
                "shadow-local",
                "error[krs::analysis::collection-element-sort]: `b`, bound to the parameter `x` of `Narrow`, has type `Map<Id, Value>`, which does not fit the result of `Narrow`, declared `Map<Id, Int>`: Value is not an Int at `b`",
            ),
            (
                "part",
                "error[krs::analysis::collection-element-sort]: `first`, bound to an element of the parameter `x` of `Narrow`, has type `Map<Id, Value>`, which does not fit the result of `Narrow`, declared `Map<Id, Int>`: Value is not an Int at `first`",
            ),
            (
                "part-local",
                "error[krs::analysis::collection-element-sort]: `b`, bound to an element of the parameter `x` of `Narrow`, has type `Map<Id, Value>`, which does not fit the result of `Narrow`, declared `Map<Id, Int>`: Value is not an Int at `b`",
            ),
            (
                "part-second-local",
                "error[krs::analysis::collection-element-sort]: `d`, bound to an element of the parameter `x` of `Narrow`, has type `Map<Id, Value>`, which does not fit the result of `Narrow`, declared `Map<Id, Int>`: Value is not an Int at `d`",
            ),
            (
                "read",
                "error[krs::analysis::collection-element-sort]: `list::get(..)`, read from the parameter `x` of `Narrow`, has type `Map<Id, Value>`, which does not fit the result of `Narrow`, declared `Map<Id, Int>`: Value is not an Int at `list::get`",
            ),
            (
                "read-in-block",
                "error[krs::analysis::collection-element-sort]: `list::get(..)`, read from the parameter `x` of `Narrow`, has type `Map<Id, Value>`, which does not fit the result of `Narrow`, declared `Map<Id, Int>`: Value is not an Int at `list::get`",
            ),
            (
                "read-in-block-local",
                "error[krs::analysis::collection-element-sort]: `b`, bound to the parameter `x` of `Narrow`, has type `Map<Id, Value>`, which does not fit the result of `Narrow`, declared `Map<Id, Int>`: Value is not an Int at `b`",
            ),
            (
                "read-of-block",
                "error[krs::analysis::collection-element-sort]: `list::get(..)`, read from the parameter `x` of `Narrow`, has type `Map<Id, Value>`, which does not fit the result of `Narrow`, declared `Map<Id, Int>`: Value is not an Int at `list::get`",
            ),
            (
                "read-of-block-local",
                "error[krs::analysis::collection-element-sort]: `b`, bound to the parameter `x` of `Narrow`, has type `Map<Id, Value>`, which does not fit the result of `Narrow`, declared `Map<Id, Int>`: Value is not an Int at `b`",
            ),
            (
                "untyped-read",
                "error[krs::analysis::untyped-collection]: `list::get(..)` reads a collection whose element types are not declared, so nothing checks the elements it writes to the result of `Narrow`, declared `Map<Id, Value>` at `list::get`",
            ),
            (
                "untyped-read-in-block-local",
                "error[krs::analysis::untyped-collection]: `b` is bound to `list::get(..)`, and `list::get(..)` reads a collection whose element types are not declared, so nothing checks the elements it writes to the result of `Narrow`, declared `Map<Id, Value>` at `b`",
            ),
            (
                "built-in-block",
                "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `stack`, declared `List<Value>`, and Stmt is not a Value at `s`",
            ),
            (
                "built-through-operation",
                "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as a value of the cell `env`, declared `Map<Id, Value>`, and Stmt is not a Value at `s`",
            ),
            (
                "built-through-operation-local",
                "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as a value of the cell `env`, declared `Map<Id, Value>`, and Stmt is not a Value at `s`",
            ),
            (
                "built-through-two-operations-local",
                "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `stack`, declared `List<Value>`, and Stmt is not a Value at `s`",
            ),
            (
                "built-in-block-local",
                "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `stack`, declared `List<Value>`, and Stmt is not a Value at `s`",
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// A configuration with list cells of three kinds (a typed and a bare builtin `List`, a cons
/// list), and constructors whose fields declare lists, `KItem` and `K`.
const BRACKETS: &str = r#"
use k::builtin::{Id, Int, KSequence, List, list};
use k::{KItem, KResult, Term};

k::sorts! {
    Stmt;
    Value: KResult;
    impl Value for Int;
    WordStack: KItem;
}

#[k::constructors(sort = WordStack, result = KResult)]
#[k::cons_list]
#[k::precedence((StackEmpty, StackCons))]
pub enum Stack {
    #[k::syntax(".WordStack")]
    StackEmpty(),
    #[k::syntax("{head} : {tail}")]
    StackCons { head: Int, tail: WordStack },
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Go, Put, Hold, HoldV, Both, Twice, Item, Code, Mixed))]
pub enum StmtSyntax {
    #[k::syntax("go")]
    Go(),
    #[k::syntax("put {name} {s}")]
    Put { name: Id, s: Stmt },
    #[k::syntax("hold {l}")]
    Hold { l: List },
    #[k::syntax("holdv {l}")]
    HoldV { l: List<Value> },
    #[k::syntax("both {l} {w}")]
    Both { l: List, w: WordStack },
    #[k::syntax("twice {a} {v}")]
    Twice { a: List<Int>, v: List<Value> },
    #[k::syntax("item {x}")]
    Item { x: KItem },
    #[k::syntax("code {c}")]
    Code { c: KSequence },
    #[k::syntax("mixed {x} {l}")]
    Mixed { x: KItem, l: List },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub stack: List<Value>,
    #[k::cell]
    pub bare: List,
    #[k::cell]
    pub words: WordStack,
    #[k::cell]
    pub gas: Int,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            stack: list::empty(),
            bare: list::empty(),
            words: WORDS,
            gas: 0,
        }
    }
}
"#;

/// Brackets denote the list of the sort they are read at, and a local names its value, so
/// brackets bound by a local are read at the sort its uses stand at, as the same brackets
/// written there are: a builtin `List` (typed or bare) or a cons list, through one local or
/// two, on every route a `let` reaches (a readable result, a `cells!` result, a claim, an
/// initializer), and the accepted forms run to the same configuration. Uses at several
/// sorts give the brackets the one sort those share (`List` beside `KItem`); uses at sorts
/// no list shares, a local no use sorts, and a use at a sort that is no list are refused, the
/// last as the brackets written there are.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of spellings, each with its verdict."
)]
fn brackets_bound_by_a_local_are_the_list_of_its_uses() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = |cell: &str, value: &str| {
        rules(&format!(
            "probe: {{ k: [Go(), ..], {cell}: _ }} => {{ k: [..], {cell}: {value} }};"
        ))
    };
    let item = |value: &str| {
        rules(&format!(
            "probe: {{ k: [HoldV([v, ..]), ..] }} => {{ k: [{value}, ..] }};"
        ))
    };
    let cells = |value: &str| {
        format!(
            "#[k::rule]\npub fn probe(\n    k::cells! {{ k: k::configuration::KCell(StmtSyntax::Go(), tail @ ..), words: k::configuration::Cell(_), state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), words: k::configuration::Cell({value}), ..state }}\n}}\n"
        )
    };
    let claim = |value: &str| {
        format!(
            "k::claims! {{\n    for Machine;\n    use StmtSyntax::*;\n\n    #[k::claim(all_paths)]\n    probe: {{ k: [Go()], words: _ }} => {{ k: [], words: {value} }};\n}}\n"
        )
    };
    let local = |value: &str| format!("{{ let b = {value}; b }}");
    let second = |value: &str| format!("{{ let b = {value}; let c = b; c }}");
    // (name, library, words' initializer, the cell `krs run go` reads).
    let mut forms = Vec::<(String, String, String, Option<&str>)>::new();
    let empty = "Stack::StackEmpty()".to_owned();
    for (cell, value) in [
        ("stack", "[1, 2]"),
        ("bare", "[1, 2]"),
        ("words", "[1, 2]"),
        ("words", "[]"),
    ] {
        for (spelling, written) in [
            ("direct", value.to_owned()),
            ("local", local(value)),
            ("second-local", second(value)),
        ] {
            forms.push((
                format!("{cell}-{value}-{spelling}"),
                readable(cell, &written),
                empty.clone(),
                Some(cell),
            ));
        }
    }
    let spellings = |name: &str, direct: &str, written: &str| {
        [
            (format!("{name}-direct"), direct.to_owned()),
            (format!("{name}-local"), written.to_owned()),
        ]
    };
    for (name, written) in spellings("cells", "[1, 2]", &local("[1, 2]")) {
        forms.push((name, cells(&written), empty.clone(), Some("words")));
    }
    for (name, written) in spellings("claim", "[1, 2]", &local("[1, 2]")) {
        forms.push((name, claim(&written), empty.clone(), None));
    }
    for (name, written) in spellings("init", "[1, 2]", &local("[1, 2]")) {
        forms.push((name, String::new(), written, Some("words")));
    }
    let neighbours = [
        // An element that fits the list it is read as, through the local as directly.
        (
            "element-direct",
            readable("stack", "[1, s]").replace("Go()", "Put(_, s)"),
        ),
        (
            "element-local",
            readable("stack", &local("[1, s]")).replace("Go()", "Put(_, s)"),
        ),
        // Two element types: the binder takes the narrower, as written twice directly.
        ("element-types-direct", item("Twice([v], [v])")),
        ("element-types-local", item("{ let b = [v]; Twice(b, b) }")),
        // `List` beside `KItem`: the list, which is a `KItem`.
        ("list-and-item", item("{ let b = [1]; Mixed(b, b) }")),
        // A `KItem` or `K` position alone is no list, as for the brackets written there.
        ("item-direct", item("Item([1])")),
        ("item-local", item("{ let b = [1]; Item(b) }")),
        ("sequence-direct", item("Code([1])")),
        ("sequence-local", item("{ let b = [1]; Code(b) }")),
        // A builtin `List` and a cons list: no one list.
        ("two-lists", item("{ let b = [1, 2]; Both(b, b) }")),
        // No use where a sort is declared.
        ("unused", readable("gas", "{ let b = [1, 2]; 3 }")),
        ("index", readable("gas", "{ let b = [1, 2]; b[0] }")),
        // Inside a built value, at an ascription, in a block.
        (
            "concat-direct",
            readable("bare", "list::concat([1, 2], [3])"),
        ),
        (
            "concat-local",
            readable("bare", "{ let b = [1, 2]; list::concat(b, [3]) }"),
        ),
        ("ascribed", readable("bare", "{ let b: List = [1, 2]; b }")),
        (
            "ascribed-other",
            readable("words", "{ let b: List = [1, 2]; b }"),
        ),
        (
            "block",
            readable("bare", "{ let b = { let n = 1; [n, 2] }; b }"),
        ),
    ];
    for (name, library) in neighbours {
        forms.push((name.to_owned(), library, empty.clone(), None));
    }
    let mut outcomes = Vec::new();
    for (name, library, words, cell) in forms {
        let source = format!("{}{library}", BRACKETS.replace("WORDS", &words));
        let manifest = package(
            temporary.path(),
            &name.replace(['[', ']', ',', ' '], "_"),
            &source,
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        if !success {
            let (headline, marked) = diagnostics(&stderr)
                .into_iter()
                .next()
                .unwrap_or_else(|| panic!("{name}: {stderr}"));
            outcomes.push((name, format!("{headline} at `{marked}`")));
            continue;
        }
        let output = manifest.with_file_name("emitted");
        let (success, _, stderr) = krs(
            target.path(),
            &manifest,
            "emit-k",
            &["--output", output.to_str().unwrap()],
        );
        assert!(success, "{name}: {stderr}");
        let read = |file: &str| {
            krs_test_support::without_source_comments(
                &fs::read_to_string(output.join(file)).unwrap_or_default(),
            )
        };
        let mut verdict = if library.is_empty() {
            let definition = read("definition.k");
            let start = definition.find("<words>").unwrap();
            let end = definition[start..].find("</words>").unwrap() + start;
            format!("accepted: {}", &definition[start..end + "</words>".len()])
        } else if library.contains("k::claims!") {
            // A claim's block is lifted into a function whose one equation is the block.
            let spec = read("spec.k");
            let start = spec.find("claim").unwrap();
            let claim = spec[start..]
                .lines()
                .skip(1)
                .take_while(|line| !line.trim().is_empty());
            let lifted = read("definition.k")
                .lines()
                .map(str::trim)
                .filter(|line| line.starts_with("rule krsLocal_"))
                .map(|line| line.split(" [label(").next().unwrap().to_owned())
                .collect::<Vec<_>>();
            format!(
                "accepted: {}{}",
                claim.map(str::trim).collect::<Vec<_>>().join(" "),
                lifted.iter().fold(String::new(), |mut out, rule| {
                    write!(out, "; {rule}").unwrap();
                    out
                })
            )
        } else {
            format!("accepted: {}", rule(&read("definition.k"), "probe"))
        };
        if let Some(cell) = cell {
            let program = manifest.with_file_name("program.txt");
            fs::write(&program, "go").unwrap();
            let (_, stdout, stderr) = krs(
                target.path(),
                &manifest,
                "run",
                &[program.to_str().unwrap()],
            );
            let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
            let open = format!("<{cell}> ");
            let start = flat
                .find(&open)
                .unwrap_or_else(|| panic!("{name}: no <{cell}>:\n{stdout}\n{stderr}"))
                + open.len();
            let end = start + flat[start..].find(&format!(" </{cell}>")).unwrap();
            write!(
                verdict,
                "; runs to <{cell}> {} </{cell}>",
                &flat[start..end]
            )
            .unwrap();
        }
        outcomes.push((name, verdict));
    }
    expect_test::expect![[r#"
        [
            (
                "stack-[1, 2]-direct",
                "accepted: <k> go => .K ... </k> <stack> _ => ListItem(1) ListItem(2) </stack> endmodule; runs to <stack> ListItem ( 1 ) ListItem ( 2 ) </stack>",
            ),
            (
                "stack-[1, 2]-local",
                "accepted: <k> go => .K ... </k> <stack> _ => ( #let B:List = ListItem(1) ListItem(2) #in B:List ) </stack> endmodule; runs to <stack> ListItem ( 1 ) ListItem ( 2 ) </stack>",
            ),
            (
                "stack-[1, 2]-second-local",
                "accepted: <k> go => .K ... </k> <stack> _ => ( #let B:List = ListItem(1) ListItem(2) #in ( #let C:List = B:List #in C:List ) ) </stack> endmodule; runs to <stack> ListItem ( 1 ) ListItem ( 2 ) </stack>",
            ),
            (
                "bare-[1, 2]-direct",
                "accepted: <k> go => .K ... </k> <bare> _ => ListItem(1) ListItem(2) </bare> endmodule; runs to <bare> ListItem ( 1 ) ListItem ( 2 ) </bare>",
            ),
            (
                "bare-[1, 2]-local",
                "accepted: <k> go => .K ... </k> <bare> _ => ( #let B:List = ListItem(1) ListItem(2) #in B:List ) </bare> endmodule; runs to <bare> ListItem ( 1 ) ListItem ( 2 ) </bare>",
            ),
            (
                "bare-[1, 2]-second-local",
                "accepted: <k> go => .K ... </k> <bare> _ => ( #let B:List = ListItem(1) ListItem(2) #in ( #let C:List = B:List #in C:List ) ) </bare> endmodule; runs to <bare> ListItem ( 1 ) ListItem ( 2 ) </bare>",
            ),
            (
                "words-[1, 2]-direct",
                "accepted: <k> go => .K ... </k> <words> _ => 1 : 2 : . WordStack </words> endmodule; runs to <words> 1 : 2 : .WordStack </words>",
            ),
            (
                "words-[1, 2]-local",
                "accepted: <k> go => .K ... </k> <words> _ => ( #let B:WordStack = 1 : 2 : . WordStack #in B:WordStack ) </words> endmodule; runs to <words> 1 : 2 : .WordStack </words>",
            ),
            (
                "words-[1, 2]-second-local",
                "accepted: <k> go => .K ... </k> <words> _ => ( #let B:WordStack = 1 : 2 : . WordStack #in ( #let C:WordStack = B:WordStack #in C:WordStack ) ) </words> endmodule; runs to <words> 1 : 2 : .WordStack </words>",
            ),
            (
                "words-[]-direct",
                "accepted: <k> go => .K ... </k> <words> _ => . WordStack </words> endmodule; runs to <words> .WordStack </words>",
            ),
            (
                "words-[]-local",
                "accepted: <k> go => .K ... </k> <words> _ => ( #let B:WordStack = . WordStack #in B:WordStack ) </words> endmodule; runs to <words> .WordStack </words>",
            ),
            (
                "words-[]-second-local",
                "accepted: <k> go => .K ... </k> <words> _ => ( #let B:WordStack = . WordStack #in ( #let C:WordStack = B:WordStack #in C:WordStack ) ) </words> endmodule; runs to <words> .WordStack </words>",
            ),
            (
                "cells-direct",
                "accepted: <k> go ~> Tail:K => .K ~> Tail:K </k> <words> _ => 1 : 2 : . WordStack </words> endmodule; runs to <words> 1 : 2 : .WordStack </words>",
            ),
            (
                "cells-local",
                "accepted: <k> go ~> Tail:K => .K ~> Tail:K </k> <words> _ => ( #let B:WordStack = 1 : 2 : . WordStack #in B:WordStack ) </words> endmodule; runs to <words> 1 : 2 : .WordStack </words>",
            ),
            (
                "claim-direct",
                "accepted: <k> go => .K </k> <words> _ => 1 : 2 : . WordStack </words> endmodule",
            ),
            (
                "claim-local",
                "accepted: <k> go => .K </k> <words> _ => krsLocal_e28842afa37a9a0306ce89f7 ( ) </words> endmodule; rule krsLocal_e28842afa37a9a0306ce89f7 ( ) => ( #let B:WordStack = 1 : 2 : . WordStack #in B:WordStack )",
            ),
            (
                "init-direct",
                "accepted: <words> 1 : 2 : . WordStack </words>; runs to <words> 1 : 2 : .WordStack </words>",
            ),
            (
                "init-local",
                "accepted: <words> ( #let B:WordStack = 1 : 2 : . WordStack #in B:WordStack ):WordStack </words>; runs to <words> 1 : 2 : .WordStack </words>",
            ),
            (
                "element-direct",
                "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `stack`, declared `List<Value>`, and Stmt is not a Value at `s`",
            ),
            (
                "element-local",
                "error[krs::analysis::collection-element-sort]: `s` of sort Stmt is stored as an element of the cell `stack`, declared `List<Value>`, and Stmt is not a Value at `s`",
            ),
            (
                "element-types-direct",
                "accepted: <k> holdv ListItem(V:Int) _ => twice ListItem(V:Int) ListItem(V:Int) ... </k> endmodule",
            ),
            (
                "element-types-local",
                "accepted: <k> holdv ListItem(V:Int) _ => ( #let B:List = ListItem(V:Int) #in twice B:List B:List ) ... </k> endmodule",
            ),
            (
                "list-and-item",
                "accepted: <k> holdv ListItem(V:Value) _ => ( #let B:List = ListItem(1) #in mixed B:List B:List ) ... </k> endmodule",
            ),
            (
                "item-direct",
                "error[krs::analysis::invalid-list-notation]: list notation builds a list, but this position has sort `KItem`, which is not one: a list is the builtin `List`, a `#[k::syntax_list]` sort, or the sort of a `#[k::cons_list]` constructors enum at `1]`",
            ),
            (
                "item-local",
                "error[krs::analysis::invalid-list-notation]: list notation builds a list, but this position has sort `KItem`, which is not one: a list is the builtin `List`, a `#[k::syntax_list]` sort, or the sort of a `#[k::cons_list]` constructors enum at `1]`",
            ),
            (
                "sequence-direct",
                "error[krs::analysis::invalid-list-notation]: list notation builds a list, but this position has sort `K`, which is not one: a list is the builtin `List`, a `#[k::syntax_list]` sort, or the sort of a `#[k::cons_list]` constructors enum; brackets are a computation's items only as the entry of a computation cell or child (`KCell(x, ..)`, `cc: [x, ..]`), and a term of sort `K` elsewhere, a constructor's field or a function's argument, is a binder of that sort, such as a computation cell's `rest @ ..`; an instance or group child's brackets with a named rest (`rest @ ..`, `..rest`), and a `?` computation's items in a readable record, are not supported yet at `1]`",
            ),
            (
                "sequence-local",
                "error[krs::analysis::invalid-list-notation]: list notation builds a list, but this position has sort `K`, which is not one: a list is the builtin `List`, a `#[k::syntax_list]` sort, or the sort of a `#[k::cons_list]` constructors enum; brackets are a computation's items only as the entry of a computation cell or child (`KCell(x, ..)`, `cc: [x, ..]`), and a term of sort `K` elsewhere, a constructor's field or a function's argument, is a binder of that sort, such as a computation cell's `rest @ ..`; an instance or group child's brackets with a named rest (`rest @ ..`, `..rest`), and a `?` computation's items in a readable record, are not supported yet at `1]`",
            ),
            (
                "two-lists",
                "error[krs::analysis::invalid-list-notation]: `b` is bound to list brackets, which denote the list of the sort they are read at, and `b` is used at `WordStack` and at `List`, which share no one sort, so the brackets name no one list; bind a list for each position at `1, 2]`",
            ),
            (
                "unused",
                "error[krs::analysis::invalid-list-notation]: `b` is bound to list brackets, which denote the list of the sort they are read at, but no use of `b` stands where a sort is declared, so they name no list; use `b` where a constructor field, a cell, a function parameter, or a result declares the builtin `List` or a cons-list sort, or ascribe it (`let b: List = ..`) at `1, 2]`",
            ),
            (
                "index",
                "error[krs::analysis::invalid-list-notation]: `b` is bound to list brackets, which denote the list of the sort they are read at, but no use of `b` stands where a sort is declared, so they name no list; use `b` where a constructor field, a cell, a function parameter, or a result declares the builtin `List` or a cons-list sort, or ascribe it (`let b: List = ..`) at `1, 2]`",
            ),
            (
                "concat-direct",
                "accepted: <k> go => .K ... </k> <bare> _ => ListItem(1) ListItem(2) ListItem(3) </bare> endmodule",
            ),
            (
                "concat-local",
                "accepted: <k> go => .K ... </k> <bare> _ => ( #let B:List = ListItem(1) ListItem(2) #in B:List ListItem(3) ) </bare> endmodule",
            ),
            (
                "ascribed",
                "accepted: <k> go => .K ... </k> <bare> _ => ( #let B:List = ListItem(1) ListItem(2) #in B:List ) </bare> endmodule",
            ),
            (
                "ascribed-other",
                "error[krs::analysis::invalid-let]: `b` is bound by a `let` or `ml::exists` at sort `List`, which is not admissible at sort `WordStack` at `b`",
            ),
            (
                "block",
                "accepted: <k> go => .K ... </k> <bare> _ => ( #let B:List = ( #let N:Int = 1 #in ListItem(N:Int) ListItem(2) ) #in B:List ) </bare> endmodule",
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
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
    let definition = krs_test_support::without_source_comments(
        &fs::read_to_string(output.join("definition.k")).unwrap(),
    );
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
            "rewrite-dot-k",
            "#[k::rule]\npub fn probe(\n    k::cells! { k: k::configuration::KCell(k::rewrite!(StmtSyntax::Skip() => ()), ..), env: k::configuration::Cell(map![k::id!(\"$x\") -> k::rewrite!(_ => ()), ..]), .. }: Machine,\n) {}\n".to_owned(),
            stored("()", "K", env_value, "a Value"),
            "()",
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
        krs_test_support::without_source_comments(
            &fs::read_to_string(output.join("definition.k")).unwrap()
        )
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
