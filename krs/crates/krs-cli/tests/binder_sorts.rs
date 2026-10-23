//! The sort a binder gets, end to end: an existential or fresh binder has
//! exactly its declared sort in every rule form, and every sort but `K` is a
//! `KItem`, so a `KItem` position admits a term of any other sort and never
//! narrows a binder.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Id, Int, KSequence, List, Map, Set, list, map, set};
use k::{KItem, KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
    Exp;
    impl Exp for Int;
    Frame;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Skip, Seq, Op, Put, Pair))]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("seq ( {first} , {second} )")]
    Seq { first: Stmt, second: Stmt },
    #[k::syntax("op {code}")]
    Op { code: Int },
    #[k::syntax("put {name} {s}")]
    Put { name: Id, s: Stmt },
    #[k::syntax("pair ( {a} , {b} )")]
    Pair { a: Exp, b: Exp },
}

#[k::constructors(sort = Frame, result = KResult)]
#[k::precedence((Hold))]
pub enum FrameSyntax {
    #[k::syntax("hold ( {saved} )")]
    Hold { saved: KItem },
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
    pub queue: List,
    #[k::cell]
    pub acc: Int,
    #[k::cell]
    pub raw: Map,
    #[k::cell]
    pub raw2: Map,
    #[k::cell]
    pub bag: Set,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: map::empty(),
            stack: list::empty(),
            queue: list::empty(),
            acc: 0,
            raw: map::empty(),
            raw2: map::empty(),
            bag: set::empty(),
        }
    }
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is the preamble and `body`.
fn package(root: &Path, name: &str, body: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{PREAMBLE}{body}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-BINDERS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// Emits the package's K and returns `definition.k`.
fn emitted(target: &Path, manifest: &Path) -> String {
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

/// The rule's body lines in the emitted K, joined.
fn rule(definition: &str, label: &str) -> String {
    let start = definition
        .find(&format!("rule [{label}]:"))
        .unwrap_or_else(|| panic!("no rule {label}:\n{definition}"));
    definition[start..]
        .lines()
        .skip(1)
        .take_while(|line| {
            let line = line.trim();
            !line.is_empty()
                && !["rule", "//", "endmodule"]
                    .iter()
                    .any(|start| line.starts_with(start))
        })
        .map(str::trim)
        .collect::<Vec<_>>()
        .join(" ")
}

fn rules(body: &str) -> String {
    format!(
        "k::rules! {{\n    for Machine;\n    use StmtSyntax::*;\n    use FrameSyntax::*;\n\n    {body}\n}}\n"
    )
}

/// Asserts that `krs check` rejects each case with the expected first
/// diagnostic and caret.
fn assert_rejected(target: &Path, root: &Path, cases: &[(&str, String, String, &str)]) {
    for (name, source, headline, marked) in cases {
        let manifest = package(root, name, source);
        let (success, _, stderr) = krs(target, &manifest, "check", &["--backend", "haskell"]);
        assert!(!success, "{name}: krs check unexpectedly passed:\n{stderr}");
        assert_eq!(
            diagnostics(&stderr).first(),
            Some(&(headline.clone(), (*marked).to_owned())),
            "{name}:\n{stderr}"
        );
    }
}

/// An existential or fresh binder is a value of exactly its declared sort:
/// an occurrence whose position needs a sort the declared one is not below
/// is rejected in every rule form, at the declaration or, at a typed element
/// position, at the occurrence with the declared element type; one that fits
/// keeps its declared sort.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of rejected rules, each with its expected diagnostic."
)]
fn existential_and_fresh_binders_keep_their_declared_sort() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let incompatible = |name: &str, declared: &str, needed: &str| {
        format!(
            "error[krs::analysis::incompatible-binder]: binder `{name}` is declared `{declared}` but this occurrence needs `{needed}`"
        )
    };
    let stored = |term: &str, sort: &str, position: &str, element: &str| {
        format!(
            "error[krs::analysis::collection-element-sort]: `{term}` of sort {sort} is stored as {position}, and {sort} is not {element}"
        )
    };
    let env_value = "a value of the cell `env`, declared `Map<Id, Value>`";
    let cells_rule = |sort: &str| {
        format!(
            "#[k::rule]\n#[k::exists(v: {sort})]\npub fn probe(\n    k::cells! {{ k: k::configuration::KCell(StmtSyntax::Op(1), tail @ ..), state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(StmtSyntax::Op(v), ..tail), ..state }}\n}}\n"
        )
    };
    assert_rejected(
        target.path(),
        temporary.path(),
        &[
            (
                "unrelated",
                rules("#[k::exists(v: Stmt)]\n    probe: { k: [Op(1), ..] } => { k: [Op(v), ..] };"),
                incompatible("v", "Stmt", "Int"),
                "Stmt",
            ),
            (
                "wider",
                rules("#[k::exists(v: Value)]\n    probe: { k: [Op(1), ..] } => { k: [Op(v), ..] };"),
                incompatible("v", "Value", "Int"),
                "Value",
            ),
            (
                "map-value",
                rules(
                    "#[k::exists(v: Stmt)]\n    probe: { k: [Put(name, _), ..], env: e } => { k: [..], env: map::update(e, name, v) };",
                ),
                stored("v", "Stmt", env_value, "a Value"),
                "v",
            ),
            (
                "fresh-element",
                rules(
                    "#[k::fresh(n: Id)]\n    probe: { k: [Op(1), ..], stack: l } => { k: [..], stack: [n, ..l] };",
                ),
                stored(
                    "n",
                    "Id",
                    "an element of the cell `stack`, declared `List<Value>`",
                    "a Value",
                ),
                "n",
            ),
            (
                "claim",
                "k::claims! {\n    for Machine;\n    use StmtSyntax::*;\n\n    #[k::claim(all_paths)]\n    #[k::exists(v: Stmt)]\n    probe: { k: [Put(name, _)], env: e } => { k: [], env: map::update(e, name, v) };\n}\n".to_owned(),
                stored("v", "Stmt", env_value, "a Value"),
                "v",
            ),
            (
                "term-rule",
                "#[k::rule]\n#[k::exists(v: Stmt)]\npub fn probe(k::term![StmtSyntax::Op(1)]: Term<Stmt>) -> Term<Stmt> {\n    StmtSyntax::Op(v)\n}\n".to_owned(),
                incompatible("v", "Stmt", "Int"),
                "Stmt",
            ),
            (
                "cells-unrelated",
                cells_rule("Stmt"),
                incompatible("v", "Stmt", "Int"),
                "Stmt",
            ),
            (
                "cells-wider",
                cells_rule("Value"),
                incompatible("v", "Value", "Int"),
                "Value",
            ),
        ],
    );

    let manifest = package(
        temporary.path(),
        "fitting",
        &format!(
            "{}{}",
            rules(
                "#[k::exists(v: Int)]\n    narrow: { k: [Op(1), ..] } => { k: [Op(v), ..] };\n    #[k::exists(w: Int)]\n    store: { k: [Put(name, _), ..], env: e } => { k: [..], env: map::update(e, name, w) };\n    #[k::fresh(n: Int)]\n    push: { k: [Op(2), ..], stack: l } => { k: [..], stack: [n, ..l] };"
            ),
            cells_rule("Int")
                .replace("probe", "cells_probe")
                .replace("Op(1)", "Op(3)"),
        ),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &["--backend", "haskell"]);
    assert!(success, "{stderr}");
    let definition = emitted(target.path(), &manifest);
    expect_test::expect![[r#"
        [
            "<k> op 1 => op ?V:Int ... </k>",
            "<k> put Name:Id _ => .K ... </k> <env> E:Map => E:Map [ Name:Id <- ?W:Int ] </env>",
            "<k> op 2 => .K ... </k> <stack> L:List => ListItem(!N:Int) L:List </stack>",
        ]
    "#]]
    .assert_debug_eq(&[
        rule(&definition, "narrow"),
        rule(&definition, "store"),
        rule(&definition, "push"),
    ]);
}

/// Every sort but `K` is a `KItem`, declared or not: a `KItem` field,
/// parameter, or result admits a term of any such sort, and a `KItem`
/// occurrence never narrows a binder, which takes the most specific sort its
/// other occurrences admit, its declared sort, or `KItem` alone.
#[test]
fn a_k_item_position_admits_every_sort_and_never_narrows() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "k-item",
        &format!(
            "{}{}",
            r"
/// Holds a statement as a computation item.
#[k::function(total, internal)]
pub fn Wrapped(s: Term<Stmt>) -> Term<KItem> {
    s
}

/// Holds any item in a frame.
#[k::function(total, internal)]
pub fn Keep(x: Term<KItem>) -> Term<Frame> {
    FrameSyntax::Hold(x)
}

#[k::rule]
pub fn cells_unhold(
    s: Term<Stmt>,
    k::cells! { k: k::configuration::KCell(StmtSyntax::Op(9), FrameSyntax::Hold(s), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(s, ..tail), ..state }
}

#[k::rule]
fn unhold(s: Term<Stmt>, k::term![FrameSyntax::Hold(s)]: Term<Frame>) -> Term<KItem> {
    s
}

#[k::rule]
fn unhold_twice(k::term![FrameSyntax::Hold(FrameSyntax::Hold(s))]: Term<Frame>) -> Term<KItem> {
    s
}
",
            rules(
                "declared: { k: [Op(1), Hold { saved: s }, ..] } => { k: [s, ..] } where s: Stmt;
    inferred: { k: [Op(2), Hold { saved: s }, ..] } => { k: [Seq { first: s, second: s }, ..] };
    nested: { k: [Op(3), Hold { saved: Seq { first: a, second: b } }, ..] } => { k: [a, b, ..] };
    store_skip: { k: [Op(4), ..] } => { k: [Hold { saved: Skip() }, ..] };
    store_bool: { k: [Op(5), ..] } => { k: [Hold { saved: true }, ..] };
    store_frame: { k: [Op(6), Hold { saved: Hold { saved: s } }, ..] } => { k: [s, ..] };
    only_k_item: { k: [Op(7), Hold { saved: s }, ..] } => { k: [s, ..] };
    narrower: { k: [Op(8), Hold { saved: s }, ..] } => { k: [s, ..] } where s: Int;
    call: { k: [Op(10), ..] } => { k: [Keep(Skip()), Wrapped(Skip()), ..] };"
            ),
        ),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");
    let definition = emitted(target.path(), &manifest);
    let mut term_rules = definition
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("rule ") && !line.starts_with("rule ["))
        .map(|line| line.split(" [label").next().unwrap().to_owned())
        .collect::<Vec<_>>();
    term_rules.sort();
    expect_test::expect![[r#"
        (
            [
                "<k> op 1 ~> hold ( S:Stmt ) => S:Stmt ... </k>",
                "<k> op 2 ~> hold ( S:Stmt ) => seq ( S:Stmt , S:Stmt ) ... </k>",
                "<k> op 3 ~> hold ( seq ( A:Stmt , B:Stmt ) ) => A:Stmt ~> B:Stmt ... </k>",
                "<k> op 4 => hold ( skip ) ... </k>",
                "<k> op 5 => hold ( true ) ... </k>",
                "<k> op 6 ~> hold ( hold ( S:KItem ) ) => S:KItem ... </k>",
                "<k> op 7 ~> hold ( S:KItem ) => S:KItem ... </k>",
                "<k> op 8 ~> hold ( S:Int ) => S:Int ... </k>",
                "<k> op 9 ~> hold ( S:Stmt ) ~> Tail:K => S:Stmt ~> Tail:K </k>",
                "<k> op 10 => keep ( skip ) ~> wrapped ( skip ) ... </k>",
            ],
            [
                "rule hold ( S:Stmt ) => S:Stmt",
                "rule hold ( hold ( S:KItem ) ) => S:KItem",
                "rule keep ( X:KItem ) => hold ( X:KItem )",
                "rule wrapped ( S:Stmt ) => S:Stmt",
            ],
        )
    "#]]
    .assert_debug_eq(&(
        [
            "declared",
            "inferred",
            "nested",
            "store-skip",
            "store-bool",
            "store-frame",
            "only-k-item",
            "narrower",
            "cells_unhold",
            "call",
        ]
        .map(|label| rule(&definition, label)),
        term_rules,
    ));
}

/// A binder that is narrowed to `Stmt` rather than `Value` runs on every
/// statement: `holdit` saves the second statement of a `seq` and `unhold`
/// restores it, so `seq(skip, skip)` runs to an empty computation.
#[test]
fn a_held_statement_runs_natively() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "holdit",
        &rules(
            "holdit: { k: [Seq { first: Skip(), second: b }, ..] } => { k: [Hold { saved: b }, ..] };
    unhold: { k: [Hold { saved: s }, ..] } => { k: [s, ..] } where s: Stmt;
    skip: { k: [Skip(), ..] } => { k: [..] };",
        ),
    );
    let definition = emitted(target.path(), &manifest);
    assert_eq!(
        rule(&definition, "holdit"),
        "<k> seq ( skip , B:Stmt ) => hold ( B:Stmt ) ... </k>"
    );
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "seq ( skip , skip )").unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{stdout}\n{stderr}");
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("<k> .K </k>"), "{stdout}\n{stderr}");
}

/// What the completed lattice still rejects: an operator whose operands no
/// occurrence sorts as a builtin domain (the `KItem` occurrence no longer
/// narrows `x` to `Int`), two rules that both apply to a held statement,
/// and a `K` item beside items in a pattern.
#[test]
fn a_k_item_occurrence_chooses_no_operator_and_overlaps_every_sort() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    assert_rejected(
        target.path(),
        temporary.path(),
        &[
            (
                "operator",
                rules(
                    "sum: { k: [Hold { saved: x }, Pair { a: x, b: y }, ..], acc: _ } => { k: [..], acc: x + y };",
                ),
                "error[krs::analysis::ambiguous-operator]: `+` has operands of sorts `Exp` and `Exp`, which choose no builtin domain; write the operation you mean: `a.add::<Int>(b)`, `a.concat::<String>(b)`, or `a.add::<Float>(b)`".to_owned(),
                "+",
            ),
            (
                "overlap",
                rules(
                    "any: { k: [Hold { saved: x }, ..] } => { k: [x, ..] };\n    skip: { k: [Hold { saved: Skip() }, ..] } => { k: [..] };",
                ),
                "error[krs::analysis::overlapping-rule-heads]: rules `any` and `skip` can both apply to the same configuration at the same priority; K would take either one (nondeterminism). If that is intended, put both in one group with `#[k::rule(nondet = NAME)]`; otherwise refine a pattern, add disjoint `where` sorts or complementary requires guards, or order them with `owise` or `priority = N`.".to_owned(),
                "Hold",
            ),
            (
                "sequence",
                format!(
                    "{}{}",
                    "#[k::constructors(sort = Stmt, result = KResult)]\n#[k::precedence((Wrap))]\npub enum WrapSyntax {\n    #[k::syntax(\"wrap ( {body} )\")]\n    Wrap { body: KSequence },\n}\n",
                    rules(
                        "use WrapSyntax::*;\n    probe: { k: [Wrap { body: b }, b, Skip(), ..] } => { k: [..] };"
                    ),
                ),
                "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-BINDERS::probe (rule): K sequence items do not have one most-specific common sort; a `K` item splices into a sequence only in a rule result".to_owned(),
                "",
            ),
        ],
    );
    let manifest = package(
        temporary.path(),
        "turbofish",
        &rules(
            "sum: { k: [Hold { saved: x }, Pair { a: x, b: y }, ..], acc: _ } => { k: [..], acc: x.add::<Int>(y) };",
        ),
    );
    assert_eq!(
        rule(&emitted(target.path(), &manifest), "sum"),
        "<k> hold ( X:Int ) ~> pair ( X:Int , Y:Int ) => .K ... </k> <acc> _ => X:Int +Int Y:Int </acc>"
    );
}
