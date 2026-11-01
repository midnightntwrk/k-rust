//! The terms of a `#[k::init]` initializer are KRS terms, as a rule result's
//! are: constructors (tuple-like or with fields), function applications,
//! builtin calls, and configuration variables, inside a `k::k!` item, a
//! `k::map!` key or value, or a call. rustc checks only what it can check
//! meaningfully: that each name resolves, through the payload's type keys.
//! KRS checks the terms' sorts, a configuration variable's included. Every
//! configuration variable a term names counts as used, so a package that
//! denies warnings builds.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Bytes, Id, Int, KSequence, List, Map, bytes, list};
use k::{KResult, Term};

k::sorts! {
    Stmt;
    Value: KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Skip, Tag, Seq))]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("tag {b}")]
    Tag { b: Bytes },
    #[k::syntax("seq {first} ;")]
    Seq { first: Stmt },
}

#[k::function(total, syntax = "mk({n})")]
pub fn Mk(n: Term<Int>) -> Term<Stmt>;

#[k::equation]
fn mk(n: Term<Int>, Mk(n): Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::Skip()
}

#[k::function(total, syntax = "five()")]
pub fn Five() -> Term<Value>;

#[k::equation]
fn five(Five(): Term<Value>) -> Term<Value> {
    5
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Value>,
    #[k::cell]
    pub stack: List<Stmt>,
    #[k::cell]
    pub acc: Value,
}

"#;

/// The initializer with `k` as its computation cell's value.
fn initializer(k: &str) -> String {
    format!(
        "impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt, n: Id, y: Stmt, x: Value) -> Self {{\n        Self {{\n            k: {k},\n            env: k::map![n -> Five()],\n            stack: list::item(y),\n            acc: x,\n        }}\n    }}\n}}\n"
    )
}

const K: &str = "k::k![pgm, StmtSyntax::Tag(bytes::empty()), Mk(1), StmtSyntax::Seq(pgm), Five()]";

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
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-INIT-TERMS\"\n\n[package.metadata.krs.definitions.main]\n\n[lints.rust]\nwarnings = \"deny\"\n\n[workspace]\nresolver = \"3\"\n",
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

/// The emitted `definition.k`.
fn emit(target: &Path, manifest: &Path) -> String {
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

/// The `configuration` declaration's cell lines.
fn configuration(definition: &str) -> String {
    let start = definition.find("configuration").unwrap();
    definition[start..]
        .lines()
        .skip(1)
        .take_while(|line| !line.trim().is_empty())
        .map(str::trim)
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn initializer_terms_are_krs_terms() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "terms",
        &format!("{PREAMBLE}{}", initializer(K)),
    );
    let definition = emit(target.path(), &manifest);
    expect_test::expect![[r"
        <k> $PGM:Stmt ~> tag .Bytes ~> mk ( 1 ) ~> seq $PGM:Stmt ; ~> five ( ) </k>
        <env> $N:Id |-> five ( ) </env>
        <stack> ListItem($Y:Stmt) </stack>
        <acc> $X:Value </acc>"]]
    .assert_eq(&configuration(&definition));

    // The run starts from the configuration with the functions evaluated.
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "skip").unwrap();
    let (_, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[
            "-c",
            "N=x",
            "-c",
            "Y=skip",
            "-c",
            "X=7",
            program.to_str().unwrap(),
        ],
    );
    let state = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    for cell in [
        r#"<k> skip ~> tag b"" ~> skip ~> seq skip ; ~> 5 ~> .K </k>"#,
        "<env> x |-> 5 </env>",
        "<stack> ListItem ( skip ) </stack>",
        "<acc> 7 </acc>",
    ] {
        assert!(state.contains(cell), "{cell}\n{stdout}\n{stderr}");
    }

    // The expanded initializer reads back to the same configuration.
    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let reference = package(temporary.path(), "expanded", &expanded);
    assert_eq!(
        configuration(&emit(target.path(), &reference)),
        configuration(&definition)
    );
}

#[test]
fn initializer_terms_are_resolved_by_rustc_and_sorted_by_krs() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "misspelled",
            "k::k![pgm, StmtSyntax::Tag(bytes::empty()), Mkk(1)]",
            "error[E0422]: cannot find struct, variant or union type `Mkk` in this scope",
            "Mkk",
        ),
        (
            "ill-sorted",
            "k::k![pgm, StmtSyntax::Tag(bytes::empty()), StmtSyntax::Tag(x)]",
            "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-INIT-TERMS::Machine (configuration): configuration variable `x` of sort ORG-KRS-INIT-TERMS::Value (sort) is not admissible at sort Bytes: it stands for the value given at start, a term of its declared sort; declare the parameter at that sort (`x: Bytes`)",
            "x",
        ),
    ];
    for (name, k, headline, marked) in cases {
        let manifest = package(
            temporary.path(),
            name,
            &format!("{PREAMBLE}{}", initializer(k)),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: {stderr}");
        let lines = stderr.lines().collect::<Vec<_>>();
        let index = lines
            .iter()
            .position(|line| line.starts_with("error"))
            .unwrap_or_else(|| panic!("{name}: {stderr}"));
        assert_eq!(lines[index], headline, "{name}: {stderr}");
        if !marked.is_empty() {
            // `--> path`, ` |`, `N | source`, ` |   ^^^`.
            let source = lines[index + 3].split_once(" | ").unwrap().1;
            let carets = lines[index + 4].split_once(" | ").unwrap().1;
            let start = carets.find('^').unwrap();
            let width = carets[start..].chars().take_while(|c| *c == '^').count();
            assert_eq!(&source[start..start + width], marked, "{name}: {stderr}");
        }
    }
}

/// An initializer that places `item` in `k`, `y` in `stack`, and `acc` in
/// `acc`.
fn shared_initializer(item: &str, acc: &str) -> String {
    format!(
        "impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt, x: Value, y: Stmt) -> Self {{\n        Self {{\n            k: k::k![pgm, {item}, StmtSyntax::Tag(bytes::empty())],\n            env: k::map![],\n            stack: list::item(y),\n            acc: {acc},\n        }}\n    }}\n}}\n"
    )
}

/// A configuration variable denotes the value given at startup, so any
/// number of cells may start from it, and it is a term of its declared sort
/// wherever it stands: a cell's whole content whose sort it is not below is
/// refused at the variable, as any term of that sort would be.
#[test]
fn a_configuration_variable_is_a_term_of_its_declared_sort() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "shared",
        &format!("{PREAMBLE}{}", shared_initializer("y", "x")),
    );
    expect_test::expect![[r"
        <k> $PGM:Stmt ~> $Y:Stmt ~> tag .Bytes </k>
        <env> .Map </env>
        <stack> ListItem($Y:Stmt) </stack>
        <acc> $X:Value </acc>"]]
    .assert_eq(&configuration(&emit(target.path(), &manifest)));

    let manifest = package(
        temporary.path(),
        "wider",
        &format!("{PREAMBLE}{}", shared_initializer("x", "y")),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(!success, "{stderr}");
    let headline = stderr
        .lines()
        .find(|line| line.starts_with("error"))
        .unwrap_or_default();
    assert_eq!(
        headline,
        "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-INIT-TERMS::Machine (configuration): configuration variable `y` of sort ORG-KRS-INIT-TERMS::Stmt (sort) is not admissible at sort ORG-KRS-INIT-TERMS::Value (sort): it stands for the value given at start, a term of its declared sort; declare the parameter at that sort (`y: Value`)",
        "{stderr}"
    );
    assert!(stderr.contains("acc: y,"), "{stderr}");
}

/// Record constructors in initializer terms, as in rule results.
const RECORDS: &str = r#"
#[k::constructors(sort = Value, result = KResult)]
pub enum ValueSyntax {
    #[k::syntax("boxed {v}")]
    Boxed { v: Int },
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    retag: Seq(s) => k::k![s, Tag { b: bytes::empty() }];
}
"#;

/// An initializer whose terms are `k`, `env`, and `stack`.
fn record_initializer(k: &str, env: &str, stack: &str) -> String {
    format!(
        "{PREAMBLE}{RECORDS}impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt, n: Id, y: Stmt, x: Value) -> Self {{\n        Self {{\n            k: {k},\n            env: {env},\n            stack: {stack},\n            acc: x,\n        }}\n    }}\n}}\n"
    )
}

/// `Tag { b: v }` is the term `Tag(v)` is: a record constructor is an
/// initializer term below a cell root, in a `k::map!` value, and as a
/// `k::k!` item, where a rule result may now write one too. Every field is
/// named, or taken from a base with `..base`; an open record is rejected.
#[test]
fn initializer_terms_take_record_syntax() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let records = package(
        temporary.path(),
        "records",
        &record_initializer(
            "k::k![pgm, StmtSyntax::Tag { b: bytes::empty() }, StmtSyntax::Seq { first: pgm }]",
            "k::map![n -> ValueSyntax::Boxed { v: 1 }]",
            "list::concat(list::item(y), list::item(StmtSyntax::Tag { b: bytes::empty() }))",
        ),
    );
    let positional = package(
        temporary.path(),
        "positional",
        &record_initializer(
            "k::k![pgm, StmtSyntax::Tag(bytes::empty()), StmtSyntax::Seq(pgm)]",
            "k::map![n -> ValueSyntax::Boxed(1)]",
            "list::concat(list::item(y), list::item(StmtSyntax::Tag(bytes::empty())))",
        ),
    );
    let definition = emit(target.path(), &records);
    expect_test::expect![[r"
        <k> $PGM:Stmt ~> tag .Bytes ~> seq $PGM:Stmt ; </k>
        <env> $N:Id |-> boxed 1 </env>
        <stack> ListItem($Y:Stmt) ListItem(tag .Bytes) </stack>
        <acc> $X:Value </acc>"]]
    .assert_eq(&configuration(&definition));
    assert_eq!(
        configuration(&emit(target.path(), &positional)),
        configuration(&definition)
    );
    assert!(
        definition.contains("<k> seq S:Stmt ; => S:Stmt ~> tag .Bytes ... </k>"),
        "{definition}"
    );

    let cases = [
        (
            "missing-field",
            "k::map![n -> ValueSyntax::Boxed { }]",
            "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-INIT-TERMS::Machine (configuration): application expects 1 arguments but received 0",
        ),
        (
            "wrong-field",
            "k::map![n -> ValueSyntax::Boxed { w: 1 }]",
            "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-INIT-TERMS::Machine (configuration): named application lacks field \"v\"",
        ),
        (
            "open",
            "k::map![n -> ValueSyntax::Boxed { .. }]",
            "error[krs::expand::initializer-record-update]: `..` leaves a record's other fields open, which only a pattern can: an initializer builds its record, which has no value for them, so name every field, or write `..base` to take them from the record `base`; here it stands in the value of an initializer",
        ),
    ];
    for (name, env, headline) in cases {
        let manifest = package(
            temporary.path(),
            name,
            &record_initializer(
                "k::k![pgm, StmtSyntax::Tag { b: bytes::empty() }]",
                env,
                "list::item(y)",
            ),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: {stderr}");
        let first = stderr
            .lines()
            .find(|line| line.starts_with("error"))
            .unwrap_or_else(|| panic!("{name}: {stderr}"));
        assert_eq!(first, headline, "{name}: {stderr}");
    }
}

/// A configuration with two cells of each kind and a nested group.
const SIBLINGS: &str = r#"
use k::KResult;
use k::builtin::{Bytes, Id, Int, KSequence, List, Map, list};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("tick")]
    Tick(),
    #[k::syntax("wrap ( {v} )")]
    Wrap { v: Int },
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub fk: KSequence,
    #[k::cell]
    pub fenv: Map<Id, Value>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub slot: KSequence,
    #[k::cell]
    pub env: Map<Id, Value>,
    #[k::cell]
    pub env2: Map<Id, Value>,
    #[k::cell]
    pub mem: Bytes,
    #[k::cell]
    pub mem2: Bytes,
    #[k::cell]
    pub stack: List<Stmt>,
    #[k::cell]
    pub stack2: List<Stmt>,
    #[k::cell(nested)]
    pub frame: Frame,
}
"#;

/// An initializer for `SIBLINGS` with `env2` as that cell's value.
fn sibling_initializer(env2: &str) -> String {
    format!(
        "{SIBLINGS}impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt, n: Id) -> Self {{\n        Self {{\n            k: k::k![pgm, StmtSyntax::Tick()],\n            slot: k::k![1, 2],\n            env: k::map![n -> 1],\n            env2: {env2},\n            mem: k::bytes!(b\"a\"),\n            mem2: k::bytes!(b\"b\"),\n            stack: list::item(StmtSyntax::Wrap {{ v: 1 }}),\n            stack2: list::item(StmtSyntax::Wrap {{ v: 2 }}),\n            frame: Frame {{ fk: k::k![3], fenv: k::map![n -> 4] }},\n        }}\n    }}\n}}\n"
    )
}

/// Any number of cells may start with a non-empty `k::k!` or `k::map!`: each
/// node is its own part of the one configuration term, so a second one of a
/// kind, in a sibling cell or in a nested group, is checked, emitted, and run
/// like the first.
#[test]
fn sibling_cells_each_start_with_their_own_structure() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "siblings",
        &sibling_initializer("k::map![n -> 2]"),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");
    let definition = emit(target.path(), &manifest);
    expect_test::expect![[r#"
        <k> $PGM:Stmt ~> tick </k>
        <slot> 1 ~> 2 </slot>
        <env> $N:Id |-> 1 </env>
        <env2> $N:Id |-> 2 </env2>
        <mem> b"a" </mem>
        <mem2> b"b" </mem2>
        <stack> ListItem(wrap ( 1 )) </stack>
        <stack2> ListItem(wrap ( 2 )) </stack2>
        <frame>
        <fk> 3 </fk>
        <fenv> $N:Id |-> 4 </fenv>
        </frame>"#]]
    .assert_eq(&configuration(&definition));

    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "skip").unwrap();
    let (_, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &["--depth", "0", "-c", "N=x", program.to_str().unwrap()],
    );
    let state = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    for cell in [
        "<k> skip ~> tick ~> .K </k>",
        "<slot> 1 ~> 2 ~> .K </slot>",
        "<env> x |-> 1 </env>",
        "<env2> x |-> 2 </env2>",
        "<fk> 3 ~> .K </fk>",
        "<fenv> x |-> 4 </fenv>",
    ] {
        assert!(state.contains(cell), "{cell}\n{stdout}\n{stderr}");
    }

    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let reference = package(temporary.path(), "siblings-expanded", &expanded);
    assert_eq!(emit(target.path(), &reference), definition);

    // A diagnostic in the second map lands on that map's value.
    let ill_sorted = package(
        temporary.path(),
        "siblings-ill-sorted",
        &sibling_initializer("k::map![n -> StmtSyntax::Tick()]"),
    );
    let (success, _, stderr) = krs(target.path(), &ill_sorted, "check", &[]);
    assert!(!success, "{stderr}");
    let lines = stderr.lines().collect::<Vec<_>>();
    let index = lines
        .iter()
        .position(|line| line.starts_with("error"))
        .unwrap_or_else(|| panic!("{stderr}"));
    assert!(
        lines[index].starts_with("error[krs::analysis::collection-element-sort]"),
        "{stderr}"
    );
    let source = lines[index + 3].split_once(" | ").unwrap().1;
    let carets = lines[index + 4].split_once(" | ").unwrap().1;
    let start = carets.find('^').unwrap();
    let width = carets[start..].chars().take_while(|c| *c == '^').count();
    assert!(source.trim_start().starts_with("env2:"), "{stderr}");
    assert_eq!(
        &source[start..start + width],
        "StmtSyntax::Tick",
        "{stderr}"
    );
}

/// A configuration whose cells, map values and list elements are `Int`s,
/// so that a literal stands at each.
const LITERALS: &str = r#"
use k::builtin::{Id, Int, KSequence, List, Map, int, list};

k::sorts! {
    Stmt;
}

#[k::constructors(sort = Stmt, result = k::KResult)]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Int>,
    #[k::cell]
    pub stack: List<Int>,
    #[k::cell]
    pub acc: Int,
    #[k::cell]
    pub total: Int,
}
"#;

/// An initializer for `LITERALS` with `stack`, `acc` and `total` as those
/// cells' values.
fn literal_initializer(stack: &str, acc: &str, total: &str) -> String {
    format!(
        "{LITERALS}impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt, n: Id) -> Self {{\n        Self {{\n            k: k::k![pgm],\n            env: k::map![n -> 1],\n            stack: {stack},\n            acc: {acc},\n            total: {total},\n        }}\n    }}\n}}\n"
    )
}

/// Each literal of an initializer is a node of its own (N26): at a cell's
/// root, in a map value, in a `list::item`, and nested in builtin calls, it
/// is checked like any term, and a diagnostic about one lands on that
/// literal, not on the term that holds it.
#[test]
fn initializer_literals_are_terms_of_their_own() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "literals",
        &literal_initializer("list::item(2)", "3", "int::mul(int::add(1, 2), 4)"),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");

    let cases = [
        ("call", "list::item(2)", "int::add(0, true)"),
        ("item", "list::item(true)", "3"),
    ];
    for (name, stack, acc) in cases {
        let manifest = package(
            temporary.path(),
            &format!("literals-{name}"),
            &literal_initializer(stack, acc, "int::add(1, 2)"),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: {stderr}");
        let lines = stderr.lines().collect::<Vec<_>>();
        let index = lines
            .iter()
            .position(|line| line.starts_with("error"))
            .unwrap_or_else(|| panic!("{name}: {stderr}"));
        // `--> path`, ` |`, `N | source`, ` |   ^^^`.
        let source = lines[index + 3].split_once(" | ").unwrap().1;
        let carets = lines[index + 4].split_once(" | ").unwrap().1;
        let start = carets.find('^').unwrap();
        let width = carets[start..].chars().take_while(|c| *c == '^').count();
        assert_eq!(&source[start..start + width], "true", "{name}: {stderr}");
    }
}

/// A configuration whose computation cell holds the initializer's local terms, with an `Int` and a
/// `Bool` cell for a whole value.
const LOCAL_TERMS: &str = r#"
use k::builtin::{Bool, Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Val: Exp + KResult;
    impl Val for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("pair({a}, {b})")]
    Pair { a: Int, b: Int },
    #[k::syntax("done")]
    Done(),
}

/// A parametric constructor, whose turbofish names its instance.
#[k::constructor(sort = S, syntax = "wrap({inner})")]
pub struct Wrap<S: ?Sized> {
    pub inner: Term<S>,
}

#[k::constant]
pub const BASE: Exp = ExpSyntax::Pair { a: 1, b: 2 };

#[k::constant]
pub const DONE: Exp = ExpSyntax::Done();

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub proj: Int,
    #[k::cell]
    pub flag: Bool,
}
"#;

/// An initializer for `LOCAL_TERMS` whose computation cell holds `pgm` and `items`, with `proj`
/// and `flag` as those cells' values.
fn local_initializer(items: &str, proj: &str, flag: &str) -> String {
    format!(
        "{LOCAL_TERMS}impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Exp, p: Exp, v: Val) -> Self {{\n        Self {{\n            k: k::k![pgm, {items}],\n            proj: {proj},\n            flag: {flag},\n        }}\n    }}\n}}\n"
    )
}

/// Each local term below a cell's root, in the order the run shows its value.
const LOCAL_ITEMS: &str = "Wrap::<dyn ExpSort>(p), { let ExpSyntax::Pair(a, b) = p; ExpSyntax::Pair(b, a) }, k::matches!(p, ExpSyntax::Pair(_, _)), k::matches!(pgm, ExpSyntax::Pair(_, _)), k::is!(Int, v), ExpSyntax::Pair { a: 5, ..p }, ExpSyntax::Pair { b: 7, ..BASE }";

/// An initializer builds a term from its configuration variables and constants as a result builds
/// one from a rule's binders, so it holds what a result holds: a turbofish names a parametric
/// constructor's instance, a `let` block is the term it computes (K's `#let`), `k::matches!` the
/// Bool its test computes (`:=K`), `k::is!` and `k::project!` the sort's predicate and projection,
/// and `Ctor { f: e, ..base }` the record `base` with `f` replaced, which no pattern matched, so its
/// other fields are read by the `let` that destructures it. Each is evaluated when the
/// configuration is built, as any function is.
#[test]
fn an_initializer_holds_what_a_result_holds() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "local-terms",
        &local_initializer(LOCAL_ITEMS, "k::project!(Int, v)", "true"),
    );
    let definition = emit(target.path(), &manifest);
    expect_test::expect![[r"
        <k> $PGM:Exp ~> wrap ( $P:Exp ) ~> ( #let pair ( A:Int , B:Int ) = $P:Exp #in pair ( B:Int , A:Int ) ) ~> ( pair ( _ , _ ) :=K $P:Exp ) ~> ( pair ( _ , _ ) :=K $PGM:Exp ) ~> isInt($V:Val) ~> ( #let pair ( _ , B_2:Int ) = $P:Exp #in pair ( 5 , B_2:Int ) ) ~> ( #let pair ( A_2:Int , _ ) = pair ( 1 , 2 ) #in pair ( A_2:Int , 7 ) ) </k>
        <proj> {$V:Val}:>Int </proj>
        <flag> true </flag>"]]
    .assert_eq(&configuration(&definition));

    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "done").unwrap();
    let (_, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[
            "--depth",
            "0",
            "-c",
            "P=pair(1, 2)",
            "-c",
            "V=7",
            program.to_str().unwrap(),
        ],
    );
    let state = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    for cell in [
        "<k> done ~> wrap ( pair(1, 2) ) ~> pair(2, 1) ~> true ~> false ~> true ~> pair(5, 2) ~> pair(1, 7) ~> .K </k>",
        "<proj> 7 </proj>",
    ] {
        assert!(state.contains(cell), "{cell}\n{stdout}\n{stderr}");
    }

    // The expanded initializer reads back to the same configuration.
    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let reference = package(temporary.path(), "local-terms-expanded", &expanded);
    assert_eq!(
        configuration(&emit(target.path(), &reference)),
        configuration(&definition)
    );
}

/// What an initializer's local terms cannot be, and why: a pattern's `@`, which K's right side
/// does not hold; an open record, which leaves fields no initializer builds; a base of another
/// constructor, or of a sort no record of the update's shares, which has none of the update's
/// fields; and a parametric constructor's update, whose fields take its instance's sort.
#[test]
fn an_initializer_refuses_what_has_no_meaning_or_no_tool_there() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "alias",
            "p, k::matches!(p, q @ ExpSyntax::Pair(_, _))",
            "k::project!(Int, v)",
            "true",
            "error[krs::syntax::invalid-pattern-as]: `name @ pattern` (K's #as) names the term a pattern matched, so it stands only where a sentence matches: a subject, or a `k::matches!` pattern in a condition; a single-body rule's subject outside its `k::rewrite!` islands is kept as it is, and a result only builds; here it stands in a `k::matches!` pattern in the value of an initializer",
        ),
        (
            "open",
            "p, ExpSyntax::Pair { a: 1, .. }",
            "k::project!(Int, v)",
            "true",
            "error[krs::expand::initializer-record-update]: `..` leaves a record's other fields open, which only a pattern can: an initializer builds its record, which has no value for them, so name every field, or write `..base` to take them from the record `base`; here it stands in the value of an initializer",
        ),
        (
            "other-constructor",
            "p, ExpSyntax::Pair { a: 5, ..DONE }",
            "k::project!(Int, v)",
            "true",
            "error[krs::analysis::invalid-record-update]: the base is a record of another constructor, which has none of the update's fields to take: write the record whole",
        ),
        (
            "base-sort",
            "p, { let t = true; ExpSyntax::Pair { a: 1, ..t } }",
            "k::project!(Int, v)",
            "true",
            "error[krs::analysis::invalid-record-update]: the base has sort `Bool` and the record has sort `Exp`, which share no subsort, so the base is never a record of the update's constructor and the update never has a value",
        ),
        (
            "parametric",
            "Wrap::<dyn ExpSort> { inner: p, ..p }",
            "k::project!(Int, v)",
            "true",
            "error[krs::analysis::invalid-record-update]: an initializer's record update takes its base's fields by matching the base against the record's constructor, which needs the fields' sorts; a parametric constructor's fields take its instance's sort, so name every field",
        ),
    ];
    for (name, items, proj, flag, headline) in cases {
        let manifest = package(
            temporary.path(),
            &format!("local-{name}"),
            &local_initializer(items, proj, flag),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: {stderr}");
        let first = stderr
            .lines()
            .find(|line| line.starts_with("error"))
            .unwrap_or_else(|| panic!("{name}: {stderr}"));
        assert_eq!(first, headline, "{name}: {stderr}");
    }
}

/// A leaf cell's whole value is any initializer term of the cell's sort or a subsort. K reads a
/// leaf cell's sort from its initial content's head, and a `let` block (`#let`), `k::matches!`
/// (`:=K`), `k::is!` (a sort predicate) and a parametric constructor's application head no
/// production that gives it, so KRS states the cell's sort by a cast, `( .. ):Int`, as it does
/// for a value of a strict subsort (finding NT-7-2). Each starts the cell with its value.
#[test]
fn a_leaf_cell_s_whole_value_is_cast_to_the_cell_s_sort() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "let-matches",
            "{ let w = v; k::project!(Int, w) }",
            "k::matches!(p, ExpSyntax::Pair(_, _))",
            [
                "<proj> ( #let W:Val = $V:Val #in {W:Val}:>Int ):Int </proj>",
                "<flag> ( pair ( _ , _ ) :=K $P:Exp ):Bool </flag>",
            ],
            ["<proj> 7 </proj>", "<flag> true </flag>"],
        ),
        (
            "is",
            "k::project!(Int, v)",
            "k::is!(Int, v)",
            [
                "<proj> {$V:Val}:>Int </proj>",
                "<flag> ( isInt($V:Val) ):Bool </flag>",
            ],
            ["<proj> 7 </proj>", "<flag> true </flag>"],
        ),
    ];
    for (name, proj, flag, emitted, started) in cases {
        let manifest = package(
            temporary.path(),
            &format!("whole-{name}"),
            &local_initializer("p", proj, flag),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(success, "{name}: {stderr}");
        let definition = emit(target.path(), &manifest);
        for cell in emitted {
            assert!(definition.contains(cell), "{name}: {cell}\n{definition}");
        }
        let state = start(target.path(), &manifest);
        for cell in started {
            assert!(state.contains(cell), "{name}: {cell}\n{state}");
        }
        // The expanded initializer reads back to the same configuration.
        let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
        assert!(success, "{name}: {stderr}");
        let reference = package(
            temporary.path(),
            &format!("whole-{name}-expanded"),
            &expanded,
        );
        assert_eq!(
            configuration(&emit(target.path(), &reference)),
            configuration(&definition),
            "{name}"
        );
    }

    // A `let` block whose body is a strict subsort of the cell's, and a parametric constructor
    // whose instance is the cell's sort.
    let manifest = package(
        temporary.path(),
        "whole-exp",
        &format!(
            "{}{}",
            LOCAL_TERMS.replace(
                "    #[k::cell]\n    pub flag: Bool,\n",
                "    #[k::cell]\n    pub flag: Bool,\n    #[k::cell]\n    pub swapped: Exp,\n    #[k::cell]\n    pub wrapped: Exp,\n",
            ),
            "impl Machine {\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Exp, p: Exp, v: Val) -> Self {\n        Self {\n            k: k::k![pgm],\n            proj: k::project!(Int, v),\n            flag: true,\n            swapped: { let w = v; w },\n            wrapped: crate::Wrap::<dyn ExpSort>(p),\n        }\n    }\n}\n",
        ),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");
    let definition = emit(target.path(), &manifest);
    for cell in [
        "<swapped> ( #let W:Val = $V:Val #in W:Val ):Exp </swapped>",
        "<wrapped> ( wrap ( $P:Exp ) ):Exp </wrapped>",
    ] {
        assert!(definition.contains(cell), "{cell}\n{definition}");
    }
    let state = start(target.path(), &manifest);
    for cell in [
        "<swapped> 7 </swapped>",
        "<wrapped> wrap ( pair(1, 2) ) </wrapped>",
    ] {
        assert!(state.contains(cell), "{cell}\n{state}");
    }
}

/// The configuration `krs run` starts from on the program `done` with `P` bound to `pair(1, 2)`
/// and `V` to 7, flattened, with the run's messages after it.
fn start(target: &Path, manifest: &Path) -> String {
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "done").unwrap();
    let (_, stdout, stderr) = krs(
        target,
        manifest,
        "run",
        &[
            "--depth",
            "0",
            "-c",
            "P=pair(1, 2)",
            "-c",
            "V=7",
            program.to_str().unwrap(),
        ],
    );
    let state = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    format!("{state}\n{stderr}")
}

/// A configuration variable read inside a local term's scope, a `let` body or a `k::matches!`
/// pattern's subject below one, is the start value as anywhere else, which the native route
/// passes to the `let`'s generated function as its own argument; and a local pattern may leave a
/// record's other fields open, as a rule's local pattern may.
#[test]
fn an_initializer_reads_its_variables_inside_local_terms() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "local-scopes",
        &local_initializer(
            "{ let q = 1; p }, { let q = 3; ExpSyntax::Pair { a: q, ..p } }, { let q = 1; k::matches!(p, ExpSyntax::Pair(_, _)) }, { let q = v; k::project!(Exp, p) }, k::matches!(p, ExpSyntax::Pair { a: 1, .. }), { let ExpSyntax::Pair { a, .. } = p; a }",
            "k::project!(Int, v)",
            "k::matches!(p, ExpSyntax::Pair(_, _)) && true",
        ),
    );
    let definition = emit(target.path(), &manifest);
    expect_test::expect![[r"
        <k> $PGM:Exp ~> ( #let Q:Int = 1 #in $P:Exp ) ~> ( #let Q_2:Int = 3 #in ( #let pair ( _ , B:Int ) = $P:Exp #in pair ( Q_2:Int , B:Int ) ) ) ~> ( #let Q_3:Int = 1 #in ( pair ( _ , _ ) :=K $P:Exp ) ) ~> ( #let Q_4:Val = $V:Val #in {$P:Exp}:>Exp ) ~> ( pair ( 1 , _ ) :=K $P:Exp ) ~> ( #let pair ( A:Int , _ ) = $P:Exp #in A:Int ) </k>
        <proj> {$V:Val}:>Int </proj>
        <flag> ( pair ( _ , _ ) :=K $P:Exp ) andThenBool true </flag>"]].assert_eq(&configuration(&definition));

    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "done").unwrap();
    let (_, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[
            "--depth",
            "0",
            "-c",
            "P=pair(1, 2)",
            "-c",
            "V=7",
            program.to_str().unwrap(),
        ],
    );
    let state = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    for cell in [
        "<k> done ~> pair(1, 2) ~> pair(3, 2) ~> true ~> pair(1, 2) ~> true ~> 1 ~> .K </k>",
        "<flag> true </flag>",
    ] {
        assert!(state.contains(cell), "{cell}\n{stdout}\n{stderr}");
    }
}

/// A configuration whose top-level computation cell is `top` and whose group `frame` holds a
/// second one, `code`, with `go => done` as its one cell-free sentence (a `#[k::rule]` fn,
/// emitted without a cell), which K runs in the main cell. (A `for Stmt` clause runs there too:
/// the collector writes it in the main cell.)
fn main_cell_source(top: &str, top_value: &str, code_value: &str) -> String {
    format!(
        r#"
use k::builtin::{{Int, KSequence}};
use k::{{KResult, Term}};

k::sorts! {{
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {{
    #[k::syntax("go")]
    Go(),
    #[k::syntax("done")]
    Done(),
}}

#[k::rule]
fn step(k::term![Cmd::Go()]: Term<Stmt>) -> Term<Stmt> {{
    Cmd::Done()
}}

#[k::cell]
pub struct Frame {{
    #[k::cell]
    pub code: KSequence,
}}

#[k::configuration]
pub struct Machine {{
    #[k::cell]
    pub {top}: KSequence,
    #[k::cell(nested)]
    pub frame: Frame,
}}

impl Machine {{
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {{
        Self {{
            {top}: {top_value},
            frame: Frame {{ code: {code_value} }},
        }}
    }}
}}
"#
    )
}

/// The text route: the emitted `definition.k` loaded and compiled by k-rust's text frontend, as
/// `krust kcompile` reads it, and the KORE axiom of the cell-free rule `step`, which compilation
/// places in the main cell.
fn text_route_step_axiom(definition: &str) -> String {
    let label = definition
        .lines()
        .find(|line| line.contains("rule cmd") || line.contains("rule go"))
        .and_then(|line| line.split("label(").nth(1))
        .and_then(|rest| rest.split(')').next())
        .unwrap_or_else(|| panic!("the rule `step` is emitted:\n{definition}"))
        .to_owned();
    text_route_axiom(definition, &label)
}

/// The text route's KORE axiom labelled `label`: the emitted `definition.k` loaded and compiled by
/// k-rust's text frontend, as `krust kcompile` reads it.
fn text_route_axiom(definition: &str, label: &str) -> String {
    use k_rust::builtin;
    use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
    use k_rust::outer::{LoadOptions, ResolvedSource, load_for_compilation};

    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("definition.k", definition.to_owned()),
        "ORG-KRS-INIT-TERMS",
        Some("ORG-KRS-INIT-TERMS-SYNTAX"),
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![builtin::embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust
                    .excluded_module_attribute()
                    .to_owned(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("the text route loads the definition: {error}"));
    let kore = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("the text route compiles the definition: {error}"))
        .definition_kore;
    let needle = format!("label{{}}(\"{label}\")");
    let at = kore.find(&needle).unwrap_or_else(|| {
        let labels = kore
            .match_indices("label{}(")
            .map(|(at, _)| kore[at..].split(')').next().unwrap_or_default())
            .collect::<Vec<_>>();
        panic!("no axiom {label} among {labels:?}")
    });
    let start = kore[..at].rfind("axiom{").expect("an axiom");
    kore[start..at].to_owned()
}

/// The main cell is the computation cell that holds the program, whatever its name or depth
/// (`k_surface::main_cell`): the text says so with `maincell=""` on a cell not named `k`, both
/// routes run the cell-free rule there, and a cell named `k` that is not the main cell, which K
/// would take as the computation cell by its name, is refused.
#[test]
fn the_main_cell_is_the_computation_cell_that_holds_the_program_on_both_routes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    fs::write(temporary.path().join("program.txt"), "go\n").unwrap();
    let program = temporary.path().join("program.txt");
    for (name, top, top_value, code_value, marked, main) in [
        (
            "prog",
            "prog",
            "k::k![pgm]",
            "k::k![]",
            "<prog maincell=\"\"> $PGM:Stmt </prog>",
            "prog",
        ),
        (
            "code",
            "prog",
            "k::k![]",
            "k::k![pgm]",
            "<code maincell=\"\"> $PGM:Stmt </code>",
            "code",
        ),
        ("k", "k", "k::k![pgm]", "k::k![]", "<k> $PGM:Stmt </k>", "k"),
    ] {
        let manifest = package(
            temporary.path(),
            &format!("main-{name}"),
            &main_cell_source(top, top_value, code_value),
        );
        let definition = emit(target.path(), &manifest);
        assert!(definition.contains(marked), "{name}:\n{definition}");
        assert_eq!(
            definition.matches("maincell").count(),
            usize::from(name != "k"),
            "{name}"
        );
        let axiom = text_route_step_axiom(&definition);
        assert!(
            axiom.contains(&format!("Lbl'-LT-'{main}'-GT-'")),
            "{name}: the text route runs `step` in <{main}>:\n{axiom}"
        );
        let (success, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &[program.to_str().unwrap()],
        );
        let stdout = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(
            stdout.contains(&format!("<{main}> done ~> .K </{main}>")),
            "{name}: `krs run` runs `step` in <{main}> ({success}):\n{stdout}\n{stderr}"
        );
    }

    // `k` beside the computation cell that holds the program.
    let manifest = package(
        temporary.path(),
        "main-k-beside",
        &main_cell_source("k", "k::k![]", "k::k![pgm]"),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(!success, "{stderr}");
    assert!(
        stderr.contains("error[krs::analysis::main-cell]: the cell `k` is not this configuration's computation cell; the computation cell is `code`"),
        "{stderr}"
    );
    assert!(!stderr.contains("internal error"), "{stderr}");
}

/// A machine with the computation cells `prog` and `frame.code`, whose initializer `init` writes
/// both, and the extra sentences `extra`.
fn two_computations_source(init: &str, extra: &str) -> String {
    format!(
        r#"
use k::builtin::{{Int, KSequence}};
use k::{{KResult, Term}};

k::sorts! {{
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {{
    #[k::syntax("go")]
    Go(),
    #[k::syntax("done")]
    Done(),
}}

#[k::rule]
fn step(k::term![Cmd::Go()]: Term<Stmt>) -> Term<Stmt> {{
    Cmd::Done()
}}

{extra}

#[k::cell]
pub struct Frame {{
    #[k::cell]
    pub code: KSequence,
}}

#[k::configuration]
pub struct Machine {{
    #[k::cell]
    pub prog: KSequence,
    #[k::cell(nested)]
    pub frame: Frame,
}}

impl Machine {{
    #[k::init]
    {init}
}}
"#
    )
}

/// A configuration with several computation cells names its main cell only by placing the
/// program in one of them (`krs_ir::select_main_cell`). Where none or both read the program it
/// has none, so nothing says where the sentences that name no cell run. That is the
/// configuration's mistake, and the author is told it once, at the initializer (`main-cell`):
/// `for Stmt` clauses, whose computation cell the collector picks, and `#[k::rule]` fns stated over
/// the computation cell, which lowering places, report that one refusal and add none of their
/// own, never an internal error. Every error the check prints is listed, with where it points.
#[test]
fn a_configuration_whose_computation_cells_do_not_name_one_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let both = "pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {\n        Self { prog: k::k![pgm], frame: Frame { code: k::k![pgm] } }\n    }";
    let neither = "pub fn init() -> Self {\n        Self { prog: k::k![], frame: Frame { code: k::k![] } }\n    }";
    let head = "k::rules! {\n    for Stmt;\n    use Cmd::*;\n\n    hop: Go() => Done();\n    hip: Done() => Go();\n}";
    let collection = "#[k::rule]\nfn unset(x: Term<k::KItem>, k::term![k::builtin::set::item(x)]: Term<k::KItem>) -> Term<k::KItem> {\n    Cmd::Done()\n}\n\n#[k::rule]\nfn unget(k::term![k::builtin::set::item(Cmd::Go())]: Term<k::KItem>) -> Term<k::KItem> {\n    Cmd::Go()\n}";
    // Lowering takes descriptors in identity order and stops at the first error, so a rule whose
    // name sorts before the configuration's is lowered before it.
    let first = "#[k::rule]\n#[allow(non_snake_case)]\nfn Aunset(x: Term<k::KItem>, k::term![k::builtin::set::item(x)]: Term<k::KItem>) -> Term<k::KItem> {\n    Cmd::Done()\n}";
    let mut refused = Vec::new();
    for (name, init, extra) in [
        ("both", both, ""),
        ("both-head", both, head),
        ("neither", neither, ""),
        ("neither-head", neither, head),
        ("neither-collection", neither, collection),
        ("neither-collection-first", neither, first),
    ] {
        let manifest = package(
            temporary.path(),
            &format!("two-{name}"),
            &two_computations_source(init, extra),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: {stderr}");
        assert!(!stderr.contains("internal"), "{name}: {stderr}");
        let lines = stderr.lines().collect::<Vec<_>>();
        let errors = lines
            .iter()
            .enumerate()
            .filter(|(_, line)| line.starts_with("error"))
            .map(|(at, line)| {
                // The source line the error points at, as the report quotes it.
                let place = lines[at..]
                    .iter()
                    .skip_while(|line| !line.trim_start().starts_with("-->"))
                    .find_map(|line| line.split_once(" | ").map(|(_, source)| source.trim()))
                    .unwrap_or("nowhere");
                let code = line.split(']').next().unwrap_or(line);
                format!("{code}] at `{place}`")
            })
            .collect::<Vec<_>>();
        refused.push(format!("{name}: {}", errors.join("; ")));
        let reading = if init == both {
            "more than one reads the program"
        } else {
            "none of them reads the program"
        };
        assert!(
            stderr.contains(&format!("configuration `Machine` has 2 `KSequence` cells, `prog`, `code`, and {reading}: the computation is the `KSequence` cell whose initial value reads the main configuration variable, where the program starts and where every sentence that names no cell runs. Place the program, the `main` configuration variable, in the one `KSequence` cell that holds the computation")),
            "{name}: {stderr}"
        );
    }
    expect_test::expect![[r#"
        both: error[krs::analysis::main-cell] at `pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {`
        both-head: error[krs::analysis::main-cell] at `pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {`
        neither: error[krs::analysis::main-cell] at `pub fn init() -> Self {`
        neither-head: error[krs::analysis::main-cell] at `pub fn init() -> Self {`
        neither-collection: error[krs::analysis::main-cell] at `pub fn init() -> Self {`
        neither-collection-first: error[krs::analysis::main-cell] at `pub fn init() -> Self {`"#]]
    .assert_eq(&refused.join("\n"));
}

/// The program is read where the main variable occurs free (R1, NT-29): a `let` in the frame's
/// computation cell that binds the name `pgm` makes another variable, which lowering gives its
/// own identity, so `frame.code` does not read the program and `prog`, which does, is the main
/// cell. Both readers of the main cell, the descriptor's (the collector's, a `for Stmt` clause's
/// cell) and the lowered configuration's (the backends' marking), agree: the configuration is
/// accepted, `prog` is marked, `krs run` runs the cell-free `step` there (and its status line
/// names `<prog>`, the computation), and the clause `hop` rewrites `prog`.
#[test]
fn a_let_that_binds_the_program_s_name_does_not_read_the_program() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let shadow = "pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {\n        Self { prog: k::k![pgm], frame: Frame { code: k::k![{ let pgm = Cmd::Done(); pgm }] } }\n    }";
    let head = "k::rules! {\n    for Stmt;\n    use Cmd::*;\n\n    hop: Done() => Go();\n}";
    let program = temporary.path().join("program.txt");
    fs::write(&program, "go\n").unwrap();
    for (name, extra) in [("shadow", ""), ("shadow-head", head)] {
        let manifest = package(
            temporary.path(),
            name,
            &two_computations_source(shadow, extra),
        );
        let definition = emit(target.path(), &manifest);
        assert!(
            definition.contains("<prog maincell=\"\"> $PGM:Stmt </prog>"),
            "{name}:\n{definition}"
        );
        assert_eq!(definition.matches("maincell").count(), 1, "{name}");
        if extra.is_empty() {
            let (success, stdout, stderr) = krs(
                target.path(),
                &manifest,
                "run",
                &[program.to_str().unwrap()],
            );
            let stdout = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
            assert!(
                stdout.contains("<prog> done ~> .K </prog>")
                    && stdout.contains("<code> done ~> .K </code>"),
                "{name}: `krs run` runs `step` in <prog> ({success}):\n{stdout}\n{stderr}"
            );
            // The status line names the computation by the main cell (R6, NT-29).
            assert!(
                stderr.contains("krs run: stuck after 1 step; <prog> starts with `done`"),
                "{name}: {stderr}"
            );
        } else {
            let hop = definition
                .lines()
                .find(|line| line.contains("label(hop)") || line.contains("done => go"))
                .unwrap_or_else(|| panic!("{name}: the clause `hop` is emitted:\n{definition}"));
            assert!(
                hop.contains("<prog>"),
                "{name}: `hop` rewrites <prog>: {hop}"
            );
        }
    }
}

/// One sort of the class-matrix bases' lattice ([`CAST_SORTS`]).
struct CastSort {
    name: &'static str,
    parents: &'static [&'static str],
    /// A ground value of the sort; none for `KItem`.
    value: Option<&'static str>,
    /// Whether its values are domain values, at which a parametric production has no instance.
    domain: bool,
    /// The turbofish marker that names it; empty where none is written.
    marker: &'static str,
}

/// The sort lattice of the class-matrix bases (`k::sorts! { Stmt; Value: Stmt + KResult; impl
/// Value for Int; }`) with the builtin `Bool`, `KItem` above them all.
const CAST_SORTS: [CastSort; 5] = [
    CastSort {
        name: "Int",
        parents: &["Value"],
        value: Some("1"),
        domain: true,
        marker: "",
    },
    CastSort {
        name: "Value",
        parents: &["Stmt"],
        value: Some("Val::Unit()"),
        domain: false,
        marker: "dyn ValueSort",
    },
    CastSort {
        name: "Stmt",
        parents: &["KItem"],
        value: Some("Cmd::Go()"),
        domain: false,
        marker: "dyn StmtSort",
    },
    CastSort {
        name: "Bool",
        parents: &["KItem"],
        value: Some("true"),
        domain: true,
        marker: "",
    },
    CastSort {
        name: "KItem",
        parents: &[],
        value: None,
        domain: false,
        marker: "dyn k::KItemSort",
    },
];

/// Whether `sort` is `above` or one of its subsorts in [`CAST_SORTS`].
fn cast_subsort(sort: &str, above: &str) -> bool {
    sort == above
        || CAST_SORTS
            .iter()
            .find(|candidate| candidate.name == sort)
            .is_some_and(|sort| {
                sort.parents
                    .iter()
                    .any(|parent| cast_subsort(parent, above))
            })
}

/// One generated leaf cell of the cast machine: its name, its declared sort, its initial value,
/// and, for a value the initializer computes (a `let` block, `k::matches!`, `k::is!`), the value
/// the run must start the cell with: the name of a cell holding it plainly, or a literal.
struct CastCell {
    name: String,
    sort: &'static str,
    value: String,
    computes: Option<String>,
}

/// Every leaf cell the cast machine starts, one per root kind KRS may write cast to its cell's
/// sort (`k_surface::initial_value_needs_cell_sort`) at each pair of a cell sort and a value sort
/// below it in [`CAST_SORTS`]: the plain value (`p`), a `let` block computing it (`l`), the
/// parametric `Wrap` of it with its instance solved (`w`) and named by a turbofish at that least
/// instance (`t`); the configuration variable `v: Value` and its `Wrap` (`v`, `wv`); and in a
/// `Bool` or `KItem` cell a `k::matches!` test (`m`) and a sort predicate (`i`) of `v`.
fn cast_cells() -> Vec<CastCell> {
    let mut cells = Vec::new();
    let cell = |name: String, sort, value: String, computes: Option<String>| CastCell {
        name,
        sort,
        value,
        computes,
    };
    for cell_sort in CAST_SORTS.iter().filter(|sort| sort.name != "Int") {
        let cell_sort = cell_sort.name;
        let c = cell_sort.to_lowercase();
        for value_sort in &CAST_SORTS {
            let Some(value) = value_sort.value else {
                continue;
            };
            if !cast_subsort(value_sort.name, cell_sort) {
                continue;
            }
            let v = value_sort.name.to_lowercase();
            cells.push(cell(format!("p{v}{c}"), cell_sort, value.to_owned(), None));
            cells.push(cell(
                format!("l{v}{c}"),
                cell_sort,
                format!("{{ let x = {value}; x }}"),
                Some(format!("p{v}{c}")),
            ));
            if !value_sort.domain {
                cells.push(cell(
                    format!("w{v}{c}"),
                    cell_sort,
                    format!("crate::Wrap({value})"),
                    None,
                ));
                cells.push(cell(
                    format!("t{v}{c}"),
                    cell_sort,
                    format!("crate::Wrap::<{}>({value})", value_sort.marker),
                    None,
                ));
            }
        }
        if cast_subsort("Value", cell_sort) {
            cells.push(cell(format!("v{c}"), cell_sort, "v".to_owned(), None));
            cells.push(cell(
                format!("wv{c}"),
                cell_sort,
                "crate::Wrap(v)".to_owned(),
                None,
            ));
        }
        if cast_subsort("Bool", cell_sort) {
            cells.push(cell(
                format!("m{c}"),
                cell_sort,
                "k::matches!(v, Val::Unit())".to_owned(),
                Some("true".to_owned()),
            ));
            cells.push(cell(
                format!("i{c}"),
                cell_sort,
                "k::is!(Int, v)".to_owned(),
                Some("false".to_owned()),
            ));
        }
    }
    cells
}

/// A machine over [`CAST_SORTS`] whose computation cell `k` holds the program, `held` the
/// configuration variable `v`, and whose other leaf cells are `cells` (name, sort, initial
/// value), with `extra` items beside it.
fn cast_machine(cells: &[(&str, &str, &str)], extra: &str) -> String {
    use std::fmt::Write as _;
    let mut declared = String::new();
    let mut initial = String::new();
    for (name, sort, value) in cells {
        writeln!(declared, "    #[k::cell]\n    pub {name}: {sort},").unwrap();
        writeln!(initial, "            {name}: {value},").unwrap();
    }
    format!(
        r#"#![allow(unused_imports)]
use k::builtin::{{Bool, Int, KSequence}};
use k::{{KItem, KResult, Term}};

k::sorts! {{
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}}

#[k::constructors(sort = Value, result = KResult)]
pub enum Val {{
    #[k::syntax("unit")]
    Unit(),
}}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {{
    #[k::syntax("go")]
    Go(),
    #[k::syntax("uns({{a}})")]
    Uns {{ a: Stmt }},
}}

#[k::constructor(sort = S, syntax = "wrap({{inner}})")]
pub struct Wrap<S: ?Sized> {{
    pub inner: Term<S>,
}}

{extra}

#[k::configuration]
pub struct Machine {{
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub held: Value,
{declared}}}

impl Machine {{
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "V")] v: Value,
    ) -> Self {{
        Self {{
            k: k::k![pgm],
            held: v,
{initial}        }}
    }}
}}
"#
    )
}

/// The text route's KORE definition: the emitted `definition.k` compiled by k-rust's text
/// frontend, as `krust kcompile` compiles it, or the frontend's error.
fn text_route_kore(definition: &str) -> Result<String, String> {
    use k_rust::builtin;
    use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
    use k_rust::outer::{LoadOptions, ResolvedSource, load_for_compilation};

    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("definition.k", definition.to_owned()),
        "ORG-KRS-INIT-TERMS",
        Some("ORG-KRS-INIT-TERMS-SYNTAX"),
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![builtin::embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust
                    .excluded_module_attribute()
                    .to_owned(),
            ],
            ..LoadOptions::default()
        },
    )
    .map_err(|error| format!("the text route loads the definition: {error}"))?;
    compile_loaded_definition(&loaded, CompileOptions::default())
        .map(|compiled| compiled.definition_kore)
        .map_err(|error| format!("the text route compiles the definition: {error}"))
}

/// The initial value of each leaf cell `<name>` a KORE definition builds: the content of the
/// cell in the axiom of its initializer function `init<Name>Cell`, whitespace normalized, in the
/// order `names` lists.
fn kore_initial_cells(kore: &str, names: &[&str]) -> Vec<String> {
    names
        .iter()
        .map(|name| {
            let init = format!("Lblinit{}Cell{{}}(", name[..1].to_uppercase() + &name[1..]);
            let cell = format!("Lbl'-LT-'{name}'-GT-'{{}}(");
            // Each axiom up to the declaration that follows it.
            let axiom = kore
                .split("axiom{")
                .skip(1)
                .map(|axiom| {
                    [
                        "\n  symbol ",
                        "\n  hooked-symbol ",
                        "\n  sort ",
                        "\n  hooked-sort ",
                        "\nendmodule",
                    ]
                    .iter()
                    .filter_map(|next| axiom.find(next))
                    .min()
                    .map_or(axiom, |end| &axiom[..end])
                })
                .find(|axiom| axiom.contains(&init) && axiom.contains(&cell))
                .unwrap_or_else(|| panic!("no initializer axiom of <{name}>"));
            let axiom = axiom.split_whitespace().collect::<Vec<_>>().join(" ");
            let start = axiom.find(&cell).expect("the cell") + cell.len();
            let mut depth = 1;
            let end = axiom[start..]
                .char_indices()
                .find_map(|(at, character)| {
                    match character {
                        '(' => depth += 1,
                        ')' => depth -= 1,
                        _ => {}
                    }
                    (depth == 0).then_some(start + at)
                })
                .expect("a closed cell");
            format!("{name}: {}", &axiom[start..end])
        })
        .collect()
}

/// The values no function computes compile to one KORE term on both routes: the native initial
/// values of the cells of `cells` that compute nothing, which the text route (`definition`
/// without the computed cells, NT-29-1) compiles alike. The whole `definition` does not load on
/// the text route, until NT-29-1 is fixed.
fn uncomputed_cells_agree(definition: &str, native_kore: &str, cells: &[CastCell]) -> Vec<String> {
    let uncomputed = cells
        .iter()
        .filter(|cell| cell.computes.is_none())
        .map(|cell| cell.name.as_str())
        .collect::<Vec<_>>();
    let readable = definition
        .lines()
        .filter(|line| {
            !cells.iter().any(|cell| {
                cell.computes.is_some()
                    && line.trim_start().starts_with(&format!("<{}> ", cell.name))
            })
        })
        .collect::<Vec<_>>()
        .join("\n");
    let text_kore = text_route_kore(&readable).unwrap_or_else(|error| panic!("{error}"));
    let native = kore_initial_cells(native_kore, &uncomputed);
    assert_eq!(
        native,
        kore_initial_cells(&text_kore, &uncomputed),
        "{}",
        configuration(definition)
    );
    let unread = text_route_kore(definition).expect_err(
        "the text frontend reads a computed configuration value (NT-29-1 fixed): compare those \
         cells too",
    );
    assert!(unread.contains("could not parse configuration"), "{unread}");
    native
}

/// The values the initializer computes: the native run of the package `manifest` starts each
/// computed cell of `cells` with its value, a plain cell's or a literal.
fn computed_cells_start_with_their_values(target: &Path, manifest: &Path, cells: &[CastCell]) {
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "go").unwrap();
    let (success, stdout, stderr) = krs(
        target,
        manifest,
        "run",
        &["-c", "V=unit", program.to_str().unwrap()],
    );
    let state = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    let started = |name: &str| {
        let open = format!("<{name}> ");
        let start = state
            .find(&open)
            .unwrap_or_else(|| panic!("no <{name}> in the run ({success}):\n{stdout}\n{stderr}"))
            + open.len();
        let end = state[start..].find(&format!(" </{name}>")).expect("closed") + start;
        state[start..end].to_owned()
    };
    for cell in cells {
        let Some(expected) = &cell.computes else {
            continue;
        };
        let expected = if expected.starts_with('p') {
            started(expected)
        } else {
            expected.clone()
        };
        assert_eq!(started(&cell.name), expected, "<{}>", cell.name);
    }
}

/// A turbofish above the instance the arguments solve, where nothing fixes it: at a leaf cell's
/// root, at every pair of a value sort and a cell sort strictly above it, and in a rule's result.
/// Each package, under `root`, is checked alone; the first error of each.
fn turbofishes_above_the_solved_instance(target: &Path, root: &Path) -> Vec<String> {
    let mut above = Vec::new();
    for value_sort in CAST_SORTS.iter().filter(|sort| !sort.domain) {
        let Some(value) = value_sort.value else {
            continue;
        };
        for cell_sort in &CAST_SORTS {
            if cell_sort.name != value_sort.name
                && cast_subsort(value_sort.name, cell_sort.name)
                && !cell_sort.marker.is_empty()
            {
                above.push((
                    format!("{}-in-{}", value_sort.name, cell_sort.name),
                    cast_machine(
                        &[(
                            "x",
                            cell_sort.name,
                            &format!("crate::Wrap::<{}>({value})", cell_sort.marker),
                        )],
                        "",
                    ),
                ));
            }
        }
    }
    above.push((
        "Value-in-a-result".to_owned(),
        cast_machine(
            &[],
            "#[k::rule]\nfn go(k::term![Cmd::Go()]: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Uns(crate::Wrap::<dyn StmtSort>(Val::Unit()))\n}",
        ),
    ));
    above
        .iter()
        .map(|(name, source)| {
            let manifest = package(root, &format!("above-{}", name.to_lowercase()), source);
            let (success, _, stderr) = krs(target, &manifest, "check", &[]);
            assert!(!success, "{name}: {stderr}");
            let error = stderr
                .lines()
                .find(|line| line.starts_with("error"))
                .unwrap_or_else(|| panic!("{name}: {stderr}"));
            format!("{name}: {error}")
        })
        .collect()
}

/// A cast KRS writes means the same on every route that reads it (NT-22-F3), checked at every
/// pair of a cell sort and a value sort below it that the bases' lattice has ([`cast_cells`]).
/// KRS casts a leaf cell's whole initial value to the cell's sort where its head does not give
/// that sort (a strict subsort, a parametric production, a `let` block, `k::matches!`, a sort
/// predicate); the cast states the sort and computes nothing, so the cell starts with the value,
/// and a parametric application keeps the instance its arguments solve (`wrap{Value}(unit)` in a
/// `Stmt` cell, injected), which is the only instance a turbofish may name there.
///
/// - A value no function computes compiles to the same initial value through the emitted text
///   (k-rust's text frontend) and natively (`krs build`, which `krs run` runs).
/// - A computed value starts its cell, on the native route, with the value it computes: a `let`
///   block's is the plain value's, the test's and the predicate's the Bool of `v = unit`. The text
///   frontend does not read `#let`, `:=K` or a sort predicate in a configuration (NT-29-1), so
///   these cells are left out of its definition, and the whole definition is checked to fail.
/// - A turbofish above the instance the arguments solve, at a cell's root or in a rule's result
///   (no head, so no strict cast fixes it), would hold another term on each route: it is refused
///   (`parametric-instance`) at each such pair.
#[test]
fn a_cast_initial_value_is_the_same_value_on_both_routes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cells = cast_cells();
    let listed = cells
        .iter()
        .map(|cell| (cell.name.as_str(), cell.sort, cell.value.as_str()))
        .collect::<Vec<_>>();
    let manifest = package(temporary.path(), "casts", &cast_machine(&listed, ""));
    let definition = emit(target.path(), &manifest);
    let output = manifest.with_file_name("native");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "build",
        &["--backend", "haskell", "--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let native_kore = fs::read_to_string(output.join("definition.kore")).unwrap();
    let native = uncomputed_cells_agree(&definition, &native_kore, &cells);
    computed_cells_start_with_their_values(target.path(), &manifest, &cells);
    let refused = turbofishes_above_the_solved_instance(target.path(), temporary.path());
    expect_test::expect![[r#"
        <k> $PGM:Stmt </k>
        <held> $V:Value </held>
        <pintvalue> ( 1 ):Value </pintvalue>
        <lintvalue> ( #let X:Int = 1 #in X:Int ):Value </lintvalue>
        <pvaluevalue> unit </pvaluevalue>
        <lvaluevalue> ( #let X_2:Value = unit #in X_2:Value ):Value </lvaluevalue>
        <wvaluevalue> ( wrap ( unit ) ):Value </wvaluevalue>
        <tvaluevalue> ( wrap ( unit ) ):Value </tvaluevalue>
        <vvalue> $V:Value </vvalue>
        <wvvalue> ( wrap ( $V:Value ) ):Value </wvvalue>
        <pintstmt> ( 1 ):Stmt </pintstmt>
        <lintstmt> ( #let X_3:Int = 1 #in X_3:Int ):Stmt </lintstmt>
        <pvaluestmt> ( unit ):Stmt </pvaluestmt>
        <lvaluestmt> ( #let X_4:Value = unit #in X_4:Value ):Stmt </lvaluestmt>
        <wvaluestmt> ( wrap ( unit ) ):Stmt </wvaluestmt>
        <tvaluestmt> ( wrap ( unit ) ):Stmt </tvaluestmt>
        <pstmtstmt> go </pstmtstmt>
        <lstmtstmt> ( #let X_5:Stmt = go #in X_5:Stmt ):Stmt </lstmtstmt>
        <wstmtstmt> ( wrap ( go ) ):Stmt </wstmtstmt>
        <tstmtstmt> ( wrap ( go ) ):Stmt </tstmtstmt>
        <vstmt> ( $V:Value ):Stmt </vstmt>
        <wvstmt> ( wrap ( $V:Value ) ):Stmt </wvstmt>
        <pboolbool> true </pboolbool>
        <lboolbool> ( #let X_6:Bool = true #in X_6:Bool ):Bool </lboolbool>
        <mbool> ( unit :=K $V:Value ):Bool </mbool>
        <ibool> ( isInt($V:Value) ):Bool </ibool>
        <pintkitem> ( 1 ):KItem </pintkitem>
        <lintkitem> ( #let X_7:Int = 1 #in X_7:Int ):KItem </lintkitem>
        <pvaluekitem> ( unit ):KItem </pvaluekitem>
        <lvaluekitem> ( #let X_8:Value = unit #in X_8:Value ):KItem </lvaluekitem>
        <wvaluekitem> ( wrap ( unit ) ):KItem </wvaluekitem>
        <tvaluekitem> ( wrap ( unit ) ):KItem </tvaluekitem>
        <pstmtkitem> ( go ):KItem </pstmtkitem>
        <lstmtkitem> ( #let X_9:Stmt = go #in X_9:Stmt ):KItem </lstmtkitem>
        <wstmtkitem> ( wrap ( go ) ):KItem </wstmtkitem>
        <tstmtkitem> ( wrap ( go ) ):KItem </tstmtkitem>
        <pboolkitem> ( true ):KItem </pboolkitem>
        <lboolkitem> ( #let X_10:Bool = true #in X_10:Bool ):KItem </lboolkitem>
        <vkitem> ( $V:Value ):KItem </vkitem>
        <wvkitem> ( wrap ( $V:Value ) ):KItem </wvkitem>
        <mkitem> ( unit :=K $V:Value ):KItem </mkitem>
        <ikitem> ( isInt($V:Value) ):KItem </ikitem>
        pintvalue: inj{SortInt{}, SortValue{}}(\dv{SortInt{}}("1"))
        pvaluevalue: LblvalUnit{}()
        wvaluevalue: Lblwrap{SortValue{}}(LblvalUnit{}())
        tvaluevalue: Lblwrap{SortValue{}}(LblvalUnit{}())
        vvalue:  Lblproject'Coln'Value{}( Lbl'Hash'unboxKConfigValue{}( LblMap'Coln'lookup{}( VarInit:SortMap{}, inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}("$V")) ) ) ) 
        wvvalue:  Lblwrap{SortValue{}}( Lblproject'Coln'Value{}( Lbl'Hash'unboxKConfigValue{}( LblMap'Coln'lookup{}( VarInit:SortMap{}, inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}("$V")) ) ) ) ) 
        pintstmt: inj{SortInt{}, SortStmt{}}(\dv{SortInt{}}("1"))
        pvaluestmt: inj{SortValue{}, SortStmt{}}(LblvalUnit{}())
        wvaluestmt:  inj{SortValue{}, SortStmt{}}(Lblwrap{SortValue{}}(LblvalUnit{}())) 
        tvaluestmt:  inj{SortValue{}, SortStmt{}}(Lblwrap{SortValue{}}(LblvalUnit{}())) 
        pstmtstmt: LblcmdGo{}()
        wstmtstmt: Lblwrap{SortStmt{}}(LblcmdGo{}())
        tstmtstmt: Lblwrap{SortStmt{}}(LblcmdGo{}())
        vstmt:  inj{SortValue{}, SortStmt{}}( Lblproject'Coln'Value{}( Lbl'Hash'unboxKConfigValue{}( LblMap'Coln'lookup{}( VarInit:SortMap{}, inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}("$V")) ) ) ) ) 
        wvstmt:  inj{SortValue{}, SortStmt{}}( Lblwrap{SortValue{}}( Lblproject'Coln'Value{}( Lbl'Hash'unboxKConfigValue{}( LblMap'Coln'lookup{}( VarInit:SortMap{}, inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}("$V")) ) ) ) ) ) 
        pboolbool: \dv{SortBool{}}("true")
        pintkitem: inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1"))
        pvaluekitem: inj{SortValue{}, SortKItem{}}(LblvalUnit{}())
        wvaluekitem:  inj{SortValue{}, SortKItem{}}(Lblwrap{SortValue{}}(LblvalUnit{}())) 
        tvaluekitem:  inj{SortValue{}, SortKItem{}}(Lblwrap{SortValue{}}(LblvalUnit{}())) 
        pstmtkitem: inj{SortStmt{}, SortKItem{}}(LblcmdGo{}())
        wstmtkitem:  inj{SortStmt{}, SortKItem{}}(Lblwrap{SortStmt{}}(LblcmdGo{}())) 
        tstmtkitem:  inj{SortStmt{}, SortKItem{}}(Lblwrap{SortStmt{}}(LblcmdGo{}())) 
        pboolkitem: inj{SortBool{}, SortKItem{}}(\dv{SortBool{}}("true"))
        vkitem:  inj{SortValue{}, SortKItem{}}( Lblproject'Coln'Value{}( Lbl'Hash'unboxKConfigValue{}( LblMap'Coln'lookup{}( VarInit:SortMap{}, inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}("$V")) ) ) ) ) 
        wvkitem:  inj{SortValue{}, SortKItem{}}( Lblwrap{SortValue{}}( Lblproject'Coln'Value{}( Lbl'Hash'unboxKConfigValue{}( LblMap'Coln'lookup{}( VarInit:SortMap{}, inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}("$V")) ) ) ) ) ) 
        Value-in-Stmt: error[krs::analysis::parametric-instance]: K and k-rust solve the sort parameter `S` of this `Wrap` from its arguments and position as Value, not the turbofish's Stmt; the turbofish of a term that is not an equation or rule head must name the instance K solves
        Value-in-KItem: error[krs::analysis::parametric-instance]: K and k-rust solve the sort parameter `S` of this `Wrap` from its arguments and position as Value, not the turbofish's KItem; the turbofish of a term that is not an equation or rule head must name the instance K solves
        Stmt-in-KItem: error[krs::analysis::parametric-instance]: K and k-rust solve the sort parameter `S` of this `Wrap` from its arguments and position as Stmt, not the turbofish's KItem; the turbofish of a term that is not an equation or rule head must name the instance K solves
        Value-in-a-result: error[krs::analysis::parametric-instance]: K and k-rust solve the sort parameter `S` of this `Wrap` from its arguments and position as Value, not the turbofish's Stmt; the turbofish of a term that is not an equation or rule head must name the instance K solves"#]].assert_eq(&format!(
        "{}\n{}\n{}",
        configuration(&definition),
        native.join("\n"),
        refused.join("\n")
    ));
}

/// A machine whose List collection `job` starts with one instance of its template: a `Job` holds
/// `payload`, the group `info` with the optional `mark`, and the optional `note`, their templates
/// `{note}` and `{mark}`; `{rules}` are the machine's rules.
fn jobs_source(note: &str, mark: &str, rules: &str) -> String {
    format!(
        r#"
use k::KResult;
use k::builtin::{{Int, KSequence}};

k::sorts! {{
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {{
    #[k::syntax("spawn")]
    Spawn(),
}}

#[k::cell]
pub struct Queue {{
    #[k::cell(multiplicity = "*", cell_type = "List", nested, initial)]
    pub job: Job,
}}

#[k::cell]
pub struct Job {{
    #[k::cell]
    pub payload: Int,
    #[k::cell(nested)]
    pub info: Info,
    #[k::cell(multiplicity = "?")]
    pub note: Option<Int>,
}}

#[k::cell]
pub struct Info {{
    #[k::cell(multiplicity = "?")]
    pub mark: Option<Int>,
}}

#[k::configuration]
pub struct Machine {{
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub queue: Queue,
}}

impl Machine {{
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {{
        Self {{
            k: k::k![pgm],
            queue: Queue {{ job: Job {{ payload: 0, info: Info {{ mark: {mark} }}, note: {note} }} }},
        }}
    }}
}}

{rules}
"#
    )
}

/// `spawn` appends a `Job` whose other cells take their template defaults.
const SPAWN: &str = "k::rules! {
    for Machine;
    use Cmd::*;

    spawn: { k: [Spawn(), ..], job: [..] } => { k: [..], job: [.., Job { payload: 5, .. }] };
}";

/// An optional cell inside a collection's template says whether each instance holds it: the
/// instance `initial` starts holds `Some(v)`'s cell and not `k::absent!(t)`'s. A created
/// instance's `..` writes no optional cell, so it defaults one whose template starts absent, on
/// both routes, and one whose template starts present, the child itself or a cell inside it, is
/// refused: an instance record cannot name an optional cell to write it.
#[test]
fn a_created_instance_s_defaults_are_its_template_s_optional_cells_included() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    fs::write(temporary.path().join("program.txt"), "spawn\n").unwrap();
    let program = temporary.path().join("program.txt");
    let run = |manifest: &Path| {
        let (_, stdout, stderr) = krs(target.path(), manifest, "run", &[program.to_str().unwrap()]);
        let stdout = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        (stdout, stderr)
    };

    // The instance `initial` starts holds the optional cells written `Some(..)`.
    let manifest = package(
        temporary.path(),
        "jobs-present",
        &jobs_source("Some(1)", "Some(2)", ""),
    );
    let (stdout, stderr) = run(&manifest);
    assert!(
        stdout.contains(
            "<job> <payload> 0 </payload> <info> <mark> 2 </mark> </info> <note> 1 </note> </job>"
        ),
        "{stdout}\n{stderr}"
    );

    // Written `k::absent!(..)`, neither the instance at the start nor a created one holds them.
    let manifest = package(
        temporary.path(),
        "jobs-absent",
        &jobs_source("k::absent!(1)", "k::absent!(2)", SPAWN),
    );
    let definition = emit(target.path(), &manifest);
    let created =
        "(.Bag => <job>\n            <payload> 5 </payload>\n            ...\n        </job>)";
    assert!(definition.contains(created), "{definition}");
    let axiom = text_route_axiom(&definition, "ORG-KRS-INIT-TERMS.spawn");
    assert!(
        axiom.contains("Lbl'-LT-'payload'-GT-'{}(\\dv{SortInt{}}(\"5\"))")
            && !axiom.contains("Lbl'-LT-'note'-GT-'")
            && !axiom.contains("Lbl'-LT-'mark'-GT-'"),
        "the text route creates the job without its optional cells:\n{axiom}"
    );
    let (stdout, stderr) = run(&manifest);
    assert!(
        stdout.contains("<job> <payload> 0 </payload> <info> .MarkCell </info> .NoteCell </job> <job> <payload> 5 </payload> <info> .MarkCell </info> .NoteCell </job>"),
        "{stdout}\n{stderr}"
    );

    // Started present, an optional cell `..` would leave out is refused, at the created instance.
    for (name, note, mark, child, optional) in [
        ("jobs-note", "Some(1)", "k::absent!(2)", "note", "note"),
        ("jobs-mark", "k::absent!(1)", "Some(2)", "info", "mark"),
    ] {
        let manifest = package(temporary.path(), name, &jobs_source(note, mark, SPAWN));
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: accepted:\n{stderr}");
        assert!(
            stderr.contains(&format!(
                "error[krs::analysis::no-cell-default]: `..` cannot default `{child}` of a new `Job`: its template starts the optional cell `{optional}` present, which `..` does not write and an instance record cannot name yet; start it absent in the template with `k::absent!(..)`"
            )),
            "{name}:\n{stderr}"
        );
        assert!(
            stderr.contains("Job { payload: 5, .. }"),
            "{name}:\n{stderr}"
        );
        assert!(!stderr.contains("internal error"), "{name}:\n{stderr}");
    }
}
