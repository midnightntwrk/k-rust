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
