//! A failed `#[k::init]` is reported once, by KRS: whether its syntax, its
//! body's shape, or one of its terms is rejected, `krs check` prints the KRS
//! error and nothing about the payload function the configuration names,
//! which the failed expansion leaves as a stand-in.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Id, Int, KSequence, List, Map, list, map};
use k::KResult;

k::sorts! {
    Stmt;
    Value: KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Value>,
    #[k::cell]
    pub stack: List<Value>,
}
"#;

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
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-INIT-DIAGNOSTICS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs check` on the package's `main` definition.
fn check(target: &Path, manifest: &Path) -> (bool, String) {
    let package = manifest
        .parent()
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())
        .unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args(["check", "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main"])
        .env("NO_COLOR", "1")
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

fn initializer(body: &str) -> String {
    format!(
        "impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt, n: Id) -> Self {{\n        {body}\n    }}\n}}\n"
    )
}

#[test]
fn a_failed_initializer_reports_only_its_krs_error() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "syntax",
            "Self { k: k::k![pgm], env: k::map![n -> 1 2], stack: list::empty() }",
            "krs::syntax::",
        ),
        (
            "body-shape",
            "let x = 1;\n        Self { k: k::k![pgm], env: map::empty(), stack: list::empty() }",
            "error[krs::syntax::unsupported-initializer-body]",
        ),
        (
            "expansion",
            "Self { k: k::k![pgm], env: map::empty(), stack: list::item(k::anonymous!(Value, \"_V\")) }",
            "error[krs::expand::",
        ),
    ];
    for (name, body, expected) in cases {
        let manifest = package(
            temporary.path(),
            name,
            &format!("{PREAMBLE}{}", initializer(body)),
        );
        let (success, stderr) = check(target.path(), &manifest);
        assert!(!success, "{name}: {stderr}");
        let errors = stderr
            .lines()
            .filter(|line| line.starts_with("error"))
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{name}: {stderr}");
        assert!(errors[0].contains(expected), "{name}: {stderr}");
        assert!(!stderr.contains("E0599"), "{name}: {stderr}");
        assert!(
            !stderr.contains("__krs_initializer_payload"),
            "{name}: {stderr}"
        );
    }
}

#[test]
fn a_configuration_without_an_initializer_is_reported_at_its_name() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let name = PREAMBLE.find("pub struct Machine").unwrap();
    let line = PREAMBLE[..name].lines().count() + 1;
    let location = format!("lib.rs:{line}:12");
    let removed = format!(
        "{PREAMBLE}\nimpl Machine {{\n    #[cfg(any())]\n    #[k::init]\n    pub fn init() -> Self {{\n        Self {{ k: k::k![], env: map::empty(), stack: list::empty() }}\n    }}\n}}\n"
    );
    let cases = [("missing", PREAMBLE.to_owned()), ("cfg-removed", removed)];
    for (name, library) in cases {
        let manifest = package(temporary.path(), name, &library);
        let (success, stderr) = check(target.path(), &manifest);
        assert!(!success, "{name}: {stderr}");
        let errors = stderr
            .lines()
            .filter(|line| line.starts_with("error"))
            .collect::<Vec<_>>();
        assert_eq!(
            errors,
            [
                "error[krs::expand::missing-initializer]: configuration `Machine` has no `#[k::init]` initializer"
            ],
            "{name}: {stderr}"
        );
        assert!(stderr.contains(&location), "{name}: {stderr}");
        assert!(
            stderr.contains("= note: an initializer gives each cell its initial value"),
            "{name}: {stderr}"
        );
        for internal in ["E0599", "E0277", "__krs", "__Krs"] {
            assert!(!stderr.contains(internal), "{name}: {stderr}");
        }
    }
}

/// A machine with a cell of each kind brackets mark nothing in at its own level: a plain leaf, an
/// optional leaf, an optional list (whose brackets need its presence) and a collection inside a
/// group, beside the computation and a list.
const KINDS: &str = r#"
use k::builtin::{Int, KSequence, List, list};
use k::KResult;

k::sorts! {
    Stmt;
    Value: KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
}

#[k::cell]
pub struct Obj {
    #[k::cell]
    pub key: Int,
}

#[k::cell]
pub struct Shelf {
    #[k::cell(multiplicity = "*", cell_type = "Set", nested)]
    pub bag: Obj,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub stack: List<Value>,
    #[k::cell(multiplicity = "?")]
    pub counter: Option<Int>,
    #[k::cell(multiplicity = "?")]
    pub olist: Option<List<Value>>,
    #[k::cell(nested)]
    pub shelf: Shelf,
}
"#;

/// The kinds machine's initializer, with `value` in the cell `cell` and every other cell's own
/// typed value.
fn kinds_initializer(cell: &str, value: &str) -> String {
    let fields = [
        ("k", "k::k![pgm]"),
        ("pc", "0"),
        ("stack", "list::empty()"),
        ("counter", "k::absent!(0)"),
        ("olist", "k::absent!(list::empty())"),
        ("shelf", "Shelf { bag: Obj { key: 0 } }"),
    ]
    .map(|(name, typed)| {
        let value = if name == cell { value } else { typed };
        format!("{name}: {value}")
    })
    .join(", ");
    format!(
        "{KINDS}impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {{\n        Self {{ {fields} }}\n    }}\n}}\n"
    )
}

/// Where the byte `at` of `library` is, as `lib.rs:line:column` (both from 1).
fn location_at(library: &str, at: usize) -> String {
    let before = &library[..at];
    let line = before.matches('\n').count() + 1;
    let column = at - before.rfind('\n').map_or(0, |newline| newline + 1) + 1;
    format!("lib.rs:{line}:{column}")
}

#[test]
fn brackets_on_a_cell_whose_kind_they_mark_nothing_in_are_the_table_s_refusal_at_the_brackets() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    // The cell, its bracketed value, the brackets the refusal stands at, and the class's code.
    let cases = [
        ("pc", "[0]", "[0]", "krs::analysis::invalid-list-notation"),
        (
            "counter",
            "Some([0])",
            "[0]",
            "krs::analysis::invalid-list-notation",
        ),
        ("olist", "[0]", "[0]", "krs::analysis::optional-presence"),
        (
            "shelf",
            "Shelf { bag: [0] }",
            "[0]",
            "krs::analysis::invalid-list-notation",
        ),
        // Brackets mark nothing in a plain cell whatever they hold: an item that is an
        // operator's application is a term, and the brackets around it are still refused.
        (
            "pc",
            "[0 + 1]",
            "[0 + 1]",
            "krs::analysis::invalid-list-notation",
        ),
        (
            "counter",
            "Some([0 + 1])",
            "[0 + 1]",
            "krs::analysis::invalid-list-notation",
        ),
        (
            "shelf",
            "Shelf { bag: [0 + 1] }",
            "[0 + 1]",
            "krs::analysis::invalid-list-notation",
        ),
    ];
    for (index, (cell, value, at, code)) in cases.into_iter().enumerate() {
        let name = format!("kinds-refused-{index}");
        let library = kinds_initializer(cell, value);
        let manifest = package(temporary.path(), &name, &library);
        let (success, stderr) = check(target.path(), &manifest);
        assert!(!success, "{cell}: {value}: {stderr}");
        let errors = stderr
            .lines()
            .filter(|line| line.starts_with("error"))
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{cell}: {value}: {stderr}");
        assert!(
            errors[0].starts_with(&format!("error[{code}]")),
            "{cell}: {value}: {stderr}"
        );
        let value_at = library.find(&format!("{cell}: {value}")).unwrap() + cell.len() + 2;
        let location = location_at(&library, value_at + value.find(at).unwrap());
        assert!(
            stderr.contains(&location),
            "{cell}: {value}: {location}: {stderr}"
        );
        for internal in ["undecided", "E0308", "__krs", "__Krs"] {
            assert!(!stderr.contains(internal), "{cell}: {value}: {stderr}");
        }
    }
}

#[test]
fn brackets_inside_an_optional_list_s_presence_are_its_list() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    for (index, (cell, value)) in [("olist", "Some([0])"), ("stack", "[0]"), ("stack", "[]")]
        .into_iter()
        .enumerate()
    {
        let name = format!("kinds-admitted-{index}");
        let manifest = package(temporary.path(), &name, &kinds_initializer(cell, value));
        let (success, stderr) = check(target.path(), &manifest);
        assert!(success, "{cell}: {value}: {stderr}");
    }
}

#[test]
fn a_value_of_another_kind_than_its_cell_is_the_table_s_refusal_at_the_value() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    // The cell, its value, and the class's code. An initializer's value is its cell's whole
    // initial content, of the cell's declared kind, so the table answers a value of another kind
    // at the value, and rustc says nothing of it.
    let cases = [
        // cell-wrapper: a term on the computation cell, a computation on a leaf.
        ("k", "0", "krs::analysis::cell-wrapper"),
        ("pc", "k::k![0]", "krs::analysis::cell-wrapper"),
        // optional-without-presence, presence-on-plain-cell; a value that is no entry has its
        // marks judged too.
        ("counter", "0", "krs::analysis::optional-presence"),
        ("counter", "0 + 1", "krs::analysis::optional-presence"),
        ("pc", "Some(0)", "krs::analysis::optional-presence"),
        ("pc", "k::absent!(0)", "krs::analysis::optional-presence"),
        // map-notation-at-non-map.
        ("pc", "k::map![0 -> 1]", "krs::analysis::invalid-term"),
        // content-sort: a term on a group, a group record on a leaf, another group's record.
        ("shelf", "0", "krs::analysis::invalid-term"),
        ("pc", "Obj { key: 0 }", "krs::analysis::invalid-term"),
        ("shelf", "Obj { key: 0 }", "krs::analysis::invalid-term"),
    ];
    for (index, (cell, value, code)) in cases.into_iter().enumerate() {
        let name = format!("kinds-kind-{index}");
        let library = kinds_initializer(cell, value);
        let manifest = package(temporary.path(), &name, &library);
        let (success, stderr) = check(target.path(), &manifest);
        assert!(!success, "{cell}: {value}: {stderr}");
        let errors = stderr
            .lines()
            .filter(|line| line.starts_with("error"))
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{cell}: {value}: {stderr}");
        assert!(
            errors[0].starts_with(&format!("error[{code}]")),
            "{cell}: {value}: {stderr}"
        );
        let value_at = library.find(&format!("{cell}: {value}")).unwrap() + cell.len() + 2;
        let location = location_at(&library, value_at);
        assert!(
            stderr.contains(&location),
            "{cell}: {value}: {location}: {stderr}"
        );
        for internal in ["E0308", "E0063", "invalid-configuration", "__krs", "__Krs"] {
            assert!(!stderr.contains(internal), "{cell}: {value}: {stderr}");
        }
    }
}

#[test]
fn a_value_of_its_cell_s_kind_is_admitted_however_it_is_written() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    // A term with an operator, inside its presence or not, and a value written with its Rust
    // wrapper, which rustc checks against the field's type.
    for (index, (cell, value)) in [
        ("pc", "0 + 1"),
        ("counter", "Some(0 + 1)"),
        ("pc", "k::configuration::Cell::new(0)"),
        ("k", "k::configuration::KCell::new(k::k![pgm])"),
    ]
    .into_iter()
    .enumerate()
    {
        let name = format!("kinds-kind-admitted-{index}");
        let manifest = package(temporary.path(), &name, &kinds_initializer(cell, value));
        let (success, stderr) = check(target.path(), &manifest);
        assert!(success, "{cell}: {value}: {stderr}");
    }
}

/// A configuration with a leaf of sort `KSequence` beside the computation: only the explicit
/// `Cell<KSequence>` declares one, and a configuration that writes one wrapper writes them all.
const K_LEAF: &str = r#"
use k::builtin::{Int, KSequence};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {
    #[k::syntax("bump")]
    Bump(),
    #[k::syntax("save")]
    Save(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: k::configuration::KCell<KSequence>,
    #[k::cell]
    pub saved: k::configuration::Cell<KSequence>,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "SAVED")] saved: KSequence,
    ) -> Self {
        Self { k: k::k![pgm], saved: SAVED }
    }
}
"#;

/// A leaf of sort `KSequence` holds one term of that sort, as a `KSequence` field does, on every
/// route: a name bound to one writes it (a configuration variable, a subject's binder, a `cells!`
/// remainder), and the computation's notations, which list a sequence's items, are refused there
/// for what the leaf holds, not as on the computation: `k::k![..]` in an initializer and
/// `KCell(..)` in `cells!` are `cell-wrapper`, brackets in an initializer, a readable record, a
/// claim and inside `Cell(..)` are `invalid-list-notation`.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of routes, each with its admitted or refused spelling."
)]
fn a_leaf_of_sort_k_is_written_by_a_term_of_that_sort_on_every_route() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = |subject: &str, result: &str| {
        format!(
            "k::rules! {{\n    for Machine;\n    use Cmd::*;\n\n    r: {{ k: [Save(), ..], saved: {subject} }} => {{ k: [..], saved: {result} }};\n}}\n"
        )
    };
    let cells = |subject: &str, result: &str| {
        format!(
            "#[k::rule]\npub fn r(\n    k::cells! {{ k: k::configuration::KCell(Cmd::Save(), tail @ ..), saved: {subject}, state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), saved: {result}, ..state }}\n}}\n"
        )
    };
    let claim = |subject: &str, result: &str| {
        format!(
            "k::claims! {{\n    for Machine;\n    use Cmd::*;\n\n    #[k::claim(all_paths)]\n    c: {{ k: [Save()], saved: {subject} }} => {{ k: [], saved: {result} }};\n}}\n"
        )
    };
    let library =
        |saved: &str, sentences: &str| format!("{}{sentences}", K_LEAF.replace("SAVED", saved));
    let admitted = [
        ("initializer-variable", library("saved", "")),
        ("readable-binder", library("saved", &readable("s", "s"))),
        (
            "cells-remainder",
            library(
                "saved",
                &cells("k::configuration::Cell(_)", "k::configuration::Cell(tail)"),
            ),
        ),
    ];
    for (name, source) in admitted {
        let manifest = package(temporary.path(), &format!("k-leaf-{name}"), &source);
        let (success, stderr) = check(target.path(), &manifest);
        assert!(success, "{name}: {stderr}");
    }
    let leaf = "a leaf of sort `KSequence` is no computation: it holds one term of that sort";
    let wrapper = "krs::analysis::cell-wrapper";
    let brackets = "krs::analysis::invalid-list-notation";
    let refused = [
        (
            "initializer-k",
            library("k::k![Cmd::Bump()]", ""),
            wrapper,
            "k::k![Cmd::Bump()]",
        ),
        (
            "initializer-k-empty",
            library("k::k![]", ""),
            wrapper,
            "k::k![]",
        ),
        (
            "initializer-brackets",
            library("[Cmd::Bump()]", ""),
            brackets,
            "[Cmd::Bump()]",
        ),
        (
            "readable-result",
            library("saved", &readable("_", "[Bump()]")),
            brackets,
            "[Bump()]",
        ),
        (
            "readable-subject",
            library("saved", &readable("[Bump(), ..]", "[]")),
            brackets,
            "[Bump(), ..]",
        ),
        (
            "claim-result",
            library("saved", &claim("_", "[Bump()]")),
            brackets,
            "[Bump()]",
        ),
        (
            "cells-result",
            library(
                "saved",
                &cells(
                    "k::configuration::Cell(_)",
                    "k::configuration::KCell(Cmd::Bump())",
                ),
            ),
            wrapper,
            "k::configuration::KCell(Cmd::Bump())",
        ),
        (
            "cells-subject",
            library(
                "saved",
                &cells(
                    "k::configuration::KCell(Cmd::Bump(), rest @ ..)",
                    "k::configuration::Cell(rest)",
                ),
            ),
            wrapper,
            "k::configuration::KCell(Cmd::Bump(), rest @ ..)",
        ),
        (
            "cells-brackets",
            library(
                "saved",
                &cells(
                    "k::configuration::Cell(_)",
                    "k::configuration::Cell([Cmd::Bump()])",
                ),
            ),
            brackets,
            "[Cmd::Bump()]",
        ),
    ];
    for (name, source, code, at) in refused {
        let manifest = package(temporary.path(), &format!("k-leaf-{name}"), &source);
        let (success, stderr) = check(target.path(), &manifest);
        assert!(!success, "{name}: {stderr}");
        let errors = stderr
            .lines()
            .filter(|line| line.starts_with("error"))
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{name}: {stderr}");
        assert!(
            errors[0].starts_with(&format!(
                "error[{code}]: the cell `saved` holds a leaf of sort `KSequence`"
            )) && errors[0].contains(leaf)
                && !errors[0].contains("a value alone"),
            "{name}: {stderr}"
        );
        let location = location_at(&source, source.rfind(at).unwrap());
        assert!(stderr.contains(&location), "{name}: {location}: {stderr}");
    }
}

/// A machine with an `Int` leaf `pc` and a List collection of `T` instances, each with an `Int`
/// leaf child `tn`, whose initializer writes `pc` as `PC`.
const LEAF_TERMS: &str = r#"
use k::builtin::{Int, KSequence};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {
    #[k::syntax("go")]
    Go(),
}

#[k::cell]
pub struct T {
    #[k::cell]
    pub tk: KSequence,
    #[k::cell]
    pub tn: Int,
}

#[k::cell]
pub struct Tqueue {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub tjob: T,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell(nested)]
    pub tqueue: Tqueue,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            pc: PC,
            tqueue: Tqueue { tjob: T { tk: k::k![], tn: 0 } },
        }
    }
}
"#;

/// The inventory of `k::k![..]` where a leaf's term stands (COHERE F1, AUDIT-R A1-4, RDRA item
/// 4): one construct, the computation's item notation, the term of sort `K` its items make. A
/// sentence's leaf entry, readable or `cells!`, is judged by the leaf's sort, one class on both
/// routes ([`the_computation_s_items_on_a_sentence_s_leaf_are_one_verdict_on_every_route`]). Still
/// apart: an initializer reads it as the computation's mark on every cell (`cell-wrapper`, the
/// principles' reading of an initializer's `k::k![..]`), a readable instance child refuses it in
/// the term reader, and a `cells!` instance child's is lowered as the computation's sequence,
/// whose sort the compiler checks. This pins each route's class, so a drift is seen.
#[test]
fn the_computation_s_items_where_a_leaf_s_term_stands_are_pinned_on_each_route() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let library = |pc: &str, sentences: &str| {
        format!(
            "{}{sentences}",
            LEAF_TERMS.replace("pc: PC", &format!("pc: {pc}"))
        )
    };
    let readable = |clause: &str| {
        format!("k::rules! {{\n    for Machine;\n    use Cmd::*;\n\n    {clause}\n}}\n")
    };
    let cells = |subject: &str, result: &str| {
        format!(
            "#[k::rule]\npub fn r(\n    k::cells! {{ k: k::configuration::KCell(Cmd::Go(), tail @ ..), {subject}state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), {result}..state }}\n}}\n"
        )
    };
    let routes = [
        (
            "readable-leaf",
            library(
                "0",
                &readable("go: { k: [Go(), ..], pc: _ } => { k: [..], pc: k::k![1] };"),
            ),
        ),
        (
            "readable-instance-child",
            library(
                "0",
                &readable(
                    "go: { k: [Go(), ..], tjob: [T { tn: k::k![1], .. }, ..] } => { k: [..] };",
                ),
            ),
        ),
        (
            "cells-leaf",
            library(
                "0",
                &cells(
                    "pc: k::configuration::Cell(_), ",
                    "pc: k::configuration::Cell(k::k![1]), ",
                ),
            ),
        ),
        (
            "cells-instance-child",
            library(
                "0",
                &cells(
                    "Tqueue::tjob: [k::fragment![crate::T { tn: k::k![1], .. }], rest @ ..], ",
                    "Tqueue::tjob: [..rest], ",
                ),
            ),
        ),
        ("initializer-value", library("k::k![1]", "")),
        (
            "initializer-constructor",
            library("k::configuration::Cell::new(k::k![1])", ""),
        ),
    ];
    let classes = routes.map(|(route, source)| {
        let manifest = package(temporary.path(), &format!("leaf-items-{route}"), &source);
        let (success, stderr) = check(target.path(), &manifest);
        assert!(!success, "{route}: {stderr}");
        let headline = stderr
            .lines()
            .find(|line| line.starts_with("error["))
            .unwrap_or_else(|| panic!("{route}: no error headline:\n{stderr}"));
        let code = &headline["error[".len()..headline.find(']').unwrap()];
        format!("{route}: {code}")
    });
    expect_test::expect![[r#"
        [
            "readable-leaf: krs::analysis::invalid-term",
            "readable-instance-child: krs::syntax::unsupported-term-expression",
            "cells-leaf: krs::analysis::invalid-term",
            "cells-instance-child: krs::analysis::invalid-term",
            "initializer-value: krs::analysis::cell-wrapper",
            "initializer-constructor: krs::analysis::cell-wrapper",
        ]
    "#]]
    .assert_debug_eq(&classes);
}

/// `k::k![..]`, the computation's item notation, is the term of sort `K` its items make
/// (`a ~> b ~> rest`). Where a sentence's leaf entry writes it, readable or `cells!`, subject or
/// result, rule or claim, the collector judges it by the leaf's sort once the entries are
/// admitted, with one line on every route, at the notation: on a leaf of sort `KSequence` it is
/// a term of the leaf's own sort, written by its items, which a leaf's entry does not lower yet,
/// a stated limit; on a leaf of another sort its sort is not below the leaf's, the sort-mismatch
/// class `invalid-term`, naming the leaf's sort. A clause the readable route reads no
/// computation of (no bracketed value) keeps the term reader's refusal.
#[test]
fn the_computation_s_items_on_a_sentence_s_leaf_are_one_verdict_on_every_route() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let k_leaf = |sentences: &str| {
        format!(
            "{}{sentences}",
            K_LEAF.replace("saved: SAVED", "saved: saved")
        )
    };
    let int_leaf =
        |sentences: &str| format!("{}{sentences}", LEAF_TERMS.replace("pc: PC", "pc: 0"));
    let readable = |save: &str, subject: &str, result: &str| {
        format!(
            "k::rules! {{\n    for Machine;\n    use Cmd::*;\n\n    r: {{ k: [{save}(), ..], {subject} }} => {{ k: [..], {result} }};\n}}\n"
        )
    };
    let claim = |save: &str, subject: &str, result: &str| {
        format!(
            "k::claims! {{\n    for Machine;\n    use Cmd::*;\n\n    #[k::claim(all_paths)]\n    c: {{ k: [{save}()], {subject} }} => {{ k: [], {result} }};\n}}\n"
        )
    };
    let cells = |save: &str, subject: &str, result: &str| {
        format!(
            "#[k::rule]\npub fn r(\n    k::cells! {{ k: k::configuration::KCell(Cmd::{save}(), tail @ ..), {subject}, state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), {result}, ..state }}\n}}\n"
        )
    };
    let leaves: [(&str, &dyn Fn(&str) -> String, [(&str, String, &str); 6]); 2] = [
        (
            "k-leaf",
            &k_leaf,
            [
                (
                    "readable-subject",
                    readable("Save", "saved: k::k![Bump()]", "saved: k::k![]"),
                    "k::k![Bump()]",
                ),
                (
                    "readable-result",
                    readable("Save", "saved: _", "saved: k::k![Bump()]"),
                    "k::k![Bump()]",
                ),
                (
                    "claim-result",
                    claim("Save", "saved: _", "saved: k::k![Bump()]"),
                    "k::k![Bump()]",
                ),
                (
                    "cells-subject",
                    cells(
                        "Save",
                        "saved: k::configuration::Cell(k::k![Cmd::Bump(), r @ ..])",
                        "saved: k::configuration::Cell(k::k![..r])",
                    ),
                    "k::k![Cmd::Bump(), r @ ..]",
                ),
                (
                    "cells-result",
                    cells(
                        "Save",
                        "saved: k::configuration::Cell(_)",
                        "saved: k::configuration::Cell(k::k![Cmd::Bump()])",
                    ),
                    "k::k![Cmd::Bump()]",
                ),
                (
                    "cells-claim-result",
                    cells(
                        "Save",
                        "saved: k::configuration::Cell(_)",
                        "saved: k::configuration::Cell(k::k![])",
                    )
                    .replace("#[k::rule]", "#[k::claim(all_paths, label = \"c\")]"),
                    "k::k![]",
                ),
            ],
        ),
        (
            "int-leaf",
            &int_leaf,
            [
                (
                    "readable-subject",
                    readable("Go", "pc: k::k![1]", "pc: 0"),
                    "k::k![1]",
                ),
                (
                    "readable-result",
                    readable("Go", "pc: _", "pc: k::k![1]"),
                    "k::k![1]",
                ),
                (
                    "claim-result",
                    claim("Go", "pc: _", "pc: k::k![1]"),
                    "k::k![1]",
                ),
                (
                    "cells-subject",
                    cells(
                        "Go",
                        "pc: k::configuration::Cell(k::k![1])",
                        "pc: k::configuration::Cell(0)",
                    ),
                    "k::k![1]",
                ),
                (
                    "cells-result",
                    cells(
                        "Go",
                        "pc: k::configuration::Cell(_)",
                        "pc: k::configuration::Cell(k::k![1])",
                    ),
                    "k::k![1]",
                ),
                (
                    "cells-claim-result",
                    cells(
                        "Go",
                        "pc: k::configuration::Cell(_)",
                        "pc: k::configuration::Cell(k::k![1])",
                    )
                    .replace("#[k::rule]", "#[k::claim(all_paths, label = \"c\")]"),
                    "k::k![1]",
                ),
            ],
        ),
    ];
    let mut verdicts = Vec::new();
    for (leaf, library, routes) in leaves {
        let mut lines = Vec::new();
        for (route, sentence, at) in routes {
            let source = library(&sentence);
            let manifest = package(temporary.path(), &format!("items-{leaf}-{route}"), &source);
            let (success, stderr) = check(target.path(), &manifest);
            assert!(!success, "{leaf} {route}: {stderr}");
            let errors = stderr
                .lines()
                .filter(|line| line.starts_with("error"))
                .collect::<Vec<_>>();
            assert_eq!(errors.len(), 1, "{leaf} {route}: {stderr}");
            let location = location_at(&source, source.find(at).unwrap());
            assert!(
                stderr.contains(&location),
                "{leaf} {route}: {location}: {stderr}"
            );
            lines.push((route, errors[0].to_owned()));
        }
        let (_, first) = &lines[0];
        for (route, line) in &lines {
            assert_eq!(
                line, first,
                "{leaf}: the {route} is told as the readable subject is"
            );
        }
        verdicts.push(format!("{leaf}: {first}"));
    }
    expect_test::expect![[r#"
        [
            "k-leaf: error[krs::analysis::invalid-term]: the cell `saved` holds a leaf of sort `KSequence`, and `k::k![..]` writes a term of that sort by its items (`a ~> b ~> rest`), which a leaf holds; a leaf's entry written by its items is not supported yet: write it with a name bound to such a value",
            "int-leaf: error[krs::analysis::invalid-term]: the cell `pc` holds a leaf of sort `Int`, and the entry gives it `k::k![..]`, the computation's item notation, a term of sort `K` (its items in order), whose sort is not below the leaf's",
        ]
    "#]].assert_debug_eq(&verdicts);
}

/// A value written with its Rust wrapper, `Cell::new(v)` or `KCell::new(v)`, at any depth, is the
/// value `v` (COHERE F2): KRS judges `v` against its cell's kind as it judges the plain value,
/// with the plain value's line at `v`, before rustc reads anything of it. So `k::k![..]` on a
/// leaf of sort `KSequence` is the initializer's `cell-wrapper` in either spelling (rustc's
/// `E0308` for the `KCell::new` one), a term alone on the computation is too (rustc's `E0308` for
/// `Cell::new(pgm)`), and a group's child the same. A wrapper of the other family than its value
/// (`Cell::new(k::k![..])`, `KCell::new(x)`) is the reader's refusal once the value has been
/// judged; one of the value's family is admitted as the plain value is.
#[test]
fn a_value_written_with_its_rust_wrapper_is_judged_as_the_value_it_wraps() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let k_leaf = |k: &str, saved: &str| {
        K_LEAF
            .replace("saved: SAVED", &format!("saved: {saved}"))
            .replace("k: k::k![pgm]", &format!("k: {k}"))
    };
    let admitted = [
        (
            "wrapped-both",
            k_leaf(
                "k::configuration::KCell::new(k::k![pgm])",
                "k::configuration::Cell::new(saved)",
            ),
        ),
        ("plain-both", k_leaf("k::k![pgm]", "saved")),
    ];
    for (name, source) in admitted {
        let manifest = package(temporary.path(), &format!("wrapped-{name}"), &source);
        let (success, stderr) = check(target.path(), &manifest);
        assert!(success, "{name}: {stderr}");
    }
    let twins = [
        (
            "k-leaf-items",
            k_leaf(
                "k::k![pgm]",
                "k::configuration::KCell::new(k::k![Cmd::Bump()])",
            ),
            k_leaf("k::k![pgm]", "k::k![Cmd::Bump()]"),
            "k::k![Cmd::Bump()]",
        ),
        (
            "k-leaf-items-in-cell",
            k_leaf(
                "k::k![pgm]",
                "k::configuration::Cell::new(k::k![Cmd::Bump()])",
            ),
            k_leaf("k::k![pgm]", "k::k![Cmd::Bump()]"),
            "k::k![Cmd::Bump()]",
        ),
        (
            "computation-term",
            k_leaf("k::configuration::Cell::new(pgm)", "saved"),
            k_leaf("pgm", "saved"),
            "pgm",
        ),
    ];
    let mut lines = Vec::new();
    for (name, wrapped, plain, at) in twins {
        let mut headlines = Vec::new();
        for (spelling, source) in [("wrapped", wrapped), ("plain", plain)] {
            let manifest = package(
                temporary.path(),
                &format!("wrapped-{name}-{spelling}"),
                &source,
            );
            let (success, stderr) = check(target.path(), &manifest);
            assert!(!success, "{name} {spelling}: {stderr}");
            let errors = stderr
                .lines()
                .filter(|line| line.starts_with("error"))
                .collect::<Vec<_>>();
            assert_eq!(errors.len(), 1, "{name} {spelling}: {stderr}");
            let location = location_at(&source, source.rfind(at).unwrap());
            assert!(
                stderr.contains(&location),
                "{name} {spelling}: {location}: {stderr}"
            );
            headlines.push(errors[0].to_owned());
        }
        assert_eq!(
            headlines[0], headlines[1],
            "{name}: the wrapper changes nothing"
        );
        lines.push(format!("{name}: {}", headlines[0]));
    }
    let family = [
        (
            "cell-around-items",
            k_leaf("k::configuration::Cell::new(k::k![pgm])", "saved"),
        ),
        (
            "kcell-around-a-term",
            k_leaf("k::k![pgm]", "k::configuration::KCell::new(saved)"),
        ),
    ];
    for (name, source) in family {
        let manifest = package(temporary.path(), &format!("wrapped-{name}"), &source);
        let (success, stderr) = check(target.path(), &manifest);
        assert!(!success, "{name}: {stderr}");
        let headline = stderr
            .lines()
            .find(|line| line.starts_with("error"))
            .unwrap_or_else(|| panic!("{name}: {stderr}"));
        lines.push(format!("{name}: {headline}"));
    }
    expect_test::expect![[r#"
        [
            "k-leaf-items: error[krs::analysis::cell-wrapper]: the cell `saved` holds a leaf of sort `KSequence`, and the entry's wrapper is not that content's: `k::k![..]` lists a computation's items, which only a computation cell holds, and a leaf's initial value is one term of its sort; a leaf of sort `KSequence` is no computation: it holds one term of that sort, as a `KSequence` field does, and no KRS term lists a sequence's items, so a name bound to such a value writes it; write its entry as `x`",
            "k-leaf-items-in-cell: error[krs::analysis::cell-wrapper]: the cell `saved` holds a leaf of sort `KSequence`, and the entry's wrapper is not that content's: `k::k![..]` lists a computation's items, which only a computation cell holds, and a leaf's initial value is one term of its sort; a leaf of sort `KSequence` is no computation: it holds one term of that sort, as a `KSequence` field does, and no KRS term lists a sequence's items, so a name bound to such a value writes it; write its entry as `x`",
            "computation-term: error[krs::analysis::cell-wrapper]: the cell `k` holds a computation, and the entry's wrapper is not that content's: a computation's initial value is its items, in `k::k![..]` or in brackets, and a value alone is no computation; write its entry as `k::k![x]`",
            "cell-around-items: error[krs::syntax::unsupported-initializer-body]: unsupported declarative initializer body: `KCell` requires `k!`; `Cell` accepts ordinary terms or `map!`",
            "kcell-around-a-term: error[krs::syntax::unsupported-initializer-body]: unsupported declarative initializer body: `KCell::new` requires an explicit `k!` payload",
        ]
    "#]].assert_debug_eq(&lines);
}
