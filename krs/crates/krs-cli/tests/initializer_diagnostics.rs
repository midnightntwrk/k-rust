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
