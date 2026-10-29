//! The empty Map, List, and Set of a leaf cell, end to end: `map::empty()`,
//! `[]`, and `set::empty()` in readable claims and rules emit the K of the
//! reference `cells!` spelling (`map![.Map]`, `list::empty()`,
//! `set::empty()`), and `krs expand` writes them as the calls.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, List, Map, Set, list, map, set};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum Cmd {
    #[k::syntax("reset")]
    Reset(),
    #[k::syntax("load({n})")]
    Load { n: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub functions: Map,
    #[k::cell]
    pub stack: List,
    #[k::cell]
    pub seen: Set,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            functions: k::map![],
            stack: list::empty(),
            seen: set::empty(),
        }
    }
}

/// The empty map, as a function body.
#[k::function(total, internal)]
pub fn NoFunctions(n: Term<Int>) -> Term<Map>;

k::equations! {
    for NoFunctions;
    none: _ => map::empty();
}

/// The empty list, as a function body.
#[k::function(total, internal)]
pub fn NoItems(n: Term<Int>) -> Term<List>;

k::equations! {
    for NoItems;
    none_items: _ => [];
}
"#;

/// A readable rule that empties every collection cell and one that applies
/// only to empty ones, and a readable claim over empty collections.
const READABLE: &str = r"
k::rules! {
    for Machine;
    use Cmd::*;

    reset: { k: [Reset(), ..], functions: _, stack: _, seen: _ } => {
        k: [..],
        functions: map::empty(),
        stack: [],
        seen: set::empty(),
    };
    load: { k: [Load { n }, ..], functions: map::empty(), stack: [], seen: set::empty() } => {
        k: [n, ..],
    };
}

k::claims! {
    for Machine;
    use Cmd::*;

    #[k::claim(all_paths)]
    loads: { k: [Load { n: 3 }], functions: map::empty(), stack: [], seen: set::empty() } => {
        k: [3],
    };
}
";

/// The same rules and claim in the reference `cells!` spelling.
const REFERENCE: &str = r#"
#[k::rule(label = "reset")]
pub fn reset(
    k::cells! {
        k: k::configuration::KCell(Cmd::Reset(), tail @ ..),
        functions: k::configuration::Cell(_),
        stack: k::configuration::Cell(_),
        seen: k::configuration::Cell(_),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        functions: k::configuration::Cell(map![.Map]),
        stack: k::configuration::Cell(list::empty()),
        seen: k::configuration::Cell(set::empty()),
        ..state
    }
}

#[k::rule(label = "load")]
pub fn load(
    n: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Load(n), tail @ ..),
        functions: k::configuration::Cell(map![.Map]),
        stack: k::configuration::Cell(list::empty()),
        seen: k::configuration::Cell(set::empty()),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(n, ..tail),
        ..state
    }
}

#[k::claim(all_paths, label = "loads")]
fn loads(
    k::cells! {
        k: k::configuration::KCell(Cmd::Load(3)),
        functions: k::configuration::Cell(map![.Map]),
        stack: k::configuration::Cell(list::empty()),
        seen: k::configuration::Cell(set::empty()),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(3),
        ..state
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

/// Writes a one-package workspace whose library is `library`.
fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-EMPTY\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The emitted `definition.k` and `spec.k`.
fn emitted(target: &Path, manifest: &Path) -> (String, String) {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let read = |file: &str| fs::read_to_string(output.join(file)).unwrap();
    (read("definition.k"), read("spec.k"))
}

/// `map::empty()`, `[]`, and `set::empty()` are the empty Map, List, and Set
/// on either side of a readable rule and of a readable claim: the K is the
/// reference spelling's, `.Map`, `.List`, and `.Set`.
#[test]
fn readable_empty_collections_are_the_reference_units() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = package(
        temporary.path(),
        "readable",
        &format!("{PREAMBLE}{READABLE}"),
    );
    let reference = package(
        temporary.path(),
        "reference",
        &format!("{PREAMBLE}{REFERENCE}"),
    );
    let (definition, spec) = emitted(target.path(), &readable);
    let (reference_definition, reference_spec) = emitted(target.path(), &reference);
    // The reference rules write the computation cell's tail; the cells
    // agree line for line.
    assert_eq!(spec, reference_spec);
    let leaf_cells = |text: &str| {
        text.lines()
            .filter(|line| !line.trim_start().starts_with("<k>"))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
    assert_eq!(leaf_cells(&definition), leaf_cells(&reference_definition));
    let rule = |text: &str, label: &str| {
        let start = text.find(&format!("[{label}]:")).unwrap();
        let end = start + text[start..].find("\n\n").unwrap_or(text.len() - start);
        text[start..end]
            .lines()
            .skip(1)
            .map(str::trim)
            .collect::<Vec<_>>()
            .join(" ")
    };
    expect_test::expect![[r#"
        [
            "<k> reset => .K ... </k> <functions> _ => .Map </functions> <stack> _ => .List </stack> <seen> _ => .Set </seen> endmodule",
            "<k> load ( N:Int ) => N:Int ... </k> <functions> .Map </functions> <stack> .List </stack> <seen> .Set </seen> rule [reset]: <k> reset => .K ... </k> <functions> _ => .Map </functions> <stack> _ => .List </stack> <seen> _ => .Set </seen> endmodule",
            "<k> load ( 3 ) => 3 </k> <functions> .Map </functions> <stack> .List </stack> <seen> .Set </seen> endmodule",
        ]
    "#]]
    .assert_debug_eq(&[
        rule(&definition, "reset"),
        rule(&definition, "load"),
        rule(&spec, "loads"),
    ]);
    assert!(
        definition.contains("rule noFunctions ( _ ) => .Map"),
        "{definition}"
    );
    assert!(
        definition.contains("rule noItems ( _ ) => .List"),
        "{definition}"
    );

    let (success, expanded, stderr) = krs(target.path(), &readable, "expand", &[]);
    assert!(success, "{stderr}");
    for call in [
        "k::configuration::Cell(k::builtin::map::empty())",
        "k::configuration::Cell(k::builtin::list::empty())",
        "k::configuration::Cell(k::builtin::set::empty())",
    ] {
        assert!(
            expanded
                .replace(['\n', ' '], "")
                .contains(&call.replace(' ', "")),
            "{call}:\n{expanded}"
        );
    }
}

/// The `error[..]` headlines of `krs check` and the locations they point at.
fn check_errors(target: &Path, manifest: &Path) -> Vec<String> {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    let directory = format!("{}/", manifest.parent().unwrap().display());
    stderr
        .lines()
        .filter(|line| line.starts_with("error[") || line.trim_start().starts_with("--> "))
        .map(|line| line.trim().replace(&directory, ""))
        .collect()
}

/// `map![]` is the empty map literal in a readable result, as in every term
/// (`map::empty()`), and braces name collection instances: their error names
/// the spelling of the empty collection.
#[test]
fn other_spellings_name_the_empty_collections() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let clause = |name: &str, clause: &str| {
        package(
            temporary.path(),
            name,
            &format!(
                "{PREAMBLE}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    step: {{ k: [Reset(), ..], {clause}\n}}\n"
            ),
        )
    };
    let literal = clause(
        "map-macro",
        "functions: _ } => { k: [..], functions: k::map![] };",
    );
    let (success, _, stderr) = krs(target.path(), &literal, "check", &[]);
    assert!(success, "the empty map literal is refused:\n{stderr}");
    let errors = check_errors(
        target.path(),
        &clause("braces", "functions: {} } => { k: [..] };"),
    );
    expect_test::expect![[r#"
        [
            "error[krs::analysis::collection-entry]: `functions` is not a cell collection: an instance list names a cell declared `#[k::cell(multiplicity = \"*\", cell_type = .., nested)]`; the empty Map or Set a leaf cell holds is `map::empty()` or `set::empty()`, and its empty List is `[]`",
            "--> src/lib.rs:63:31",
        ]
    "#]]
    .assert_debug_eq(&errors);
}
