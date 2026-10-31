//! Builtin literals in `#[k::init]` initializers: `k::bytes!(b"..")`,
//! `k::id!("$x")`, and `k::lexeme!(Sort, "text")` each denote one constant
//! of their sort, so an initializer may hold them wherever it holds a term:
//! as a cell's whole value, as an argument, as a map key or value. A rule's
//! literal pattern matches the initializer's literal, since both denote the
//! same constant. `k::anonymous!` and `k::or_bool!` have no meaning in an
//! initial configuration and are rejected at their own span.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Bytes, Id, Int, KSequence, List, Map, list};
use k::KResult;

k::sorts! {
    Stmt;
    Value: KResult;
    impl Value for Int;
    impl Value for Bytes;
}

#[k::token(regex = "[a-z]+")]
pub struct Label(String);

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
    pub mem: Bytes,
    #[k::cell]
    pub who: Id,
    #[k::cell]
    pub label: Label,
    #[k::cell]
    pub labels: List<Label>,
    #[k::cell]
    pub env: Map<Id, Value>,
    #[k::cell]
    pub stack: List<Value>,
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    elf: {
        k: [Skip(), ..],
        mem: k::bytes!(b"\x7fELF"),
        who: k::id!("$main"),
        label: k::lexeme!(Label, "entry"),
    } => { k: [..], mem: k::bytes!(b"ok") };
}
"#;

/// The initializer's fields, one per line, in declaration order.
const FIELDS: [(&str, &str); 7] = [
    ("k", "k::k![pgm]"),
    ("mem", r#"k::bytes!(b"\x7fELF")"#),
    ("who", r#"k::id!("$main")"#),
    ("label", r#"k::lexeme!(Label, "entry")"#),
    ("labels", r#"list::item(k::lexeme!(Label, "exit"))"#),
    (
        "env",
        r#"k::map![k::id!("$x") -> k::bytes!(b"\x00\xff"), k::id!("$y") -> 1]"#,
    ),
    (
        "stack",
        r#"list::concat(list::item(k::bytes!(b"")), list::item(k::bytes!(b"ab")))"#,
    ),
];

/// The initializer with `replacement` as the value of its field.
fn initializer(replacement: Option<(&str, &str)>) -> String {
    let mut fields = String::new();
    for (name, value) in FIELDS {
        let value = match replacement {
            Some((field, replaced)) if field == name => replaced,
            _ => value,
        };
        writeln!(fields, "            {name}: {value},").unwrap();
    }
    format!(
        "impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {{\n        Self {{\n{fields}        }}\n    }}\n}}\n"
    )
}

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
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-INIT-LITERALS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
fn initializers_hold_builtin_literals_and_lexemes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "literals",
        &format!("{PREAMBLE}{}", initializer(None)),
    );
    let definition = emit(target.path(), &manifest);
    // Two Bytes literals in one list and two Id keys in one map take
    // distinct ordinals in source order: transport checks every key.
    expect_test::expect![[r#"
        <k> $PGM:Stmt </k>
        <mem> #token("b\"\x7fELF\"","Bytes") </mem>
        <who> #token("$main","Id") </who>
        <label> #token("entry","Label") </label>
        <labels> ListItem(#token("exit","Label")) </labels>
        <env> #token("$x","Id") |-> #token("b\"\x00\xff\"","Bytes") #token("$y","Id") |-> 1 </env>
        <stack> ListItem(#token("b\"\"","Bytes")) ListItem(#token("b\"ab\"","Bytes")) </stack>"#]]
    .assert_eq(&configuration(&definition));

    // The rule's literal patterns match the initializer's literals.
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "skip").unwrap();
    let (_, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[program.to_str().unwrap()],
    );
    let state = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    for cell in [
        "<k> .K </k>",
        r#"<mem> b"ok" </mem>"#,
        "<who> $main </who>",
        "<label> entry </label>",
        "<labels> ListItem ( exit ) </labels>",
        r#"<env> $x |-> b"\x00\xff" $y |-> 1 </env>"#,
        r#"<stack> ListItem ( b"" ) ListItem ( b"ab" ) </stack>"#,
    ] {
        assert!(state.contains(cell), "{cell}\n{stdout}\n{stderr}");
    }

    // The expanded initializer reads back to the same configuration.
    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    assert!(
        expanded.contains(r#"mem: k::configuration::Cell::new(k::bytes!(b"\x7fELF")),"#),
        "{expanded}"
    );
    let reference = package(temporary.path(), "expanded", &expanded);
    assert_eq!(
        configuration(&emit(target.path(), &reference)),
        configuration(&definition)
    );
}

#[test]
fn initializers_reject_symbolic_islands_and_ill_sorted_literals() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let anonymous = "error[krs::expand::claim-subject-only-term]: `k::anonymous!` is a value nothing determines, which only a claim's start state may hold; here it stands in the value of an initializer";
    let cases = [
        (
            "anonymous-root",
            ("mem", r#"k::anonymous!(Bytes, "_M")"#),
            anonymous,
            r#""_M""#,
        ),
        (
            "anonymous-nested",
            ("stack", r#"list::item(k::anonymous!(Value, "_V"))"#),
            anonymous,
            r#""_V""#,
        ),
        (
            "or-bool",
            ("stack", "list::item(k::or_bool!(true, false))"),
            "error[krs::expand::claim-only-term]: `k::or_bool!` joins a claim's symbolic conditions, so it stands only in a claim; here it stands in the value of an initializer",
            "k::or_bool!(true, false)",
        ),
        (
            "invalid-id",
            ("who", r#"k::id!("main")"#),
            "error[krs::syntax::unsupported-term-expression]: unsupported term expression: invalid builtin `Id` token; expected `$` followed by ASCII letters, digits, or `_`",
            r#""main""#,
        ),
        (
            "ill-sorted",
            ("stack", r#"list::item(k::id!("$x"))"#),
            "error[krs::analysis::collection-element-sort]: `k::id!(..)` of sort Id is stored as an element of the cell `stack`, declared `List<Value>`, and Id is not a Value",
            r#""$x""#,
        ),
    ];
    for (name, replacement, headline, marked) in cases {
        let manifest = package(
            temporary.path(),
            name,
            &format!("{PREAMBLE}{}", initializer(Some(replacement))),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: {stderr}");
        let lines = stderr.lines().collect::<Vec<_>>();
        let errors = lines
            .iter()
            .enumerate()
            .filter(|(_, line)| line.starts_with("error"))
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{name}: {stderr}");
        let (index, line) = errors[0];
        assert_eq!(*line, headline, "{name}: {stderr}");
        // `--> path`, ` |`, `N | source`, ` |   ^^^`.
        let source = lines[index + 3].split_once(" | ").unwrap().1;
        let carets = lines[index + 4].split_once(" | ").unwrap().1;
        let start = carets.find('^').unwrap();
        let width = carets[start..].chars().take_while(|c| *c == '^').count();
        assert_eq!(&source[start..start + width], marked, "{name}: {stderr}");
    }
}
