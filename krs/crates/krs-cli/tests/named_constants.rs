//! `#[k::constant]` end to end: authored packages through `krs check`,
//! `emit-k`, `run`, `prove`, and `expand`.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
    Instr;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Load, Fetch, Wrap))]
pub enum ExpSyntax {
    #[k::syntax("load({n})")]
    Load { n: Int },
    #[k::syntax("fetch({i})")]
    Fetch { i: Instr },
    #[k::syntax("wrap({n})")]
    Wrap { n: Int },
}

#[k::constructors(sort = Instr, result = KResult)]
pub enum Instruction {
    #[k::syntax("nop")]
    Nop {},
    #[k::syntax("jump({target})")]
    Jump { target: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
}

#[k::function(total, internal)]
pub fn Port(value: Term<Int>) -> Term<Int>;
"#;

/// Every place a constant may stand: a table row, a rule pattern and
/// result, a readable record, an initializer, a claim, a guard, a constant
/// of a user sort defined from another constant, one imported from a module,
/// and one a qualified path names.
const NAMED: &str = r#"
/// Interrupt flag register.
#[k::constant]
pub const IF: Int = 0xFF0F;

#[k::constant]
pub const IE: Int = 0xFFFF;

#[k::constant]
pub const ALIAS: Int = IF;

#[k::constant]
pub const START: Instr = Instruction::Jump(IF);

#[k::constant]
pub const PC_START: Int = 0x100;

mod io {
    use k::builtin::Int;

    #[k::constant]
    pub const LCDC: Int = 0xFF40;
}

use io::LCDC;

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm], pc: PC_START }
    }
}

k::equations! {
    for Port;
    port_if   : IF        => 1;
    port_ie   : crate::IE => 2;
    port_lcdc : LCDC      => 3;
    #[k::equation(owise)]
    port_other: n         => 0;
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    load : Load(n)      => Port(n);
    fetch: Fetch(START) => ALIAS;
}

k::rules! {
    for Machine;
    use ExpSyntax::*;

    #[k::requires(n.lt::<Int>(IE))]
    step: { k: [Wrap(n), ..], pc: PC_START } => { k: [Load(n), ..], pc: IF };
}

#[k::claim(all_paths, label = "wrap-to-port")]
pub fn wrap_to_port(
    k::cells! { k: k::configuration::KCell(ExpSyntax::Wrap(IF), tail @ ..), pc: k::configuration::Cell(PC_START), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(1, ..tail), pc: k::configuration::Cell(IF), ..state }
}
"#;

/// [`NAMED`] with every constant's value written at its uses.
const INLINE: &str = r#"
impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm], pc: 256 }
    }
}

k::equations! {
    for Port;
    port_if   : 65295 => 1;
    port_ie   : 65535 => 2;
    port_lcdc : 65344 => 3;
    #[k::equation(owise)]
    port_other: n     => 0;
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    load : Load(n)                          => Port(n);
    fetch: Fetch(Instruction::Jump(65295))  => 65295;
}

k::rules! {
    for Machine;
    use ExpSyntax::*;

    #[k::requires(n.lt::<Int>(65535))]
    step: { k: [Wrap(n), ..], pc: 256 } => { k: [Load(n), ..], pc: 65295 };
}

#[k::claim(all_paths, label = "wrap-to-port")]
pub fn wrap_to_port(
    k::cells! { k: k::configuration::KCell(ExpSyntax::Wrap(65295), tail @ ..), pc: k::configuration::Cell(256), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(1, ..tail), pc: k::configuration::Cell(65295), ..state }
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a package named `name` under `root` whose library is `source`,
/// and returns its manifest. `dependencies` are extra `[dependencies]` lines.
fn write_package(root: &Path, name: &str, source: &str, dependencies: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CONSTANTS-{}\"\n\n[package.metadata.krs.definitions.main]\n",
            krs_path(),
            name.to_ascii_uppercase()
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// A one-package workspace named `constants` whose library is the preamble
/// and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    let manifest = write_package(root, "constants", &format!("{PREAMBLE}{source}"), "");
    let mut text = fs::read_to_string(&manifest).unwrap();
    text.push_str("\n[workspace]\nresolver = \"3\"\n");
    fs::write(&manifest, text).unwrap();
    manifest
}

/// Runs `krs <command>` on `package`'s `main` definition.
fn krs(
    target: &Path,
    manifest: &Path,
    package: &str,
    command: &str,
    extra: &[&str],
) -> (bool, String, String) {
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
fn emitted_k(target: &Path, manifest: &Path) -> (String, String) {
    let output = emit_k(target, manifest);
    (
        fs::read_to_string(output.join("definition.k")).unwrap(),
        fs::read_to_string(output.join("spec.k")).unwrap(),
    )
}

/// The directory `krs emit-k` wrote.
fn emit_k(target: &Path, manifest: &Path) -> PathBuf {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "constants",
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    output
}

/// The `<k>` and `<pc>` cells after `krs run` of `program`.
fn run(target: &Path, manifest: &Path, program: &str) -> String {
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, program).unwrap();
    let (_, stdout, stderr) = krs(
        target,
        manifest,
        "constants",
        "run",
        &[file.to_str().unwrap()],
    );
    let cell = |name: &str| {
        let mut lines = stdout.lines().skip_while(|line| line.trim() != name);
        lines.nth(1).map_or_else(
            || panic!("`krs run {program}` printed no {name} cell:\n{stdout}\n{stderr}"),
            |line| line.trim().trim_end_matches(" ~> .K").to_owned(),
        )
    };
    format!("{} / pc {}", cell("<k>"), cell("<pc>"))
}

/// The `error[..]` headlines of `krs check` and the locations they point at.
fn check_errors(target: &Path, manifest: &Path) -> Vec<String> {
    let (success, _, stderr) = krs(target, manifest, "constants", "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    let directory = format!("{}/", manifest.parent().unwrap().display());
    stderr
        .lines()
        .filter(|line| line.starts_with("error") || line.trim_start().starts_with("--> "))
        .map(|line| line.trim().replace(&directory, ""))
        .collect()
}

#[test]
fn a_constant_stands_for_its_value_at_every_use() {
    let target = shared_fixture_target();
    let named = temp_dir();
    let inline = temp_dir();
    let named_manifest = package(named.path(), NAMED);
    let inline_manifest = package(inline.path(), INLINE);
    assert_eq!(
        emitted_k(target.path(), &named_manifest),
        emitted_k(target.path(), &inline_manifest)
    );
    let outcomes = [
        "load(65295)",
        "load(65535)",
        "load(65344)",
        "load(7)",
        "fetch(jump(65295))",
        "wrap(3)",
    ]
    .map(|program| {
        format!(
            "{program} => {}",
            run(target.path(), &named_manifest, program)
        )
    });
    expect_test::expect![[r#"
        [
            "load(65295) => 1 / pc 256",
            "load(65535) => 2 / pc 256",
            "load(65344) => 3 / pc 256",
            "load(7) => 0 / pc 256",
            "fetch(jump(65295)) => 65295 / pc 256",
            "wrap(3) => 0 / pc 65295",
        ]
    "#]]
    .assert_debug_eq(&outcomes);
    let (proven, stdout, stderr) = krs(target.path(), &named_manifest, "constants", "prove", &[]);
    assert!(proven, "{stdout}\n{stderr}");
    assert!(stdout.contains("wrap-to-port: proven"), "{stdout}");
    // `krs expand` names each use by the constant's path.
    let (expanded, stdout, stderr) =
        krs(target.path(), &named_manifest, "constants", "expand", &[]);
    assert!(expanded, "{stderr}");
    assert!(
        stdout.contains("Port(crate ::IF)") || stdout.contains("Port(crate::IF)"),
        "{stdout}"
    );
}

/// The constant islands `k::id!`, `k::bytes!` and `k::lexeme!` as constant
/// values, used in a pattern and a result directly and through a constant
/// built from them.
const ISLANDS: &str = r#"
use k::builtin::{Bytes, Id};

/// A closed token sort, for `k::lexeme!`.
#[k::token(regex = r"w[a-z]*")]
pub struct Word(pub String);

#[k::constructors(sort = Instr, result = KResult)]
pub enum Named {
    #[k::syntax("named({name}, {code}, {word})")]
    Entry { name: Id, code: Bytes, word: Word },
}
"#;

#[test]
fn a_constant_island_stands_for_its_token_at_every_use() {
    let target = shared_fixture_target();
    let named = temp_dir();
    let inline = temp_dir();
    let named_manifest = package(
        named.path(),
        &format!(
            r#"{ISLANDS}{INITIALIZER}
#[k::constant]
pub const MAIN: Id = k::id!("$main");

#[k::constant]
pub const MAGIC: Bytes = k::bytes!(b"ab");

#[k::constant]
pub const WORD: Word = k::lexeme!(Word, "word");

#[k::constant]
pub const ENTRY: Instr = Named::Entry(MAIN, MAGIC, WORD);

k::rules! {{
    for Exp;
    use ExpSyntax::*;

    entry: Fetch(Named::Entry(MAIN, MAGIC, WORD)) => Wrap(1);
    exit : Load(0)                                => Fetch(ENTRY);
}}
"#
        ),
    );
    let inline_manifest = package(
        inline.path(),
        &format!(
            r#"{ISLANDS}{INITIALIZER}
k::rules! {{
    for Exp;
    use ExpSyntax::*;

    entry: Fetch(Named::Entry(k::id!("$main"), k::bytes!(b"ab"), k::lexeme!(Word, "word")))
        => Wrap(1);
    exit : Load(0)
        => Fetch(Named::Entry(k::id!("$main"), k::bytes!(b"ab"), k::lexeme!(Word, "word")));
}}
"#
        ),
    );
    let definition = |manifest| {
        fs::read_to_string(emit_k(target.path(), manifest).join("definition.k")).unwrap()
    };
    let named = definition(&named_manifest);
    assert_eq!(named, definition(&inline_manifest));
    let entry =
        r#"named ( #token("$main","Id") , #token("b\"ab\"","Bytes") , #token("word","Word") )"#;
    assert_eq!(named.matches(entry).count(), 2, "{named}");
}

#[test]
fn a_constant_from_a_dependency_is_used_by_its_path() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    write_package(
        temporary.path(),
        "base",
        "use k::builtin::Int;\n\n/// The base package's answer.\n#[k::constant]\npub const ANSWER: Int = 42;\n",
        "",
    );
    let root = write_package(
        temporary.path(),
        "root",
        r#"
use k::builtin::{Int, KSequence};
use k::KResult;

use base::ANSWER;

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("ask({n})")]
    Ask { n: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    ask: Ask(ANSWER) => base::ANSWER;
}
"#,
        "base = { path = \"../base\" }\n",
    );
    fs::write(
        temporary.path().join("Cargo.toml"),
        "[workspace]\nmembers = [\"base\", \"root\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    let output = root.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &root,
        "root",
        "emit-k",
        &[
            "--dependency",
            "base:main",
            "--output",
            output.to_str().unwrap(),
        ],
    );
    assert!(success, "{stderr}");
    let emitted = fs::read_to_string(output.join("definition.k")).unwrap();
    assert!(
        emitted.contains("<k> ask ( 42 ) => 42 ... </k>"),
        "{emitted}"
    );
}

#[test]
fn a_constant_names_a_ground_constructor_term_of_its_sort() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "function",
            "#[k::constant]\npub const BAD: Int = Port(1);\n",
        ),
        (
            "notation",
            "#[k::constant]\npub const BAD: Int = 1.add::<Int>(2);\n",
        ),
        ("sort", "#[k::constant]\npub const BAD: Instr = 5;\n"),
        (
            "cycle",
            "#[k::constant]\npub const AA: Int = BB;\n\n#[k::constant]\npub const BB: Int = AA;\n",
        ),
        (
            "unresolved",
            "#[k::constant]\npub const IF: Int = 0xFF0F;\n\nk::rules! {\n    for Exp;\n    use ExpSyntax::*;\n    load: Load(IFF) => 1;\n}\n",
        ),
        (
            "arguments",
            "#[k::constant]\npub const IF: Int = 0xFF0F;\n\nk::rules! {\n    for Exp;\n    use ExpSyntax::*;\n    load: Load(n) => IF(n);\n}\n",
        ),
    ];
    let errors = cases.map(|(name, source)| {
        let directory = temporary.path().join(name);
        let manifest = package(&directory, &format!("{source}{INITIALIZER}"));
        (name, check_errors(target.path(), &manifest))
    });
    expect_test::expect![[r#"
        [
            (
                "function",
                [
                    "error[krs::analysis::invalid-constant]: the value of constant `BAD` applies the function `Port`; a constant names a ground constructor term, which every use can match, and a function application is evaluated, not matched",
                    "--> src/lib.rs:42:22",
                ],
            ),
            (
                "notation",
                [
                    "error[krs::syntax::invalid-constant]: the value of constant `BAD` must be a ground constructor term (a literal, a constructor application of ground terms, or another constant), so that it is matchable wherever it is used; a builtin operation is not one",
                    "--> src/lib.rs:42:22",
                ],
            ),
            (
                "sort",
                [
                    "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-CONSTANTS-CONSTANTS::BAD (constant): literal `5` of sort Int is not admissible at sort ORG-KRS-CONSTANTS-CONSTANTS::Instr (sort)",
                    "--> src/lib.rs:42:24",
                ],
            ),
            (
                "cycle",
                [
                    "error[krs::analysis::invalid-constant]: constants refer to each other in a cycle (`AA` -> `BB` -> `AA`), so none of them names a term",
                    "--> src/lib.rs:42:11",
                ],
            ),
            (
                "unresolved",
                [
                    "error[E0422]: cannot find struct, variant or union type `IFF` in this scope",
                    "--> src/lib.rs:47:16",
                ],
            ),
            (
                "arguments",
                [
                    "error[krs::analysis::invalid-constant]: `IF` is a constant, a value rather than a function: write `IF` without arguments",
                    "--> src/lib.rs:47:22",
                ],
            ),
        ]
    "#]].assert_debug_eq(&errors);
}

const INITIALIZER: &str = r"
impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm], pc: 0 }
    }
}
";
