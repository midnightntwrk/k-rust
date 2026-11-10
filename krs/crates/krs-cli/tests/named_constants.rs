//! `#[k::constant]` end to end: authored packages through `krs check`,
//! `emit-k`, `run`, `prove`, and `expand`.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{
    fixture_build_env, krs_command, shared_fixture_target, temp_dir, without_constant_names,
};

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

/// The constants that the literals of emitted K `text` name, in order: each `NAME` of
/// ` /* NAME */`.
fn constant_names(text: &str) -> Vec<&str> {
    text.match_indices(" /* ")
        .map(|(at, _)| {
            let rest = &text[at + " /* ".len()..];
            &rest[..rest.find(" */").unwrap()]
        })
        .collect()
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
    // The same K, but that a literal which is the whole value of a constant written at its
    // place names the constant: `ALIAS` by the name written, not `IF`'s; `START`'s `65295` is a
    // part of its value and names none.
    let (definition, spec) = emitted_k(target.path(), &named_manifest);
    assert_eq!(
        (
            without_constant_names(&definition),
            without_constant_names(&spec)
        ),
        emitted_k(target.path(), &inline_manifest)
    );
    expect_test::expect![[r#"
        (
            [
                "PC_START",
                "ALIAS",
                "IE",
                "IF",
                "LCDC",
                "PC_START",
                "IF",
                "IE",
            ],
            [
                "IF",
                "PC_START",
                "IF",
            ],
        )
    "#]]
    .assert_debug_eq(&(constant_names(&definition), constant_names(&spec)));
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
    let inline = definition(&inline_manifest);
    assert_eq!(without_constant_names(&named), inline);
    let entry =
        r#"named ( #token("$main","Id") , #token("b\"ab\"","Bytes") , #token("word","Word") )"#;
    assert_eq!(inline.matches(entry).count(), 2, "{inline}");
    // Each token `entry` writes is a constant's whole value; `exit`'s are parts of `ENTRY`'s.
    let named_entry = r#"named ( #token("$main","Id") /* MAIN */ , #token("b\"ab\"","Bytes") /* MAGIC */ , #token("word","Word") /* WORD */ )"#;
    assert_eq!(named.matches(named_entry).count(), 1, "{named}");
    assert_eq!(named.matches(entry).count(), 1, "{named}");
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
        emitted.contains("<k> ask ( 42 /* ANSWER */ ) => 42 /* ANSWER */ ... </k>"),
        "{emitted}"
    );
}

/// A stop named by the crate name of a dependency none of whose items writes a rule or an
/// equation, here one that declares only a sort and its constructors, is refused saying so: the
/// package is the definition's, as its packages say, though the rule catalog holds nothing of
/// it. A name no package has, such as the root manifest's rename of the dependency, is still
/// one the definition records no package by.
#[test]
fn a_stop_in_a_dependency_that_writes_no_rule_says_so() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    write_package(
        temporary.path(),
        "base",
        r#"
use k::{KItem, KItemSort, Term};

#[k::sort(alias = Common, parents = [KItem])]
pub trait CommonSort: KItemSort {}
pub type Common = Term<dyn CommonSort>;

#[k::constructor(sort = Common, syntax = "same")]
pub struct Same;

#[k::constructor(sort = Common, syntax = "unit")]
pub struct Unit;
"#,
        "",
    );
    let root = write_package(
        temporary.path(),
        "root",
        r"
use k::builtin::KSequence;

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::k![semantic_base::Unit] }
    }
}

k::rules! {
    for semantic_base::Common;
    cross: semantic_base::Unit => semantic_base::Same;
}
",
        "semantic_base = { package = \"base\", path = \"../base\" }\n",
    );
    fs::write(
        temporary.path().join("Cargo.toml"),
        "[workspace]\nmembers = [\"base\", \"root\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    let stop = |name: &str| {
        krs(
            target.path(),
            &root,
            "root",
            "run",
            &["--dependency", "base:main", "--stop-before", name],
        )
    };
    let (success, _, stderr) = stop("base::cross");
    assert!(!success, "{stderr}");
    assert!(
        stderr.contains(
            "no rewrite rule is written by KRS item `base::cross`: no sentence of the definition is the item's, and no item of the package `base` writes a rule or an equation of the definition; did you mean `crate::cross`?"
        ),
        "{stderr}"
    );
    let (success, _, stderr) = stop("semantic_base::cross");
    assert!(!success, "{stderr}");
    assert!(
        stderr.contains("the definition records no package by the name `semantic_base`"),
        "{stderr}"
    );
    let (success, _, stderr) = stop("crate::cross");
    assert!(success, "{stderr}");
}

/// A dependency whose `[lib]` section names its library otherwise than its package name is
/// named by the library's crate name, by which its own and its dependers' Rust source names it:
/// a stop flag and a case's `run` stop at its rule by `sm83_isa::step`, and its package name's
/// spelling `isa_core::step` is refused in both, naming the library's crate name and the item by
/// it.
#[test]
fn a_dependency_is_named_by_its_library_name() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let base = write_package(
        temporary.path(),
        "isa-core",
        r#"
use k::KResult;

k::sorts! {
    Common;
}

#[k::constructors(sort = Common, result = KResult)]
pub enum Word {
    #[k::syntax("unit")]
    Unit(),
    #[k::syntax("same")]
    Same(),
}

k::rules! {
    for Common;
    use Word::*;
    step: Unit() => Same();
}
"#,
        "",
    );
    let manifest = fs::read_to_string(&base).unwrap();
    fs::write(
        &base,
        manifest.replacen(
            "publish = false\n",
            "publish = false\n\n[lib]\nname = \"sm83_isa\"\n",
            1,
        ),
    )
    .unwrap();
    let root = write_package(
        temporary.path(),
        "root",
        r"
use k::builtin::KSequence;

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::k![sm83_isa::Word::Unit()] }
    }
}
",
        "isa-core = { path = \"../isa-core\" }\n",
    );
    fs::write(
        temporary.path().join("Cargo.toml"),
        "[workspace]\nmembers = [\"isa-core\", \"root\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    for (name, stop) in [("library", "sm83_isa::step"), ("package", "isa_core::step")] {
        fs::write(
            temporary.path().join(format!("{name}.json")),
            format!(r#"{{"run": {{"stop_before": ["{stop}"]}}}}"#),
        )
        .unwrap();
    }
    let case = |name: &str| format!("{}/{name}.json", temporary.path().display());
    let run = |extra: &[&str]| {
        krs(
            target.path(),
            &root,
            "root",
            "run",
            &[&["--dependency", "isa-core:main"][..], extra].concat(),
        )
    };
    let stopped = "krs run: stopped after 0 steps, before `sm83_isa::step` (stop 1 of 1)";
    for accepted in [
        run(&["--stop-before", "sm83_isa::step"]),
        run(&["--case", &case("library")]),
    ] {
        let (success, _, stderr) = accepted;
        assert!(success, "{stderr}");
        assert!(stderr.contains(stopped), "{stderr}");
    }
    let hint = "no rewrite rule is written by KRS item `isa_core::step`: no sentence of the definition is the item's, and `isa_core` is the package name of a dependency whose `[lib]` section names its library `sm83_isa`: a dependency's item is named by the crate name of its library, `sm83_isa`; did you mean `sm83_isa::step`?";
    for refused in [
        run(&["--stop-before", "isa_core::step"]),
        run(&["--case", &case("package")]),
    ] {
        let (success, _, stderr) = refused;
        assert!(!success, "{stderr}");
        assert!(stderr.contains(hint), "{stderr}");
    }
}

/// `krs expand` prints a readable clause over a dependency package's sort with each of the
/// dependency's declarations by the crate name the source gives it (here a Cargo rename), and the
/// printed source checks and emits the clause's rewrite.
#[test]
fn a_readable_clause_over_a_dependency_sort_expands_by_its_crate_name() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    write_package(
        temporary.path(),
        "base",
        r#"
use k::{KItem, KItemSort, Term};

#[k::sort(alias = Common, parents = [KItem])]
pub trait CommonSort: KItemSort {}
pub type Common = Term<dyn CommonSort>;

#[k::constructor(sort = Common, syntax = "same")]
pub struct Same;

#[k::constructor(sort = Common, syntax = "unit")]
pub struct Unit;
"#,
        "",
    );
    let root = write_package(
        temporary.path(),
        "root",
        r"
use k::builtin::KSequence;

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::k![semantic_base::Same] }
    }
}

k::rules! {
    for semantic_base::Common;
    cross: semantic_base::Unit => semantic_base::Same;
}
",
        "semantic_base = { package = \"base\", path = \"../base\" }\n",
    );
    fs::write(
        temporary.path().join("Cargo.toml"),
        "[workspace]\nmembers = [\"base\", \"root\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    let dependency = ["--dependency", "base:main"];
    let (success, printed, stderr) = krs(target.path(), &root, "root", "expand", &dependency);
    assert!(success, "{stderr}");
    // Each reference prints by the path the clause writes there.
    for path in ["KCell(semantic_base::Unit,", "KCell(semantic_base::Same,"] {
        assert!(printed.replace(' ', "").contains(path), "{printed}");
    }
    fs::write(root.with_file_name("src").join("lib.rs"), &printed).unwrap();
    let output = root.with_file_name("emitted");
    let mut emit = dependency.to_vec();
    emit.extend(["--output", output.to_str().unwrap()]);
    let (success, _, stderr) = krs(target.path(), &root, "root", "emit-k", &emit);
    assert!(success, "{printed}\n{stderr}");
    let emitted = fs::read_to_string(output.join("definition.k")).unwrap();
    assert!(
        emitted
            .lines()
            .any(|line| line.contains("<k> unit") && line.contains("=> same")),
        "{emitted}"
    );
}

/// A dependency's declarations in a private module (`mod sorts; pub use sorts::{..};`) print by
/// the paths the clause writes to them, through the public re-export: their declaring path
/// `::semantic_base::sorts::Unit` does not compile from another crate (E0603). A path through a
/// name the module's `use` gives the crate (`use semantic_base as sb;`) prints as written, which
/// names the same item where the long form stands. Where the clause writes no path to such an
/// item (a name a glob imports), no printed path is known to compile, and `krs expand` refuses
/// with `dependency-path` rather than print one.
#[test]
fn a_dependency_item_in_a_private_module_expands_by_the_path_the_source_writes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    write_package(
        temporary.path(),
        "base",
        r#"
pub use sorts::{Common, CommonSort, Same, Unit};

mod sorts {
    use k::{KItem, KItemSort, Term};

    #[k::sort(alias = Common, parents = [KItem])]
    pub trait CommonSort: KItemSort {}
    pub type Common = Term<dyn CommonSort>;

    #[k::constructor(sort = Common, syntax = "same")]
    pub struct Same;

    #[k::constructor(sort = Common, syntax = "unit")]
    pub struct Unit;
}
"#,
        "",
    );
    let root_source = |rule: &str| {
        format!(
            r"
use k::builtin::KSequence;

#[k::configuration]
pub struct Machine {{
    #[k::cell]
    pub k: KSequence,
}}

impl Machine {{
    #[k::init]
    pub fn init() -> Self {{
        Self {{ k: k::k![semantic_base::Same] }}
    }}
}}

k::rules! {{
    for semantic_base::Common;
    {rule}
}}
"
        )
    };
    let root = write_package(
        temporary.path(),
        "root",
        &root_source("cross: semantic_base::Unit => semantic_base::Same;"),
        "semantic_base = { package = \"base\", path = \"../base\" }\n",
    );
    fs::write(
        temporary.path().join("Cargo.toml"),
        "[workspace]\nmembers = [\"base\", \"root\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    let dependency = ["--dependency", "base:main"];
    let (success, printed, stderr) = krs(target.path(), &root, "root", "expand", &dependency);
    assert!(success, "{stderr}");
    let collapsed = printed.replace(' ', "");
    for path in ["KCell(semantic_base::Unit,", "KCell(semantic_base::Same,"] {
        assert!(collapsed.contains(path), "{printed}");
    }
    assert!(!collapsed.contains("semantic_base::sorts::"), "{printed}");
    let source = root.with_file_name("src").join("lib.rs");
    fs::write(&source, &printed).unwrap();
    let (success, _, stderr) = krs(target.path(), &root, "root", "check", &dependency);
    assert!(success, "{printed}\n{stderr}");
    // The same rule, where the source names the crate only through a `use` renaming it.
    let renamed = root_source("cross: sb::Unit => sb::Same;")
        .replace("for semantic_base::Common;", "for sb::Common;")
        .replace(
            "use k::builtin::KSequence;",
            "use k::builtin::KSequence;\nuse semantic_base as sb;",
        )
        .replace("k::k![semantic_base::Same]", "k::k![sb::Same]");
    fs::write(&source, &renamed).unwrap();
    let (success, printed, stderr) = krs(target.path(), &root, "root", "expand", &dependency);
    assert!(success, "{stderr}");
    let collapsed = printed.replace(' ', "");
    for path in ["KCell(sb::Unit,", "KCell(sb::Same,"] {
        assert!(collapsed.contains(path), "{printed}");
    }
    fs::write(&source, &printed).unwrap();
    let (success, _, stderr) = krs(target.path(), &root, "root", "check", &dependency);
    assert!(success, "{printed}\n{stderr}");
    // A source that reaches `Same` only through a glob writes no path to it.
    let globbed = root_source("cross: semantic_base::Unit => Same;")
        .replace(
            "use k::builtin::KSequence;",
            "use k::builtin::KSequence;\nuse semantic_base::*;",
        )
        .replace("k::k![semantic_base::Same]", "k::k![Same]");
    fs::write(&source, globbed).unwrap();
    let (success, printed, stderr) = krs(target.path(), &root, "root", "expand", &dependency);
    assert!(!success, "{printed}");
    assert!(
        stderr.contains("krs::reference::dependency-path"),
        "{stderr}"
    );
}

/// A package the root does not depend on directly (`base`, which `mid` depends on and
/// re-exports) has no crate name in the root's source: its declarations print by the path the
/// clause writes to them through `mid`'s re-export (a name of one segment through the `use` of
/// the module that binds it), and the printed source checks. Where the clause writes no path to
/// one (a name a glob imports), `krs expand` refuses with `external-declaration`, saying so.
#[test]
fn a_transitive_dependency_item_expands_by_the_re_export_the_source_writes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    write_package(
        temporary.path(),
        "base",
        r#"
pub use sorts::{Common, CommonSort, Same, Unit};

mod sorts {
    use k::{KItem, KItemSort, Term};

    #[k::sort(alias = Common, parents = [KItem])]
    pub trait CommonSort: KItemSort {}
    pub type Common = Term<dyn CommonSort>;

    #[k::constructor(sort = Common, syntax = "same")]
    pub struct Same;

    #[k::constructor(sort = Common, syntax = "unit")]
    pub struct Unit;
}
"#,
        "",
    );
    write_package(
        temporary.path(),
        "mid",
        "pub use semantic_base::{Common, CommonSort, Same, Unit};\n",
        "semantic_base = { package = \"base\", path = \"../base\" }\n",
    );
    let root_source = |rule: &str| {
        format!(
            r"
use k::builtin::KSequence;
use mid::{{Common, Same}};

#[k::configuration]
pub struct Machine {{
    #[k::cell]
    pub k: KSequence,
}}

impl Machine {{
    #[k::init]
    pub fn init() -> Self {{
        Self {{ k: k::k![Same] }}
    }}
}}

k::rules! {{
    for Common;
    {rule}
}}
"
        )
    };
    let root = write_package(
        temporary.path(),
        "root",
        &root_source("cross: mid::Unit => Same;"),
        "mid = { path = \"../mid\" }\n",
    );
    fs::write(
        temporary.path().join("Cargo.toml"),
        "[workspace]\nmembers = [\"base\", \"mid\", \"root\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    let dependency = ["--dependency", "base:main"];
    let (success, printed, stderr) = krs(target.path(), &root, "root", "expand", &dependency);
    assert!(success, "{stderr}");
    let collapsed = printed.replace(' ', "");
    for path in ["KCell(mid::Unit,", "KCell(mid::Same,"] {
        assert!(collapsed.contains(path), "{printed}");
    }
    let source = root.with_file_name("src").join("lib.rs");
    fs::write(&source, &printed).unwrap();
    let (success, _, stderr) = krs(target.path(), &root, "root", "check", &dependency);
    assert!(success, "{printed}\n{stderr}");
    // `Same` reached only through a glob: the source writes no path to it.
    fs::write(
        &source,
        root_source("cross: mid::Unit => Same;")
            .replace("use mid::{Common, Same};", "use mid::{Common, *};"),
    )
    .unwrap();
    let (success, printed, stderr) = krs(target.path(), &root, "root", "expand", &dependency);
    assert!(!success, "{printed}");
    assert!(
        stderr.contains("krs::reference::external-declaration")
            && stderr.contains("the clause writes no path to it that the long form can print"),
        "{stderr}"
    );
}

/// The `<k>` side of each rule `definition` holds, by line, with a `cells!` rule's tail
/// (`~> Tail:K`) and a readable clause's `...` both left out: the two spell one open `<k>`.
fn k_rules(definition: &str) -> Vec<String> {
    definition
        .lines()
        .filter(|line| line.trim_start().starts_with("<k>") && line.contains("=>"))
        .map(|line| {
            let words = line.split_whitespace().collect::<Vec<_>>();
            let mut kept = Vec::new();
            let mut at = 0;
            while at < words.len() {
                match (words[at], words.get(at + 1)) {
                    ("~>", Some(tail)) if tail.ends_with(":K") => at += 2,
                    ("...", _) => at += 1,
                    (word, _) => {
                        kept.push(word);
                        at += 1;
                    }
                }
            }
            kept.join(" ")
        })
        .collect()
}

/// `krs expand` of `root` (with the `base:main` dependency), then `krs emit-k` of the original
/// and of the printed source in its place: the printed source and the `<k>` rules of each.
fn expand_and_emit(target: &Path, root: &Path) -> (String, Vec<String>, Vec<String>) {
    let dependency = ["--dependency", "base:main"];
    let emitted = |name: &str| {
        let output = root.with_file_name(name);
        let mut emit = dependency.to_vec();
        emit.extend(["--output", output.to_str().unwrap()]);
        let (success, _, stderr) = krs(target, root, "root", "emit-k", &emit);
        assert!(success, "{stderr}");
        k_rules(&fs::read_to_string(output.join("definition.k")).unwrap())
    };
    let before = emitted("emitted-authored");
    let (success, printed, stderr) = krs(target, root, "root", "expand", &dependency);
    assert!(success, "{stderr}");
    let source = root.with_file_name("src").join("lib.rs");
    let authored = fs::read_to_string(&source).unwrap();
    fs::write(&source, &printed).unwrap();
    let after = emitted("emitted-printed");
    fs::write(&source, authored).unwrap();
    (printed, before, after)
}

/// `base`, whose `alt` module re-exports `Same` under the name `Unit`, with `Common`, `Same`,
/// `Unit` and the constructors enum `Syntax` (`A`, `B`) re-exported at its root.
const RENAMING_BASE: &str = r#"
pub use m::Syntax;
pub use sorts::{Common, CommonSort, Same, Unit};

mod sorts {
    use k::{KItem, KItemSort, Term};

    #[k::sort(alias = Common, parents = [KItem])]
    pub trait CommonSort: KItemSort {}
    pub type Common = Term<dyn CommonSort>;

    #[k::constructor(sort = Common, syntax = "same")]
    pub struct Same;

    #[k::constructor(sort = Common, syntax = "unit")]
    pub struct Unit;
}

/// `Same`, re-exported under the name `Unit`.
pub mod alt {
    pub use crate::sorts::Same as Unit;
}

pub mod m {
    #[k::constructors(sort = crate::Common, result = k::KResult)]
    pub enum Syntax {
        #[k::syntax("one")]
        A,
        #[k::syntax("two")]
        B,
    }
}
"#;

/// A root over `dependency` (`semantic_base` or `mid`), whose rule `cross` is `rule`. It writes
/// an unused `use` of `alt::Unit` (base's `Same`) and a module `p` re-exporting all of
/// `dependency`, so `p::Unit` is base's `Unit`.
fn renaming_root(dependency: &str, rule: &str) -> String {
    format!(
        r"
use k::builtin::KSequence;
use {dependency}::{{Common, Same}};
#[allow(unused_imports)]
use {dependency}::alt::Unit as AltUnit;

mod p {{
    pub use {dependency}::*;
}}

#[k::configuration]
pub struct Machine {{
    #[k::cell]
    pub k: KSequence,
}}

impl Machine {{
    #[k::init]
    pub fn init() -> Self {{
        Self {{ k: k::k![Same] }}
    }}
}}

k::rules! {{
    for Common;
    cross: {rule};
}}
"
    )
}

/// A path's last segment is the name a module exports, which a renaming re-export gives another
/// item: `alt::Unit` is base's `Same`, while `p::Unit` is base's `Unit`. `krs expand` prints each
/// reference by the path the clause writes there, which names the same item where the long form
/// stands, so the printed source emits the K the clause does (`same => unit`), whether the
/// source depends on base directly or only on `mid`, which re-exports it. A path chosen by its
/// last segment from elsewhere in the file (`alt::Unit`, the one path ending in `Unit` from a
/// crate name) would print `same => same`.
#[test]
fn a_dependency_item_expands_by_the_path_the_clause_writes_at_that_reference() {
    let target = shared_fixture_target();
    for direct in [true, false] {
        let temporary = temp_dir();
        write_package(temporary.path(), "base", RENAMING_BASE, "");
        let dependency = if direct {
            "semantic_base"
        } else {
            write_package(
                temporary.path(),
                "mid",
                "pub use semantic_base::{Common, CommonSort, Same, Syntax, Unit};\npub use semantic_base::alt;\n",
                "semantic_base = { package = \"base\", path = \"../base\" }\n",
            );
            "mid"
        };
        let root = write_package(
            temporary.path(),
            "root",
            &renaming_root(dependency, &format!("{dependency}::Same => p::Unit")),
            &if direct {
                "semantic_base = { package = \"base\", path = \"../base\" }\n".to_owned()
            } else {
                "mid = { path = \"../mid\" }\n".to_owned()
            },
        );
        let members = if direct {
            "\"base\", \"root\""
        } else {
            "\"base\", \"mid\", \"root\""
        };
        fs::write(
            temporary.path().join("Cargo.toml"),
            format!("[workspace]\nmembers = [{members}]\nresolver = \"3\"\n"),
        )
        .unwrap();
        let (printed, before, after) = expand_and_emit(target.path(), &root);
        let collapsed = printed.replace(' ', "");
        assert!(
            collapsed.contains(&format!("KCell({dependency}::Same,"))
                && collapsed.contains("KCell(p::Unit,"),
            "{printed}"
        );
        assert_eq!(before, ["<k> same => unit </k>"], "{dependency}");
        assert_eq!(after, before, "{dependency}: {printed}");
    }
}

/// A constructors enum's variant of a package the root reaches only through `mid` prints by the
/// path the clause writes to it (`mid::Syntax::A`), and the printed source emits the same K.
#[test]
fn a_transitive_dependency_variant_expands_by_the_path_the_clause_writes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    write_package(temporary.path(), "base", RENAMING_BASE, "");
    write_package(
        temporary.path(),
        "mid",
        "pub use semantic_base::{Common, CommonSort, Same, Syntax, Unit};\npub use semantic_base::alt;\n",
        "semantic_base = { package = \"base\", path = \"../base\" }\n",
    );
    let root = write_package(
        temporary.path(),
        "root",
        &renaming_root("mid", "mid::Syntax::A => mid::Syntax::B"),
        "mid = { path = \"../mid\" }\n",
    );
    fs::write(
        temporary.path().join("Cargo.toml"),
        "[workspace]\nmembers = [\"base\", \"mid\", \"root\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    let (printed, before, after) = expand_and_emit(target.path(), &root);
    let collapsed = printed.replace(' ', "");
    assert!(
        collapsed.contains("KCell(mid::Syntax::A,") && collapsed.contains("KCell(mid::Syntax::B,"),
        "{printed}"
    );
    assert_eq!(before, ["<k> one => two </k>"]);
    assert_eq!(after, before, "{printed}");
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
            "overlapping",
            "#[k::constant]\npub const BAD: k::builtin::Set = k::builtin::set::concat(k::builtin::set::item(1), k::builtin::set::item(1));\n",
        ),
        (
            "map",
            "#[k::constant]\npub const BAD: k::builtin::Map = map![1 -> 2];\n",
        ),
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
                "overlapping",
                [
                    "error[krs::analysis::invalid-constant]: the value of constant `BAD` concatenates sets whose elements are not provably different values, and a concatenation is a set only where its parts are disjoint; a constant names a ground constructor term, a value every use can match",
                    "--> src/lib.rs:42:34",
                ],
            ),
            (
                "map",
                [
                    "error[krs::analysis::invalid-constant]: the value of constant `BAD` applies the map update `k::builtin::map::update(..)`, which a map literal with entries (`map![k -> v]`) denotes; a constant names a ground constructor term, which every use can match, and a function application is evaluated, not matched",
                    "--> src/lib.rs:42:34",
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
