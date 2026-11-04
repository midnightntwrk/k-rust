//! A `#[k::cell]` group declared in one crate and nested in another crate's
//! `#[k::configuration]`: what the containing definition's rules can do with
//! the group's cells, and what a rule written for the group itself gives.
//!
//! The library `lib` declares the group `Core { k, pc, acc }` and the
//! program syntax; the package `small` declares `Small { core: lib::Core,
//! mem }`, composes `lib`'s facet, and writes its initializer and its rules.
//! A cell of a nested group keeps its own name at any depth: the readable rules
//! for `Small` name `k`, `pc` and `acc` flat, a `cells!` rule names them
//! through the group's struct, and the emitted configuration nests them under
//! `<core>`.
//!
//! A rule typed by the group (`for lib::Core`, or `for Core` in the library)
//! is refused today: a rule's subject is a configuration, and a group is not
//! one. The refusal is pinned here as it stands.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// The group and the program syntax. `rules` is appended, so a case can give
/// the library rules of its own.
const LIB: &str = r#"
use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Instr;
    Prog;
}

#[k::constructors(sort = Instr, result = KResult)]
pub enum Op {
    #[k::syntax("inc")]
    Inc(),
    #[k::syntax("store ( {addr} )")]
    Store { addr: Int },
    #[k::syntax("load ( {addr} )")]
    Load { addr: Int },
}

#[k::constructors(sort = Prog, result = KResult)]
#[k::precedence((Done, Then))]
pub enum Code {
    #[k::syntax("done")]
    Done(),
    #[k::syntax("{head} ; {tail}")]
    Then { head: Instr, tail: Prog },
}

/// A reusable core: its own computation cell, a program counter and an
/// accumulator.
#[k::cell]
pub struct Core {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub acc: Int,
}
"#;

/// The containing configuration and its initializer. The initializer writes
/// the group as a record of the dependency's struct.
const SMALL: &str = r"
use k::builtin::{Int, Map, map};

#[k::configuration]
pub struct Small {
    #[k::cell(nested)]
    pub core: lib::Core,
    #[k::cell]
    pub mem: Map<Int, Int>,
}

impl Small {
    #[k::init]
    pub fn init(pgm: lib::Prog) -> Self {
        Self {
            core: lib::Core { k: k::k![pgm], pc: 0, acc: 0 },
            mem: map::empty(),
        }
    }
}
";

/// Rules for `Small` that name the group's cells: readable rules, which name
/// them flat, and a `cells!` rule, which names them as `lib::Core::<cell>`
/// beside `mem`, reads `mem` and writes `acc`.
const SMALL_RULES: &str = r#"
k::rules! {
    for Small;
    use lib::Code::*;
    use lib::Op::*;

    next: { k: [Then { head, tail }, ..] } => { k: [head, tail, ..] };
    end: { k: [Done(), ..] } => { k: [..] };
    inc: { k: [Inc(), ..], pc, acc } => { k: [..], pc: k::builtin::int::add(pc, 1), acc: k::builtin::int::add(acc, 1) };
    store: { k: [Store { addr }, ..], acc, mem } => { k: [..], acc, mem: map::update(mem, addr, acc) };
}

#[k::rule(label = "load")]
pub fn load(
    addr: Int,
    value: Int,
    k::cells! {
        lib::Core::k: k::configuration::KCell(lib::Op::Load { addr }, tail @ ..),
        lib::Core::acc: k::configuration::Cell(_),
        mem: k::configuration::Cell(k::map![addr -> value, ..]),
        state @ ..
    }: Small,
) -> Small {
    k::cells! {
        lib::Core::k: k::configuration::KCell(..tail),
        lib::Core::acc: k::configuration::Cell(value),
        ..state
    }
}
"#;

/// A `cells!` rule for `Small` that names the group's cell `acc` flat, where
/// the group's struct must qualify it.
const SMALL_FLAT_CELLS_RULE: &str = r#"
#[k::rule(label = "load")]
pub fn load(
    addr: Int,
    value: Int,
    k::cells! {
        lib::Core::k: k::configuration::KCell(lib::Op::Load { addr }, tail @ ..),
        acc: k::configuration::Cell(_),
        mem: k::configuration::Cell(k::map![addr -> value, ..]),
        state @ ..
    }: Small,
) -> Small {
    k::cells! {
        lib::Core::k: k::configuration::KCell(..tail),
        acc: k::configuration::Cell(value),
        ..state
    }
}
"#;

/// A readable rule typed by the group, as `small` writes it.
const SMALL_GROUP_RULE: &str = r"
k::rules! {
    for lib::Core;
    use lib::Op::*;

    inc: { k: [Inc(), ..], pc, acc } => { k: [..], pc: k::builtin::int::add(pc, 1), acc: k::builtin::int::add(acc, 1) };
}
";

/// A `cells!` rule typed by the group, as `small` writes it.
const SMALL_GROUP_CELLS_RULE: &str = r#"
#[k::rule(label = "inc")]
pub fn inc(
    pc: Int,
    k::cells! {
        k: k::configuration::KCell(lib::Op::Inc(), tail @ ..),
        pc: k::configuration::Cell(pc),
        state @ ..
    }: lib::Core,
) -> lib::Core {
    k::cells! {
        k: k::configuration::KCell(..tail),
        pc: k::configuration::Cell(k::builtin::int::add(pc, 1)),
        ..state
    }
}
"#;

/// The same readable rule as the library writes it, for its own group.
const LIB_GROUP_RULE: &str = r"
k::rules! {
    for Core;
    use Op::*;

    inc: { k: [Inc(), ..], pc, acc } => { k: [..], pc: k::builtin::int::add(pc, 1), acc: k::builtin::int::add(acc, 1) };
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

fn write_package(root: &Path, name: &str, source: &str, dependencies: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-GROUPS-{}\"\n\n[package.metadata.krs.definitions.main]\n",
            krs_path(),
            name.to_ascii_uppercase()
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// A workspace of `lib` (the group, plus `lib_rules`) and `small` (the
/// configuration, plus `small_rules`); the manifest of `small`.
fn workspace(root: &Path, lib_rules: &str, small_rules: &str) -> PathBuf {
    write_package(root, "lib", &format!("{LIB}{lib_rules}"), "");
    let small = write_package(
        root,
        "small",
        &format!("{SMALL}{small_rules}"),
        "lib = { path = \"../lib\" }\n",
    );
    fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"lib\", \"small\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    small
}

/// Runs `krs <command>` on `small`'s `main` definition, composed with `lib`'s.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", "small", "--definition", "main"])
        .args(["--dependency", "lib:main"])
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

/// The `error[..]` headlines of a failed `krs check` and the locations they
/// point at. A location is shown as its file, relative to the workspace, and
/// the source text that starts there, not as a line and column: the shared
/// sources above are prefixes of every generated file, so an edit to them
/// would move every line number without changing what a diagnostic points at.
fn check_errors(target: &Path, manifest: &Path) -> Vec<String> {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    let root = manifest.parent().unwrap().parent().unwrap();
    let workspace = format!("{}/", root.display());
    stderr
        .lines()
        .filter(|line| line.starts_with("error") || line.trim_start().starts_with("--> "))
        .map(|line| match line.trim().strip_prefix("--> ") {
            Some(location) => location_text(root, &location.replace(&workspace, "")),
            None => line.to_owned(),
        })
        .collect()
}

/// `<file>:<line>:<column>`, relative to `root`, as the file and the first
/// characters of its source from that position.
fn location_text(root: &Path, location: &str) -> String {
    let mut parts = location.rsplitn(3, ':');
    let column: usize = parts.next().unwrap().parse().unwrap();
    let line: usize = parts.next().unwrap().parse().unwrap();
    let file = parts.next().unwrap();
    let source = fs::read_to_string(root.join(file)).unwrap();
    let text = source.lines().nth(line - 1).unwrap();
    let excerpt = text.chars().skip(column - 1).take(16).collect::<String>();
    format!("--> {file}: `{}`", excerpt.trim_end())
}

/// The content of the first `<name>` cell in whitespace-flattened text.
fn cell(flat: &str, name: &str) -> String {
    let open = format!("<{name}> ");
    let start = flat
        .find(&open)
        .unwrap_or_else(|| panic!("no `<{name}>` in:\n{flat}"))
        + open.len();
    let end = start + flat[start..].find(&format!(" </{name}>")).unwrap();
    flat[start..end].to_owned()
}

/// The containing definition checks, emits `<core>` around the group's cells
/// inside the configuration, and runs. The readable rules name the group's
/// cells flat; the `cells!` rule names them through the group's struct
/// (`lib::Core::acc`), as for any group. Both emit the cells unnested, which K
/// completes to their one position.
#[test]
fn a_dependency_group_nests_in_a_configuration_whose_rules_name_its_cells() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let small = workspace(temporary.path(), "", SMALL_RULES);

    let (success, _, stderr) = krs(target.path(), &small, "check", &[]);
    assert!(success, "{stderr}");

    let output = small.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &small,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    let flat = definition.split_whitespace().collect::<Vec<_>>().join(" ");
    for sentence in [
        "configuration <core> <k> $PGM:Prog </k> <pc> 0 </pc> <acc> 0 </acc> </core> <mem> .Map </mem>",
        "rule [inc]: <k> inc => .K ... </k> <pc> Pc:Int => Pc:Int +Int 1 </pc> <acc> Acc:Int => Acc:Int +Int 1 </acc>",
        "rule [load]: <k> load ( Addr:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> _ => Value:Int </acc> <mem> Addr:Int |-> Value:Int ... </mem>",
    ] {
        assert!(flat.contains(sentence), "no `{sentence}` in:\n{definition}");
    }

    let program = small.with_file_name("program.txt");
    fs::write(
        &program,
        "inc ; inc ; store ( 7 ) ; inc ; load ( 7 ) ; done",
    )
    .unwrap();
    let (success, stdout, stderr) = krs(target.path(), &small, "run", &[program.to_str().unwrap()]);
    assert!(success, "{stdout}\n{stderr}");
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    let core = cell(&flat, "core");
    assert_eq!(
        [cell(&core, "k"), cell(&core, "pc"), cell(&core, "acc")],
        [".K", "3", "2"].map(str::to_owned),
        "{flat}"
    );
    assert_eq!(cell(&flat, "mem"), "7 |-> 2", "{flat}");
}

/// A `cells!` rule must name a group's cell through the group's struct: `acc`
/// flat is refused, because `Small` itself declares no cell of that name.
#[test]
fn a_cells_rule_that_names_a_group_cell_flat_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let small = workspace(temporary.path(), "", SMALL_FLAT_CELLS_RULE);
    let errors = check_errors(target.path(), &small);
    expect_test::expect![[r#"
        [
            "error[krs::expand::undeclared-cell]: `Small` declares no cell of this name",
            "--> small/src/lib.rs: `acc: k::configur`",
        ]
    "#]]
    .assert_debug_eq(&errors);
}

/// A rule typed by the group is refused today, whether the containing
/// package writes it (`for lib::Core`, or a `cells!` rule typed `lib::Core`)
/// or the library writes it for its own group (`for Core`): the collector
/// resolves the path to a cell group where a configuration is required. A
/// readable block's refusal points at its rule, a `cells!` rule's at its
/// parameter type.
#[test]
fn a_rule_typed_by_the_group_is_refused_today() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let outer = workspace(&temporary.path().join("outer"), "", SMALL_GROUP_RULE);
    let cells = workspace(&temporary.path().join("cells"), "", SMALL_GROUP_CELLS_RULE);
    let inner = workspace(&temporary.path().join("inner"), LIB_GROUP_RULE, "");
    let outcomes = [
        check_errors(target.path(), &outer),
        check_errors(target.path(), &cells),
        check_errors(target.path(), &inner),
    ];
    expect_test::expect![[r#"
        [
            [
                "error[krs::collect::reference-kind-mismatch]: Rust path `lib :: Core` resolves to `ORG-KRS-GROUPS-LIB::Core (cell)`, but a configuration is required",
                "--> small/src/lib.rs: `inc: { k: [Inc()`",
            ],
            [
                "error[krs::collect::reference-kind-mismatch]: Rust path `lib :: Core` resolves to `ORG-KRS-GROUPS-LIB::Core (cell)`, but a configuration is required",
                "--> small/src/lib.rs: `lib::Core,`",
            ],
            [
                "error[krs::collect::reference-kind-mismatch]: Rust path `Core` resolves to `ORG-KRS-GROUPS-LIB::Core (cell)`, but a configuration is required",
                "--> lib/src/lib.rs: `inc: { k: [Inc()`",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}
