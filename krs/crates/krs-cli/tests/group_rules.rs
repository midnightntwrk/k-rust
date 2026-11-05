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
//! is about the group's cells at the group's one position in the containing
//! definition's configuration: it names only those cells, and every other cell
//! is framed. The library's rules for its group therefore apply in every
//! definition whose configuration holds the group, here `small` and `big`
//! (`Big { core: lib::Core, timer, mem }`). A group below an optional or a
//! collection cell, a group the configuration does not hold, a cell outside
//! the group, and a claim typed by a group are refused, each with its own
//! code; a configuration that holds the group twice is refused as it is for
//! any rule.

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

/// The library's rules for its group: the whole of `Core`'s meaning.
const LIB_CORE_RULES: &str = r"
k::rules! {
    for Core;
    use Code::*;
    use Op::*;

    next: { k: [Then { head, tail }, ..] } => { k: [head, tail, ..] };
    end: { k: [Done(), ..] } => { k: [..] };
    inc: { k: [Inc(), ..], pc, acc } => { k: [..], pc: k::builtin::int::add(pc, 1), acc: k::builtin::int::add(acc, 1) };
}
";

/// `small`'s own rules beside the library's: the memory operations, which
/// need `mem`, so they are rules for `Small`.
const SMALL_MEMORY_RULES: &str = r#"
k::rules! {
    for Small;
    use lib::Op::*;

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

/// A second machine holding `Core`, beside a timer and a memory.
const BIG: &str = r"
use k::builtin::{Int, Map, map};

#[k::configuration]
pub struct Big {
    #[k::cell(nested)]
    pub core: lib::Core,
    #[k::cell]
    pub timer: Int,
    #[k::cell]
    pub mem: Map<Int, Int>,
}

impl Big {
    #[k::init]
    pub fn init(pgm: lib::Prog) -> Self {
        Self {
            core: lib::Core { k: k::k![pgm], pc: 0, acc: 0 },
            timer: 0,
            mem: map::empty(),
        }
    }
}
";

/// `big`'s own rules beside the library's: the memory operations, which also
/// advance the timer, in the same step.
const BIG_RULES: &str = r"
k::rules! {
    for Big;
    use lib::Op::*;

    store: { k: [Store { addr }, ..], acc, timer, mem } => { k: [..], acc, timer: k::builtin::int::add(timer, 1), mem: map::update(mem, addr, acc) };
    load: { k: [Load { addr }, ..], acc: _, timer, mem: { addr -> value, .. } } => { k: [..], acc: value, timer: k::builtin::int::add(timer, 1) };
}
";

/// A rule for the group that names `mem`, a cell of `Small` outside the
/// group.
const SMALL_GROUP_RULE_OUTSIDE: &str = r"
k::rules! {
    for lib::Core;
    use lib::Op::*;

    store: { k: [Store { addr }, ..], acc, mem } => { k: [..], acc, mem: map::update(mem, addr, acc) };
}
";

/// A rule for a group that no cell of `Small` holds.
const SMALL_SPARE_GROUP_RULE: &str = r"
#[k::cell]
pub struct Spare {
    #[k::cell]
    pub ticks: Int,
}

k::rules! {
    for Spare;

    tick: { ticks } => { ticks: k::builtin::int::add(ticks, 1) };
}
";

/// A readable claim typed by the group.
const SMALL_GROUP_READABLE_CLAIM: &str = r"
k::claims! {
    for lib::Core;
    use lib::Op::*;

    #[k::claim(all_paths)]
    inc_once: { k: [Inc()], pc } => { k: [], pc: k::builtin::int::add(pc, 1) };
}
";

/// A `cells!` claim typed by the group.
const SMALL_GROUP_CELLS_CLAIM: &str = r#"
#[k::claim(all_paths, label = "inc-once")]
fn inc_once(
    pc: Int,
    k::cells! {
        k: k::configuration::KCell(lib::Op::Inc()),
        pc: k::configuration::Cell(pc),
        state @ ..
    }: lib::Core,
) -> lib::Core {
    k::cells! {
        k: k::configuration::KCell(.K),
        pc: k::configuration::Cell(k::builtin::int::add(pc, 1)),
        ..state
    }
}
"#;

/// A readable rule for the group that names `core`, the cell of `Small` that
/// holds the group.
const SMALL_GROUP_RULE_HOLDER: &str = r"
k::rules! {
    for lib::Core;
    use lib::Op::*;

    inc: { k: [Inc(), ..], core } => { k: [..], core };
}
";

/// A `cells!` rule typed by the group that names, by its owner, the cell
/// `cell` of sort `sort`, and writes it back unchanged.
fn group_cells_rule_naming(cell: &str, sort: &str) -> String {
    format!(
        r#"
#[k::rule(label = "inc")]
pub fn inc(
    value: {sort},
    k::cells! {{
        k: k::configuration::KCell(lib::Op::Inc(), tail @ ..),
        {cell}: k::configuration::Cell(value),
        state @ ..
    }}: lib::Core,
) -> lib::Core {{
    k::cells! {{
        k: k::configuration::KCell(..tail),
        {cell}: k::configuration::Cell(value),
        ..state
    }}
}}
"#
    )
}

/// A group of `small`'s own, which `Small` holds beside `lib::Core` in the
/// cases that use it, or does not hold.
const OTHER: &str = "#[k::cell]\npub struct Other {\n    #[k::cell]\n    pub x: Int,\n}";

/// A containing configuration whose `held` field is `held_field`, initialized
/// as `held_value`, and whose package declares `declarations` and `rules`: a
/// group at a position with no one fixed place.
fn small_holding(declarations: &str, held_field: &str, held_value: &str, rules: &str) -> String {
    format!(
        r"
use k::builtin::{{Int, Map, map}};

{declarations}

#[k::configuration]
pub struct Small {{
    #[k::cell(nested)]
    pub core: lib::Core,
    {held_field}
    #[k::cell]
    pub mem: Map<Int, Int>,
}}

impl Small {{
    #[k::init]
    pub fn init(pgm: lib::Prog) -> Self {{
        Self {{
            core: lib::Core {{ k: k::k![pgm], pc: 0, acc: 0 }},
            held: {held_value},
            mem: map::empty(),
        }}
    }}
}}

{rules}
"
    )
}

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
    definitions(
        root,
        lib_rules,
        &[("small", &format!("{SMALL}{small_rules}"))],
    )
    .remove(0)
}

/// A workspace of `lib` (the group, plus `lib_rules`) and one package per
/// definition, each given as its name and its source, which depends on `lib`;
/// the definitions' manifests, in order.
fn definitions(root: &Path, lib_rules: &str, packages: &[(&str, &str)]) -> Vec<PathBuf> {
    write_package(root, "lib", &format!("{LIB}{lib_rules}"), "");
    let manifests = packages
        .iter()
        .map(|(name, source)| write_package(root, name, source, "lib = { path = \"../lib\" }\n"))
        .collect();
    let members = std::iter::once("lib")
        .chain(packages.iter().map(|(name, _)| *name))
        .map(|name| format!("\"{name}\""))
        .collect::<Vec<_>>()
        .join(", ");
    fs::write(
        root.join("Cargo.toml"),
        format!("[workspace]\nmembers = [{members}]\nresolver = \"3\"\n"),
    )
    .unwrap();
    manifests
}

/// Runs `krs <command>` on `small`'s `main` definition, composed with `lib`'s.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    krs_on(target, manifest, "small", command, extra)
}

/// Runs `krs <command>` on `package`'s `main` definition, composed with
/// `lib`'s unless `package` is `lib`.
fn krs_on(
    target: &Path,
    manifest: &Path,
    package: &str,
    command: &str,
    extra: &[&str],
) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main"]);
    if package != "lib" {
        process.args(["--dependency", "lib:main"]);
    }
    let output = process
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
    check_report(target, manifest, "small")
        .into_iter()
        .filter(|line| !line.starts_with("= help: "))
        .collect()
}

/// [`check_errors`] of `package`'s definition, with each diagnostic's help.
fn check_report(target: &Path, manifest: &Path, package: &str) -> Vec<String> {
    let (success, _, stderr) = krs_on(target, manifest, package, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    let root = manifest.parent().unwrap().parent().unwrap();
    let workspace = format!("{}/", root.display());
    stderr
        .lines()
        .filter(|line| {
            line.starts_with("error")
                || line.trim_start().starts_with("--> ")
                || line.trim_start().starts_with("= help: ")
        })
        .map(|line| match line.trim().strip_prefix("--> ") {
            Some(location) => location_text(root, &location.replace(&workspace, "")),
            None => line.trim().to_owned(),
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

    let output = small.parent().unwrap().parent().unwrap().join("emitted");
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

/// The whitespace-flattened `definition.k` that `krs emit-k` gives for
/// `package`'s definition, written beside the workspace's packages, never
/// inside one.
fn emitted(target: &Path, manifest: &Path, package: &str) -> String {
    let output = manifest
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join(format!("emitted-{package}"));
    let (success, _, stderr) = krs_on(
        target,
        manifest,
        package,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    definition.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The sentence of `flat` that starts with `start`, up to the next sentence.
fn sentence<'a>(flat: &'a str, start: &str) -> &'a str {
    let begin = flat
        .find(start)
        .unwrap_or_else(|| panic!("no `{start}` in:\n{flat}"));
    let rest = &flat[begin..];
    let end = [" rule ", " syntax ", " endmodule", " claim "]
        .iter()
        .filter_map(|next| rest[1..].find(next).map(|at| at + 1))
        .min()
        .unwrap_or(rest.len());
    &rest[..end]
}

/// A rule typed by the group resolves against the containing definition's
/// one configuration, whether the containing package writes it (`for
/// lib::Core`, or a `cells!` rule typed `lib::Core`) or the library writes it
/// for its own group (`for Core`). It names the group's cells only, and is
/// lowered as the same rule written for `Small`: the cells it leaves out are
/// framed wherever the group sits.
#[test]
fn a_rule_typed_by_the_group_resolves_against_the_containing_configuration() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let outer = workspace(&temporary.path().join("outer"), "", SMALL_GROUP_RULE);
    let cells = workspace(&temporary.path().join("cells"), "", SMALL_GROUP_CELLS_RULE);
    let inner = workspace(&temporary.path().join("inner"), LIB_GROUP_RULE, "");
    let readable = "rule [inc]: <k> inc => .K ... </k> <pc> Pc:Int => Pc:Int +Int 1 </pc> <acc> Acc:Int => Acc:Int +Int 1 </acc>";
    for manifest in [&outer, &inner] {
        let (success, _, stderr) = krs(target.path(), manifest, "check", &[]);
        assert!(success, "{stderr}");
        let flat = emitted(target.path(), manifest, "small");
        assert_eq!(sentence(&flat, "rule [inc]:"), readable, "{flat}");
    }
    let (success, _, stderr) = krs(target.path(), &cells, "check", &[]);
    assert!(success, "{stderr}");
    let flat = emitted(target.path(), &cells, "small");
    expect_test::expect![
        "rule [inc]: <k> inc ~> Tail:K => .K ~> Tail:K </k> <pc> Pc:Int => Pc:Int +Int 1 </pc>"
    ]
    .assert_eq(sentence(&flat, "rule [inc]:"));
}

/// The library's rules for its group are rules of every definition whose
/// configuration holds the group: the same program runs through them in
/// `small` and in `big`, the group's cells end alike, and each definition's
/// own rules give its other cells (`big`'s timer counts the memory steps).
/// Each definition emits the library's rules with the same text.
#[test]
fn the_library_rules_for_its_group_apply_in_every_containing_definition() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifests = definitions(
        temporary.path(),
        LIB_CORE_RULES,
        &[
            ("small", &format!("{SMALL}{SMALL_MEMORY_RULES}")),
            ("big", &format!("{BIG}{BIG_RULES}")),
        ],
    );
    let small = &manifests[0];
    let program = temporary.path().join("program.txt");
    fs::write(
        &program,
        "inc ; inc ; store ( 7 ) ; inc ; load ( 7 ) ; done",
    )
    .unwrap();
    let mut library = Vec::new();
    for package in ["small", "big"] {
        let (success, stdout, stderr) = krs_on(
            target.path(),
            small,
            package,
            "run",
            &[program.to_str().unwrap()],
        );
        assert!(success, "{package}: {stdout}\n{stderr}");
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        let core = cell(&flat, "core");
        assert_eq!(
            [cell(&core, "k"), cell(&core, "pc"), cell(&core, "acc")],
            [".K", "3", "2"].map(str::to_owned),
            "{package}: {flat}"
        );
        assert_eq!(cell(&flat, "mem"), "7 |-> 2", "{package}: {flat}");
        if package == "big" {
            assert_eq!(cell(&flat, "timer"), "2", "{flat}");
        }
        let emitted = emitted(target.path(), small, package);
        library.push(
            ["rule [next]:", "rule [end]:", "rule [inc]:"]
                .map(|start| sentence(&emitted, start).to_owned()),
        );
    }
    assert_eq!(library[0], library[1]);
}

/// The refusals of a sentence typed by a group, each at the `for` header or
/// the parameter type that names the group, or at the cell it names:
/// - a cell outside the group is `cell-outside-subject`, whether a readable
///   rule names it flat (`mem`, or `core`, which holds the group) or a
///   `cells!` entry names it by its owner (`Small::mem`, `Other::x` of a group
///   `Small` holds beside `Core`, or of one it does not hold);
/// - a group no cell of the configuration holds is
///   `group-not-in-configuration`;
/// - a group held by an optional or a collection cell has no one fixed
///   position, `group-subject-position`;
/// - a configuration that holds the group twice is refused as it is for any
///   rule, `ambiguous-cell-sort`: the fault is the configuration's;
/// - a claim, readable or `cells!`, is typed by the configuration,
///   `group-claim`.
#[test]
fn a_sentence_typed_by_a_group_is_refused_where_it_leaves_the_group() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let outcomes = refused_workspaces(temporary.path())
        .iter()
        .map(|manifest| check_errors(target.path(), manifest))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            [
                "error[krs::analysis::cell-outside-subject]: `Core` has no cell `mem`: a sentence about the cell group `Core` names only the cells inside the group, and `mem` is another cell of configuration `Small`; write the sentence for `Small` to name it",
                "--> small/src/lib.rs: `mem } => { k: [.`",
            ],
            [
                "error[krs::analysis::cell-outside-subject]: `Core` has no cell `core`: a sentence about the cell group `Core` names only the cells inside the group, and `core` is the cell of configuration `Small` that holds the group; write the sentence for `Small` to name it",
                "--> small/src/lib.rs: `core } => { k: [`",
            ],
            [
                "error[krs::analysis::cell-outside-subject]: `Core` has no cell `Small::mem`: a sentence about the cell group `Core` names only the cells inside the group, and `Small::mem` is another cell of configuration `Small`; write the sentence for `Small` to name it",
                "--> small/src/lib.rs: `mem: k::configur`",
            ],
            [
                "error[krs::analysis::cell-outside-subject]: `Core` has no cell `Other::x`: a sentence about the cell group `Core` names only the cells inside the group, and `Other::x` is another cell of configuration `Small`; write the sentence for `Small` to name it",
                "--> small/src/lib.rs: `x: k::configurat`",
            ],
            [
                "error[krs::analysis::cell-outside-subject]: `Core` has no cell `Other::x`: a sentence about the cell group `Core` names only the cells inside the group, and `Other::x` is a cell of the group `Other`, which configuration `Small` does not hold",
                "--> small/src/lib.rs: `x: k::configurat`",
            ],
            [
                "error[krs::analysis::group-not-in-configuration]: no cell of configuration `Small` holds the cell group `Spare`, so a rule for `Spare` has no cells to apply to: a group's rules apply at the group's position in the definition's configuration",
                "--> small/src/lib.rs: `Spare;`",
            ],
            [
                "error[krs::analysis::group-subject-position]: the cell group `Mark` is held by the optional cell `held` of configuration `Small`, so its cells exist only in some states: a rule for a group applies at the group's one fixed position; write the rule for `Small`, or hold `Mark` in a cell that is always present",
                "--> small/src/lib.rs: `Mark;`",
            ],
            [
                "error[krs::analysis::group-subject-position]: the cell group `Job` is held by the collection cell `held` of configuration `Small`, so each instance holds its own copy of its cells: a rule for a group applies at the group's one fixed position, and a group inside a `*` collection is not supported yet; write the rule for `Small`, or hold `Job` at a fixed position",
                "--> small/src/lib.rs: `Job;`",
            ],
            [
                "error[krs::analysis::ambiguous-cell-sort]: cell declaration `Core` is the content of more than one cell field (`core`, `held`), so its K cell sort is ambiguous; declare one struct per nested cell",
                "--> small/src/lib.rs: `held: lib::Core,`",
            ],
            [
                "error[krs::analysis::group-claim]: a claim is typed by its definition's configuration, not by the cell group `Core`: a claim states what the definition's transition system does and leaves every cell it does not name unchanged, so the same claim would state something else in each configuration that holds `Core`; write the claim for the configuration",
                "--> small/src/lib.rs: `lib::Core;`",
            ],
            [
                "error[krs::analysis::group-claim]: a claim is typed by its definition's configuration, not by the cell group `Core`: a claim states what the definition's transition system does and leaves every cell it does not name unchanged, so the same claim would state something else in each configuration that holds `Core`; write the claim for the configuration",
                "--> small/src/lib.rs: `lib::Core,`",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// The workspaces of
/// [`a_sentence_typed_by_a_group_is_refused_where_it_leaves_the_group`], each
/// in its own directory below `temporary`; the manifests of their `small`.
fn refused_workspaces(temporary: &Path) -> [PathBuf; 11] {
    let root = |name: &str| temporary.join(name);
    let alone =
        |name: &str, source: &str| definitions(&root(name), "", &[("small", source)]).remove(0);
    let mark = "#[k::cell]\npub struct Mark {\n    #[k::cell]\n    pub seen: Int,\n}";
    let job = "#[k::cell]\npub struct Job {\n    #[k::cell]\n    pub payload: Int,\n}";
    [
        workspace(&root("outside"), "", SMALL_GROUP_RULE_OUTSIDE),
        workspace(&root("holder"), "", SMALL_GROUP_RULE_HOLDER),
        workspace(
            &root("cells-configuration-cell"),
            "",
            &group_cells_rule_naming("Small::mem", "Map"),
        ),
        alone(
            "cells-other-group",
            &small_holding(
                OTHER,
                "#[k::cell(nested)]\n    pub held: Other,",
                "Other { x: 0 }",
                &group_cells_rule_naming("Other::x", "Int"),
            ),
        ),
        workspace(
            &root("cells-group-not-held"),
            "",
            &format!("{OTHER}\n{}", group_cells_rule_naming("Other::x", "Int")),
        ),
        workspace(&root("spare"), "", SMALL_SPARE_GROUP_RULE),
        alone(
            "optional",
            &small_holding(
                mark,
                "#[k::cell(multiplicity = \"?\", nested)]\n    pub held: Option<Mark>,",
                "k::absent!(Mark { seen: 0 })",
                "k::rules! {\n    for Mark;\n\n    see: { seen } => { seen: k::builtin::int::add(seen, 1) };\n}",
            ),
        ),
        alone(
            "collection",
            &small_holding(
                job,
                "#[k::cell(multiplicity = \"*\", cell_type = \"List\", nested, initial)]\n    pub held: Job,",
                "Job { payload: 0 }",
                "k::rules! {\n    for Job;\n\n    bump: { payload } => { payload: k::builtin::int::add(payload, 1) };\n}",
            ),
        ),
        alone(
            "twice",
            &small_holding(
                "",
                "#[k::cell(nested)]\n    pub held: lib::Core,",
                "lib::Core { k: k::k![], pc: 0, acc: 0 }",
                SMALL_GROUP_RULE,
            ),
        ),
        workspace(&root("readable-claim"), "", SMALL_GROUP_READABLE_CLAIM),
        workspace(&root("cells-claim"), "", SMALL_GROUP_CELLS_CLAIM),
    ]
}

/// The library alone has no configuration, so its rules for its group have
/// no position: they are checked through a definition whose configuration
/// holds the group.
#[test]
fn a_librarys_group_rules_alone_are_refused_with_where_they_are_checked() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let small = workspace(temporary.path(), LIB_CORE_RULES, "");
    let lib = small
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("lib/Cargo.toml");
    expect_test::expect![[r#"
        [
            "error[krs::analysis::configuration-count]: this rule is for the cell group `Core`, but the definition has no `#[k::configuration]`: `Core` is a cell group, not a configuration, and rules for a group are checked through a definition whose configuration holds it",
            "--> lib/src/lib.rs: `Core;`",
        ]
    "#]].assert_debug_eq(&check_report(target.path(), &lib, "lib"));
}

/// A workspace of `lib` (the group, without rules) and `small`, whose source
/// is `small` in full; the manifest of `small`.
fn small_package(root: &Path, small: &str) -> PathBuf {
    write_package(root, "lib", LIB, "");
    let manifest = write_package(root, "small", small, "lib = { path = \"../lib\" }\n");
    fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"lib\", \"small\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    manifest
}

/// A second group of the library, which `Small` does not hold.
const OTHER_GROUP: &str = r"
/// A group no configuration of these tests holds.
#[k::cell]
pub struct Other {
    #[k::cell]
    pub x: Int,
}
";

/// A `cells!` rule for `Small` that names, through its group, the cell
/// `lib::Other::x`, which `Small` does not hold.
const SMALL_OTHER_CELLS_RULE: &str = r#"
#[k::rule(label = "poke")]
pub fn poke(
    k::cells! {
        lib::Core::k: k::configuration::KCell(lib::Op::Inc(), tail @ ..),
        lib::Other::x: k::configuration::Cell(_),
        state @ ..
    }: Small,
) -> Small {
    k::cells! {
        lib::Core::k: k::configuration::KCell(..tail),
        lib::Other::x: k::configuration::Cell(1),
        ..state
    }
}
"#;

/// A `cells!` rule names a cell through its group as written; a cell of a
/// group the configuration does not hold is refused at the name, where it
/// used to reach lowering as a broken rewrite.
#[test]
fn a_cells_rule_naming_a_cell_the_configuration_does_not_hold_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let small = workspace(temporary.path(), OTHER_GROUP, SMALL_OTHER_CELLS_RULE);
    expect_test::expect![[r#"
        [
            "error[krs::analysis::cell-outside-subject]: `poke` names the cell `Other::x`, but the configuration `Small` does not hold the group `Other`",
            "--> small/src/lib.rs: `x: k::configurat`",
        ]
    "#]].assert_debug_eq(&check_report(target.path(), &small, "small"));
}

/// A configuration whose own cell `pc` has the K name of the group's cell
/// `pc`: K names each cell of a configuration once, at any depth. `{fields}`
/// declares the two fields, in either order.
const SMALL_PC_BESIDE_CORE: &str = r"
use k::builtin::Int;

#[k::configuration]
pub struct Small {
{fields}
}

impl Small {
    #[k::init]
    pub fn init(pgm: lib::Prog) -> Self {
        Self {
            core: lib::Core { k: k::k![pgm], pc: 0, acc: 0 },
            pc: 0,
        }
    }
}
";

/// A group's cell names are taken in every configuration that holds it: a
/// cell beside the group with one of them is refused, naming both cells. The
/// error points at the containing configuration's own cell, which its author
/// can rename, whichever of the two fields comes first.
#[test]
fn a_cell_with_the_name_of_a_group_cell_is_refused_naming_both_cells() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let core = "    #[k::cell(nested)]\n    pub core: lib::Core,";
    let pc = "    #[k::cell]\n    pub pc: Int,";
    let reports = [("core-first", [core, pc]), ("pc-first", [pc, core])].map(|(name, fields)| {
        let source = SMALL_PC_BESIDE_CORE.replace("{fields}", &fields.join("\n"));
        let small = small_package(&temporary.path().join(name), &source);
        check_report(target.path(), &small, "small")
    });
    expect_test::expect![[r#"
        [
            [
                "error[krs::analysis::duplicate-cell-name]: cells `Core::pc` and `Small::pc` both have the K cell name `pc`; a configuration names each of its cells once",
                "--> small/src/lib.rs: `pc: Int,`",
                "= help: rename one of the two cells with `#[k::cell(name = \"..\")]`",
            ],
            [
                "error[krs::analysis::duplicate-cell-name]: cells `Small::pc` and `Core::pc` both have the K cell name `pc`; a configuration names each of its cells once",
                "--> small/src/lib.rs: `pc: Int,`",
                "= help: rename one of the two cells with `#[k::cell(name = \"..\")]`",
            ],
        ]
    "#]].assert_debug_eq(&reports);
}

/// A configuration that holds the group twice.
const SMALL_TWO_CORES: &str = r"
#[k::configuration]
pub struct Small {
    #[k::cell(nested)]
    pub left: lib::Core,
    #[k::cell(nested)]
    pub right: lib::Core,
}

impl Small {
    #[k::init]
    pub fn init(pgm: lib::Prog) -> Self {
        Self {
            left: lib::Core { k: k::k![pgm], pc: 0, acc: 0 },
            right: lib::Core { k: k::k![], pc: 0, acc: 0 },
        }
    }
}
";

/// A group held by two fields has no one position; the refusal says that
/// several instances of a group are a collection, which rules for the group
/// do not support yet.
#[test]
fn a_group_held_twice_is_refused_with_the_advice_for_its_rules() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let small = small_package(temporary.path(), SMALL_TWO_CORES);
    expect_test::expect![[r#"
        [
            "error[krs::analysis::ambiguous-cell-sort]: cell declaration `Core` is the content of more than one cell field (`left`, `right`), so its K cell sort is ambiguous; declare one struct per nested cell",
            "--> small/src/lib.rs: `right: lib::Core`",
            "= help: a group has one position in a configuration, where its rules apply; several instances of a group are a `*` collection of it, which rules for the group do not support yet",
        ]
    "#]].assert_debug_eq(&check_report(target.path(), &small, "small"));
}

/// The library alone declares a group and no configuration: it is no
/// definition, and the refusal says where its group's rules are checked.
#[test]
fn a_library_of_groups_alone_is_refused_with_where_its_rules_are_checked() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let small = workspace(temporary.path(), "", SMALL_RULES);
    let lib = small
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("lib/Cargo.toml");
    expect_test::expect![[r#"
        [
            "error[krs::analysis::configuration-count]: the definition has no `#[k::configuration]`; every definition declares its state with exactly one",
            "= help: `Core` is a cell group, not a configuration: rules for a group are checked through a definition whose configuration holds it",
        ]
    "#]].assert_debug_eq(&check_report(target.path(), &lib, "lib"));
}
