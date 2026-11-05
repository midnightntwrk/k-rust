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
//! (`Big { core: lib::Core, timer, mem }`). Held in an optional cell or as a
//! Map collection's instance type, a rule for the group is a local step of
//! one instance. A group in a Set or a List collection, a group the
//! configuration does not hold, a cell outside the group, and a claim typed
//! by a group are refused, each with its own code; a configuration that holds
//! the group twice is refused as it is for any rule.
//!
//! A context alias and a function context typed by the group are about the
//! group's cells in the same way: the library's serve every definition that
//! holds the group. A claim is about one definition's transition system, so
//! it is typed by the configuration, never by a group.

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

/// The sentence of `flat` that starts with `start`, up to the next sentence
/// or the source comment above it.
fn sentence<'a>(flat: &'a str, start: &str) -> &'a str {
    let begin = flat
        .find(start)
        .unwrap_or_else(|| panic!("no `{start}` in:\n{flat}"));
    let rest = &flat[begin..];
    let end = [
        " rule ",
        " syntax ",
        " endmodule",
        " claim ",
        " context ",
        " // KRS ",
    ]
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
/// - a group held by a Set or a List collection cell has no position a local
///   step of one instance applies at, `group-subject-position` (a group held
///   by an optional cell or a Map collection is admitted, below);
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
                "error[krs::analysis::group-subject-position]: the cell group `Mark` is held by the Set collection cell `held` of configuration `Small`: a sentence about `Mark` is about one instance, which a rule rewrites as a local step, and a Set identifies an instance by its whole content, so a step that makes one instance equal to another merges the two, removing an instance the rule never matched; write the sentence for `Small`, or hold the instances in a Map collection keyed by an id",
                "--> small/src/lib.rs: `Mark;`",
            ],
            [
                "error[krs::analysis::group-subject-position]: the cell group `Job` is held by the List collection cell `held` of configuration `Small`: a sentence about `Job` is about one instance, which in a List is the instance at any position, and matching one instance between others is not supported yet; write the sentence for `Small`, or hold the instances in a Map collection keyed by an id",
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
            "set",
            &small_holding(
                mark,
                "#[k::cell(multiplicity = \"*\", cell_type = \"Set\", nested, initial)]\n    pub held: Mark,",
                "Mark { seen: 0 }",
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
            "= help: a group has one position in a configuration, where its rules apply; several instances of a group are a `*` collection of it, and in a Map collection, keyed by the instance's first child, a rule for the group is a step of one instance",
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

/// The library's evaluation of a shown expression, for its group: a context
/// alias over `Core` that evaluates at the head of the group's computation,
/// and a function whose context reads the group's `acc`. Neither names a
/// cell outside the group, so both serve every definition that holds `Core`.
const LIB_CONTEXTS: &str = r#"
use k::Term;
use k::builtin::int;

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum Calc {
    #[k::syntax("plusAcc ( {n} )")]
    #[k::strict]
    PlusAcc { n: Exp },
}

#[k::constructors(sort = Instr, result = KResult)]
pub enum Out {
    #[k::syntax("show ( {value} )")]
    #[k::strict(using = core_eval)]
    Show { value: Exp },
}

/// Evaluate at the head of the group's computation.
#[k::context_alias(name = core_eval, here = site)]
fn core_eval(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        state @ ..
    }: Core,
) {
}

/// `n` plus the group's accumulator.
#[k::function(total, sort = Int, syntax = "accPlus({n})")]
pub struct AccPlus {
    pub n: Term<Int>,
}

#[k::equation]
fn acc_plus(
    n: Term<Int>,
    a: Term<Int>,
    k::term![AccPlus(n)]: Term<Int>,
    k::cells! {
        acc: k::configuration::Cell(a),
        ..
    }: Core,
) -> Term<Int> {
    int::add(a, n)
}

k::rules! {
    for Exp;
    use Calc::*;

    plus_acc: PlusAcc(n) => crate::AccPlus(n) where n: Int;
}

k::rules! {
    for Core;
    use Out::*;

    show: { k: [Show { value }, ..], pc: _ } => { k: [..], pc: value } where value: Int;
}
"#;

/// A context alias and a function context typed by the group as a containing
/// package writes them, `lib::Core`, and an expression that uses both: the
/// alias evaluates `plusPc`'s operand, and the function reads the group's
/// `pc`.
const SMALL_CONTEXTS: &str = r#"
use k::Term;

#[k::constructors(sort = lib::Exp, result = k::KResult)]
pub enum Peek {
    #[k::syntax("plusPc ( {n} )")]
    #[k::strict(using = small_eval)]
    PlusPc { n: lib::Exp },
}

/// Evaluate at the head of the group's computation.
#[k::context_alias(name = small_eval, here = site)]
fn small_eval(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        state @ ..
    }: lib::Core,
) {
}

/// `n` plus the group's program counter.
#[k::function(total, sort = Int, syntax = "pcPlus({n})")]
pub struct PcPlus {
    pub n: Term<Int>,
}

#[k::equation]
fn pc_plus(
    n: Term<Int>,
    p: Term<Int>,
    k::term![PcPlus(n)]: Term<Int>,
    k::cells! {
        pc: k::configuration::Cell(p),
        ..
    }: lib::Core,
) -> Term<Int> {
    k::builtin::int::add(p, n)
}

k::rules! {
    for lib::Exp;
    use Peek::*;

    plus_pc: PlusPc(n) => crate::PcPlus(n) where n: Int;
}
"#;

/// The context alias and the function context of `lib` and `small` as
/// `krs emit-k` writes them: each names the group's cells only, unnested,
/// which K completes to the group's one position.
const EMITTED_CONTEXTS: [&str; 4] = [
    "context alias [coreEval]: <k> HERE ~> Tail:K </k>",
    "rule [[ accPlus ( N:Int ) => A:Int +Int N:Int ]] <acc> A:Int </acc> [label(org_krs_groups_lib--acc_plus)]",
    "context alias [smallEval]: <k> HERE ~> Tail:K </k>",
    "rule [[ pcPlus ( N:Int ) => P:Int +Int N:Int ]] <pc> P:Int </pc> [label(org_krs_groups_small--pc_plus)]",
];

/// The core cells `krs run` ends with for `program` in `package`'s
/// definition: `k`, `pc` and `acc`.
fn core_end(target: &Path, manifest: &Path, package: &str, program: &Path) -> [String; 3] {
    let (success, stdout, stderr) = krs_on(
        target,
        manifest,
        package,
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{package}: {stdout}\n{stderr}");
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    let core = cell(&flat, "core");
    [cell(&core, "k"), cell(&core, "pc"), cell(&core, "acc")]
}

/// The library's context alias and function context, both typed by `Core`,
/// are sentences of every definition whose configuration holds the group:
/// `show ( plusAcc ( 5 ) )` evaluates its operand through the alias and reads
/// the group's `acc` through the function's context, alike in `small` and in
/// `big`, and each definition emits the two sentences with the same text.
#[test]
fn the_librarys_contexts_for_its_group_apply_in_every_containing_definition() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifests = definitions(
        temporary.path(),
        &format!("{LIB_CORE_RULES}{LIB_CONTEXTS}"),
        &[
            ("small", &format!("{SMALL}{SMALL_MEMORY_RULES}")),
            ("big", &format!("{BIG}{BIG_RULES}")),
        ],
    );
    let small = &manifests[0];
    let program = temporary.path().join("program.txt");
    fs::write(&program, "inc ; inc ; show ( plusAcc ( 5 ) ) ; done").unwrap();
    for package in ["small", "big"] {
        let (success, _, stderr) = krs_on(target.path(), small, package, "check", &[]);
        assert!(success, "{package}: {stderr}");
        assert_eq!(
            core_end(target.path(), small, package, &program),
            [".K", "7", "2"].map(str::to_owned),
            "{package}"
        );
        let flat = emitted(target.path(), small, package);
        assert_eq!(
            ["context alias [coreEval]:", "rule [[ accPlus"].map(|start| sentence(&flat, start)),
            [EMITTED_CONTEXTS[0], EMITTED_CONTEXTS[1]],
            "{package}: {flat}"
        );
    }
}

/// A containing package's own context alias and function context typed by
/// the group, `lib::Core`, resolve against its configuration as the
/// library's do, and run beside them: `plusPc ( plusAcc ( 1 ) )` evaluates
/// `plusAcc ( 1 )` through `small`'s alias, then reads `pc` through `small`'s
/// function context.
#[test]
fn a_containing_packages_contexts_typed_by_the_group_resolve_as_the_librarys() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let small = workspace(
        temporary.path(),
        &format!("{LIB_CORE_RULES}{LIB_CONTEXTS}"),
        &format!("{SMALL_MEMORY_RULES}{SMALL_CONTEXTS}"),
    );
    let (success, _, stderr) = krs(target.path(), &small, "check", &[]);
    assert!(success, "{stderr}");
    let flat = emitted(target.path(), &small, "small");
    assert_eq!(
        [
            "context alias [coreEval]:",
            "rule [[ accPlus",
            "context alias [smallEval]:",
            "rule [[ pcPlus",
        ]
        .map(|start| sentence(&flat, start)),
        EMITTED_CONTEXTS,
        "{flat}"
    );
    let program = small.with_file_name("program.txt");
    fs::write(
        &program,
        "inc ; inc ; show ( plusPc ( plusAcc ( 1 ) ) ) ; done",
    )
    .unwrap();
    assert_eq!(
        core_end(target.path(), &small, "small", &program),
        [".K", "5", "2"].map(str::to_owned)
    );
}

/// A function context typed by the group that names `Small::mem`, a cell of
/// the configuration outside the group.
const SMALL_GROUP_FUNCTION_CONTEXT_OUTSIDE: &str = r#"
use k::Term;

#[k::function(total, sort = Int, syntax = "memSize({n})")]
pub struct MemSize {
    pub n: Term<Int>,
}

#[k::equation]
fn mem_size(
    n: Term<Int>,
    m: Map,
    k::term![MemSize(n)]: Term<Int>,
    k::cells! {
        Small::mem: k::configuration::Cell(m),
        ..
    }: lib::Core,
) -> Term<Int> {
    k::builtin::int::add(map::size(m), n)
}
"#;

/// A context alias typed by the group that names `Small::mem`.
const SMALL_GROUP_CONTEXT_ALIAS_OUTSIDE: &str = r"
#[k::context_alias(name = mem_eval, here = site)]
fn mem_eval(
    m: Map,
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        Small::mem: k::configuration::Cell(m),
        state @ ..
    }: lib::Core,
) {
}
";

/// A function context typed by a group that no cell of `Small` holds.
const SMALL_SPARE_FUNCTION_CONTEXT: &str = r#"
use k::Term;

#[k::cell]
pub struct Spare {
    #[k::cell]
    pub ticks: Int,
}

#[k::function(total, sort = Int, syntax = "ticksPlus({n})")]
pub struct TicksPlus {
    pub n: Term<Int>,
}

#[k::equation]
fn ticks_plus(
    n: Term<Int>,
    t: Term<Int>,
    k::term![TicksPlus(n)]: Term<Int>,
    k::cells! {
        ticks: k::configuration::Cell(t),
        ..
    }: Spare,
) -> Term<Int> {
    k::builtin::int::add(t, n)
}
"#;

/// A context typed by a group is refused as a rule typed by the group is: a
/// function context or a context alias that names a cell outside the group
/// is `cell-outside-subject`, at the cell, and a function context typed by a
/// group no cell of the configuration holds is `group-not-in-configuration`,
/// at the type.
#[test]
fn a_context_typed_by_a_group_is_refused_where_it_leaves_the_group() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let outcomes = [
        ("function-context", SMALL_GROUP_FUNCTION_CONTEXT_OUTSIDE),
        ("context-alias", SMALL_GROUP_CONTEXT_ALIAS_OUTSIDE),
        ("spare", SMALL_SPARE_FUNCTION_CONTEXT),
    ]
    .map(|(name, source)| {
        let small = workspace(&temporary.path().join(name), "", source);
        check_errors(target.path(), &small)
    });
    expect_test::expect![[r#"
        [
            [
                "error[krs::analysis::cell-outside-subject]: `Core` has no cell `Small::mem`: a sentence about the cell group `Core` names only the cells inside the group, and `Small::mem` is another cell of configuration `Small`; write the sentence for `Small` to name it",
                "--> small/src/lib.rs: `mem: k::configur`",
            ],
            [
                "error[krs::analysis::cell-outside-subject]: `Core` has no cell `Small::mem`: a sentence about the cell group `Core` names only the cells inside the group, and `Small::mem` is another cell of configuration `Small`; write the sentence for `Small` to name it",
                "--> small/src/lib.rs: `mem: k::configur`",
            ],
            [
                "error[krs::analysis::group-not-in-configuration]: no cell of configuration `Small` holds the cell group `Spare`, so a rule for `Spare` has no cells to apply to: a group's rules apply at the group's position in the definition's configuration",
                "--> small/src/lib.rs: `Spare,`",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// A readable claim the library writes for its own group.
const LIB_GROUP_READABLE_CLAIM: &str = r"
k::claims! {
    for Core;
    use Op::*;

    #[k::claim(all_paths)]
    inc_once: { k: [Inc()], pc } => { k: [], pc: k::builtin::int::add(pc, 1) };
}
";

/// A `cells!` claim the library writes for its own group.
const LIB_GROUP_CELLS_CLAIM: &str = r#"
#[k::claim(all_paths, label = "inc-once")]
fn inc_once(
    pc: Int,
    k::cells! {
        k: k::configuration::KCell(Op::Inc()),
        pc: k::configuration::Cell(pc),
        state @ ..
    }: Core,
) -> Core {
    k::cells! {
        k: k::configuration::KCell(.K),
        pc: k::configuration::Cell(k::builtin::int::add(pc, 1)),
        ..state
    }
}
"#;

/// The claim about the group's cells written for the configuration: it names
/// them flat.
const SMALL_CLAIM: &str = r"
k::claims! {
    for Small;
    use lib::Op::*;

    #[k::claim(all_paths)]
    inc_once: { k: [Inc()], pc, acc } => { k: [], pc: k::builtin::int::add(pc, 1), acc: k::builtin::int::add(acc, 1) };
}
";

/// A claim is about one definition's transition system, so the library's
/// claims for its own group are refused in both forms, `group-claim` at the
/// type that names the group, as a containing package's are. The same claim
/// written for the containing configuration names the group's cells flat and
/// is proven.
#[test]
fn a_claim_about_a_groups_cells_is_written_for_the_configuration() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let refused = [
        ("readable", LIB_GROUP_READABLE_CLAIM),
        ("cells", LIB_GROUP_CELLS_CLAIM),
    ]
    .map(|(name, claim)| {
        let small = workspace(
            &temporary.path().join(name),
            &format!("{LIB_CORE_RULES}{claim}"),
            "",
        );
        check_errors(target.path(), &small)
    });
    expect_test::expect![[r#"
        [
            [
                "error[krs::analysis::group-claim]: a claim is typed by its definition's configuration, not by the cell group `Core`: a claim states what the definition's transition system does and leaves every cell it does not name unchanged, so the same claim would state something else in each configuration that holds `Core`; write the claim for the configuration",
                "--> lib/src/lib.rs: `Core;`",
            ],
            [
                "error[krs::analysis::group-claim]: a claim is typed by its definition's configuration, not by the cell group `Core`: a claim states what the definition's transition system does and leaves every cell it does not name unchanged, so the same claim would state something else in each configuration that holds `Core`; write the claim for the configuration",
                "--> lib/src/lib.rs: `Core,`",
            ],
        ]
    "#]].assert_debug_eq(&refused);

    let small = workspace(
        &temporary.path().join("configuration"),
        LIB_CORE_RULES,
        SMALL_CLAIM,
    );
    let (success, stdout, stderr) = krs(target.path(), &small, "prove", &[]);
    assert!(success, "{stdout}\n{stderr}");
    let proven = stdout
        .lines()
        .filter(|line| line.contains(": proven"))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "ORG-KRS-GROUPS-SMALL-SPEC.inc-once: proven",
        ]
    "#]]
    .assert_debug_eq(&proven);
}

// A cell group held in an optional cell or a Map collection (OT-11-U8, stage 1).
//
// A rule for a group is a local step of one instance: applied inside one
// instance, it changes that instance and frames everything else. So a group
// held at a fixed position, in an optional (`?`) cell, or as the instance type
// of a Map collection takes the same library rules, in both spellings, and a
// rule for the group names the instance's cells flat from the instance's
// level. A Set collection merges a stepped instance with an equal one, so it
// holds no local step; a List collection's instance at any position cannot be
// matched yet. A Map instance's key is its identity, so a rule restates it or
// leaves it out. A function context typed by such a group reads the one
// instance it is evaluated in, so only a sentence inside that instance may
// apply it.

/// The library of the instance cases: a hart (its key `id`, its computation
/// and its program counter) and a floating-point unit, with the program
/// syntax. `rules` is appended.
const INSTANCE_LIB: &str = r#"
use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Instr;
}

#[k::constructors(sort = Instr, result = KResult)]
pub enum Op {
    #[k::syntax("inc")]
    Inc(),
    #[k::syntax("dec")]
    Dec(),
    #[k::syntax("tick")]
    Tick(),
    #[k::syntax("spawn")]
    Spawn(),
}

/// One hart; in a Map collection, its first child `id` is its key.
#[k::cell]
pub struct Hart {
    #[k::cell]
    pub id: Int,
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
}

/// A floating-point unit, which a definition may hold as an optional cell.
#[k::cell]
pub struct Fpu {
    #[k::cell]
    pub busy: Int,
    #[k::cell]
    pub fa: Int,
}
"#;

/// The library's rules for `Hart`, readable: `inc` leaves the key out,
/// `dec` restates it as the binder its subject matched it with, and `tick`
/// as the literal it matched. Each changes the program counter.
const HART_RULES: &str = r"
k::rules! {
    for Hart;
    use Op::*;

    inc: { k: [Inc(), ..], pc } => { k: [..], pc: k::builtin::int::add(pc, 1) };
    dec: { id: me, k: [Dec(), ..], pc } => { id: me, k: [..], pc: k::builtin::int::add(pc, 3) };
    tick: { id: 0, k: [Tick(), ..], pc } => { id: 0, k: [..], pc: k::builtin::int::add(pc, 2) };
}
";

/// [`HART_RULES`] as `#[k::rule]` fns over `k::cells! { .. }: Hart`.
const HART_CELLS_RULES: &str = r#"
#[k::rule(label = "inc")]
pub fn inc(
    pc: Int,
    k::cells! {
        k: k::configuration::KCell(Op::Inc(), tail @ ..),
        pc: k::configuration::Cell(pc),
        state @ ..
    }: Hart,
) -> Hart {
    k::cells! {
        k: k::configuration::KCell(..tail),
        pc: k::configuration::Cell(k::builtin::int::add(pc, 1)),
        ..state
    }
}

#[k::rule(label = "dec")]
pub fn dec(
    me: Int,
    pc: Int,
    k::cells! {
        id: k::configuration::Cell(me),
        k: k::configuration::KCell(Op::Dec(), tail @ ..),
        pc: k::configuration::Cell(pc),
        state @ ..
    }: Hart,
) -> Hart {
    k::cells! {
        id: k::configuration::Cell(me),
        k: k::configuration::KCell(..tail),
        pc: k::configuration::Cell(k::builtin::int::add(pc, 3)),
        ..state
    }
}

#[k::rule(label = "tick")]
pub fn tick(
    pc: Int,
    k::cells! {
        id: k::configuration::Cell(0),
        k: k::configuration::KCell(Op::Tick(), tail @ ..),
        pc: k::configuration::Cell(pc),
        state @ ..
    }: Hart,
) -> Hart {
    k::cells! {
        id: k::configuration::Cell(0),
        k: k::configuration::KCell(..tail),
        pc: k::configuration::Cell(k::builtin::int::add(pc, 2)),
        ..state
    }
}
"#;

/// `uni`: the hart at a fixed position.
const UNI: &str = r"
use k::builtin::{Int, Map, map};

#[k::configuration]
pub struct Uni {
    #[k::cell(nested)]
    pub hart: lib::Hart,
    #[k::cell]
    pub mem: Map<Int, Int>,
}

impl Uni {
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {
        Self {
            hart: lib::Hart { id: 0, k: k::k![pgm], pc: 0 },
            mem: map::empty(),
        }
    }
}
";

/// `smp`: the harts as a collection ordered by `order`, starting with one,
/// beside a memory and a counter; `rules` is appended.
fn smp(order: &str, rules: &str) -> String {
    format!(
        r#"
use k::builtin::{{Int, Map, map}};

#[k::cell]
pub struct Harts {{
    #[k::cell(multiplicity = "*", cell_type = "{order}", initial, nested)]
    pub hart: lib::Hart,
}}

#[k::configuration]
pub struct Smp {{
    #[k::cell(nested)]
    pub harts: Harts,
    #[k::cell]
    pub mem: Map<Int, Int>,
    #[k::cell]
    pub ticks: Int,
}}

impl Smp {{
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {{
        Self {{
            harts: Harts {{
                hart: lib::Hart {{ id: 0, k: k::k![pgm], pc: 0 }},
            }},
            mem: map::empty(),
            ticks: 0,
        }}
    }}
}}

{rules}
"#
    )
}

/// `opt`: the hart at a fixed position and an optional floating-point unit,
/// with `rules` for the unit.
fn opt(rules: &str) -> String {
    format!(
        r#"
use k::builtin::{{Int, Map, map}};

#[k::configuration]
pub struct Opt {{
    #[k::cell(nested)]
    pub hart: lib::Hart,
    #[k::cell(multiplicity = "?", nested)]
    pub fpu: Option<lib::Fpu>,
    #[k::cell]
    pub mem: Map<Int, Int>,
}}

impl Opt {{
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {{
        Self {{
            hart: lib::Hart {{ id: 0, k: k::k![pgm], pc: 0 }},
            fpu: k::absent!(lib::Fpu {{ busy: 0, fa: 0 }}),
            mem: map::empty(),
        }}
    }}
}}

{rules}
"#
    )
}

/// `opt`'s rule for its unit, readable.
const FPU_RULE: &str = r"
k::rules! {
    for lib::Fpu;

    finish: { busy: 1, fa } => { busy: 0, fa: k::builtin::int::add(fa, 1) };
}
";

/// [`FPU_RULE`] as a `#[k::rule]` fn over `k::cells! { .. }: lib::Fpu`.
const FPU_CELLS_RULE: &str = r#"
#[k::rule(label = "finish")]
pub fn finish(
    fa: Int,
    k::cells! {
        busy: k::configuration::Cell(1),
        fa: k::configuration::Cell(fa),
        state @ ..
    }: lib::Fpu,
) -> lib::Fpu {
    k::cells! {
        busy: k::configuration::Cell(0),
        fa: k::configuration::Cell(k::builtin::int::add(fa, 1)),
        ..state
    }
}
"#;

/// A workspace of `lib` ([`INSTANCE_LIB`] plus `lib_rules`) and one package
/// per definition, each depending on `lib`; the definitions' manifests, in
/// order.
fn instance_definitions(root: &Path, lib_rules: &str, packages: &[(&str, &str)]) -> Vec<PathBuf> {
    write_package(root, "lib", &format!("{INSTANCE_LIB}{lib_rules}"), "");
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

/// The library's rules for `Hart` are rules of a definition that holds the
/// hart at a fixed position (`uni`), as a Map collection's instance type
/// (`smp`), or beside an optional unit whose own rules are for `lib::Fpu`
/// (`opt`), in both spellings: each definition checks. A rule that restates
/// a Map instance's key, as the binder its subject matched it with (`dec`) or
/// as the same literal (`tick`), is admitted. In `smp` the emitted rule names
/// the instance's leaf cells inside the instance's cell `<hart>`, and in `opt`
/// inside the optional cell `<fpu>`; the one hart runs.
#[test]
fn group_rules_apply_at_a_fixed_position_in_an_optional_cell_and_in_a_map() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let mut emitted_inc = Vec::new();
    for (spelling, hart_rules, fpu_rule) in [
        ("readable", HART_RULES, FPU_RULE),
        ("cells", HART_CELLS_RULES, FPU_CELLS_RULE),
    ] {
        let manifests = instance_definitions(
            &temporary.path().join(spelling),
            hart_rules,
            &[
                ("uni", UNI),
                ("smp", &smp("Map", "")),
                ("opt", &opt(fpu_rule)),
            ],
        );
        for (manifest, package) in manifests.iter().zip(["uni", "smp", "opt"]) {
            let (success, _, stderr) = krs_on(target.path(), manifest, package, "check", &[]);
            assert!(success, "{spelling} {package}:\n{stderr}");
        }
        let flat = emitted(target.path(), &manifests[1], "smp");
        emitted_inc.push(sentence(&flat, "rule [inc]:").to_owned());
        let flat = emitted(target.path(), &manifests[2], "opt");
        emitted_inc.push(sentence(&flat, "rule [finish]:").to_owned());
        // The one hart steps by `dec`, which restates its key.
        let program = manifests[1].with_file_name("program.txt");
        fs::write(&program, "dec").unwrap();
        let (success, stdout, stderr) = krs_on(
            target.path(),
            &manifests[1],
            "smp",
            "run",
            &[program.to_str().unwrap()],
        );
        assert!(success, "{spelling}:\n{stdout}\n{stderr}");
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        let hart = cell(&flat, "hart");
        assert_eq!(
            [cell(&hart, "id"), cell(&hart, "k"), cell(&hart, "pc")],
            ["0", ".K", "3"].map(str::to_owned),
            "{spelling}: {flat}"
        );
    }
    expect_test::expect![[r#"
        [
            "rule [inc]: <hart> <k> inc => .K ... </k> <pc> Pc:Int => Pc:Int +Int 1 </pc> ... </hart>",
            "rule [finish]: <fpu> <busy> 1 => 0 </busy> <fa> Fa:Int => Fa:Int +Int 1 </fa> ... </fpu>",
            "rule [inc]: <hart> <k> inc ~> Tail:K => .K ~> Tail:K </k> <pc> Pc:Int => Pc:Int +Int 1 </pc> ... </hart>",
            "rule [finish]: <fpu> <busy> 1 => 0 </busy> <fa> Fa:Int => Fa:Int +Int 1 </fa> ... </fpu>",
        ]
    "#]].assert_debug_eq(&emitted_inc);
}

/// A rule a definition writes for the hart, and a table clause, which runs at
/// the main cell, the hart's `k`.
const HOLDER_HART_RULES: &str = r"
k::rules! {
    for lib::Hart;
    use lib::Op::*;

    inc: { k: [Inc(), ..], pc } => { k: [..], pc: k::builtin::int::add(pc, 1) };
}

k::rules! {
    for lib::Instr;
    use lib::Op::*;

    tick: Tick() => Inc();
}
";

/// The `#[k::rule]` fn labelled `label` in a `krs expand` print, up to its
/// closing brace.
fn printed_rule<'a>(print: &'a str, label: &str) -> &'a str {
    let start = print
        .find(&format!("#[k::rule(label = \"{label}\")]"))
        .unwrap_or_else(|| panic!("no rule `{label}` in:\n{print}"));
    let end = start + print[start..].find("\n}\n").unwrap() + 2;
    &print[start..end]
}

/// `package`'s print checks, and each rule `labels` names emits as the
/// readable rule does.
fn assert_print_emits_the_readable_k(
    target: &Path,
    readable: &Path,
    printed: &Path,
    package: &str,
    labels: &[&str],
) {
    let (success, _, stderr) = krs_on(target, printed, package, "check", &[]);
    assert!(success, "printed {package}:\n{stderr}");
    let (readable, printed) = (
        emitted(target, readable, package),
        emitted(target, printed, package),
    );
    for label in labels {
        let start = format!("rule [{label}]:");
        assert_eq!(
            sentence(&readable, &start),
            sentence(&printed, &start),
            "{package}"
        );
    }
}

/// `krs expand` prints a rule for a group as a `cells!` rule typed by the
/// group, naming the group's cells flat, whatever holds the group: a fixed
/// position (`uni`), a Map collection (`smp`) or an optional cell (`opt`'s
/// rule for `lib::Fpu`). A table clause is typed by the group whose instance
/// holds the main cell (`smp`), and by the configuration where the main cell
/// sits at a fixed position (`uni`). Each print checks and emits the
/// readable rule's K.
#[test]
fn a_rule_for_a_group_prints_typed_by_the_group_wherever_the_group_is_held() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let packages = [
        (
            "uni",
            format!("{UNI}{HOLDER_HART_RULES}"),
            &["inc", "tick"][..],
        ),
        ("smp", smp("Map", HOLDER_HART_RULES), &["inc", "tick"][..]),
        ("opt", opt(FPU_RULE), &["finish"][..]),
    ];
    let sources = packages
        .iter()
        .map(|(name, source, _)| (*name, source.as_str()))
        .collect::<Vec<_>>();
    let readable = instance_definitions(&temporary.path().join("readable"), "", &sources);
    let mut prints = Vec::new();
    let mut printed_sources = Vec::new();
    for (manifest, (package, _, labels)) in readable.iter().zip(&packages) {
        let (success, print, stderr) = krs_on(target.path(), manifest, package, "expand", &[]);
        assert!(success, "{package}:\n{stderr}");
        for label in *labels {
            prints.push(format!("// {package}\n{}", printed_rule(&print, label)));
        }
        printed_sources.push((*package, print));
    }
    let sources = printed_sources
        .iter()
        .map(|(name, source)| (*name, source.as_str()))
        .collect::<Vec<_>>();
    let printed = instance_definitions(&temporary.path().join("printed"), "", &sources);
    for ((readable, printed), (package, _, labels)) in readable.iter().zip(&printed).zip(&packages)
    {
        assert_print_emits_the_readable_k(target.path(), readable, printed, package, labels);
    }
    expect_test::expect![[r#"
        // uni
        #[k::rule(label = "inc")]
        pub fn inc(
            pc: k::Term<k::builtin::Int>,
            k::cells! {
                k : k::configuration::KCell(::lib::Op::Inc(), ..), pc :
                k::configuration::Cell(pc), state @ ..
            }: ::lib::Hart,
        ) -> ::lib::Hart {
            k::cells! {
                k : k::configuration::KCell(..), pc :
                k::configuration::Cell(k::builtin::int::add(pc, 1)), ..state
            }
        }
        // uni
        #[k::rule(label = "tick")]
        pub fn tick(
            k::cells! {
                ::lib::Hart::k : k::configuration::KCell(::lib::Op::Tick(), ..), state @ ..
            }: crate::Uni,
        ) -> crate::Uni {
            k::cells! {
                ::lib::Hart::k : k::configuration::KCell(::lib::Op::Inc(), ..), ..state
            }
        }
        // smp
        #[k::rule(label = "inc")]
        pub fn inc(
            pc: k::Term<k::builtin::Int>,
            k::cells! {
                k : k::configuration::KCell(::lib::Op::Inc(), ..), pc :
                k::configuration::Cell(pc), state @ ..
            }: ::lib::Hart,
        ) -> ::lib::Hart {
            k::cells! {
                k : k::configuration::KCell(..), pc :
                k::configuration::Cell(k::builtin::int::add(pc, 1)), ..state
            }
        }
        // smp
        #[k::rule(label = "tick")]
        pub fn tick(
            k::cells! {
                k : k::configuration::KCell(::lib::Op::Tick(), ..), state @ ..
            }: ::lib::Hart,
        ) -> ::lib::Hart {
            k::cells! {
                k : k::configuration::KCell(::lib::Op::Inc(), ..), ..state
            }
        }
        // opt
        #[k::rule(label = "finish")]
        pub fn finish(
            fa: k::Term<k::builtin::Int>,
            k::cells! {
                busy : k::configuration::Cell(1), fa : k::configuration::Cell(fa), state @ ..
            }: ::lib::Fpu,
        ) -> ::lib::Fpu {
            k::cells! {
                busy : k::configuration::Cell(0), fa :
                k::configuration::Cell(k::builtin::int::add(fa, 1)), ..state
            }
        }"#]]
    .assert_eq(&prints.join("\n"));
}

/// A boot rule for `Smp`, over the collection's instance records: the first
/// hart's `spawn` becomes `inc`, and a second hart, keyed `1`, starts with
/// `dec` and its program counter at 10.
const SMP_BOOT: &str = r"
k::rules! {
    for Smp;
    use lib::Op::*;

    spawn: { hart: { me @ lib::Hart { k: [Spawn(), ..], .. }, .. } } => { hart: { lib::Hart { k: [Inc(), ..], ..me }, lib::Hart { id: 1, k: [Dec()], pc: 10 }, .. } };
}
";

/// Every `<hart> .. </hart>` of whitespace-flattened text, in order.
fn harts(flat: &str) -> Vec<String> {
    flat.split("<hart> ")
        .skip(1)
        .map(|rest| rest[..rest.find(" </hart>").unwrap()].to_owned())
        .collect()
}

/// Two harts step by the library's rules for `Hart`: each step is a local step
/// of one hart, which changes that hart and frames the other, so hart 0 ends
/// with `inc` applied once (`pc` 1) and hart 1 with `dec` once (`pc` 13). The
/// two harts' steps commute, so every interleaving reaches one final state:
/// `krs search --mode final` finds exactly that one.
#[test]
fn each_step_of_a_group_rule_changes_one_instance() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = instance_definitions(
        temporary.path(),
        HART_RULES,
        &[("smp", &smp("Map", SMP_BOOT))],
    )
    .remove(0);
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "spawn").unwrap();
    let program = program.to_str().unwrap();
    let flat = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    let (success, stdout, stderr) = krs_on(target.path(), &manifest, "smp", "run", &[program]);
    assert!(success, "{stdout}\n{stderr}");
    let run = harts(&flat(&stdout));
    let (success, stdout, stderr) = krs_on(
        target.path(),
        &manifest,
        "smp",
        "search",
        &[program, "--mode", "final"],
    );
    assert!(success, "{stdout}\n{stderr}");
    let searched = flat(&stdout);
    assert_eq!(searched.matches("<generatedTop>").count(), 1, "{searched}");
    expect_test::expect![[r#"
        (
            [
                "<id> 0 </id> <k> .K </k> <pc> 1 </pc>",
                "<id> 1 </id> <k> .K </k> <pc> 13 </pc>",
            ],
            "<generatedTop> <harts> <hart> <id> 0 </id> <k> .K </k> <pc> 1 </pc> </hart> <hart> <id> 1 </id> <k> .K </k> <pc> 13 </pc> </hart> </harts> <mem> .Map </mem> <ticks> 0 </ticks> </generatedTop>",
        )
    "#]].assert_debug_eq(&(run, searched));
}

/// A Map instance's key (`id`) written as another value than the subject
/// matched it with.
const KEY_CHANGE_RULE: &str = r"
k::rules! {
    for lib::Hart;
    use lib::Op::*;

    renumber: { id: me, k: [Inc(), ..] } => { id: k::builtin::int::add(me, 1), k: [..] };
}
";

/// [`KEY_CHANGE_RULE`] as a `#[k::rule]` fn.
const KEY_CHANGE_CELLS_RULE: &str = r#"
#[k::rule(label = "renumber")]
pub fn renumber(
    me: Int,
    k::cells! {
        id: k::configuration::Cell(me),
        k: k::configuration::KCell(lib::Op::Inc(), tail @ ..),
        state @ ..
    }: lib::Hart,
) -> lib::Hart {
    k::cells! {
        id: k::configuration::Cell(k::builtin::int::add(me, 1)),
        k: k::configuration::KCell(..tail),
        ..state
    }
}
"#;

/// A rule for the hart that names `hart`, the collection cell that holds it.
const HOLDER_RULE: &str = r"
k::rules! {
    for lib::Hart;
    use lib::Op::*;

    hold: { k: [Inc(), ..], hart } => { k: [..], hart };
}
";

/// [`HOLDER_RULE`] as a `#[k::rule]` fn, naming the holder by its owner.
const HOLDER_CELLS_RULE: &str = r#"
#[k::rule(label = "hold")]
pub fn hold(
    k::cells! {
        k: k::configuration::KCell(lib::Op::Inc(), tail @ ..),
        Harts::hart: { me @ k::fragment![lib::Hart { .. }], others @ .. },
        state @ ..
    }: lib::Hart,
) -> lib::Hart {
    k::cells! {
        k: k::configuration::KCell(..tail),
        ..state
    }
}
"#;

/// A configuration whose instances are `Core`s, each holding a List
/// collection of jobs, with `rules` appended.
fn cores(rules: &str) -> String {
    format!(
        r#"
use k::builtin::{{Int, KSequence}};

#[k::cell]
pub struct Cores {{
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub core: Core,
}}

#[k::cell]
pub struct Core {{
    #[k::cell]
    pub id: Int,
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub jobs: Jobs,
}}

#[k::cell]
pub struct Jobs {{
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub job: Job,
}}

#[k::cell]
pub struct Job {{
    #[k::cell]
    pub payload: Int,
}}

#[k::configuration]
pub struct Many {{
    #[k::cell(nested)]
    pub cores: Cores,
}}

impl Many {{
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {{
        Self {{
            cores: Cores {{
                core: Core {{ id: 0, k: k::k![pgm], jobs: Jobs {{ job: Job {{ payload: 0 }} }} }},
            }},
        }}
    }}
}}

{rules}
"#
    )
}

/// A rule for `Core` that names `payload`, a cell of the List collection
/// inside the instance, flat.
const INNER_FLAT_RULE: &str = r"
k::rules! {
    for Core;
    use lib::Op::*;

    work: { k: [Inc(), ..], payload } => { k: [..], payload: k::builtin::int::add(payload, 1) };
}
";

/// [`INNER_FLAT_RULE`] as a `#[k::rule]` fn.
const INNER_FLAT_CELLS_RULE: &str = r#"
#[k::rule(label = "work")]
pub fn work(
    p: Int,
    k::cells! {
        k: k::configuration::KCell(lib::Op::Inc(), tail @ ..),
        Job::payload: k::configuration::Cell(p),
        state @ ..
    }: Core,
) -> Core {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Job::payload: k::configuration::Cell(k::builtin::int::add(p, 1)),
        ..state
    }
}
"#;

/// A rule for `Core` that writes the inner collection's front instance
/// through its instance record: admitted by the entries, but not emitted
/// inside an instance yet.
const INNER_RECORD_RULE: &str = r"
k::rules! {
    for Core;
    use lib::Op::*;

    work: { k: [Inc(), ..], job: [j @ Job { payload: p }, ..] } => { k: [..], job: [Job { payload: k::builtin::int::add(p, 1), ..j }, ..] };
}
";

/// [`INNER_RECORD_RULE`] as a `#[k::rule]` fn.
const INNER_RECORD_CELLS_RULE: &str = r#"
#[k::rule(label = "work")]
pub fn work(
    p: Int,
    k::cells! {
        k: k::configuration::KCell(lib::Op::Inc(), tail @ ..),
        Jobs::job: [j @ k::fragment![crate::Job { payload: p }], jobs @ ..],
        state @ ..
    }: Core,
) -> Core {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Jobs::job: [k::fragment![crate::Job { payload: k::builtin::int::add(p, 1), ..j }], ..jobs],
        ..state
    }
}
"#;

/// A function whose context reads the hart's `pc`, `pcPlus(n)`.
const PC_PLUS: &str = r#"
use k::Term;

#[k::function(total, sort = Int, syntax = "pcPlus({n})")]
pub struct PcPlus {
    pub n: Term<Int>,
}

#[k::equation]
fn pc_plus(
    n: Term<Int>,
    p: Term<Int>,
    k::term![PcPlus(n)]: Term<Int>,
    k::cells! {
        pc: k::configuration::Cell(p),
        ..
    }: lib::Hart,
) -> Term<Int> {
    k::builtin::int::add(p, n)
}
"#;

/// A function without a context of its own that applies `pcPlus`, so it is
/// evaluated where its caller is, and a rule for `Smp` that applies it.
const VIA_PC: &str = r#"
#[k::function(total, sort = Int, syntax = "viaPc({n})")]
pub struct ViaPc {
    pub n: Term<Int>,
}

#[k::equation]
fn via_pc(n: Term<Int>, k::term![ViaPc(n)]: Term<Int>) -> Term<Int> {
    crate::PcPlus(n)
}

k::rules! {
    for Smp;

    sample: { ticks: 0 } => { ticks: crate::ViaPc(1) };
}
"#;

/// A rule for `Smp`, outside every hart, that applies `pcPlus`.
const SMP_CALLER: &str = r"
k::rules! {
    for Smp;

    sample: { ticks: 0 } => { ticks: crate::PcPlus(1) };
}
";

/// [`SMP_CALLER`] as a `#[k::rule]` fn.
const SMP_CELLS_CALLER: &str = r#"
#[k::rule(label = "sample")]
pub fn sample(
    k::cells! {
        ticks: k::configuration::Cell(0),
        state @ ..
    }: Smp,
) -> Smp {
    k::cells! {
        ticks: k::configuration::Cell(crate::PcPlus(1)),
        ..state
    }
}
"#;

/// A context alias typed by the hart.
const HART_ALIAS: &str = r#"
#[k::constructors(sort = lib::Instr, result = k::KResult)]
pub enum Wait {
    #[k::syntax("wait ( {n} )")]
    #[k::strict(using = hart_eval)]
    Wait { n: lib::Instr },
}

/// Evaluate at the head of the hart's computation.
#[k::context_alias(name = hart_eval, here = site)]
fn hart_eval(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        state @ ..
    }: lib::Hart,
) {
}
"#;

/// A configuration whose only computation cell sits in a Set collection's
/// instance, so the program starts there.
const SET_MAIN: &str = r#"
use k::builtin::{Int, KSequence};

#[k::cell]
pub struct Objs {
    #[k::cell(multiplicity = "*", cell_type = "Set", initial, nested)]
    pub obj: Obj,
}

#[k::cell]
pub struct Obj {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub n: Int,
}

#[k::configuration]
pub struct Pool {
    #[k::cell(nested)]
    pub objs: Objs,
}

impl Pool {
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {
        Self {
            objs: Objs {
                obj: Obj { k: k::k![pgm], n: 0 },
            },
        }
    }
}
"#;

/// A configuration whose instances are `Node`s keyed by a group, `cpu`, with
/// `rules` appended: the whole group is the instance's identity.
fn composite(rules: &str) -> String {
    format!(
        r#"
use k::builtin::{{Int, KSequence}};

#[k::cell]
pub struct Nodes {{
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub node: Node,
}}

#[k::cell]
pub struct Node {{
    #[k::cell(nested)]
    pub cpu: Cpu,
    #[k::cell]
    pub k: KSequence,
}}

#[k::cell]
pub struct Cpu {{
    #[k::cell]
    pub pc: Int,
}}

#[k::configuration]
pub struct Grid {{
    #[k::cell(nested)]
    pub nodes: Nodes,
}}

impl Grid {{
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {{
        Self {{
            nodes: Nodes {{
                node: Node {{ cpu: Cpu {{ pc: 0 }}, k: k::k![pgm] }},
            }},
        }}
    }}
}}

{rules}
"#
    )
}

/// A rule for `Node` that writes `pc`, a cell inside the key `cpu`.
const INSIDE_KEY_RULE: &str = r"
k::rules! {
    for Node;
    use lib::Op::*;

    bump: { k: [Inc(), ..], pc } => { k: [..], pc: k::builtin::int::add(pc, 1) };
}
";

/// [`INSIDE_KEY_RULE`] as a `#[k::rule]` fn.
const INSIDE_KEY_CELLS_RULE: &str = r#"
#[k::rule(label = "bump")]
pub fn bump(
    p: Int,
    k::cells! {
        k: k::configuration::KCell(lib::Op::Inc(), tail @ ..),
        Cpu::pc: k::configuration::Cell(p),
        state @ ..
    }: Node,
) -> Node {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Cpu::pc: k::configuration::Cell(k::builtin::int::add(p, 1)),
        ..state
    }
}
"#;

/// A rule for `Cpu`, the group that is each node's key.
const KEY_GROUP_RULE: &str = r"
k::rules! {
    for Cpu;

    bump: { pc: 0 } => { pc: 1 };
}
";

/// [`KEY_GROUP_RULE`] as a `#[k::rule]` fn.
const KEY_GROUP_CELLS_RULE: &str = r#"
#[k::rule(label = "bump")]
pub fn bump(
    k::cells! {
        pc: k::configuration::Cell(0),
        state @ ..
    }: Cpu,
) -> Cpu {
    k::cells! {
        pc: k::configuration::Cell(1),
        ..state
    }
}
"#;

/// A configuration whose instances are keyed by a constructor term, `h(n)`, with
/// `rules` appended.
fn tagged(rules: &str) -> String {
    format!(
        r#"
use k::KResult;
use k::builtin::{{Int, KSequence}};

k::sorts! {{
    Hid;
}}

#[k::constructors(sort = Hid, result = KResult)]
pub enum HidC {{
    #[k::syntax("h ( {{n}} )")]
    H {{ n: Int }},
}}

#[k::cell]
pub struct Units {{
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub unit: Unit,
}}

#[k::cell]
pub struct Unit {{
    #[k::cell]
    pub id: Hid,
    #[k::cell]
    pub k: KSequence,
}}

#[k::configuration]
pub struct Tagged {{
    #[k::cell(nested)]
    pub units: Units,
}}

impl Tagged {{
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {{
        Self {{
            units: Units {{
                unit: Unit {{ id: HidC::H(0), k: k::k![pgm] }},
            }},
        }}
    }}
}}

{rules}
"#
    )
}

/// A single-body rule that rewrites in place inside the key `h(n)`.
const KEY_REWRITE_INSIDE: &str = r#"
#[k::rule(label = "rekey")]
pub fn rekey(
    n: Int,
    k::cells! {
        id: k::configuration::Cell(HidC::H(k::rewrite!(n => k::builtin::int::add(n, 1)))),
        k: k::configuration::KCell(k::rewrite!(lib::Op::Inc() => ()), ..),
        state @ ..
    }: Unit,
) {}
"#;

/// A single-body rule that rewrites the whole key in place.
const KEY_REWRITE_WHOLE: &str = r#"
#[k::rule(label = "rekey")]
pub fn rekey(
    me: Hid,
    k::cells! {
        id: k::configuration::Cell(k::rewrite!(me => HidC::H(1))),
        k: k::configuration::KCell(k::rewrite!(lib::Op::Inc() => ()), ..),
        state @ ..
    }: Unit,
) {}
"#;

/// A configuration whose computation cell is each instance's key.
const KEY_MAIN: &str = r#"
use k::builtin::{Int, KSequence};

#[k::cell]
pub struct Cpus {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub cpu: Cpu,
}

#[k::cell]
pub struct Cpu {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub n: Int,
}

#[k::configuration]
pub struct Pool {
    #[k::cell(nested)]
    pub cpus: Cpus,
}

impl Pool {
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {
        Self {
            cpus: Cpus {
                cpu: Cpu { k: k::k![pgm], n: 0 },
            },
        }
    }
}
"#;

/// The outcome of `krs check` on each case: its name, then each diagnostic's
/// headline, location and help. A case is its name, the source of its one
/// package beside `lib` and that package's name; the holder cases take the
/// library's rules for `Hart`, in each spelling.
fn instance_outcomes(cases: &[(&str, String, &str)]) -> Vec<Vec<String>> {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    cases
        .iter()
        .map(|(name, source, package)| {
            let lib_rules = match *name {
                "set" | "list" => HART_RULES,
                "set-cells" | "list-cells" => HART_CELLS_RULES,
                _ => "",
            };
            let manifest = instance_definitions(
                &temporary.path().join(name),
                lib_rules,
                &[(package, source)],
            )
            .remove(0);
            let mut report = vec![(*name).to_owned()];
            report.extend(check_report(target.path(), &manifest, package));
            report
        })
        .collect()
}

/// The cases of
/// [`a_sentence_about_one_instance_is_refused_where_its_meaning_does_not_hold`],
/// as [`instance_outcomes`] takes them.
fn meaning_cases() -> Vec<(&'static str, String, &'static str)> {
    vec![
        ("set", smp("Set", ""), "smp"),
        ("set-cells", smp("Set", ""), "smp"),
        ("list", smp("List", ""), "smp"),
        ("list-cells", smp("List", ""), "smp"),
        ("key", smp("Map", KEY_CHANGE_RULE), "smp"),
        ("key-cells", smp("Map", KEY_CHANGE_CELLS_RULE), "smp"),
        ("holder", smp("Map", HOLDER_RULE), "smp"),
        ("holder-cells", smp("Map", HOLDER_CELLS_RULE), "smp"),
        ("inner-flat", cores(INNER_FLAT_RULE), "many"),
        ("inner-flat-cells", cores(INNER_FLAT_CELLS_RULE), "many"),
        (
            "caller",
            smp("Map", &format!("{PC_PLUS}{SMP_CALLER}")),
            "smp",
        ),
        (
            "caller-cells",
            smp("Map", &format!("{PC_PLUS}{SMP_CELLS_CALLER}")),
            "smp",
        ),
        (
            "caller-through",
            smp("Map", &format!("{PC_PLUS}{VIA_PC}")),
            "smp",
        ),
        ("set-main", SET_MAIN.to_owned(), "pool"),
        (
            "initializer",
            smp("Map", PC_PLUS).replace("pc: 0 },", "pc: crate::PcPlus(0) },"),
            "smp",
        ),
    ]
}

/// The refusals of a sentence about one instance that its meaning gives,
/// each in both spellings where both exist (readable first), with its code,
/// its reason and where it points:
/// - a group in a Set or a List collection is `group-subject-position`, with
///   the Set's reason (a stepped instance merges with an equal one) and the
///   List's gap (an instance at any position is not matched yet);
/// - a written Map key other than the matched one is `map-collection-key`;
/// - the cell holding the group is `cell-outside-subject`;
/// - a cell of a collection inside the instance, named flat, is
///   `collection-entry`, whose advice names that inner holder;
/// - a function whose context reads one hart, applied by a rule for the
///   configuration, directly or through a function without a context of its
///   own, is `instance-context-caller`, at the application;
/// - a main cell inside a Set instance is `main-cell`;
/// - the initializer, which builds the configuration and so is evaluated in
///   no hart, applying that function is `instance-context-caller`, at the
///   application.
#[test]
fn a_sentence_about_one_instance_is_refused_where_its_meaning_does_not_hold() {
    let outcomes = instance_outcomes(&meaning_cases());
    expect_test::expect![[r#"
        [
            [
                "set",
                "error[krs::analysis::group-subject-position]: the cell group `Hart` is held by the Set collection cell `hart` of configuration `Smp`: a sentence about `Hart` is about one instance, which a rule rewrites as a local step, and a Set identifies an instance by its whole content, so a step that makes one instance equal to another merges the two, removing an instance the rule never matched; write the sentence for `Smp`, or hold the instances in a Map collection keyed by an id",
                "--> lib/src/lib.rs: `Hart;`",
            ],
            [
                "set-cells",
                "error[krs::analysis::group-subject-position]: the cell group `Hart` is held by the Set collection cell `hart` of configuration `Smp`: a sentence about `Hart` is about one instance, which a rule rewrites as a local step, and a Set identifies an instance by its whole content, so a step that makes one instance equal to another merges the two, removing an instance the rule never matched; write the sentence for `Smp`, or hold the instances in a Map collection keyed by an id",
                "--> lib/src/lib.rs: `Hart,`",
            ],
            [
                "list",
                "error[krs::analysis::group-subject-position]: the cell group `Hart` is held by the List collection cell `hart` of configuration `Smp`: a sentence about `Hart` is about one instance, which in a List is the instance at any position, and matching one instance between others is not supported yet; write the sentence for `Smp`, or hold the instances in a Map collection keyed by an id",
                "--> lib/src/lib.rs: `Hart;`",
            ],
            [
                "list-cells",
                "error[krs::analysis::group-subject-position]: the cell group `Hart` is held by the List collection cell `hart` of configuration `Smp`: a sentence about `Hart` is about one instance, which in a List is the instance at any position, and matching one instance between others is not supported yet; write the sentence for `Smp`, or hold the instances in a Map collection keyed by an id",
                "--> lib/src/lib.rs: `Hart,`",
            ],
            [
                "key",
                "error[krs::analysis::map-collection-key]: the rule writes `id`, the key of the instance of the Map collection `hart` it is about: a rule for `Hart` is a local step of one instance, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> smp/src/lib.rs: `k::builtin::int:`",
            ],
            [
                "key-cells",
                "error[krs::analysis::map-collection-key]: the rule writes `id`, the key of the instance of the Map collection `hart` it is about: a rule for `Hart` is a local step of one instance, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> smp/src/lib.rs: `k::configuration`",
            ],
            [
                "holder",
                "error[krs::analysis::cell-outside-subject]: `Hart` has no cell `hart`: a sentence about the cell group `Hart` names only the cells inside the group, and `hart` is the cell of configuration `Smp` that holds the group; write the sentence for `Smp` to name it",
                "--> smp/src/lib.rs: `hart } => { k: [`",
            ],
            [
                "holder-cells",
                "error[krs::analysis::cell-outside-subject]: `Hart` has no cell `Harts::hart`: a sentence about the cell group `Hart` names only the cells inside the group, and `Harts::hart` is the cell of configuration `Smp` that holds the group; write the sentence for `Smp` to name it",
                "--> smp/src/lib.rs: `hart: { me @ k::`",
            ],
            [
                "inner-flat",
                "error[krs::analysis::collection-entry]: the cell `payload` is a cell of a collection's (`*`) instance, so no single cell has the content an entry naming it at the record's level would name: there is one `payload` per instance, and an entry names the instance through its instance record; `payload` is a cell of an instance of the collection `job`; so write the entry inside its record, `job: [Job { payload: .., .. }, ..]`",
                "--> many/src/lib.rs: `payload } => { k`",
            ],
            [
                "inner-flat-cells",
                "error[krs::analysis::collection-entry]: the cell `payload` is a cell of a collection's (`*`) instance, so no single cell has the content an entry naming it at the record's level would name: there is one `payload` per instance, and an entry names the instance through its instance record; `payload` is a cell of an instance of the collection `job`; so write the entry inside its record, `job: [k::fragment![crate::Job { payload: .., .. }], ..]`",
                "--> many/src/lib.rs: `k::configuration`",
            ],
            [
                "caller",
                "error[krs::analysis::instance-context-caller]: `PcPlus` reads the cell group `Hart` through its function context in one instance of the Map collection cell `hart`, the instance it is evaluated in, and this sentence is not inside such an instance, so it determines none: a function has one value for its arguments, so it is applied only from a sentence about one instance of that holder (a rule, a context alias or a function context for the group, or for a group inside its instance)",
                "--> smp/src/lib.rs: `crate::PcPlus(1)`",
            ],
            [
                "caller-cells",
                "error[krs::analysis::instance-context-caller]: `PcPlus` reads the cell group `Hart` through its function context in one instance of the Map collection cell `hart`, the instance it is evaluated in, and this sentence is not inside such an instance, so it determines none: a function has one value for its arguments, so it is applied only from a sentence about one instance of that holder (a rule, a context alias or a function context for the group, or for a group inside its instance)",
                "--> smp/src/lib.rs: `crate::PcPlus(1)`",
            ],
            [
                "caller-through",
                "error[krs::analysis::instance-context-caller]: `ViaPc` applies `PcPlus`, which reads the cell group `Hart` through its function context in one instance of the Map collection cell `hart`, the instance it is evaluated in, and this sentence is not inside such an instance, so it determines none: a function has one value for its arguments, so it is applied only from a sentence about one instance of that holder (a rule, a context alias or a function context for the group, or for a group inside its instance)",
                "--> smp/src/lib.rs: `crate::ViaPc(1)`",
            ],
            [
                "set-main",
                "error[krs::analysis::main-cell]: the computation cell `k` sits in an instance of the Set collection cell `obj` of configuration `Pool`: a sentence that names no cell (a term rule, a context, a strict production's heating) runs at the computation cell, so it is a local step of the instance that holds it, and a Set identifies an instance by its whole content, so a step that makes that instance equal to another merges the two, removing an instance the step never touched; hold the instances in a Map collection keyed by an id",
                "--> pool/src/lib.rs: `obj: Obj,`",
            ],
            [
                "initializer",
                "error[krs::analysis::instance-context-caller]: `PcPlus` reads the cell group `Hart` through its function context in one instance of the Map collection cell `hart`, the instance it is evaluated in, and the initializer builds the configuration, so it is evaluated in no instance and determines none: a function has one value for its arguments, so it is applied only from a sentence about one instance of that holder (a rule, a context alias or a function context for the group, or for a group inside its instance)",
                "--> smp/src/lib.rs: `crate::PcPlus(0)`",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// The library's function whose context reads the hart's `pc`, `pcPlus(n)`,
/// and one without a context of its own that applies it, `viaPc(n)`; the
/// library holds [`HART_RULES`] beside them.
const LIB_PC_PLUS: &str = r#"
use k::Term;

/// The program counter of the hart it is evaluated in, plus `n`.
#[k::function(total, sort = Int, syntax = "pcPlus ( {n} )")]
pub struct PcPlus {
    pub n: Term<Int>,
}

#[k::equation]
fn pc_plus(
    n: Term<Int>,
    p: Term<Int>,
    k::term![PcPlus(n)]: Term<Int>,
    k::cells! {
        pc: k::configuration::Cell(p),
        ..
    }: Hart,
) -> Term<Int> {
    k::builtin::int::add(p, n)
}

#[k::function(total, sort = Int, syntax = "viaPc ( {n} )")]
pub struct ViaPc {
    pub n: Term<Int>,
}

#[k::equation]
fn via_pc(n: Term<Int>, k::term![ViaPc(n)]: Term<Int>) -> Term<Int> {
    PcPlus(n)
}
"#;

/// Instructions and rules for `lib::Hart` that apply the library's functions:
/// `jump` leaves the key out, `hop` restates it as its binder `me` and
/// `tock` as the literal `1`.
const HART_JUMPS: &str = r#"
#[k::constructors(sort = lib::Instr, result = k::KResult)]
#[rustfmt::skip]
pub enum Far {
    #[k::syntax("jump")] Jump(),
    #[k::syntax("hop")] Hop(),
    #[k::syntax("tock")] Tock(),
    #[k::syntax("start")] Start(),
}

k::rules! {
    for lib::Hart;
    use Far::*;

    jump: { k: [Jump(), ..], pc } => { k: [..], pc: lib::PcPlus(100) };
    hop: { id: me, k: [Hop(), ..], pc } => { id: me, k: [..], pc: lib::ViaPc(1000) };
    tock: { id: 1, k: [Tock(), ..], pc } => { id: 1, k: [..], pc: lib::PcPlus(1) };
}
"#;

/// A rule for `holder` that starts a second hart keyed `1` at `pc` 10 beside
/// the first: the first runs `jump ; hop`, the second `jump ; hop ; tock`.
fn start_rule(holder: &str) -> String {
    format!(
        r"
k::rules! {{
    for {holder};
    use Far::*;

    start: {{
        hart: {{ me @ lib::Hart {{ k: [Start(), ..], .. }}, .. }},
    }} => {{
        hart: {{ lib::Hart {{ k: [Jump(), Hop(), ..], ..me }}, lib::Hart {{ id: 1, k: [Jump(), Hop(), Tock()], pc: 10 }}, .. }},
    }};
}}
"
    )
}

/// A configuration whose instances are clusters keyed by `cid`, each holding a
/// Map collection of harts, starting with one cluster and one hart, with
/// `rules` appended.
fn clusters(rules: &str) -> String {
    format!(
        r#"
use k::builtin::Int;

#[k::cell]
pub struct Clusters {{
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub cluster: Cluster,
}}

#[k::cell]
pub struct Cluster {{
    #[k::cell]
    pub cid: Int,
    #[k::cell(nested)]
    pub harts: Harts,
}}

#[k::cell]
pub struct Harts {{
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub hart: lib::Hart,
}}

#[k::configuration]
pub struct Board {{
    #[k::cell(nested)]
    pub clusters: Clusters,
}}

impl Board {{
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {{
        Self {{
            clusters: Clusters {{
                cluster: Cluster {{
                    cid: 0,
                    harts: Harts {{ hart: lib::Hart {{ id: 0, k: k::k![pgm], pc: 0 }} }},
                }},
            }},
        }}
    }}
}}

{rules}
"#
    )
}

/// The emitted sentences that start with each of `starts`, the harts of the
/// end state of `krs run` of `start`, and the number of final states `krs
/// search --mode final` finds with their harts, each whitespace-flattened.
fn jumps(
    target: &Path,
    manifest: &Path,
    package: &str,
    starts: &[&str],
) -> (Vec<String>, Vec<String>, (usize, Vec<String>)) {
    let flat = emitted(target, manifest, package);
    let sentences = starts
        .iter()
        .map(|start| sentence(&flat, start).to_owned())
        .collect();
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "start").unwrap();
    let program = program.to_str().unwrap();
    let whitespace = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    let (success, stdout, stderr) = krs_on(target, manifest, package, "run", &[program]);
    assert!(success, "{stdout}\n{stderr}");
    let run = harts(&whitespace(&stdout));
    let (success, stdout, stderr) = krs_on(
        target,
        manifest,
        package,
        "search",
        &[program, "--mode", "final"],
    );
    assert!(success, "{stdout}\n{stderr}");
    // Each final state holds one `<harts>`, in `smp` and in `board`'s one cluster.
    let searched = whitespace(&stdout);
    let searched = (searched.matches("<harts> ").count(), harts(&searched));
    (sentences, run, searched)
}

/// A library function whose context reads the hart's `pc`, applied by rules
/// for the hart in `smp`, has one value per hart: it receives the hart's key
/// `id` after its own argument (`#instance ( Int )`), its equation's context
/// matches the hart with that key, and each rule passes its own hart's key:
/// the binder or literal its subject matches `id` with, or a key cell KRS adds
/// (`jump`), as does a `for Instr` clause, which runs at the main cell inside
/// the hart (`skip`). `viaPc`, without a context of its own, receives the key
/// and passes it on. Two harts at different program counters each read their own:
/// hart 0 from 0 ends at `0 + 100 + 1000`, hart 1 from 10 at
/// `10 + 100 + 1000 + 1`, and every interleaving reaches that one final state.
#[test]
fn a_function_context_reads_the_instance_it_is_evaluated_in() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = instance_definitions(
        temporary.path(),
        &format!("{HART_RULES}{LIB_PC_PLUS}"),
        &[(
            "smp",
            &smp(
                "Map",
                &format!("{HART_JUMPS}{}{PADS}{SKIP_RULE}", start_rule("Smp")),
            ),
        )],
    )
    .remove(0);
    let outcome = jumps(
        target.path(),
        &manifest,
        "smp",
        &[
            "syntax Int ::= \"pcPlus\"",
            "syntax Int ::= \"viaPc\"",
            "rule [[ pcPlus",
            "rule viaPc",
            "rule [jump]:",
            "rule [hop]:",
            "rule [tock]:",
            "rule [skip]:",
        ],
    );
    expect_test::expect![[r##"
        (
            [
                "syntax Int ::= \"pcPlus\" \"(\" Int \")\" \"#instance\" \"(\" Int \")\" [symbol(pcPlus), function, total]",
                "syntax Int ::= \"viaPc\" \"(\" Int \")\" \"#instance\" \"(\" Int \")\" [symbol(viaPc), function, total]",
                "rule [[ pcPlus ( N:Int ) #instance ( Krs_KeyHart:Int ) => P:Int +Int N:Int ]] <hart> <pc> P:Int </pc> <id> Krs_KeyHart:Int </id> ... </hart> [label(org_krs_groups_lib--pc_plus)]",
                "rule viaPc ( N:Int ) #instance ( Krs_KeyHart:Int ) => pcPlus ( N:Int ) #instance ( Krs_KeyHart:Int ) [label(org_krs_groups_lib--via_pc)]",
                "rule [jump]: <hart> <k> jump => .K ... </k> <pc> Pc:Int => pcPlus ( 100 ) #instance ( Krs_KeyHart:Int ) </pc> <id> Krs_KeyHart:Int </id> ... </hart>",
                "rule [hop]: <hart> <k> hop => .K ... </k> <id> Me:Int </id> <pc> Pc:Int => viaPc ( 1000 ) #instance ( Me:Int ) </pc> ... </hart>",
                "rule [tock]: <hart> <k> tock => .K ... </k> <id> 1 </id> <pc> Pc:Int => pcPlus ( 1 ) #instance ( 1 ) </pc> ... </hart>",
                "rule [skip]: <hart> <k> skip ( N:Int ) => pad ( pcPlus ( N:Int ) #instance ( Krs_KeyHart:Int ) ) ... </k> <id> Krs_KeyHart:Int </id> ... </hart>",
            ],
            [
                "<id> 0 </id> <k> .K </k> <pc> 1100 </pc>",
                "<id> 1 </id> <k> .K </k> <pc> 1111 </pc>",
            ],
            (
                1,
                [
                    "<id> 0 </id> <k> .K </k> <pc> 1100 </pc>",
                    "<id> 1 </id> <k> .K </k> <pc> 1111 </pc>",
                ],
            ),
        )
    "##]].assert_debug_eq(&outcome);
}

/// Instructions `#[k::rule]` fns over a term rewrite, applying `pcPlus`.
const TAPS: &str = r#"
use k::Term;

#[k::constructors(sort = lib::Instr, result = k::KResult)]
#[rustfmt::skip]
pub enum Tap {
    #[k::syntax("tap ( {n} )")] Tap { n: Int },
    #[k::syntax("tapped ( {n} )")] Tapped { n: Int },
    #[k::syntax("mark ( {s} , {n} )")] Mark { s: Int, n: Int },
}

/// A term rule, which runs at the head of the main cell.
#[k::rule(label = "tap")]
fn tap(k::term![Tap::Tap { n }]: Term<lib::Instr>) -> Term<lib::Instr> {
    Tap::Tapped { n: lib::PcPlus(n) }
}

/// A single-body term rule, which rewrites its subject in place.
#[k::rule(label = "mark")]
fn mark(k::term![Tap::Mark { s: k::rewrite!(0 => 1), n: k::rewrite!(n => lib::PcPlus(n)) }]: Term<lib::Instr>) {}
"#;

/// A simplification that names `pcPlus` only in its left-hand side.
const SAME_SIMPLIFICATION: &str = r"
use k::Term;

#[k::simplification]
fn same(k::term![k::builtin::int::sub(lib::PcPlus(n), lib::PcPlus(n))]: Term<Int>) -> Term<Int> {
    0
}
";

/// A `#[k::rule]` fn over a term that is not `anywhere` runs at the head of
/// the main cell, which sits in a hart, so it is about that hart, as a `for
/// Instr` clause is: it is written as the main cell's clause beside the key
/// cell KRS adds, and passes the hart's key, in both the two-sided and the
/// single-body form. With the hart at `pc` 3, `tap(5)` ends as `tapped(8)` and
/// `mark(0, 5)` as `mark(1, 8)`.
#[test]
fn a_term_rule_at_the_main_cell_passes_the_key_of_its_instance() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = instance_definitions(
        temporary.path(),
        &format!("{HART_RULES}{LIB_PC_PLUS}"),
        &[("smp", &smp("Map", TAPS).replace("pc: 0 },", "pc: 3 },"))],
    )
    .remove(0);
    let flat = emitted(target.path(), &manifest, "smp");
    let sentences = ["rule [tap]:", "rule [mark]:"].map(|start| sentence(&flat, start).to_owned());
    let whitespace = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    let ends = ["tap ( 5 )", "mark ( 0 , 5 )"].map(|program| {
        let path = manifest.with_file_name("program.txt");
        fs::write(&path, program).unwrap();
        let (success, stdout, stderr) = krs_on(
            target.path(),
            &manifest,
            "smp",
            "run",
            &[path.to_str().unwrap()],
        );
        assert!(success, "{stdout}\n{stderr}");
        harts(&whitespace(&stdout))
    });
    expect_test::expect![[r#"
        (
            [
                "rule [tap]: <hart> <k> tap ( N:Int ) => tapped ( pcPlus ( N:Int ) #instance ( Krs_KeyHart:Int ) ) ... </k> <id> Krs_KeyHart:Int </id> ... </hart>",
                "rule [mark]: <hart> <k> mark ( (0 => 1) , (N:Int => pcPlus ( N:Int ) #instance ( Krs_KeyHart:Int )) ) ... </k> <id> Krs_KeyHart:Int </id> ... </hart>",
            ],
            [
                [
                    "<id> 0 </id> <k> tapped ( 8 ) ~> .K </k> <pc> 3 </pc>",
                ],
                [
                    "<id> 0 </id> <k> mark ( 1 , 8 ) ~> .K </k> <pc> 3 </pc>",
                ],
            ],
        )
    "#]].assert_debug_eq(&(sentences, ends));
}

/// A simplification rewrites wherever its left-hand side occurs, so it passes
/// the keys its left-hand side's applications receive: both applications of
/// `pcPlus` it matches share one key variable, so it states a fact about the
/// two applications in one hart.
#[test]
fn a_simplification_passes_the_key_its_left_hand_side_matches() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = instance_definitions(
        temporary.path(),
        &format!("{HART_RULES}{LIB_PC_PLUS}"),
        &[("smp", &smp("Map", SAME_SIMPLIFICATION))],
    )
    .remove(0);
    let flat = emitted(target.path(), &manifest, "smp");
    expect_test::expect!["rule pcPlus ( N:Int ) #instance ( Krs_KeyHart:Int ) -Int pcPlus ( N:Int ) #instance ( Krs_KeyHart:Int ) => 0 [simplification, label(org_krs_groups_smp--same)]"].assert_eq(sentence(&flat, "rule pcPlus ( N:Int ) #instance"));
}

/// In a Map collection of harts inside each instance of a Map collection of
/// clusters, the library's function receives both keys, the cluster's first:
/// its equation's context matches the hart with its key inside the cluster
/// with its key, and a rule for the hart passes its cluster's key from a key
/// cell KRS adds in the cluster's cell, around the hart's. The two harts of a
/// cluster each read their own program counter.
#[test]
fn a_function_context_in_a_nested_collection_receives_every_enclosing_key() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = instance_definitions(
        temporary.path(),
        &format!("{HART_RULES}{LIB_PC_PLUS}"),
        &[(
            "board",
            &clusters(&format!("{HART_JUMPS}{}", start_rule("Cluster"))),
        )],
    )
    .remove(0);
    let outcome = jumps(
        target.path(),
        &manifest,
        "board",
        &[
            "syntax Int ::= \"pcPlus\"",
            "rule [[ pcPlus",
            "rule [jump]:",
            "rule [hop]:",
        ],
    );
    expect_test::expect![[r##"
        (
            [
                "syntax Int ::= \"pcPlus\" \"(\" Int \")\" \"#instance\" \"(\" Int \",\" Int \")\" [symbol(pcPlus), function, total]",
                "rule [[ pcPlus ( N:Int ) #instance ( Krs_KeyCluster:Int , Krs_KeyHart:Int ) => P:Int +Int N:Int ]] <cluster> <cid> Krs_KeyCluster:Int </cid> <hart> <pc> P:Int </pc> <id> Krs_KeyHart:Int </id> ... </hart> ... </cluster> [label(org_krs_groups_lib--pc_plus)]",
                "rule [jump]: <cluster> <cid> Krs_KeyCluster:Int </cid> <hart> <k> jump => .K ... </k> <pc> Pc:Int => pcPlus ( 100 ) #instance ( Krs_KeyCluster:Int , Krs_KeyHart:Int ) </pc> <id> Krs_KeyHart:Int </id> ... </hart> ... </cluster>",
                "rule [hop]: <cluster> <cid> Krs_KeyCluster:Int </cid> <hart> <k> hop => .K ... </k> <id> Me:Int </id> <pc> Pc:Int => viaPc ( 1000 ) #instance ( Krs_KeyCluster:Int , Me:Int ) </pc> ... </hart> ... </cluster>",
            ],
            [
                "<id> 0 </id> <k> .K </k> <pc> 1100 </pc>",
                "<id> 1 </id> <k> .K </k> <pc> 1111 </pc>",
            ],
            (
                1,
                [
                    "<id> 0 </id> <k> .K </k> <pc> 1100 </pc>",
                    "<id> 1 </id> <k> .K </k> <pc> 1111 </pc>",
                ],
            ),
        )
    "##]].assert_debug_eq(&outcome);
}

/// `faPlus(n)`, whose context reads the unit's `fa`.
const FA_PLUS_EQUATION: &str = r#"
use k::Term;

#[k::function(total, sort = Int, syntax = "faPlus({n})")]
pub struct FaPlus {
    pub n: Term<Int>,
}

#[k::equation]
fn fa_plus(
    n: Term<Int>,
    a: Term<Int>,
    k::term![FaPlus(n)]: Term<Int>,
    k::cells! {
        fa: k::configuration::Cell(a),
        ..
    }: lib::Fpu,
) -> Term<Int> {
    k::builtin::int::add(a, n)
}
"#;

/// A rule for the unit that applies `faPlus`, whose context reads its `fa`.
const FPU_CALLER: &str = r"
k::rules! {
    for lib::Fpu;

    finish: { busy: 1, fa } => { busy: 0, fa: crate::FaPlus(1) };
}
";

/// An optional cell holds at most one instance, so a function whose context
/// reads the optional unit receives no key: its context is read inside the
/// unit's cell.
#[test]
fn a_function_context_in_an_optional_cell_is_read_inside_it() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = instance_definitions(
        temporary.path(),
        "",
        &[("opt", &opt(&format!("{FA_PLUS_EQUATION}{FPU_CALLER}")))],
    )
    .remove(0);
    let (success, _, stderr) = krs_on(target.path(), &manifest, "opt", "check", &[]);
    assert!(success, "{stderr}");
    let flat = emitted(target.path(), &manifest, "opt");
    let sentences = [
        "syntax Int ::= \"faPlus\"",
        "rule [[ faPlus",
        "rule [finish]:",
    ]
    .map(|start| sentence(&flat, start).to_owned());
    expect_test::expect![[r#"
        [
            "syntax Int ::= \"faPlus\" \"(\" Int \")\" [symbol(faPlus), function, total]",
            "rule [[ faPlus ( N:Int ) => A:Int +Int N:Int ]] <fpu> <fa> A:Int </fa> ... </fpu> [label(org_krs_groups_opt--fa_plus)]",
            "rule [finish]: <fpu> <busy> 1 => 0 </busy> <fa> Fa:Int => faPlus ( 1 ) </fa> ... </fpu>",
        ]
    "#]].assert_debug_eq(&sentences);
}

/// The refusal cases' marker for a library of [`HART_RULES`] and [`LIB_PC_PLUS`].
const LIB_LIBRARY: &str = "library";

/// Instructions a rule for `Instr` rewrites, applying `pcPlus`.
const PADS: &str = r#"
#[k::constructors(sort = lib::Instr, result = k::KResult)]
#[rustfmt::skip]
pub enum Pad {
    #[k::syntax("skip ( {n} )")] Skip { n: Int },
    #[k::syntax("pad ( {n} )")] Padded { n: Int },
}
"#;

/// A `for Instr` clause, which runs at the head of the computation cell, the
/// main cell, inside a hart.
const SKIP_RULE: &str = r"
k::rules! {
    for lib::Instr;
    use Pad::*;

    skip: Skip { n } => Padded { n: lib::PcPlus(n) };
}
";

/// An `anywhere` rule, which rewrites wherever its left-hand side occurs.
const ANYWHERE_SKIP: &str = r#"
use k::Term;

#[k::rule(anywhere, label = "skip")]
fn skip(k::term![Pad::Skip { n }]: Term<lib::Instr>) -> Term<lib::Instr> {
    Pad::Padded { n: lib::PcPlus(n) }
}
"#;

/// A simplification whose right-hand side applies `pcPlus`, which its
/// left-hand side does not.
const UNBOUND_SIMPLIFICATION: &str = r"
use k::Term;

#[k::simplification]
fn add_zero(k::term![k::builtin::int::add(n, 0)]: Term<Int>) -> Term<Int> {
    lib::PcPlus(n)
}
";

/// A function whose context reads a node, whose key is the group `cpu`.
const NODE_CONTEXT: &str = r#"
use k::Term;

#[k::function(total, sort = Int, syntax = "nodePc ( {n} )")]
pub struct NodePc {
    pub n: Term<Int>,
}

#[k::equation]
fn node_pc(
    n: Term<Int>,
    p: Term<Int>,
    k::term![NodePc(n)]: Term<Int>,
    k::cells! {
        Cpu::pc: k::configuration::Cell(p),
        ..
    }: Node,
) -> Term<Int> {
    k::builtin::int::add(p, n)
}
"#;

/// A term rule, written before the context it reaches, that applies
/// `nodePc` in its condition.
const NODE_CALLER: &str = r#"
#[k::rule(label = "poke")]
#[k::requires(k::builtin::int::eq(crate::NodePc(0), 0))]
fn poke(k::term![lib::Op::Tick()]: k::Term<lib::Instr>) -> k::Term<lib::Instr> {
    lib::Op::Inc()
}
"#;

/// A `#[k::context]` that names no cell, whose condition applies `pcPlus`.
const GUARDED_CONTEXT: &str = r"
use k::Term;

#[k::context(hole = n)]
#[k::requires(k::builtin::int::eq(lib::PcPlus(0), 0))]
fn skip_operand(k::term![Pad::Skip { n }]: Term<lib::Instr>) {}
";

/// A function whose context reads a unit's key, and a rule for the unit that
/// matches the key with the constructor pattern `h(n)` and applies it.
const UNIT_PROBE: &str = r#"
use k::Term;

#[k::function(total, sort = lib::Instr, syntax = "probe ( {m} )")]
pub struct Probe {
    pub m: Term<Hid>,
}

#[k::equation]
fn probe(
    m: Term<Hid>,
    k::term![Probe(m)]: Term<lib::Instr>,
    k::cells! {
        id: k::configuration::Cell(m),
        ..
    }: Unit,
) -> Term<lib::Instr> {
    lib::Op::Inc()
}

k::rules! {
    for Unit;

    look: { id: HidC::H(n), k: [lib::Op::Tick(), ..] } => { k: [crate::Probe(HidC::H(n)), ..] };
}
"#;

/// The sentences that cannot pass a function the key of the instance it is
/// evaluated in are refused, at the application or the context:
/// - an `anywhere` rule and a simplification, which rewrite wherever their
///   left-hand side occurs, whose right-hand side applies `pcPlus` while their
///   left-hand side applies nothing that receives the key, so they determine
///   no instance (`instance-context-caller`);
/// - a context in a Map collection keyed by a group of cells: passing such a
///   key is not emitted yet (`group-subject-position`), refused at the
///   context whichever sentence passes the key first;
/// - a rule that matches its key cell with a constructor pattern, so no one
///   term of it is the key it passes (`group-subject-position`, at the
///   pattern).
/// - a `#[k::context]` that names no cell, which runs at the main cell inside
///   the hart but is K's `context`, which binds no key cell: passing the key
///   from it is not emitted yet (`group-subject-position`, at the
///   application).
#[test]
fn a_sentence_that_cannot_pass_an_instance_key_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let outcomes = [
        (
            "anywhere",
            LIB_LIBRARY,
            smp("Map", &format!("{PADS}{ANYWHERE_SKIP}")),
            "smp",
        ),
        (
            "simplification",
            LIB_LIBRARY,
            smp("Map", UNBOUND_SIMPLIFICATION),
            "smp",
        ),
        (
            "group-key",
            "",
            composite(&format!("{NODE_CALLER}{NODE_CONTEXT}")),
            "grid",
        ),
        ("key-pattern", "", tagged(UNIT_PROBE), "tagged"),
        (
            "context",
            LIB_LIBRARY,
            smp("Map", &format!("{PADS}{GUARDED_CONTEXT}")),
            "smp",
        ),
    ]
    .iter()
    .map(|(name, lib_rules, source, package)| {
        let lib_rules = if *lib_rules == LIB_LIBRARY {
            format!("{HART_RULES}{LIB_PC_PLUS}")
        } else {
            String::new()
        };
        let manifest = instance_definitions(
            &temporary.path().join(name),
            &lib_rules,
            &[(package, source)],
        )
        .remove(0);
        let mut report = vec![(*name).to_owned()];
        report.extend(check_report(target.path(), &manifest, package));
        report
    })
    .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            [
                "anywhere",
                "error[krs::analysis::instance-context-caller]: `PcPlus` is evaluated in one instance of the Map collection cell `hart` (its function context reads that instance, or the context of a function it applies does), so it receives that instance's key `id`, and this sentence rewrites wherever its left-hand side matches (a simplification, an `anywhere` rule, a desugar), which applies no function receiving that key, so it determines no instance: a function has one value for its arguments, so such a sentence applies it only where its left-hand side applies a function evaluated in the same instance",
                "--> smp/src/lib.rs: `lib::PcPlus(n) }`",
            ],
            [
                "simplification",
                "error[krs::analysis::instance-context-caller]: `PcPlus` is evaluated in one instance of the Map collection cell `hart` (its function context reads that instance, or the context of a function it applies does), so it receives that instance's key `id`, and this sentence rewrites wherever its left-hand side matches (a simplification, an `anywhere` rule, a desugar), which applies no function receiving that key, so it determines no instance: a function has one value for its arguments, so such a sentence applies it only where its left-hand side applies a function evaluated in the same instance",
                "--> smp/src/lib.rs: `lib::PcPlus(n)`",
            ],
            [
                "group-key",
                "error[krs::analysis::group-subject-position]: the instances of the Map collection cell `node` are keyed by `cpu`, a group of cells, and a function evaluated in one of them receives that instance's key: passing a key that is a group of cells is not emitted yet; key the instances by a leaf cell, declared first",
                "--> grid/src/lib.rs: `Node,`",
            ],
            [
                "key-pattern",
                "error[krs::analysis::group-subject-position]: the sentence matches `id`, the key of the instances of the Map collection cell `unit`, with a pattern that is no variable, literal or `_`, and passes that key to a function evaluated in its instance, so no one term of the pattern is the key it passes; bind the key to a variable and test it in the condition",
                "--> tagged/src/lib.rs: `HidC::H(n), k: [`",
            ],
            [
                "context",
                "error[krs::analysis::group-subject-position]: `PcPlus` is evaluated in one instance of the Map collection cell `hart` (its function context reads that instance, or the context of a function it applies does), so it receives that instance's key `id`, and this context names no cell: it runs at the main cell, inside that instance, but it is emitted as K's `context`, which binds no key cell, so passing the instance's key from it is not emitted yet; write it as a context alias typed by the cell group, which names the instance's cells",
                "--> smp/src/lib.rs: `lib::PcPlus(0),`",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// A function evaluated in one hart, of the program's sort.
const AT_PC: &str = r#"
use k::Term;

#[k::function(partial, sort = lib::Instr, syntax = "atPc ( {n} )")]
pub struct AtPc {
    pub n: Term<Int>,
}

#[k::equation]
fn at_pc(
    n: Term<Int>,
    k::term![AtPc(n)]: Term<lib::Instr>,
    k::cells! {
        pc: k::configuration::Cell(n),
        ..
    }: lib::Hart,
) -> Term<lib::Instr> {
    lib::Op::Inc()
}
"#;

/// An input is evaluated in no instance, so `$call` of a function that
/// receives an instance's key is refused with the reason.
#[test]
fn an_input_does_not_apply_a_function_evaluated_in_an_instance() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest =
        instance_definitions(temporary.path(), "", &[("smp", &smp("Map", AT_PC))]).remove(0);
    let (success, stdout, stderr) = krs_on(
        target.path(),
        &manifest,
        "smp",
        "run",
        &["--input", r#"pgm={"$call": {"AtPc": [0]}}"#, "--depth", "0"],
    );
    assert!(!success, "{stdout}");
    expect_test::expect!["error[krs::exec::variable]: input `pgm` (Instr): `$call`: `smp::AtPc` is evaluated in one instance of the Map collection cell `hart` (its function context reads that instance, or the context of a function it applies does), so it receives the instance's key, and an input is evaluated in no instance: a function has one value for its arguments, so it is applied only from a sentence about one instance"].assert_eq(stderr.trim_end());
}

/// A configuration whose instances are `Cpu`s keyed by `id`, each holding a
/// group of registers, an optional reservation and a Map collection of jobs,
/// with the rules for `Cpu` that name each of them, a context alias through
/// which `wait` is strict and a `#[k::context]` that evaluates the operand of
/// `hop`; `here` is the instance's own program counter.
const CPUS: &str = r#"
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Exp;
    Value: Exp + k::KResult;
    impl Value for Int;
}

#[k::constructors(sort = lib::Instr, result = k::KResult)]
#[k::precedence(right (Seq))]
pub enum Code {
    #[k::syntax("{first} ; {second}")]
    Seq { first: lib::Instr, second: lib::Instr },
}

#[k::constructors(sort = lib::Instr, result = k::KResult)]
#[rustfmt::skip]
pub enum CpuOp {
    #[k::syntax("swap")] Swap(),
    #[k::syntax("reserve")] Reserve(),
    #[k::syntax("release")] Release(),
    #[k::syntax("post")] Post(),
    #[k::syntax("work")] Work(),
    #[k::syntax("wait ( {n} )")] #[k::strict(using = cpu_eval)] Wait { n: Exp },
    #[k::syntax("hop ( {n} )")] Hop { n: Exp },
}

#[k::constructors(sort = Exp, result = k::KResult)]
pub enum Reg {
    #[k::syntax("here")]
    Here(),
}

#[k::cell]
pub struct Cpus {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub cpu: Cpu,
}

#[k::cell]
pub struct Cpu {
    #[k::cell]
    pub id: Int,
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell(nested)]
    pub regs: Regs,
    #[k::cell(multiplicity = "?")]
    pub reservation: Option<Int>,
    #[k::cell(nested)]
    pub jobs: Jobs,
}

#[k::cell]
pub struct Regs {
    #[k::cell]
    pub a: Int,
    #[k::cell]
    pub b: Int,
}

#[k::cell]
pub struct Jobs {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub job: Job,
}

#[k::cell]
pub struct Job {
    #[k::cell]
    pub jid: Int,
    #[k::cell]
    pub payload: Int,
}

#[k::configuration]
pub struct Rack {
    #[k::cell(nested)]
    pub cpus: Cpus,
}

impl Rack {
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {
        Self {
            cpus: Cpus {
                cpu: Cpu {
                    id: 0,
                    k: k::k![pgm],
                    pc: 1,
                    regs: Regs { a: 1, b: 2 },
                    reservation: k::absent!(0),
                    jobs: Jobs { job: Job { jid: 0, payload: 0 } },
                },
            },
        }
    }
}

#[k::context_alias(name = cpu_eval, here = site)]
fn cpu_eval(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        state @ ..
    }: Cpu,
) {
}

#[k::context(hole = h)]
fn hop_operand(
    h: Exp,
    k::cells! {
        k: k::configuration::KCell(CpuOp::Hop(h), ..),
        state @ ..
    }: Cpu,
) {
}

k::rules! {
    for Cpu;
    use Code::*;
    use CpuOp::*;
    use Reg::*;

    seq: { k: [Seq { first, second }, ..] } => { k: [first, second, ..] };
    swap: { k: [Swap(), ..], regs: Regs { a, b } } => { k: [..], regs: Regs { a: b, b: a } };
    reserve: { k: [Reserve(), ..], pc, reservation: None } => { k: [..], reservation: Some(pc) };
    release: { k: [Release(), ..], pc, reservation: Some(r) } => { k: [..], pc: int::add(pc, r), reservation: None };
    post: { id: me, k: [Post(), ..], job: { .. } } => { k: [..], job: { Job { jid: me, payload: 0 }, .. } };
    work: { k: [Work(), ..], job: { j @ Job { payload: p, .. }, .. } } => { k: [..], job: { Job { payload: int::add(p, 1), ..j }, .. } };
    here: { k: [Here(), ..], pc } => { k: [pc, ..] };
    wait: { k: [Wait { n }, ..], pc } => { k: [..], pc: int::add(pc, n) } where n: Int;
    hop: { k: [Hop { n }, ..], pc } => { k: [..], pc: int::add(pc, n) } where n: Int;
}
"#;

/// Every clause of a rule about one instance is emitted inside the
/// instance's cell, `<cpu> .. ... </cpu>`, with the cells of a context alias
/// and of a `#[k::context]` typed by the instance's group: a whole group child
/// (`swap`), an optional child created and deleted (`reserve`, `release`), an
/// instance record of the collection inside the instance, created and updated
/// (`post`, `work`), the alias `cpu_eval` and the context `hop_operand`. So
/// each clause matches in the one instance the sentence is about, and the one
/// cpu runs every form: from pc 1, `release` adds the reserved 1, and `wait
/// ( here )` and `hop ( here )` each double the program counter to 8.
#[test]
fn every_clause_of_a_sentence_about_one_instance_is_emitted_inside_it() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = instance_definitions(temporary.path(), "", &[("rack", CPUS)]).remove(0);
    let (success, _, stderr) = krs_on(target.path(), &manifest, "rack", "check", &[]);
    assert!(success, "{stderr}");
    let flat = emitted(target.path(), &manifest, "rack");
    let sentences = [
        "rule [swap]:",
        "rule [reserve]:",
        "rule [release]:",
        "rule [post]:",
        "rule [work]:",
        "context alias [cpuEval]:",
        "context [hop-operand]:",
    ]
    .map(|start| sentence(&flat, start).to_owned());
    let program = manifest.with_file_name("program.txt");
    fs::write(
        &program,
        "swap ; reserve ; release ; post ; work ; wait ( here ) ; hop ( here )",
    )
    .unwrap();
    let (success, stdout, stderr) = krs_on(
        target.path(),
        &manifest,
        "rack",
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{stdout}\n{stderr}");
    let end = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    let cpu = cell(&end, "cpu");
    expect_test::expect![[r#"
        (
            [
                "rule [swap]: <cpu> <k> swap => .K ... </k> (<regs> <a> A:Int </a> <b> B:Int </b> </regs> => <regs> <a> B:Int </a> <b> A:Int </b> </regs>) ... </cpu>",
                "rule [reserve]: <cpu> <k> reserve => .K ... </k> <pc> Pc:Int </pc> (.Bag => <reservation> Pc:Int </reservation>) ... </cpu>",
                "rule [release]: <cpu> <k> release => .K ... </k> <pc> Pc:Int => Pc:Int +Int R:Int </pc> (<reservation> R:Int </reservation> => .Bag) ... </cpu>",
                "rule [post]: <cpu> <k> post => .K ... </k> <id> Me:Int </id> (.Bag => <job> <jid> Me:Int </jid> <payload> 0 </payload> </job>) ... </cpu>",
                "rule [work]: <cpu> <k> work => .K ... </k> <job> <payload> P:Int => P:Int +Int 1 </payload> ... </job> ... </cpu>",
                "context alias [cpuEval]: <cpu> <k> HERE ~> Tail:K </k> ... </cpu>",
                "context [hop-operand]: <cpu> <k> hop ( HOLE:Exp ) ... </k> ... </cpu>",
            ],
            "<id> 0 </id> <k> .K </k> <pc> 8 </pc> <regs> <a> 2 </a> <b> 1 </b> </regs> .ReservationCell <jobs> <job> <jid> 0 </jid> <payload> 1 </payload> </job> </jobs>",
        )
    "#]].assert_debug_eq(&(sentences, cpu));
}

/// The forms stage 1 held behind "not emitted yet" are admitted and emitted
/// inside the instance: an instance record of a List collection inside a
/// `Core`, in both spellings, and a context alias typed by `lib::Hart` in a Map
/// collection ([`every_clause_of_a_sentence_about_one_instance_is_emitted_inside_it`]
/// runs a `#[k::context]`).
#[test]
fn a_form_inside_an_instance_is_emitted_inside_the_instance() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let emitted_forms = [
        (
            "inner-record",
            cores(INNER_RECORD_RULE),
            "many",
            "rule [work]:",
        ),
        (
            "inner-record-cells",
            cores(INNER_RECORD_CELLS_RULE),
            "many",
            "rule [work]:",
        ),
        (
            "alias",
            smp("Map", HART_ALIAS),
            "smp",
            "context alias [hartEval]:",
        ),
    ]
    .iter()
    .map(|(name, source, package, start)| {
        let manifest =
            instance_definitions(&temporary.path().join(name), "", &[(package, source)]).remove(0);
        let (success, _, stderr) = krs_on(target.path(), &manifest, package, "check", &[]);
        assert!(success, "{name}:\n{stderr}");
        let flat = emitted(target.path(), &manifest, package);
        sentence(&flat, start).to_owned()
    })
    .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "rule [work]: <core> <k> inc => .K ... </k> <jobs> <job> <payload> P:Int => P:Int +Int 1 </payload> </job> ... </jobs> ... </core>",
            "rule [work]: <core> <k> inc ~> Tail:K => .K ~> Tail:K </k> <jobs> <job> <payload> P:Int => P:Int +Int 1 </payload> </job> ... </jobs> ... </core>",
            "context alias [hartEval]: <hart> <k> HERE ~> Tail:K </k> ... </hart>",
        ]
    "#]].assert_debug_eq(&emitted_forms);
}

/// Rules for `Smp` over the harts and a library rule for each hart: `race`
/// starts a second hart keyed `1`, and both harts `store` their own id as an
/// open item `write(..)`, which the definition's `write` resolves into `mem`
/// at address 0; `ticks` starts a second hart that runs `tick`, which the
/// library restricts to the hart keyed `0` (`id: 0`).
const SMP_RACE: &str = r#"
#[k::constructors(sort = lib::Instr, result = k::KResult)]
#[rustfmt::skip]
pub enum Bus {
    #[k::syntax("race")] Race(),
    #[k::syntax("ticks")] Ticks(),
    #[k::syntax("store")] Store(),
    #[k::syntax("write ( {value} )")] Write { value: Int },
}

k::rules! {
    for lib::Hart;
    use Bus::*;

    store: { id: me, k: [Store(), ..] } => { k: [Write { value: me }, ..] };
}

k::rules! {
    for Smp;
    use Bus::*;
    use lib::Op::*;

    race: {
        hart: { me @ lib::Hart { k: [Race(), ..], .. }, .. },
    } => {
        hart: { lib::Hart { k: [Store(), ..], ..me }, lib::Hart { id: 1, k: [Store()], pc: 0 }, .. },
    };
    ticks: {
        hart: { me @ lib::Hart { k: [Ticks(), ..], .. }, .. },
    } => {
        hart: { lib::Hart { k: [Tick(), ..], ..me }, lib::Hart { id: 1, k: [Tick()], pc: 0 }, .. },
    };
    write: {
        hart: { me @ lib::Hart { k: [Write { value }, ..], .. }, .. },
        mem,
    } => {
        hart: { lib::Hart { k: [..], ..me }, .. },
        mem: map::update(mem, 0, value),
    };
}
"#;

/// Two harts that store at one address race: each hart's `store` is a local
/// step of that hart, and the definition's `write` steps over the shared
/// memory decide which store is last, so `krs search --mode final` reaches
/// both orders, `0 |-> 0` (hart 1 wrote first) and `0 |-> 1`, each with both
/// harts done. A rule restricted by `id: 0` is a step of hart 0 alone:
/// `ticks` runs `tick` in both harts, hart 0 counts two and hart 1 is stuck at
/// its `tick`, in the one final state.
#[test]
fn two_harts_race_on_a_store_and_a_rule_restricted_by_its_key_steps_one_hart() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = instance_definitions(
        temporary.path(),
        HART_RULES,
        &[("smp", &smp("Map", SMP_RACE))],
    )
    .remove(0);
    let flat = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    let finals = ["race", "ticks"].map(|text| {
        let program = manifest.with_file_name(format!("{text}.txt"));
        fs::write(&program, text).unwrap();
        let (success, stdout, stderr) = krs_on(
            target.path(),
            &manifest,
            "smp",
            "search",
            &[program.to_str().unwrap(), "--mode", "final"],
        );
        assert!(success, "{text}:\n{stdout}\n{stderr}");
        flat(&stdout)
            .split("<generatedTop> ")
            .skip(1)
            .map(|state| {
                let state = &state[..state.find(" </generatedTop>").unwrap()];
                format!("{} mem: {}", harts(state).join(" | "), cell(state, "mem"))
            })
            .collect::<Vec<_>>()
    });
    expect_test::expect![[r#"
        [
            [
                "<id> 0 </id> <k> .K </k> <pc> 0 </pc> | <id> 1 </id> <k> .K </k> <pc> 0 </pc> mem: 0 |-> 0",
                "<id> 0 </id> <k> .K </k> <pc> 0 </pc> | <id> 1 </id> <k> .K </k> <pc> 0 </pc> mem: 0 |-> 1",
            ],
            [
                "<id> 0 </id> <k> .K </k> <pc> 2 </pc> | <id> 1 </id> <k> tick ~> .K </k> <pc> 0 </pc> mem: .Map",
            ],
        ]
    "#]].assert_debug_eq(&finals);
}

/// The whole key is a Map instance's identity, so no sentence about the
/// instance writes at or inside it, in both spellings where both exist:
/// a written cell inside a composite key (`pc` inside `cpu`), a subject that
/// is the key group, and an in-place rewrite inside the key or of the whole
/// key are `map-collection-key`; a main cell that is a key is `main-cell`.
#[test]
fn a_sentence_about_one_instance_is_refused_where_it_writes_the_key() {
    let outcomes = instance_outcomes(&[
        ("inside-key", composite(INSIDE_KEY_RULE), "grid"),
        ("inside-key-cells", composite(INSIDE_KEY_CELLS_RULE), "grid"),
        ("key-group", composite(KEY_GROUP_RULE), "grid"),
        ("key-group-cells", composite(KEY_GROUP_CELLS_RULE), "grid"),
        (
            "key-rewrite-inside-cells",
            tagged(KEY_REWRITE_INSIDE),
            "tagged",
        ),
        (
            "key-rewrite-whole-cells",
            tagged(KEY_REWRITE_WHOLE),
            "tagged",
        ),
        ("key-main", KEY_MAIN.to_owned(), "pool"),
    ]);
    expect_test::expect![[r#"
        [
            [
                "inside-key",
                "error[krs::analysis::map-collection-key]: the rule writes `pc`, a cell inside the key `cpu`, of the instance of the Map collection `node` it is about: a rule for `Node` is a local step of one instance, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> grid/src/lib.rs: `k::builtin::int:`",
            ],
            [
                "inside-key-cells",
                "error[krs::analysis::map-collection-key]: the rule writes `pc`, a cell inside the key `cpu`, of the instance of the Map collection `node` it is about: a rule for `Node` is a local step of one instance, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> grid/src/lib.rs: `k::configuration`",
            ],
            [
                "key-group",
                "error[krs::analysis::map-collection-key]: the cell group `Cpu` is the key `cpu` of the instances of the Map collection `node`, or lies inside it: the whole key is an instance's identity, which no step of the instance changes, so a sentence about `Cpu` would be about an identity; match the key from a sentence about the instance or the configuration",
                "--> grid/src/lib.rs: `Cpu;`",
            ],
            [
                "key-group-cells",
                "error[krs::analysis::map-collection-key]: the cell group `Cpu` is the key `cpu` of the instances of the Map collection `node`, or lies inside it: the whole key is an instance's identity, which no step of the instance changes, so a sentence about `Cpu` would be about an identity; match the key from a sentence about the instance or the configuration",
                "--> grid/src/lib.rs: `Cpu,`",
            ],
            [
                "key-rewrite-inside-cells",
                "error[krs::analysis::map-collection-key]: the rule writes `id`, the key of the instance of the Map collection `unit` it is about: a rule for `Unit` is a local step of one instance, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> tagged/src/lib.rs: `k::configuration`",
            ],
            [
                "key-rewrite-whole-cells",
                "error[krs::analysis::map-collection-key]: the rule writes `id`, the key of the instance of the Map collection `unit` it is about: a rule for `Unit` is a local step of one instance, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> tagged/src/lib.rs: `k::configuration`",
            ],
            [
                "key-main",
                "error[krs::analysis::main-cell]: the computation cell `k` is the key `k` of the instances of the Map collection cell `cpu` of configuration `Pool`, or lies inside it: a sentence that names no cell (a term rule, a context, a strict production's heating) runs at the computation cell, so it would rewrite an instance's key, and the whole key is the instance's identity, which no step of the instance changes; key the instances by another child, declared first",
                "--> pool/src/lib.rs: `k: KSequence,`",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}
