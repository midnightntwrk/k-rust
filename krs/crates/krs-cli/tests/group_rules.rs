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
    let (code, stdout, stderr) = krs_status_on(target, manifest, package, command, extra);
    (code == Some(0), stdout, stderr)
}

/// [`krs_on`], with the exit status.
fn krs_status_on(
    target: &Path,
    manifest: &Path,
    package: &str,
    command: &str,
    extra: &[&str],
) -> (Option<i32>, String, String) {
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
        output.status.code(),
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
/// instance, so the program starts there; `list-main` holds the same
/// instances as a List.
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

/// `solo`: the one hart in an optional cell, present from the start, so the
/// main cell, the hart's `k`, sits in the optional instance; `rules` is
/// appended.
fn solo(rules: &str) -> String {
    format!(
        r#"
#[k::configuration]
pub struct Solo {{
    #[k::cell(multiplicity = "?", nested)]
    pub hart: Option<lib::Hart>,
}}

impl Solo {{
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {{
        Self {{
            hart: Some(lib::Hart {{ id: 0, k: k::k![pgm], pc: 0 }}),
        }}
    }}
}}

{rules}
"#
    )
}

/// A main cell inside a Map collection's instance (`smp`) or an optional
/// cell's (`solo`) is accepted: each holder keeps the identity of the one
/// instance that steps, so a table clause, which names no cell and runs at
/// the main cell, is a local step of that hart. Each definition checks, emits
/// `tick` inside `<hart>`, and runs `tick` to `pc` 1 through the hart's `inc`.
#[test]
fn a_main_cell_in_a_map_or_an_optional_instance_is_accepted() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let packages = [
        ("smp", smp("Map", HOLDER_HART_RULES)),
        ("solo", solo(HOLDER_HART_RULES)),
    ];
    let sources = packages
        .iter()
        .map(|(name, source)| (*name, source.as_str()))
        .collect::<Vec<_>>();
    let manifests = instance_definitions(temporary.path(), "", &sources);
    let whitespace = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    let outcomes = manifests
        .iter()
        .zip(&packages)
        .map(|(manifest, (package, _))| {
            let (success, _, stderr) = krs_on(target.path(), manifest, package, "check", &[]);
            assert!(success, "{package}:\n{stderr}");
            let flat = emitted(target.path(), manifest, package);
            let path = manifest.with_file_name("program.txt");
            fs::write(&path, "tick").unwrap();
            let (success, stdout, stderr) = krs_on(
                target.path(),
                manifest,
                package,
                "run",
                &[path.to_str().unwrap()],
            );
            assert!(success, "{package}:\n{stdout}\n{stderr}");
            vec![
                (*package).to_owned(),
                sentence(&flat, "rule [tick]:").to_owned(),
                harts(&whitespace(&stdout)).join(" | "),
            ]
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            [
                "smp",
                "rule [tick]: <hart> <k> tick => inc ... </k> ... </hart>",
                "<id> 0 </id> <k> .K </k> <pc> 1 </pc>",
            ],
            [
                "solo",
                "rule [tick]: <hart> <k> tick => inc ... </k> ... </hart>",
                "<id> 0 </id> <k> .K </k> <pc> 1 </pc>",
            ],
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}

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
            "list-main",
            SET_MAIN.replace(r#"cell_type = "Set""#, r#"cell_type = "List""#),
            "pool",
        ),
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
/// - a cell of a List collection's instance inside the instance, named flat,
///   is `collection-entry`, whose advice names that inner holder (a Map
///   collection's is matched in one instance,
///   [`a_record_naming_a_cell_of_a_nested_instance_is_inside_it`]);
/// - a function whose context reads one hart, applied by a rule for the
///   configuration, directly or through a function without a context of its
///   own, is `instance-context-caller`, at the application;
/// - a main cell inside a Set instance is `main-cell`, with the Set's reason,
///   and one inside a List instance (`list-main`, [`SET_MAIN`] held as a
///   List) is too, with the List's gap;
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
                "error[krs::analysis::map-collection-key]: the rule writes `id`, the key of the `Hart` instance of the Map collection `hart` it steps: a rule is a local step of one instance of each Map collection its cells lie in, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> smp/src/lib.rs: `k::builtin::int:`",
            ],
            [
                "key-cells",
                "error[krs::analysis::map-collection-key]: the rule writes `id`, the key of the `Hart` instance of the Map collection `hart` it steps: a rule is a local step of one instance of each Map collection its cells lie in, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
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
                "list-main",
                "error[krs::analysis::main-cell]: the computation cell `k` sits in an instance of the List collection cell `obj` of configuration `Pool`: a sentence that names no cell (a term rule, a context, a strict production's heating) runs at the computation cell, so it is a local step of the instance that holds it, which in a List is the instance at any position, and matching one instance between others is not supported yet; hold the instances in a Map collection keyed by an id",
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

/// A library function with no parameters of its own whose context reads the
/// hart's `pc`: in a definition that holds harts in a Map collection, it
/// receives the hart's key and nothing else.
const LIB_MY_PC: &str = r#"
/// The program counter of the hart it is evaluated in.
#[k::function(total, sort = Int, syntax = "myPc ( )")]
pub struct MyPc {}

#[k::equation]
fn my_pc(
    p: Term<Int>,
    k::term![MyPc()]: Term<Int>,
    k::cells! {
        pc: k::configuration::Cell(p),
        ..
    }: Hart,
) -> Term<Int> {
    p
}
"#;

/// A library function asserted `program` whose context reads the hart's
/// `pc`: in a definition that holds harts in a Map collection, the assertion
/// cannot hold.
const LIB_PROGRAM_PC: &str = r#"
/// The program counter of the hart it is evaluated in.
#[k::function(total, sort = Int, syntax = "progPc ( )", program)]
pub struct ProgPc {}

#[k::equation]
fn prog_pc(
    p: Term<Int>,
    k::term![ProgPc()]: Term<Int>,
    k::cells! {
        pc: k::configuration::Cell(p),
        ..
    }: Hart,
) -> Term<Int> {
    p
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
                "error[krs::analysis::map-collection-key]: the rule writes `pc`, a cell inside the key `cpu`, of the `Node` instance of the Map collection `node` it steps: a rule is a local step of one instance of each Map collection its cells lie in, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> grid/src/lib.rs: `k::builtin::int:`",
            ],
            [
                "inside-key-cells",
                "error[krs::analysis::map-collection-key]: the rule writes `pc`, a cell inside the key `cpu`, of the `Node` instance of the Map collection `node` it steps: a rule is a local step of one instance of each Map collection its cells lie in, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
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
                "error[krs::analysis::map-collection-key]: the rule writes `id`, the key of the `Unit` instance of the Map collection `unit` it steps: a rule is a local step of one instance of each Map collection its cells lie in, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> tagged/src/lib.rs: `k::configuration`",
            ],
            [
                "key-rewrite-whole-cells",
                "error[krs::analysis::map-collection-key]: the rule writes `id`, the key of the `Unit` instance of the Map collection `unit` it steps: a rule is a local step of one instance of each Map collection its cells lie in, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
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

/// The keys a function evaluated in one instance of a Map collection receives
/// are an emission detail, which no grammar, input or view shows. `pcPlus`
/// (one parameter) and `myPc` (none), whose contexts read the hart's `pc`,
/// are `pub` in the library, which a definition holding the hart once may
/// use as program syntax; in `smp`, which holds harts in a Map collection, a
/// program is evaluated in no instance, so each is placed in the library's
/// semantics module with that reason, and its program-syntax module holds
/// neither; `progPc`, asserted `program`, is placed so too, with the warning
/// `krs::partition::not-program-syntax` giving the reason. An input is
/// evaluated in no instance too: a `$call`, and `$text`, `$text-file` or `-c`
/// text, written with the function's own arguments alone as its `syntax`
/// declares them or with the key its emission adds, are refused with one
/// reason before the run (exit 2: no run was asked), as the surface
/// configuration another tool is handed is; text that applies neither still
/// fails to parse. A view is evaluated in no instance, so a case's or
/// `krs compare`'s view naming either is refused before the run with that
/// reason: never as a function of two parameters with a wrapper hint, nor
/// accepted for taking one parameter.
#[test]
fn a_function_evaluated_in_one_instance_is_no_program_syntax_input_or_view() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    // `smp` with a second configuration variable, `n`, held in `ticks`.
    let source = smp("Map", "")
        .replace(
            "pub fn init(pgm: lib::Instr)",
            "pub fn init(pgm: lib::Instr, n: Int)",
        )
        .replace("ticks: 0,", "ticks: n,");
    let manifest = instance_definitions(
        temporary.path(),
        &format!("{HART_RULES}{LIB_PC_PLUS}{LIB_MY_PC}{LIB_PROGRAM_PC}"),
        &[("smp", &source)],
    )
    .remove(0);
    let root = manifest.parent().unwrap().to_owned();
    let krs_status = |command: &str, extra: &[&str]| {
        krs_status_on(target.path(), &manifest, "smp", command, extra)
    };
    let krs = |command: &str, extra: &[&str]| {
        let (code, stdout, stderr) = krs_status(command, extra);
        (code == Some(0), stdout, stderr)
    };

    // The partition, and the emitted modules: the library's program syntax holds neither.
    let (success, stdout, stderr) = krs("check", &["--partition"]);
    assert!(success, "{stderr}");
    let warnings = stderr
        .lines()
        .filter(|line| line.starts_with("warning[krs::partition::"))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "warning[krs::partition::not-program-syntax]: `ProgPc` is marked `program` but is evaluated in one instance of the Map collection cell `hart`, so it receives the instance's key, and a program is evaluated in no instance; it is placed in ORG-KRS-GROUPS-LIB and programs cannot contain it",
        ]
    "#]]
    .assert_debug_eq(&warnings);
    let placed = stdout
        .lines()
        .filter(|line| line.contains("PcPlus") || line.contains("MyPc"))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "  production MyPc: evaluated in one instance of the Map collection cell `hart`, so it receives the instance's key, and a program is evaluated in no instance",
            "  production PcPlus: evaluated in one instance of the Map collection cell `hart`, so it receives the instance's key, and a program is evaluated in no instance",
        ]
    "#]]
    .assert_debug_eq(&placed);
    let flat = emitted(target.path(), &manifest, "smp");
    let module = |name: &str| {
        let start = flat
            .find(&format!("module {name} "))
            .unwrap_or_else(|| panic!("no module {name} in {flat}"));
        let rest = &flat[start..];
        &rest[..rest.find(" endmodule").unwrap()]
    };
    let syntax = module("ORG-KRS-GROUPS-LIB-SYNTAX");
    assert!(
        !syntax.contains("\"pcPlus\"") && !syntax.contains("\"myPc\""),
        "{syntax}"
    );
    let semantics = module("ORG-KRS-GROUPS-LIB");
    assert!(
        semantics
            .contains("syntax Int ::= \"pcPlus\" \"(\" Int \")\" \"#instance\" \"(\" Int \")\"")
            && semantics
                .contains("syntax Int ::= \"myPc\" \"(\" \")\" \"#instance\" \"(\" Int \")\""),
        "{semantics}"
    );

    inputs_refuse_a_function_evaluated_in_one_instance(&krs_status, &root);
    views_refuse_a_function_evaluated_in_one_instance(&krs_status, &root);
    surface_configuration_refuses_a_function_evaluated_in_one_instance(target.path(), &manifest);
}

/// Every input route refuses `pcPlus` and `myPc` with [`instance_reason`] before the run (exit
/// 2), whether its text writes the function's own arguments alone or the key its emission adds;
/// text that applies neither fails to parse, and a plain value runs.
fn inputs_refuse_a_function_evaluated_in_one_instance(
    krs_status: &impl Fn(&str, &[&str]) -> (Option<i32>, String, String),
    root: &Path,
) {
    // Every input route gives the one reason, before the run.
    let program = root.join("inc.txt");
    fs::write(&program, "inc").unwrap();
    let program = program.to_str().unwrap();
    let text_file = |name: &str, text: &str| {
        let path = root.join(name);
        fs::write(&path, text).unwrap();
        format!(
            r#"n={{"$text-file": {}}}"#,
            serde_json::to_string(path.to_str().unwrap()).unwrap()
        )
    };
    let key_file = text_file("key.txt", "pcPlus ( 1 ) #instance ( 0 )");
    let authored_file = text_file("authored.txt", "myPc ( )");
    for (function, flag, binding) in [
        ("PcPlus", "--input", r#"n={"$call": {"PcPlus": {"n": 1}}}"#),
        ("MyPc", "--input", r#"n={"$call": {"MyPc": {}}}"#),
        (
            "PcPlus",
            "--input",
            r#"n={"$text": "pcPlus ( 1 ) #instance ( 0 )"}"#,
        ),
        (
            "MyPc",
            "--input",
            r#"n={"$text": "myPc ( ) #instance ( 0 )"}"#,
        ),
        ("PcPlus", "--input", key_file.as_str()),
        ("PcPlus", "-c", "n=pcPlus ( 1 ) #instance ( 0 )"),
        // The text an author writes against the declarations.
        ("PcPlus", "--input", r#"n={"$text": "pcPlus ( 1 )"}"#),
        ("MyPc", "--input", r#"n={"$text": "myPc ( )"}"#),
        ("MyPc", "--input", authored_file.as_str()),
        ("PcPlus", "-c", "n=pcPlus ( 1 )"),
        ("MyPc", "-c", "n=myPc ( )"),
        ("PcPlus", "-c", "n=pcPlus ( myPc ( ) )"),
    ] {
        let (code, stdout, stderr) = krs_status("run", &[program, flag, binding]);
        assert_eq!(code, Some(2), "{binding}: {stdout}\n{stderr}");
        assert_eq!(stdout, "", "{binding}");
        assert!(
            stderr.contains(&instance_reason(function, "an input")),
            "{binding}: {stderr}"
        );
    }
    // Text that applies such a function with other arguments than it declares is
    // no term of any grammar, which is all its refusal says.
    let (code, stdout, stderr) = krs_status("run", &[program, "-c", "n=pcPlus ( )"]);
    assert_eq!(code, Some(2), "{stdout}\n{stderr}");
    assert!(stderr.contains("does not parse at sort Int"), "{stderr}");
    assert!(
        !stderr.contains("an input is evaluated in no instance"),
        "{stderr}"
    );
    // A plain value runs.
    let (code, stdout, stderr) = krs_status("run", &[program, "--input", "n=7"]);
    assert_eq!(code, Some(0), "{stdout}\n{stderr}");
}

/// The surface configuration another tool is handed (`Semantics::configure_surface`, the gate
/// session's `configure`) refuses text applying `pcPlus`, with the key or without it, with the
/// reason `krs run` gives, and configures a plain value.
fn surface_configuration_refuses_a_function_evaluated_in_one_instance(
    target: &Path,
    manifest: &Path,
) {
    let emitted = manifest.parent().unwrap().join("emitted");
    let output = emitted.to_str().unwrap();
    let (success, _, stderr) = krs_on(
        target,
        manifest,
        "smp",
        "emit-k",
        &["--ir", "--output", output],
    );
    assert!(success, "{stderr}");
    let definition: krs_ir_levels::DefinitionIr =
        serde_json::from_slice(&fs::read(emitted.join("definition-ir.json")).unwrap()).unwrap();
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn_scoped(scope, || {
                let mut timings = krs_ir::measure::Timings::disabled();
                let stage = krs_exec::CompiledStage::compile(&definition, &mut timings).unwrap();
                let mut semantics =
                    krs_exec::Semantics::from_stage(&definition, stage, None, &mut timings)
                        .unwrap();
                let n = semantics
                    .variables()
                    .iter()
                    .find(|variable| variable.parameter == "n")
                    .unwrap()
                    .name
                    .clone();
                let mut configure = |text: &str| {
                    let variables = serde_json::json!({"PGM": "inc", n.as_str(): text});
                    semantics
                        .configure_surface(variables.as_object().unwrap())
                        .map_err(|error| error.to_string())
                };
                for text in ["pcPlus ( 1 ) #instance ( 0 )", "pcPlus ( 1 )"] {
                    let error = configure(text).unwrap_err();
                    assert!(
                        error.contains(&instance_reason("PcPlus", "an input")),
                        "{text}: {error}"
                    );
                }
                configure("7").unwrap();
            })
            .unwrap()
            .join()
            .unwrap();
    });
}

/// The reason every route outside a sentence gives for applying `function`,
/// evaluated in one instance of `smp`'s harts, where `outside` is evaluated.
fn instance_reason(function: &str, outside: &str) -> String {
    format!(
        "`lib::{function}` is evaluated in one instance of the Map collection cell `hart` (its function context reads that instance, or the context of a function it applies does), so it receives the instance's key, and {outside} is evaluated in no instance: a function has one value for its arguments, so it is applied only from a sentence about one instance"
    )
}

/// A case's or `krs compare`'s view naming `PcPlus` or `MyPc` is refused before
/// the run with [`instance_reason`], never as a function of some number of
/// parameters; the case without a view runs.
fn views_refuse_a_function_evaluated_in_one_instance(
    krs: &impl Fn(&str, &[&str]) -> (Option<i32>, String, String),
    root: &Path,
) {
    // A view naming either is refused before the run with the reason, in a case and in compare.
    let case = |name: &str, view: Option<&str>| {
        let mut expect =
            serde_json::json!({"halt": "stuck", "compare": ["ticks"], "cells": {"ticks": 7}});
        if let Some(view) = view {
            expect["views"] = serde_json::json!({"ticks": view});
        }
        serde_json::json!({"name": name, "inputs": {"pgm": "Inc", "n": 7}, "expect": expect})
    };
    let cases = root.join("cases.json");
    fs::write(
        &cases,
        serde_json::json!({"case": [
            case("plus", Some("PcPlus")),
            case("mine", Some("MyPc")),
            case("plain", None),
        ]})
        .to_string(),
    )
    .unwrap();
    let cases = cases.to_str().unwrap();
    let (code, stdout, stderr) = krs("run", &["--case", cases, "--case-name", "plain"]);
    assert_eq!(code, Some(0), "{stdout}\n{stderr}");
    let plain = format!("{cases}#plain");
    for (name, function) in [("plus", "PcPlus"), ("mine", "MyPc")] {
        let (code, stdout, stderr) = krs("run", &["--case", cases, "--case-name", name]);
        assert_eq!(code, Some(2), "{name}: {stdout}\n{stderr}");
        assert_eq!(stdout, "", "{name}");
        assert!(
            stderr.contains(&format!(
                "`expect.views`: the view `{function}` of the cell `ticks`: {}",
                instance_reason(function, "a view")
            )),
            "{name}: {stderr}"
        );
        let view = format!("ticks={function}");
        let (code, stdout, stderr) = krs(
            "compare",
            &[&plain, &plain, "--compare", "ticks", "--view", &view],
        );
        assert_eq!(code, Some(2), "{name}: {stdout}\n{stderr}");
        assert!(
            stderr.contains(&format!(
                "the view `{function}` of the cell `ticks`: {}",
                instance_reason(function, "a view")
            )),
            "{name}: {stderr}"
        );
    }
}

/// `smt`: cores in a Map collection keyed by `cid`, each with its computation
/// cell `k`, a map `cenv` and threads in a Map collection keyed by `tid`, each
/// with `tv` and the maps `tenv` and `tmem`; beside them a memory and devices
/// in a Map collection.
const SMT: &str = r#"
use k::Term;
use k::builtin::{Int, KSequence};

#[k::constructors(sort = lib::Instr, result = k::KResult)]
#[rustfmt::skip]
pub enum Step {
    #[k::syntax("go")] Go(),
    #[k::syntax("done ( {n} )")] Done { n: Int },
}

#[k::cell]
pub struct Thread {
    #[k::cell]
    pub tid: Int,
    #[k::cell]
    pub tv: Int,
    #[k::cell]
    pub tenv: k::builtin::Map<Int, Int>,
    #[k::cell]
    pub tmem: k::builtin::Map<Int, Int>,
}

#[k::cell]
pub struct Dev {
    #[k::cell]
    pub did: Int,
    #[k::cell]
    pub denv: k::builtin::Map<Int, Int>,
}

#[k::cell]
pub struct Devs {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub dev: Dev,
}

#[k::cell]
pub struct Threads {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub thread: Thread,
}

#[k::cell]
pub struct Core {
    #[k::cell]
    pub cid: Int,
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub cenv: k::builtin::Map<Int, Int>,
    #[k::cell(nested)]
    pub threads: Threads,
}

#[k::cell]
pub struct Cores {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub core: Core,
}

#[k::configuration]
pub struct Smt {
    #[k::cell(nested)]
    pub cores: Cores,
    #[k::cell]
    pub ticks: Int,
    #[k::cell]
    pub mem: k::builtin::Map<Int, Int>,
    #[k::cell(nested)]
    pub devs: Devs,
}

impl Smt {
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {
        Self {
            cores: Cores { core: Core { cid: 0, k: k::k![pgm], cenv: k::map![0 -> 3], threads: Threads { thread: Thread { tid: 0, tv: 5, tenv: k::map![0 -> 7], tmem: k::map![1 -> 20] } } } },
            ticks: 0,
            mem: k::map![0 -> 11],
            devs: Devs { dev: Dev { did: 0, denv: k::map![0 -> 13] } },
        }
    }
}
"#;

/// `tvPlus(n)` reads the thread's `tv`, so it receives the core's and the
/// thread's keys.
const TV_PLUS: &str = r#"
#[k::function(total, sort = Int, syntax = "tvPlus ( {n} )")]
pub struct TvPlus {
    pub n: Term<Int>,
}

#[k::equation]
fn tv_plus(
    n: Term<Int>,
    v: Term<Int>,
    k::term![TvPlus(n)]: Term<Int>,
    k::cells! {
        tv: k::configuration::Cell(v),
        ..
    }: Thread,
) -> Term<Int> {
    k::builtin::int::add(v, n)
}
"#;

/// `cidPlus(n)` reads the core's `cid`, so it receives the core's key.
const CID_PLUS: &str = r#"
#[k::function(total, sort = Int, syntax = "cidPlus ( {n} )")]
pub struct CidPlus {
    pub n: Term<Int>,
}

#[k::equation]
fn cid_plus(
    n: Term<Int>,
    c: Term<Int>,
    k::term![CidPlus(n)]: Term<Int>,
    k::cells! {
        cid: k::configuration::Cell(c),
        ..
    }: Core,
) -> Term<Int> {
    k::builtin::int::add(c, n)
}
"#;

/// The cases of [`a_rule_is_inside_the_deepest_instance_its_cells_lie_in`]:
/// a table clause at the main cell, inside a core, whose `have` names one or
/// two cells of a thread, with a thread-context call or none; a rule for the
/// configuration whose entry of the cores steps one core, readable and
/// `cells!`.
const DEEPEST_CASES: [(&str, &str); 5] = [
    (
        "thread-cell",
        r"
k::rules! {
    for lib::Instr;
    use Step::*;

    go: Go() => Done { n: crate::TvPlus(v) } where have tenv[0 -> let v];
}
",
    ),
    (
        "thread-cell-no-call",
        r"
k::rules! {
    for lib::Instr;
    use Step::*;

    go: Go() => Done { n: v } where have tenv[0 -> let v];
}
",
    ),
    (
        "two-thread-cells",
        r"
k::rules! {
    for lib::Instr;
    use Step::*;

    go: Go() => Done { n: crate::TvPlus(k::builtin::int::add(a, b)) } where have tenv[0 -> let a], have tmem[1 -> let b];
}
",
    ),
    (
        "instance-list",
        r"
k::rules! {
    for Smt;
    use Step::*;

    go: { core: { me @ Core { k: [Go(), ..], .. }, .. } } => { core: { Core { k: [Done { n: crate::CidPlus(1) }, ..], ..me }, .. } };
}
",
    ),
    (
        "instance-list-cells",
        r#"
#[k::rule(label = "go")]
pub fn go(
    k::cells! {
        Cores::core: {
            me @ k::fragment![crate::Core { k: k::k![Step::Go(), tail @ ..], .. }],
            others @ ..
        },
        state @ ..
    }: Smt,
) -> Smt {
    k::cells! {
        Cores::core: { k::fragment![crate::Core { k: k::k![Step::Done { n: crate::CidPlus(1) }, ..tail], ..me }], ..others },
        ..state
    }
}
"#,
    ),
];

/// A rule is inside the deepest instance a cell it matches lies in, and its
/// cells below one holder lie in one instance of it: the emitted rule nests
/// them in one `<core>` and, below it, one `<thread>`. So a table clause at
/// the main cell, in a core, whose `have` reads a thread's map is inside that
/// thread too, and applies `tvPlus`, passing the core's and the thread's
/// keys: from `tv` 5 with `tenv` 0 |-> 7 it ends at `done ( 12 )`, and with
/// `tmem` 1 |-> 20 read beside it, in the same thread, at `done ( 32 )`.
/// Without the call the clause is still inside the thread, which then passes
/// no key: it matches the `tenv` of one thread of the core and ends at
/// `done ( 7 )`. A rule for the
/// configuration whose entry of the cores matches one core, keeps it and
/// carries the others unchanged is a step of that core, in either spelling:
/// it applies `cidPlus`, passing the core's key, which the entry's `<core>`
/// binds, and ends at `done ( 1 )`
/// ([`an_entry_that_steps_one_instance_is_inside_it`]).
#[test]
fn a_rule_is_inside_the_deepest_instance_its_cells_lie_in() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let whitespace = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    let outcomes = DEEPEST_CASES
        .iter()
        .map(|(name, rules)| {
            let manifest = instance_definitions(
                &temporary.path().join(name),
                "",
                &[("smt", &format!("{SMT}{TV_PLUS}{CID_PLUS}{rules}"))],
            )
            .remove(0);
            let (success, _, _) = krs_on(target.path(), &manifest, "smt", "check", &[]);
            let mut report = vec![(*name).to_owned()];
            if !success {
                report.extend(check_report(target.path(), &manifest, "smt"));
                return report;
            }
            let flat = emitted(target.path(), &manifest, "smt");
            report.push(sentence(&flat, "rule [go]:").to_owned());
            let path = manifest.with_file_name("program.txt");
            fs::write(&path, "go").unwrap();
            let (success, stdout, stderr) = krs_on(
                target.path(),
                &manifest,
                "smt",
                "run",
                &[path.to_str().unwrap()],
            );
            assert!(success, "{name}:\n{stdout}\n{stderr}");
            report.push(cell(&whitespace(&stdout), "k"));
            report
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            [
                "thread-cell",
                "rule [go]: <core> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> ... </core>",
                "done ( 12 ) ~> .K",
            ],
            [
                "thread-cell-no-call",
                "rule [go]: <core> <k> go => done ( V:Int ) ... </k> <thread> <tenv> 0 |-> V:Int ... </tenv> ... </thread> ... </core>",
                "done ( 7 ) ~> .K",
            ],
            [
                "two-thread-cells",
                "rule [go]: <core> <k> go => done ( tvPlus ( A:Int +Int B:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> <thread> <tenv> 0 |-> A:Int ... </tenv> <tmem> 1 |-> B:Int ... </tmem> <tid> Krs_KeyThread:Int </tid> ... </thread> ... </core>",
                "done ( 32 ) ~> .K",
            ],
            [
                "instance-list",
                "rule [go]: <core> <k> go ~> Tail0:K => done ( cidPlus ( 1 ) #instance ( Krs_KeyCore:Int ) ) ~> Tail0:K </k> <cid> Krs_KeyCore:Int </cid> ... </core>",
                "done ( 1 ) ~> .K",
            ],
            [
                "instance-list-cells",
                "rule [go]: <core> <k> go ~> Tail:K => done ( cidPlus ( 1 ) #instance ( Krs_KeyCore:Int ) ) ~> Tail:K </k> <cid> Krs_KeyCore:Int </cid> ... </core>",
                "done ( 1 ) ~> .K",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// Edits of `go` in [`DEEPEST_CASES`]'s `instance-list`, a rule for the configuration whose
/// entry of the cores steps one core, to which KRS adds the core's key cell `<cid>`, binding the
/// key the entry's subject matches, which `go` passes to `cidPlus`.
#[cfg(feature = "kink")]
const STEPPED_MUTATIONS: &str = r##"[[mutation]]
id = "step-two"
misunderstanding = "the step adds two"

  [[mutation.edit]]
  rule = "ORG-KRS-GROUPS-SMT.go"
  find = "cidPlus ( 1 )"
  replace = "cidPlus ( 2 )"

[[mutation]]
id = "rekey"
misunderstanding = "the step renumbers the core"

  [[mutation.edit]]
  rule = "ORG-KRS-GROUPS-SMT.go"
  find = "<cid> Krs_KeyCore:Int </cid>"
  replace = "<cid> Krs_KeyCore:Int => 1 </cid>"

[[mutation]]
id = "other-core"
misunderstanding = "the step is core 1's"

  [[mutation.edit]]
  rule = "ORG-KRS-GROUPS-SMT.go"
  find = "<cid> Krs_KeyCore:Int </cid>"
  replace = "<cid> 1 </cid>"

  [[mutation.edit]]
  rule = "ORG-KRS-GROUPS-SMT.go"
  find = "#instance ( Krs_KeyCore:Int )"
  replace = "#instance ( 1 )"

[[mutation]]
id = "other-core-key-kept"
misunderstanding = "the step is core 1's, evaluated in the core it steps"

  [[mutation.edit]]
  rule = "ORG-KRS-GROUPS-SMT.go"
  find = "<cid> Krs_KeyCore:Int </cid>"
  replace = "<cid> 1 </cid>"
"##;

/// An edit of a rule whose entry of a collection steps one instance is judged as an edit of a
/// rule about that instance, in either spelling of `instance-list`. `step-two` edits the step
/// and leaves the key cell and the key `cidPlus` receives alone: it is judged, runs, and the
/// corpus kills it (`done ( 2 )` against `done ( 1 )`). The key cell KRS adds is the key of the
/// core the entry's subject matches, whether or not the author wrote it: `rekey` writes it,
/// which every Rust source that writes the core's `cid` in the step does, and is refused with
/// the reason KRS gives that source (`map-collection-key`, an update that changes the key); `other-core` matches core 1, as a
/// source that writes `cid: 1` in the entry's pattern does, with the key `cidPlus` receives
/// following, and is judged, runs and is killed, since the one core is core 0 and `go` no longer
/// steps it; `other-core-key-kept` leaves `cidPlus` the key of a core the rule no longer binds,
/// which no source writes, and is refused, KRS deriving the key the edited rule passes.
#[cfg(feature = "kink")]
#[test]
fn an_edit_of_an_entry_that_steps_one_instance_is_judged_as_that_instances_rule() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let mut spellings = Vec::new();
    for (name, rules) in &DEEPEST_CASES[3..] {
        let manifest = instance_definitions(
            &temporary.path().join(name),
            "",
            &[("smt", &format!("{SMT}{TV_PLUS}{CID_PLUS}{rules}"))],
        )
        .remove(0);
        let package = manifest.parent().unwrap();
        let corpus = package.join("kink");
        fs::create_dir_all(corpus.join("cases")).unwrap();
        fs::create_dir_all(corpus.join("mutations")).unwrap();
        fs::write(
            corpus.join("FLOW.toml"),
            "[spec]\nkrs = { package = \"smt\", definition = \"main\" }\n\n[[program]]\nid = \"go\"\nfile = \"cases/go.prog\"\n",
        )
        .unwrap();
        fs::write(corpus.join("cases/go.prog"), "go\n").unwrap();
        fs::write(corpus.join("mutations/stepped.toml"), STEPPED_MUTATIONS).unwrap();
        let mut process = krs_command!();
        fixture_build_env(&mut process, target.path());
        let output = process
            .current_dir(package)
            .args(["kink", "run", "--full", "--corpus", "kink"])
            .args(["--package", "smt", "--definition", "main"])
            .args(["--dependency", "lib:main"])
            .env("NO_COLOR", "1")
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        // The refused mutations are invalid, which the run's status reports.
        assert_eq!(output.status.code(), Some(2), "{name}:\n{stdout}\n{stderr}");
        let run: serde_json::Value = serde_json::from_str(&stdout).unwrap();
        let mutations = run["mutations"].as_array().unwrap();
        let rows = mutations
            .iter()
            .map(|row| {
                format!(
                    "{} {} {}",
                    row["id"].as_str().unwrap(),
                    row["status"].as_str().unwrap(),
                    row["reason"].as_str().unwrap_or("-"),
                )
            })
            .collect::<Vec<_>>();
        // The key write is refused with the reason KRS gives the update of the core that
        // changes its key, not a rule for the core's group.
        let rekey = mutations
            .iter()
            .find(|row| row["id"] == "stepped/rekey")
            .unwrap();
        let detail = rekey["detail"].as_str().unwrap_or_default();
        assert!(
            detail.contains(&krs_ir::subject::key_update_reason("core", "cid")),
            "{name}: {rekey:#}"
        );
        spellings.push((*name, rows));
    }
    assert_eq!(spellings[0].1, spellings[1].1, "{spellings:#?}");
    expect_test::expect![[r#"
        [
            "stepped/step-two killed -",
            "stepped/rekey invalid-mutation krs::analysis::map-collection-key",
            "stepped/other-core killed -",
            "stepped/other-core-key-kept invalid-mutation derived-mismatch",
        ]
    "#]]
    .assert_debug_eq(&spellings[0].1);
}

/// The clauses of [`a_rule_no_one_nesting_of_instances_holds_is_not_supported_yet`]:
/// a table clause at the main cell, inside a core, whose `have` reads a
/// device's map, beside the cores.
const UNNESTED_CASES: [(&str, &str); 1] = [("sibling", "have denv[0 -> let v]")];

/// A rule whose cells lie in instances of two holders neither of which holds
/// the other (a core's computation cell and a device's map) would match one
/// instance of each: no one nesting of instance cells holds its clauses, and
/// writing them otherwise is not supported yet. It is refused at the cell that
/// leaves the core (`collection-entry`), the same whether or not the
/// definition has a function context typed by a group in an instance, never
/// with the emitter's internal error. A cell outside every instance beside a
/// core's is no such rule
/// ([`a_step_of_one_instance_matches_a_cell_outside_every_instance_beside_it`]).
#[test]
fn a_rule_no_one_nesting_of_instances_holds_is_not_supported_yet() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let outcomes = UNNESTED_CASES
        .iter()
        .flat_map(|(name, have)| {
            [("contexts", TV_PLUS), ("no contexts", "")].map(|(contexts, functions)| {
                let directory = temporary.path().join(format!("{name}-{}", functions.len()));
                let rules = format!(
                    "k::rules! {{\n    for lib::Instr;\n    use Step::*;\n\n    go: Go() => Done {{ n: v }} where {have};\n}}\n"
                );
                let manifest = instance_definitions(
                    &directory,
                    "",
                    &[("smt", &format!("{SMT}{functions}{rules}"))],
                )
                .remove(0);
                let mut report = vec![format!("{name}, {contexts}")];
                report.extend(check_report(target.path(), &manifest, "smt"));
                report
            })
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            [
                "sibling, contexts",
                "error[krs::analysis::collection-entry]: the rule matches `k`, a cell of an instance of the Map collection cell `core`, and `denv`, a cell of an instance of the Map collection cell `dev`: neither instance holds the other, so the rule would match one instance of each, and a sentence whose cells lie in instances of two holders neither of which holds the other is not supported yet; name the instance of `dev` through its instance list instead, `dev: { .. }`, beside `k`",
                "--> smt/src/lib.rs: `denv[0 -> let v]`",
            ],
            [
                "sibling, no contexts",
                "error[krs::analysis::collection-entry]: the rule matches `k`, a cell of an instance of the Map collection cell `core`, and `denv`, a cell of an instance of the Map collection cell `dev`: neither instance holds the other, so the rule would match one instance of each, and a sentence whose cells lie in instances of two holders neither of which holds the other is not supported yet; name the instance of `dev` through its instance list instead, `dev: { .. }`, beside `k`",
                "--> smt/src/lib.rs: `denv[0 -> let v]`",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// The refusal of cells in instances of two holders neither of which holds the other names the
/// sentence as written, a rule, a claim or a context, and advises a spelling each of them can
/// write: the device named through its instance list beside the core's `k`, a clause outside
/// every instance, which the rule, the claim and the context then accept (the context keeps its
/// hole in the core's computation cell, where heating moves it).
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "The cases and their reports read as one verdict table."
)]
fn the_sibling_instances_refusal_names_the_sentence_and_advice_it_can_follow() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rule =
        |body: &str| format!("k::rules! {{\n    for Smt;\n    use Step::*;\n\n    {body}\n}}\n");
    let claim = |body: &str| {
        format!(
            "k::claims! {{\n    for Smt;\n    use Step::*;\n\n    #[k::claim(all_paths)]\n    {body}\n}}\n"
        )
    };
    let context = |device: &str| {
        format!(
            "
#[k::context(hole = h)]
fn done_arg(
    h: Int,
    k::cells! {{
        crate::Core::k: k::configuration::KCell(crate::Step::Done(h), ..),
        {device}
        state @ ..
    }}: crate::Smt,
) {{}}
"
        )
    };
    let flat = "{ k: [Go(), ..], denv: { 0 -> v, .. } } => { k: [Done { n: v }, ..] };";
    let listed = "{ k: [Go(), ..], dev: { Dev { denv: { 0 -> v, .. }, .. }, .. } } => { k: [Done { n: v }, ..] };";
    let cases = [
        ("rule", rule(&format!("go: {flat}")), "rule [go]:"),
        (
            "claim",
            claim(&format!("go_claim: {flat}")),
            "claim [go-claim]:",
        ),
        (
            "context",
            context("crate::Dev::denv: k::configuration::Cell(k::map![0 -> 13, ..]),"),
            "context [done-arg]:",
        ),
        ("rule-listed", rule(&format!("go: {listed}")), "rule [go]:"),
        (
            "claim-listed",
            claim(&format!("go_claim: {listed}")),
            "claim [go-claim]:",
        ),
        (
            "context-listed",
            context(
                "Devs::dev: { k::fragment![crate::Dev { denv: k::map![0 -> 13, ..], .. }], .. },",
            ),
            "context [done-arg]:",
        ),
    ];
    let outcomes = cases
        .iter()
        .map(|(name, sentences, start)| {
            let manifest = instance_definitions(
                &temporary.path().join(name),
                "",
                &[("smt", &format!("{SMT}{sentences}"))],
            )
            .remove(0);
            let (success, _, _) = krs_on(target.path(), &manifest, "smt", "check", &[]);
            let mut report = vec![(*name).to_owned()];
            if success {
                let output = manifest.with_file_name("emitted");
                let (success, _, stderr) = krs_on(
                    target.path(),
                    &manifest,
                    "smt",
                    "emit-k",
                    &["--output", output.to_str().unwrap()],
                );
                assert!(success, "{name}: {stderr}");
                let file = if start.starts_with("claim") {
                    "spec.k"
                } else {
                    "definition.k"
                };
                let flat = fs::read_to_string(output.join(file))
                    .unwrap()
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .join(" ");
                report.push(sentence(&flat, start).to_owned());
            } else {
                report.extend(check_report(target.path(), &manifest, "smt"));
            }
            report
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            [
                "rule",
                "error[krs::analysis::collection-entry]: the rule matches `k`, a cell of an instance of the Map collection cell `core`, and `denv`, a cell of an instance of the Map collection cell `dev`: neither instance holds the other, so the rule would match one instance of each, and a sentence whose cells lie in instances of two holders neither of which holds the other is not supported yet; name the instance of `dev` through its instance list instead, `dev: { .. }`, beside `k`",
                "--> smt/src/lib.rs: `denv: { 0 -> v,`",
            ],
            [
                "claim",
                "error[krs::analysis::collection-entry]: the claim matches `k`, a cell of an instance of the Map collection cell `core`, and `denv`, a cell of an instance of the Map collection cell `dev`: neither instance holds the other, so the claim would match one instance of each, and a sentence whose cells lie in instances of two holders neither of which holds the other is not supported yet; name the instance of `dev` through its instance list instead, `dev: { .. }`, beside `k`",
                "--> smt/src/lib.rs: `denv: { 0 -> v,`",
            ],
            [
                "context",
                "error[krs::analysis::collection-entry]: the context matches `k`, a cell of an instance of the Map collection cell `core`, and `denv`, a cell of an instance of the Map collection cell `dev`: neither instance holds the other, so the context would match one instance of each, and a sentence whose cells lie in instances of two holders neither of which holds the other is not supported yet; name the instance of `dev` through its instance list instead, `dev: { .. }`, beside `k`",
                "--> smt/src/lib.rs: `denv: k::configu`",
            ],
            [
                "rule-listed",
                "rule [go]: <core> <k> go => done ( V:Int ) ... </k> ... </core> <dev> <denv> 0 |-> V:Int ... </denv> ... </dev>",
            ],
            [
                "claim-listed",
                "claim [go-claim]: <core> <k> go => done ( V:Int ) ... </k> ... </core> <dev> <denv> 0 |-> V:Int ... </denv> ... </dev>",
            ],
            [
                "context-listed",
                "context [done-arg]: <core> <k> done ( HOLE:Int ) ... </k> ... </core> <dev> <denv> 0 |-> 13 ... </denv> ... </dev>",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// One case of [`a_step_of_one_instance_matches_a_cell_outside_every_instance_beside_it`]: its
/// name, its sentences after [`SMT`], [`TV_PLUS`] and [`CID_PLUS`], and the start of the sentence
/// it reports.
struct TopCase {
    name: &'static str,
    sentences: String,
    start: &'static str,
}

/// The cases of [`a_step_of_one_instance_matches_a_cell_outside_every_instance_beside_it`]: a
/// core's step that also matches the memory, outside every instance, in each spelling and
/// position, and its neighbours.
fn top_cases() -> Vec<TopCase> {
    let instr = |clause: &str| {
        format!("k::rules! {{\n    for lib::Instr;\n    use Step::*;\n\n    {clause}\n}}\n")
    };
    let core =
        |rule: &str| format!("k::rules! {{\n    for Core;\n    use Step::*;\n\n    {rule}\n}}\n");
    let rule = "rule [go]:";
    [
        ("have", instr("go: Go() => Done { n: crate::CidPlus(v) } where have mem[0 -> let v];"), rule),
        (
            "record",
            configuration_record(
                "go: { k: [Go(), ..], mem: { 0 -> v, .. } } => { k: [Done { n: crate::CidPlus(v) }, ..] };",
            ),
            rule,
        ),
        (
            "cells",
            configuration_cells(
                "v: k::Term<k::builtin::Int>,",
                "mem: k::configuration::Cell(k::map![0 -> v, ..]),",
                "crate::CidPlus(v)",
                "",
            ),
            rule,
        ),
        (
            "stepping-entry",
            configuration_record(
                "go: { core: { me @ Core { k: [Go(), ..], .. }, .. }, mem: { 0 -> v, .. } } => { core: { Core { k: [Done { n: crate::CidPlus(v) }, ..], ..me }, .. } };",
            ),
            rule,
        ),
        (
            "have-update",
            instr("go: Go() => Done { n: crate::CidPlus(1) } where update mem = k::builtin::map::update(mem, 0, 4);"),
            rule,
        ),
        (
            "record-update",
            configuration_record(
                "go: { k: [Go(), ..], mem } => { k: [Done { n: crate::CidPlus(1) }, ..], mem: k::builtin::map::update(mem, 0, 4) };",
            ),
            rule,
        ),
        (
            "have-thread",
            instr("go: Go() => Done { n: crate::TvPlus(k::builtin::int::add(a, b)) } where have tenv[0 -> let a], have mem[0 -> let b];"),
            rule,
        ),
        (
            "have-thread-call",
            instr("go: Go() => Done { n: crate::TvPlus(v) } where have mem[0 -> let v];"),
            rule,
        ),
        (
            "record-devices",
            configuration_record(
                "go: { k: [Go(), ..], dev: { Dev { did: 0, denv: { 0 -> v, .. } }, .. } } => { k: [Done { n: crate::CidPlus(v) }, ..] };",
            ),
            rule,
        ),
        (
            "context",
            r"
#[k::context(hole = h)]
fn done_arg(
    h: Int,
    k::cells! {
        crate::Core::k: k::configuration::KCell(crate::Step::Done(h), ..),
        mem: k::configuration::Cell(k::map![0 -> 11, ..]),
        state @ ..
    }: crate::Smt,
) {}
"
            .to_owned(),
            "context [done-arg]:",
        ),
        (
            "group",
            core("go: { k: [Go(), ..], mem: { 0 -> v, .. } } => { k: [Done { n: v }, ..] };"),
            rule,
        ),
    ]
    .into_iter()
    .map(|(name, sentences, start)| TopCase {
        name,
        sentences,
        start,
    })
    .collect()
}

/// A cell outside every instance occurs once in the configuration, so a rule whose other cells
/// lie in one core (a clause at its main cell whose `have` or `update` names the memory beside
/// the cores) matches that core and the one memory beside it: it is a step of the core, inside
/// it, passing its key to `cidPlus`, and its memory clause is written at the top, after the
/// core's cell. The clause, the rule for the configuration naming `k` and `mem` flat, and that
/// rule's `cells!` spelling emit one rule and run to `done ( 11 )` (memory `0 |-> 11`, core 0);
/// the rule whose instance list steps the core beside the memory matches the same, up to how its
/// computation's rest is named, with the same run. Writing the memory is the same in both
/// spellings and leaves `0 |-> 4`. Beside a thread's map the rule is inside the thread too and
/// passes both keys (`done ( 23 )`); without one it is inside no thread, so `tvPlus` is refused.
/// A devices' instance list at the top and a `#[k::context]` naming the core's `k` and the memory
/// are written the same way. A rule for `Core` cannot name the memory, which is no cell of the
/// group. `krs expand` prints each clause as the flat `cells!` rule for the configuration, and the
/// print checks and emits the clause's K.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "The cases, their runs, the comparison of the spellings and the prints read as one table."
)]
fn a_step_of_one_instance_matches_a_cell_outside_every_instance_beside_it() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let whitespace = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    let cases = top_cases();
    let mut accepted = Vec::new();
    let outcomes = cases
        .iter()
        .map(|case| {
            let manifest = instance_definitions(
                &temporary.path().join(case.name),
                "",
                &[(
                    "smt",
                    &format!("{SMT}{TV_PLUS}{CID_PLUS}{}", case.sentences),
                )],
            )
            .remove(0);
            let (success, _, _) = krs_on(target.path(), &manifest, "smt", "check", &[]);
            let mut report = vec![case.name.to_owned()];
            if !success {
                report.extend(check_report(target.path(), &manifest, "smt"));
                return report;
            }
            let flat = emitted(target.path(), &manifest, "smt");
            let sentence = sentence(&flat, case.start).to_owned();
            report.push(sentence.clone());
            if case.start != "rule [go]:" {
                return report;
            }
            let path = manifest.with_file_name("program.txt");
            fs::write(&path, "go").unwrap();
            let (success, stdout, stderr) = krs_on(
                target.path(),
                &manifest,
                "smt",
                "run",
                &[path.to_str().unwrap()],
            );
            assert!(success, "{}:\n{stdout}\n{stderr}", case.name);
            let stdout = whitespace(&stdout);
            let run = (cell(&stdout, "k"), cell(&stdout, "mem"));
            report.push(format!("{} / mem {}", run.0, run.1));
            accepted.push((case.name, manifest, sentence, run));
            report
        })
        .collect::<Vec<_>>();
    let find = |name: &str| {
        accepted
            .iter()
            .find(|(accepted, ..)| *accepted == name)
            .unwrap_or_else(|| panic!("{name} is refused: {outcomes:#?}"))
    };
    for names in [
        &["have", "record", "cells"][..],
        &["have-update", "record-update"],
    ] {
        let (_, _, first, run) = find(names[0]);
        for name in &names[1..] {
            let (_, _, rule, other) = find(name);
            assert_eq!(rule, first, "{name}");
            assert_eq!(other, run, "{name}");
        }
    }
    // The stepping entry keeps the computation's rest under a name and writes its clauses in the
    // order the rule names them: the same cells, the same key, the same run.
    let (_, _, stepped, stepped_run) = find("stepping-entry");
    let (_, _, flat_rule, flat_run) = find("have");
    let items = |rule: &str| {
        let mut items = rule
            .replace(" ~> Tail0:K =>", " =>")
            .replace(" ~> Tail0:K </k>", " ... </k>")
            .split_whitespace()
            .map(str::to_owned)
            .collect::<Vec<_>>();
        items.sort();
        items
    };
    assert_eq!(items(stepped), items(flat_rule));
    assert_eq!(stepped_run, flat_run);
    // Each clause's print is the flat rule for the configuration, which checks and emits the
    // clause's rule.
    let mut prints = Vec::new();
    for name in ["have", "have-update", "have-thread"] {
        let (_, manifest, ..) = find(name);
        let (success, print, stderr) = krs_on(target.path(), manifest, "smt", "expand", &[]);
        assert!(success, "{name}:\n{stderr}");
        prints.push(format!("// {name}\n{}", printed_rule(&print, "go")));
        let printed = instance_definitions(
            &temporary.path().join(format!("{name}-printed")),
            "",
            &[("smt", &print)],
        )
        .remove(0);
        assert_print_emits_the_readable_k(target.path(), manifest, &printed, "smt", &["go"]);
    }
    expect_test::expect![[r#"
        // have
        #[k::rule(label = "go")]
        pub fn go(
            v: k::Term<k::builtin::Int>,
            k::cells! {
                crate ::Core::k : k::configuration::KCell(crate ::Step::Go(), ..), mem :
                k::configuration::Cell(map![0 -> v, ..]), state @ ..
            }: crate::Smt,
        ) -> crate::Smt {
            k::cells! {
                crate ::Core::k : k::configuration::KCell(crate ::Step::Done(crate ::CidPlus(v)),
                ..), ..state
            }
        }
        // have-update
        #[k::rule(label = "go")]
        pub fn go(
            mem: k::Term<k::builtin::Map>,
            k::cells! {
                crate ::Core::k : k::configuration::KCell(crate ::Step::Go(), ..), mem :
                k::configuration::Cell(mem), state @ ..
            }: crate::Smt,
        ) -> crate::Smt {
            k::cells! {
                crate ::Core::k : k::configuration::KCell(crate ::Step::Done(crate ::CidPlus(1)),
                ..), mem : k::configuration::Cell(k::builtin::map::update(mem, 0, 4)), ..state
            }
        }
        // have-thread
        #[k::rule(label = "go")]
        pub fn go(
            a: k::Term<k::builtin::Int>,
            b: k::Term<k::builtin::Int>,
            k::cells! {
                crate ::Core::k : k::configuration::KCell(crate ::Step::Go(), ..), crate
                ::Thread::tenv : k::configuration::Cell(map![0 -> a, ..]), mem :
                k::configuration::Cell(map![0 -> b, ..]), state @ ..
            }: crate::Smt,
        ) -> crate::Smt {
            k::cells! {
                crate ::Core::k : k::configuration::KCell(crate ::Step::Done(crate
                ::TvPlus(k::builtin::int::add(a, b))), ..), ..state
            }
        }"#]]
    .assert_eq(&prints.join("\n"));
    expect_test::expect![[r#"
        [
            [
                "have",
                "rule [go]: <core> <k> go => done ( cidPlus ( V:Int ) #instance ( Krs_KeyCore:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> ... </core> <mem> 0 |-> V:Int ... </mem>",
                "done ( 11 ) ~> .K / mem 0 |-> 11",
            ],
            [
                "record",
                "rule [go]: <core> <k> go => done ( cidPlus ( V:Int ) #instance ( Krs_KeyCore:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> ... </core> <mem> 0 |-> V:Int ... </mem>",
                "done ( 11 ) ~> .K / mem 0 |-> 11",
            ],
            [
                "cells",
                "rule [go]: <core> <k> go => done ( cidPlus ( V:Int ) #instance ( Krs_KeyCore:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> ... </core> <mem> 0 |-> V:Int ... </mem>",
                "done ( 11 ) ~> .K / mem 0 |-> 11",
            ],
            [
                "stepping-entry",
                "rule [go]: <mem> 0 |-> V:Int ... </mem> <core> <k> go ~> Tail0:K => done ( cidPlus ( V:Int ) #instance ( Krs_KeyCore:Int ) ) ~> Tail0:K </k> <cid> Krs_KeyCore:Int </cid> ... </core>",
                "done ( 11 ) ~> .K / mem 0 |-> 11",
            ],
            [
                "have-update",
                "rule [go]: <core> <k> go => done ( cidPlus ( 1 ) #instance ( Krs_KeyCore:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> ... </core> <mem> Mem:Map => Mem:Map [ 0 <- 4 ] </mem>",
                "done ( 1 ) ~> .K / mem 0 |-> 4",
            ],
            [
                "record-update",
                "rule [go]: <core> <k> go => done ( cidPlus ( 1 ) #instance ( Krs_KeyCore:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> ... </core> <mem> Mem:Map => Mem:Map [ 0 <- 4 ] </mem>",
                "done ( 1 ) ~> .K / mem 0 |-> 4",
            ],
            [
                "have-thread",
                "rule [go]: <core> <k> go => done ( tvPlus ( A:Int +Int B:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> <thread> <tenv> 0 |-> A:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> ... </core> <mem> 0 |-> B:Int ... </mem>",
                "done ( 23 ) ~> .K / mem 0 |-> 11",
            ],
            [
                "have-thread-call",
                "error[krs::analysis::instance-context-caller]: `TvPlus` reads the cell group `Thread` through its function context in one instance of the Map collection cell `thread`, the instance it is evaluated in, and this sentence is not inside such an instance, so it determines none: a function has one value for its arguments, so it is applied only from a sentence about one instance of that holder (a rule, a context alias or a function context for the group, or for a group inside its instance)",
                "--> smt/src/lib.rs: `crate::TvPlus(v)`",
            ],
            [
                "record-devices",
                "rule [go]: <core> <k> go => done ( cidPlus ( V:Int ) #instance ( Krs_KeyCore:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> ... </core> <dev> <did> 0 </did> <denv> 0 |-> V:Int ... </denv> </dev>",
                "done ( 13 ) ~> .K / mem 0 |-> 11",
            ],
            [
                "context",
                "context [done-arg]: <core> <k> done ( HOLE:Int ) ... </k> ... </core> <mem> 0 |-> 11 ... </mem>",
            ],
            [
                "group",
                "error[krs::analysis::cell-outside-subject]: `Core` has no cell `mem`: a sentence about the cell group `Core` names only the cells inside the group, and `mem` is another cell of configuration `Smt`; write the sentence for `Smt` to name it",
                "--> smt/src/lib.rs: `mem: { 0 -> v, .`",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// The `cells!` form of [`DEEPEST_CASES`]' `thread-cell` clause, written by
/// hand: a rule for `Core` whose entry of the threads matches one thread,
/// keeps it and carries the others unchanged.
const THREAD_ENTRY_CELLS: &str = r#"
#[k::rule(label = "go")]
pub fn go(
    v: k::Term<k::builtin::Int>,
    k::cells! {
        k: k::configuration::KCell(crate::Step::Go(), ..),
        Threads::thread: {
            me @ k::fragment![crate::Thread { tenv: k::map![0 -> v, ..], .. }],
            others @ ..
        },
        state @ ..
    }: crate::Core,
) -> crate::Core {
    k::cells! {
        k: k::configuration::KCell(crate::Step::Done(crate::TvPlus(v)), ..),
        Threads::thread: { k::fragment![crate::Thread { ..me }], ..others },
        ..state
    }
}
"#;

/// The entries of [`an_entry_that_steps_one_instance_is_inside_it`] that are
/// about the holder whole, each with a thread-context call: one that matches
/// two threads, one that adds a thread beside the one it keeps, and one
/// without `..`, which names every thread.
const HOLDER_ENTRY_CASES: [(&str, &str, &str); 3] = [
    (
        "two-threads",
        "me @ k::fragment![crate::Thread { tenv: k::map![0 -> v, ..], .. }], other @ k::fragment![crate::Thread { .. }], others @ ..",
        "k::fragment![crate::Thread { ..me }], k::fragment![crate::Thread { ..other }], ..others",
    ),
    (
        "added-thread",
        "me @ k::fragment![crate::Thread { tenv: k::map![0 -> v, ..], .. }], others @ ..",
        "k::fragment![crate::Thread { ..me }], k::fragment![crate::Thread { tid: 1, .. }], ..others",
    ),
    (
        "every-thread",
        "me @ k::fragment![crate::Thread { tenv: k::map![0 -> v, ..], .. }]",
        "k::fragment![crate::Thread { ..me }]",
    ),
];

/// An entry of a collection that matches one instance, keeps it and carries
/// the other instances unchanged is a step of that instance: the instance's
/// key cell is matched, so the key is determined, and the rule is inside the
/// instance as the readable clause it prints for is. So the `cells!` form of
/// the `thread-cell` clause, a rule for `Core` whose entry steps one thread,
/// applies `tvPlus`, passing the core's and the thread's keys, and emits the
/// readable clause's K: the same cells, with the thread's `<tid>` bound inside
/// the entry's `<thread>` and the core's `<cid>` beside it, in another order
/// in `<core>`, whose cells K matches by name. It runs to the same
/// `done ( 12 )`. Writing the thread's key cell, or the core's, with a
/// wildcard says any key: the key variable names the value it matches, in
/// its place, and the rule is the same up to that cell's place, with the same
/// run. An entry about the threads whole (two
/// threads, a thread added, every thread) still determines no thread, and
/// `tvPlus` is refused from it.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "The cases, their runs and the comparison of the two accepted forms read as one table."
)]
fn an_entry_that_steps_one_instance_is_inside_it() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let whitespace = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    let mut cases = vec![
        ("readable", DEEPEST_CASES[0].1.to_owned()),
        ("cells", THREAD_ENTRY_CELLS.to_owned()),
    ];
    cases.extend(HOLDER_ENTRY_CASES.iter().map(|(name, subject, result)| {
        (
            *name,
            THREAD_ENTRY_CELLS
                .replace(
                    "me @ k::fragment![crate::Thread { tenv: k::map![0 -> v, ..], .. }],\n            others @ ..",
                    subject,
                )
                .replace(
                    "k::fragment![crate::Thread { ..me }], ..others",
                    result,
                ),
        )
    }));
    // The thread's key cell, then the core's, written with a wildcard, which
    // matches any key: the key variable takes its place.
    cases.push((
        "wildcard-key",
        THREAD_ENTRY_CELLS.replace("Thread { tenv:", "Thread { tid: _, tenv:"),
    ));
    cases.push((
        "wildcard-core-key",
        THREAD_ENTRY_CELLS.replace(
            "        k: k::configuration::KCell(crate::Step::Go(), ..),",
            "        cid: k::configuration::Cell(_),\n        k: k::configuration::KCell(crate::Step::Go(), ..),",
        ),
    ));
    let mut emitted_go = Vec::new();
    let outcomes = cases
        .iter()
        .map(|(name, rules)| {
            let manifest = instance_definitions(
                &temporary.path().join(name),
                "",
                &[("smt", &format!("{SMT}{TV_PLUS}{rules}"))],
            )
            .remove(0);
            let (success, _, _) = krs_on(target.path(), &manifest, "smt", "check", &[]);
            let mut report = vec![(*name).to_owned()];
            if !success {
                report.extend(check_report(target.path(), &manifest, "smt"));
                return report;
            }
            let flat = emitted(target.path(), &manifest, "smt");
            let rule = sentence(&flat, "rule [go]:").to_owned();
            report.push(rule.clone());
            emitted_go.push(rule);
            let path = manifest.with_file_name("program.txt");
            fs::write(&path, "go").unwrap();
            let (success, stdout, stderr) = krs_on(
                target.path(),
                &manifest,
                "smt",
                "run",
                &[path.to_str().unwrap()],
            );
            assert!(success, "{name}:\n{stdout}\n{stderr}");
            report.push(cell(&whitespace(&stdout), "k"));
            report
        })
        .collect::<Vec<_>>();
    // The same cells, each key cell bound once, to the key passed, at another
    // place among the items of its instance.
    let key_cells = [
        "<cid> Krs_KeyCore:Int </cid> ",
        "<tid> Krs_KeyThread:Int </tid> ",
    ];
    let without_keys = |rule: &str| {
        key_cells
            .iter()
            .fold(rule.to_owned(), |rule, key| rule.replace(key, ""))
    };
    assert_eq!(emitted_go.len(), 4, "{outcomes:#?}");
    for rule in &emitted_go {
        for key in key_cells {
            assert_eq!(rule.matches(key).count(), 1, "{rule}");
        }
        assert_eq!(without_keys(rule), without_keys(&emitted_go[0]));
    }
    expect_test::expect![[r#"
        [
            [
                "readable",
                "rule [go]: <core> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> ... </core>",
                "done ( 12 ) ~> .K",
            ],
            [
                "cells",
                "rule [go]: <core> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> <cid> Krs_KeyCore:Int </cid> ... </core>",
                "done ( 12 ) ~> .K",
            ],
            [
                "two-threads",
                "error[krs::analysis::instance-context-caller]: `TvPlus` reads the cell group `Thread` through its function context in one instance of the Map collection cell `thread`, the instance it is evaluated in, and this sentence is not inside such an instance, so it determines none: a function has one value for its arguments, so it is applied only from a sentence about one instance of that holder (a rule, a context alias or a function context for the group, or for a group inside its instance)",
                "--> smt/src/lib.rs: `crate::TvPlus(v)`",
            ],
            [
                "added-thread",
                "error[krs::analysis::instance-context-caller]: `TvPlus` reads the cell group `Thread` through its function context in one instance of the Map collection cell `thread`, the instance it is evaluated in, and this sentence is not inside such an instance, so it determines none: a function has one value for its arguments, so it is applied only from a sentence about one instance of that holder (a rule, a context alias or a function context for the group, or for a group inside its instance)",
                "--> smt/src/lib.rs: `crate::TvPlus(v)`",
            ],
            [
                "every-thread",
                "error[krs::analysis::instance-context-caller]: `TvPlus` reads the cell group `Thread` through its function context in one instance of the Map collection cell `thread`, the instance it is evaluated in, and this sentence is not inside such an instance, so it determines none: a function has one value for its arguments, so it is applied only from a sentence about one instance of that holder (a rule, a context alias or a function context for the group, or for a group inside its instance)",
                "--> smt/src/lib.rs: `crate::TvPlus(v)`",
            ],
            [
                "wildcard-key",
                "rule [go]: <core> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <thread> <tid> Krs_KeyThread:Int </tid> <tenv> 0 |-> V:Int ... </tenv> ... </thread> <cid> Krs_KeyCore:Int </cid> ... </core>",
                "done ( 12 ) ~> .K",
            ],
            [
                "wildcard-core-key",
                "rule [go]: <core> <cid> Krs_KeyCore:Int </cid> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> ... </core>",
                "done ( 12 ) ~> .K",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// A table clause for `Core`, at the core's main cell, whose record names a cell of a thread:
/// `{ k, tenv }`, with the `have` form's call of `tvPlus`.
const THREAD_RECORD: &str = r"
k::rules! {
    for Core;
    use Step::*;

    go: { k: [Go(), ..], tenv: { 0 -> v, .. } } => { k: [Done { n: crate::TvPlus(v) }, ..] };
}
";

/// The `cells!` spelling of [`THREAD_RECORD`]: a rule for `Core` that names the thread's cell
/// through its group's struct.
const THREAD_RECORD_CELLS: &str = r#"
#[k::rule(label = "go")]
pub fn go(
    v: k::Term<k::builtin::Int>,
    k::cells! {
        k: k::configuration::KCell(crate::Step::Go(), ..),
        crate::Thread::tenv: k::configuration::Cell(k::map![0 -> v, ..]),
        state @ ..
    }: crate::Core,
) -> crate::Core {
    k::cells! {
        k: k::configuration::KCell(crate::Step::Done(crate::TvPlus(v)), ..),
        ..state
    }
}
"#;

/// [`SMT`] with its one core at a fixed position instead of in the cores' collection.
fn smt_fixed_core() -> String {
    let fixed = SMT
        .replace(
            "    #[k::cell(nested)]\n    pub cores: Cores,",
            "    #[k::cell(nested)]\n    pub core: Core,",
        )
        .replace(
            "cores: Cores { core: Core { cid: 0,",
            "core: Core { cid: 0,",
        )
        .replace(
            "tmem: k::map![1 -> 20] } } } },",
            "tmem: k::map![1 -> 20] } } },",
        );
    assert_ne!(fixed, SMT);
    fixed
}

/// A sentence's cells lie in one instance of each holder on their deepest chain, so a rule for
/// `Core` whose record names a thread's cell, `{ k, tenv }`, matches one core and one thread of
/// it, as naming `k` matches one core: it is inside that thread, as the `have tenv[..]` form of
/// the clause for the sort is, and as the rule for `Core` whose entry steps one thread
/// ([`an_entry_that_steps_one_instance_is_inside_it`]) is. The three, and the record's `cells!`
/// spelling, which names the cell through `crate::Thread`, apply `tvPlus`, passing the core's and
/// the thread's keys, emit the same rule up to where the key cells sit among the items of their
/// instance, and run to `done ( 12 )`; without the call the record matches what the `have` form
/// matches and ends at `done ( 7 )`. Naming the thread's key cell matches its key, which the
/// call is then passed, and writing another key is refused, as for the group's own key. A
/// device's cell is no cell of the group, and stays refused. A core at a fixed position lies
/// outside every instance, so its `k` beside a thread's `tenv` is matched once beside that
/// thread, inside which the rule is, in the record and the `have` form alike.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "The cases, their runs and the comparison of the accepted forms read as one table."
)]
fn a_record_naming_a_cell_of_a_nested_instance_is_inside_it() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let whitespace = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    let record =
        |rule: &str| format!("k::rules! {{\n    for Core;\n    use Step::*;\n\n    {rule}\n}}\n");
    let smt_fixed = smt_fixed_core();
    let cases: Vec<(&str, &str, String)> = vec![
        ("have", SMT, DEEPEST_CASES[0].1.to_owned()),
        ("record", SMT, THREAD_RECORD.to_owned()),
        ("record-cells", SMT, THREAD_RECORD_CELLS.to_owned()),
        ("stepping-entry", SMT, THREAD_ENTRY_CELLS.to_owned()),
        ("have-no-call", SMT, DEEPEST_CASES[1].1.to_owned()),
        (
            "record-no-call",
            SMT,
            record("go: { k: [Go(), ..], tenv: { 0 -> v, .. } } => { k: [Done { n: v }, ..] };"),
        ),
        (
            "record-key",
            SMT,
            record(
                "go: { k: [Go(), ..], tid: t, tenv: { 0 -> v, .. } } => { k: [Done { n: crate::TvPlus(t) }, ..] };",
            ),
        ),
        (
            "record-key-written",
            SMT,
            record(
                "go: { k: [Go(), ..], tid: t, tenv: { 0 -> v, .. } } => { k: [Done { n: v }, ..], tid: 3 };",
            ),
        ),
        (
            "record-device",
            SMT,
            record("go: { k: [Go(), ..], denv: { 0 -> v, .. } } => { k: [Done { n: v }, ..] };"),
        ),
        ("record-fixed-core", &smt_fixed, THREAD_RECORD.to_owned()),
        ("have-fixed-core", &smt_fixed, DEEPEST_CASES[0].1.to_owned()),
    ];
    let mut accepted = Vec::new();
    let outcomes = cases
        .iter()
        .map(|(name, configuration, rules)| {
            let manifest = instance_definitions(
                &temporary.path().join(name),
                "",
                &[("smt", &format!("{configuration}{TV_PLUS}{rules}"))],
            )
            .remove(0);
            let (success, _, _) = krs_on(target.path(), &manifest, "smt", "check", &[]);
            let mut report = vec![(*name).to_owned()];
            if !success {
                report.extend(check_report(target.path(), &manifest, "smt"));
                return report;
            }
            let flat = emitted(target.path(), &manifest, "smt");
            let rule = sentence(&flat, "rule [go]:").to_owned();
            report.push(rule.clone());
            let path = manifest.with_file_name("program.txt");
            fs::write(&path, "go").unwrap();
            let (success, stdout, stderr) = krs_on(
                target.path(),
                &manifest,
                "smt",
                "run",
                &[path.to_str().unwrap()],
            );
            assert!(success, "{name}:\n{stdout}\n{stderr}");
            let run = cell(&whitespace(&stdout), "k");
            report.push(run.clone());
            accepted.push((*name, rule, run));
            report
        })
        .collect::<Vec<_>>();
    // The four spellings of the call's clause: one rule, each key cell bound once, to the key
    // passed, and one run.
    let key_cells = [
        "<cid> Krs_KeyCore:Int </cid> ",
        "<tid> Krs_KeyThread:Int </tid> ",
    ];
    let without_keys = |rule: &str| {
        key_cells
            .iter()
            .fold(rule.to_owned(), |rule, key| rule.replace(key, ""))
    };
    let alike = |names: &[&str]| {
        let found = names
            .iter()
            .map(|name| {
                accepted
                    .iter()
                    .find(|(accepted, _, _)| accepted == name)
                    .unwrap_or_else(|| panic!("{name} is refused: {outcomes:#?}"))
            })
            .collect::<Vec<_>>();
        for (name, rule, run) in &found {
            assert_eq!(without_keys(rule), without_keys(&found[0].1), "{name}");
            assert_eq!(run, &found[0].2, "{name}");
        }
        found
    };
    for (name, rule, _) in alike(&["have", "record", "record-cells", "stepping-entry"]) {
        for key in key_cells {
            assert_eq!(rule.matches(key).count(), 1, "{name}: {rule}");
        }
    }
    alike(&["have-no-call", "record-no-call"]);
    alike(&["record-fixed-core", "have-fixed-core"]);
    expect_test::expect![[r#"
        [
            [
                "have",
                "rule [go]: <core> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> ... </core>",
                "done ( 12 ) ~> .K",
            ],
            [
                "record",
                "rule [go]: <core> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> ... </core>",
                "done ( 12 ) ~> .K",
            ],
            [
                "record-cells",
                "rule [go]: <core> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> ... </core>",
                "done ( 12 ) ~> .K",
            ],
            [
                "stepping-entry",
                "rule [go]: <core> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> <cid> Krs_KeyCore:Int </cid> ... </core>",
                "done ( 12 ) ~> .K",
            ],
            [
                "have-no-call",
                "rule [go]: <core> <k> go => done ( V:Int ) ... </k> <thread> <tenv> 0 |-> V:Int ... </tenv> ... </thread> ... </core>",
                "done ( 7 ) ~> .K",
            ],
            [
                "record-no-call",
                "rule [go]: <core> <k> go => done ( V:Int ) ... </k> <thread> <tenv> 0 |-> V:Int ... </tenv> ... </thread> ... </core>",
                "done ( 7 ) ~> .K",
            ],
            [
                "record-key",
                "rule [go]: <core> <k> go => done ( tvPlus ( T:Int ) #instance ( Krs_KeyCore:Int , T:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> T:Int </tid> ... </thread> ... </core>",
                "done ( 5 ) ~> .K",
            ],
            [
                "record-key-written",
                "error[krs::analysis::map-collection-key]: the rule writes `tid`, the key of the `Thread` instance of the Map collection `thread` it steps: a rule is a local step of one instance of each Map collection its cells lie in, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> smt/src/lib.rs: `3 };`",
            ],
            [
                "record-device",
                "error[krs::analysis::cell-outside-subject]: `Core` has no cell `denv`: a sentence about the cell group `Core` names only the cells inside the group, and `denv` is another cell of configuration `Smt`; write the sentence for `Smt` to name it",
                "--> smt/src/lib.rs: `denv: { 0 -> v,`",
            ],
            [
                "record-fixed-core",
                "rule [go]: <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyThread:Int ) ) ... </k>",
                "done ( 12 ) ~> .K",
            ],
            [
                "have-fixed-core",
                "rule [go]: <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyThread:Int ) ) ... </k>",
                "done ( 12 ) ~> .K",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// A rule for the configuration (`for Smt`) whose record names cells of a Map collection's
/// instance flat: `k` of one core, then also `tenv` of one thread of it.
fn configuration_record(rule: &str) -> String {
    format!("k::rules! {{\n    for Smt;\n    use Step::*;\n\n    {rule}\n}}\n")
}

/// The `cells!` spelling of a rule for the configuration that names the core's `k` flat,
/// through the core's group struct, and `extra` beside it; its result writes `Done(result)` and
/// `written`.
fn configuration_cells(parameters: &str, extra: &str, result: &str, written: &str) -> String {
    format!(
        r#"
#[k::rule(label = "go")]
pub fn go(
    {parameters}
    k::cells! {{
        crate::Core::k: k::configuration::KCell(crate::Step::Go(), ..),
        {extra}
        state @ ..
    }}: crate::Smt,
) -> crate::Smt {{
    k::cells! {{
        crate::Core::k: k::configuration::KCell(crate::Step::Done({result}), ..),
        {written}
        ..state
    }}
}}
"#
    )
}

/// [`SMT`] with a fixed group `Misc` beside the cores whose cell has the cores' collection's
/// field name `core`, emitted (and named in a readable record) as `spare`.
fn smt_with_spare_core() -> String {
    let changed = SMT
        .replace(
            "#[k::configuration]\npub struct Smt {",
            "#[k::cell]\npub struct Misc {\n    #[k::cell(name = \"spare\")]\n    pub core: Int,\n}\n\n#[k::configuration]\npub struct Smt {\n    #[k::cell(nested)]\n    pub misc: Misc,",
        )
        .replace("            ticks: 0,", "            misc: Misc { core: 0 },\n            ticks: 0,");
    assert_eq!(changed.matches("Misc").count(), 3, "{changed}");
    changed
}

/// [`SMT`] with its cores held in a collection of `order` instead of a Map.
fn smt_cores_in(order: &str) -> String {
    let changed = SMT.replace(
        "pub struct Cores {\n    #[k::cell(multiplicity = \"*\", cell_type = \"Map\"",
        &format!(
            "pub struct Cores {{\n    #[k::cell(multiplicity = \"*\", cell_type = \"{order}\""
        ),
    );
    assert_ne!(changed, SMT);
    changed
}

/// A rule typed by the configuration names a cell of a Map collection's instance flat, with the
/// meaning a rule for a group has: a sentence's cells lie in one instance of each holder on
/// their deepest chain, so `for Smt { k: .. }` matches one core, the one whose `k` matches, as
/// `for Core { k: .. }` does, and `{ k, tenv }` one thread of that core. Each is inside the
/// instance it matches, passing its keys to a function evaluated there (`cidPlus`, `tvPlus`).
/// The readable record, its `cells!` spelling (`crate::Core::k:`), the rule for the group, and
/// the configuration rule whose entry steps one instance (or the `have` form) emit one rule up
/// to where the key cells sit, and run alike. Naming a core's key cell matches it, and writing
/// another key is `map-collection-key`, in both spellings. Kept refused, each with its own
/// message: a cell of a List or a Set collection's instance named flat (the List's
/// middle-match gap, the Set's merging), a core's cell beside a cell outside every instance
/// (IC finding 1), and a core's cell beside a device's (two instances on no one chain).
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "The cases, their runs and the comparison of the accepted forms read as one table."
)]
fn a_rule_for_the_configuration_names_a_cell_of_a_map_instance_flat() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let whitespace = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    let core_record =
        |rule: &str| format!("k::rules! {{\n    for Core;\n    use Step::*;\n\n    {rule}\n}}\n");
    let cid_call = "go: { k: [Go(), ..] } => { k: [Done { n: crate::CidPlus(1) }, ..] };";
    let tenv_call =
        "go: { k: [Go(), ..], tenv: { 0 -> v, .. } } => { k: [Done { n: crate::TvPlus(v) }, ..] };";
    // The cores in a List or a Set hold no instance a function context could read.
    let smt = format!("{SMT}{TV_PLUS}{CID_PLUS}");
    let smt_spare = format!("{}{TV_PLUS}{CID_PLUS}", smt_with_spare_core());
    let smt_list = smt_cores_in("List");
    let smt_set = smt_cores_in("Set");
    let no_call = "go: { k: [Go(), ..] } => { k: [Done { n: 1 }, ..] };";
    let cases: Vec<(&str, &str, String)> = vec![
        ("group-k", &smt, core_record(cid_call)),
        ("configuration-k", &smt, configuration_record(cid_call)),
        (
            "configuration-k-cells",
            &smt,
            configuration_cells("", "", "crate::CidPlus(1)", ""),
        ),
        ("stepping-entry-k", &smt, DEEPEST_CASES[3].1.to_owned()),
        ("group-tenv", &smt, THREAD_RECORD.to_owned()),
        ("configuration-tenv", &smt, configuration_record(tenv_call)),
        (
            "configuration-tenv-cells",
            &smt,
            configuration_cells(
                "v: k::Term<k::builtin::Int>,",
                "crate::Thread::tenv: k::configuration::Cell(k::map![0 -> v, ..]),",
                "crate::TvPlus(v)",
                "",
            ),
        ),
        ("have-tenv", &smt, DEEPEST_CASES[0].1.to_owned()),
        (
            "group-tv-only",
            &smt,
            "k::rules! {\n    for Thread;\n\n    go: { tv: 5 } => { tv: 6 };\n}\n".to_owned(),
        ),
        (
            "configuration-tv-only",
            &smt,
            configuration_record("go: { tv: 5 } => { tv: 6 };"),
        ),
        (
            "configuration-key",
            &smt,
            configuration_record(
                "go: { k: [Go(), ..], cid: c } => { k: [Done { n: crate::CidPlus(c) }, ..] };",
            ),
        ),
        (
            "configuration-key-written",
            &smt,
            configuration_record(
                "go: { k: [Go(), ..], cid: c } => { k: [Done { n: c }, ..], cid: 3 };",
            ),
        ),
        (
            "configuration-key-written-cells",
            &smt,
            configuration_cells(
                "c: k::Term<k::builtin::Int>,",
                "crate::Core::cid: k::configuration::Cell(c),",
                "c",
                "crate::Core::cid: k::configuration::Cell(3),",
            ),
        ),
        // A cell of another group that shares the cores' collection's field name is not the
        // holder: the core's key written flat beside it is still judged.
        (
            "configuration-key-written-beside-spare",
            &smt_spare,
            configuration_record(
                "go: { k: [Go(), ..], cid: c, spare: s } => { k: [Done { n: s }, ..], cid: 3 };",
            ),
        ),
        (
            "configuration-key-written-beside-spare-cells",
            &smt_spare,
            configuration_cells(
                "c: k::Term<k::builtin::Int>, s: k::Term<k::builtin::Int>,",
                "crate::Core::cid: k::configuration::Cell(c), crate::Misc::core: k::configuration::Cell(s),",
                "s",
                "crate::Core::cid: k::configuration::Cell(3),",
            ),
        ),
        (
            "configuration-k-list",
            &smt_list,
            configuration_record(no_call),
        ),
        (
            "configuration-k-set",
            &smt_set,
            configuration_record(no_call),
        ),
        (
            "configuration-k-mem",
            &smt,
            configuration_record(
                "go: { k: [Go(), ..], mem: { 0 -> v, .. } } => { k: [Done { n: v }, ..] };",
            ),
        ),
        (
            "configuration-k-device",
            &smt,
            configuration_record(
                "go: { k: [Go(), ..], denv: { 0 -> v, .. } } => { k: [Done { n: v }, ..] };",
            ),
        ),
    ];
    let mut accepted = Vec::new();
    let outcomes = cases
        .iter()
        .map(|(name, configuration, rules)| {
            let manifest = instance_definitions(
                &temporary.path().join(name),
                "",
                &[("smt", &format!("{configuration}{rules}"))],
            )
            .remove(0);
            let (success, _, _) = krs_on(target.path(), &manifest, "smt", "check", &[]);
            let mut report = vec![(*name).to_owned()];
            if !success {
                report.extend(check_report(target.path(), &manifest, "smt"));
                return report;
            }
            let flat = emitted(target.path(), &manifest, "smt");
            let rule = sentence(&flat, "rule [go]:").to_owned();
            report.push(rule.clone());
            let path = manifest.with_file_name("program.txt");
            fs::write(&path, "go").unwrap();
            let (success, stdout, stderr) = krs_on(
                target.path(),
                &manifest,
                "smt",
                "run",
                &[path.to_str().unwrap()],
            );
            assert!(success, "{name}:\n{stdout}\n{stderr}");
            let run = cell(&whitespace(&stdout), "k");
            report.push(run.clone());
            accepted.push((*name, rule, run));
            report
        })
        .collect::<Vec<_>>();
    let key_cells = [
        "<cid> Krs_KeyCore:Int </cid> ",
        "<tid> Krs_KeyThread:Int </tid> ",
    ];
    // The stepping entry keeps the computation's rest under a name, `go ~> Tail0:K =>
    // done(..) ~> Tail0:K`, which is `go => done(..) ...`.
    let without_keys = |rule: &str| {
        key_cells
            .iter()
            .fold(rule.to_owned(), |rule, key| rule.replace(key, ""))
            .replace(" ~> Tail0:K =>", " =>")
            .replace(" ~> Tail0:K </k>", " ... </k>")
    };
    let alike = |names: &[&str]| {
        let found = names
            .iter()
            .map(|name| {
                accepted
                    .iter()
                    .find(|(accepted, _, _)| accepted == name)
                    .unwrap_or_else(|| panic!("{name} is refused: {outcomes:#?}"))
            })
            .collect::<Vec<_>>();
        for (name, rule, run) in &found {
            assert_eq!(without_keys(rule), without_keys(&found[0].1), "{name}");
            assert_eq!(run, &found[0].2, "{name}");
        }
    };
    alike(&[
        "group-k",
        "configuration-k",
        "configuration-k-cells",
        "stepping-entry-k",
    ]);
    alike(&["group-tv-only", "configuration-tv-only"]);
    alike(&[
        "group-tenv",
        "configuration-tenv",
        "configuration-tenv-cells",
        "have-tenv",
    ]);
    expect_test::expect![[r#"
        [
            [
                "group-k",
                "rule [go]: <core> <k> go => done ( cidPlus ( 1 ) #instance ( Krs_KeyCore:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> ... </core>",
                "done ( 1 ) ~> .K",
            ],
            [
                "configuration-k",
                "rule [go]: <core> <k> go => done ( cidPlus ( 1 ) #instance ( Krs_KeyCore:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> ... </core>",
                "done ( 1 ) ~> .K",
            ],
            [
                "configuration-k-cells",
                "rule [go]: <core> <k> go => done ( cidPlus ( 1 ) #instance ( Krs_KeyCore:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> ... </core>",
                "done ( 1 ) ~> .K",
            ],
            [
                "stepping-entry-k",
                "rule [go]: <core> <k> go ~> Tail0:K => done ( cidPlus ( 1 ) #instance ( Krs_KeyCore:Int ) ) ~> Tail0:K </k> <cid> Krs_KeyCore:Int </cid> ... </core>",
                "done ( 1 ) ~> .K",
            ],
            [
                "group-tenv",
                "rule [go]: <core> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> ... </core>",
                "done ( 12 ) ~> .K",
            ],
            [
                "configuration-tenv",
                "rule [go]: <core> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> ... </core>",
                "done ( 12 ) ~> .K",
            ],
            [
                "configuration-tenv-cells",
                "rule [go]: <core> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> ... </core>",
                "done ( 12 ) ~> .K",
            ],
            [
                "have-tenv",
                "rule [go]: <core> <k> go => done ( tvPlus ( V:Int ) #instance ( Krs_KeyCore:Int , Krs_KeyThread:Int ) ) ... </k> <cid> Krs_KeyCore:Int </cid> <thread> <tenv> 0 |-> V:Int ... </tenv> <tid> Krs_KeyThread:Int </tid> ... </thread> ... </core>",
                "done ( 12 ) ~> .K",
            ],
            [
                "group-tv-only",
                "rule [go]: <thread> <tv> 5 => 6 </tv> ... </thread>",
                "go ~> .K",
            ],
            [
                "configuration-tv-only",
                "rule [go]: <thread> <tv> 5 => 6 </tv> ... </thread>",
                "go ~> .K",
            ],
            [
                "configuration-key",
                "rule [go]: <core> <k> go => done ( cidPlus ( C:Int ) #instance ( C:Int ) ) ... </k> <cid> C:Int </cid> ... </core>",
                "done ( 0 ) ~> .K",
            ],
            [
                "configuration-key-written",
                "error[krs::analysis::map-collection-key]: the rule writes `cid`, the key of the `Core` instance of the Map collection `core` it steps: a rule is a local step of one instance of each Map collection its cells lie in, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> smt/src/lib.rs: `3 };`",
            ],
            [
                "configuration-key-written-cells",
                "error[krs::analysis::map-collection-key]: the rule writes `cid`, the key of the `Core` instance of the Map collection `core` it steps: a rule is a local step of one instance of each Map collection its cells lie in, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> smt/src/lib.rs: `k::configuration`",
            ],
            [
                "configuration-key-written-beside-spare",
                "error[krs::analysis::map-collection-key]: the rule writes `cid`, the key of the `Core` instance of the Map collection `core` it steps: a rule is a local step of one instance of each Map collection its cells lie in, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> smt/src/lib.rs: `3 };`",
            ],
            [
                "configuration-key-written-beside-spare-cells",
                "error[krs::analysis::map-collection-key]: the rule writes `cid`, the key of the `Core` instance of the Map collection `core` it steps: a rule is a local step of one instance of each Map collection its cells lie in, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
                "--> smt/src/lib.rs: `k::configuration`",
            ],
            [
                "configuration-k-list",
                "error[krs::analysis::collection-entry]: the cell `k` is a cell of a collection's (`*`) instance, so no single cell has the content an entry naming it at the record's level would name: there is one `k` per instance, and an entry names the instance through its instance record; `k` is a cell of an instance of the collection `core`; so write the entry inside its record, `core: [Core { k: .., .. }, ..]`",
                "--> smt/src/lib.rs: `[Go(), ..] } =>`",
            ],
            [
                "configuration-k-set",
                "error[krs::analysis::collection-entry]: the cell `k` is a cell of a collection's (`*`) instance, so no single cell has the content an entry naming it at the record's level would name: there is one `k` per instance, and an entry names the instance through its instance record; `k` is a cell of an instance of the collection `core`; so write the entry inside its record, `core: { Core { k: .., .. }, .. }`",
                "--> smt/src/lib.rs: `[Go(), ..] } =>`",
            ],
            [
                "configuration-k-mem",
                "rule [go]: <core> <k> go => done ( V:Int ) ... </k> ... </core> <mem> 0 |-> V:Int ... </mem>",
                "done ( 11 ) ~> .K",
            ],
            [
                "configuration-k-device",
                "error[krs::analysis::collection-entry]: the rule matches `k`, a cell of an instance of the Map collection cell `core`, and `denv`, a cell of an instance of the Map collection cell `dev`: neither instance holds the other, so the rule would match one instance of each, and a sentence whose cells lie in instances of two holders neither of which holds the other is not supported yet; name the instance of `dev` through its instance list instead, `dev: { .. }`, beside `k`",
                "--> smt/src/lib.rs: `denv: { 0 -> v,`",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// [`SMT`] with `replacements` applied, each of which must change it.
fn smt_with(replacements: &[(&str, &str)]) -> String {
    replacements
        .iter()
        .fold(SMT.to_owned(), |source, (from, to)| {
            assert!(source.contains(from), "{from}");
            source.replace(from, to)
        })
}

/// A record at a configuration position, an instance record in an instance list or a group
/// record, is the record of its struct, as `k::fragment![crate::Core { .. }]` writes it: each
/// field is one of the struct's own children, written as that child's entry. A cell deeper in
/// the struct is no field of it, so each record refuses it, in a readable rule, a `cells!` rule
/// and a claim alike, naming the record that reaches it: a group child's own record
/// (`regs: Regs { r0: .., .. }`, accepted, as the group rule's), or, below a `?` or `*` cell,
/// the sentence's own record, which names a cell at any depth by its name because it is the
/// sentence's set of cells, as its `cells!` entries are (`crate::Thread::tenv:`): accepted, the
/// same step whether the sentence is for `Core` or for the configuration (IC-3). A name that
/// is no cell of the struct's tree keeps the bare refusal. A record that is not its struct's
/// (a field the struct lacks, a head naming another struct) is one mistake, a term's
/// (`invalid-term`), for a group record and an instance record alike.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "The cases and their reports read as one verdict table."
)]
fn a_record_at_a_configuration_position_names_its_struct_s_own_children() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rules = |subject: &str, body: &str| {
        format!("k::rules! {{\n    for {subject};\n    use Step::*;\n\n    {body}\n}}\n")
    };
    let instance = |fields: &str| {
        rules(
            "Smt",
            &format!(
                "go: {{ core: {{ me @ Core {{ k: [Go(), ..], {fields}, .. }}, .. }} }} => {{ core: {{ Core {{ k: [Done {{ n: v }}, ..], ..me }}, .. }} }};"
            ),
        )
    };
    let flat = |subject: &str, fields: &str| {
        rules(
            subject,
            &format!("go: {{ k: [Go(), ..], {fields} }} => {{ k: [Done {{ n: v }}, ..] }};"),
        )
    };
    let threads = "pub struct Threads {\n    #[k::cell(multiplicity = \"*\", cell_type = \"Map\"";
    let regs = smt_with(&[
        (
            "#[k::cell]\npub struct Core {",
            "#[k::cell]\npub struct Regs {\n    #[k::cell]\n    pub r0: Int,\n}\n\n#[k::cell]\npub struct Core {",
        ),
        (
            "    pub cid: Int,\n",
            "    pub cid: Int,\n    #[k::cell(nested)]\n    pub regs: Regs,\n",
        ),
        (
            "core: Core { cid: 0,",
            "core: Core { cid: 0, regs: Regs { r0: 4 },",
        ),
    ]);
    let fpu = smt_with(&[
        (
            "    pub threads: Threads,\n}",
            "    pub threads: Threads,\n    #[k::cell(multiplicity = \"?\", nested)]\n    pub fpu: Option<lib::Fpu>,\n}",
        ),
        (
            "tmem: k::map![1 -> 20] } } } },",
            "tmem: k::map![1 -> 20] } }, fpu: k::absent!(lib::Fpu { busy: 0, fa: 0 }) } },",
        ),
    ]);
    let listed = smt_with(&[(threads, &threads.replace("\"Map\"", "\"List\""))]);
    let slots = smt_with(&[
        (
            "#[k::cell]\npub struct Thread {",
            "#[k::cell]\npub struct Slot {\n    #[k::cell]\n    pub sid: Int,\n    #[k::cell]\n    pub sv: Int,\n}\n\n#[k::cell]\npub struct Slots {\n    #[k::cell(multiplicity = \"*\", cell_type = \"Map\", initial, nested)]\n    pub slot: Slot,\n}\n\n#[k::cell]\npub struct Thread {",
        ),
        (
            "    pub tmem: k::builtin::Map<Int, Int>,\n}",
            "    pub tmem: k::builtin::Map<Int, Int>,\n    #[k::cell(nested)]\n    pub slots: Slots,\n}",
        ),
        (
            "tmem: k::map![1 -> 20] }",
            "tmem: k::map![1 -> 20], slots: Slots { slot: Slot { sid: 0, sv: 9 } } }",
        ),
    ]);
    let fixed = smt_fixed_core();
    let fixed_regs = regs
        .replace(
            "    #[k::cell(nested)]\n    pub cores: Cores,",
            "    #[k::cell(nested)]\n    pub core: Core,",
        )
        .replace(
            "cores: Cores { core: Core { cid: 0,",
            "core: Core { cid: 0,",
        )
        .replace(
            "tmem: k::map![1 -> 20] } } } },",
            "tmem: k::map![1 -> 20] } } },",
        );
    let cells_instance = r#"
#[k::rule(label = "go")]
pub fn go(
    v: k::Term<k::builtin::Int>,
    k::cells! {
        Cores::core: {
            me @ k::fragment![crate::Core { k: k::k![Step::Go(), tail @ ..], tenv: k::map![0 -> v, ..], .. }],
            others @ ..
        },
        state @ ..
    }: Smt,
) -> Smt {
    k::cells! {
        Cores::core: { k::fragment![crate::Core { k: k::k![Step::Done { n: v }, ..tail], ..me }], ..others },
        ..state
    }
}
"#;
    let claim = "k::claims! {\n    for Smt;\n    use Step::*;\n\n    #[k::claim(all_paths)]\n    go_claim: { core: { me @ Core { k: [Go(), ..], tenv: { 0 -> v, .. }, .. }, .. } } => { core: { Core { k: [Done { n: v }, ..], ..me }, .. } };\n}\n";
    let tenv = "tenv: { 0 -> v, .. }";
    let list_holder = "thread: [Thread { tenv: { 0 -> v, .. }, .. }, ..]";
    let cases: Vec<(&str, &str, String)> = vec![
        ("group-flat", SMT, flat("Core", tenv)),
        ("configuration-flat", SMT, flat("Smt", tenv)),
        ("instance-record", SMT, instance(tenv)),
        ("instance-record-cells", SMT, cells_instance.to_owned()),
        ("instance-record-claim", SMT, claim.to_owned()),
        ("instance-record-list", &listed, instance(tenv)),
        (
            "instance-record-list-holder",
            &listed,
            instance(list_holder),
        ),
        (
            "configuration-list-holder",
            &listed,
            flat("Smt", list_holder),
        ),
        ("instance-record-two-levels", &slots, instance("sv: v")),
        ("configuration-two-levels", &slots, flat("Smt", "sv: v")),
        ("instance-record-optional", &fpu, instance("busy: v")),
        (
            "configuration-optional-holder",
            &fpu,
            flat("Smt", "fpu: Some(lib::Fpu { busy: v, .. })"),
        ),
        ("instance-record-group-child", &regs, instance("r0: v")),
        (
            "instance-record-group-record",
            &regs,
            instance("regs: Regs { r0: v }"),
        ),
        ("group-flat-group-child", &regs, flat("Core", "r0: v")),
        (
            "group-record-tenv",
            &fixed,
            rules(
                "Smt",
                "go: { core: Core { tenv: { 0 -> v, .. }, .. }, k: [Go(), ..] } => { k: [Done { n: v }, ..] };",
            ),
        ),
        (
            "group-record-group-child",
            &fixed_regs,
            rules(
                "Smt",
                "go: { core: Core { r0: v, .. }, k: [Go(), ..] } => { k: [Done { n: v }, ..] };",
            ),
        ),
        ("instance-record-no-such-cell", SMT, instance("nope: v")),
        (
            "group-record-no-such-cell",
            &fixed,
            rules(
                "Smt",
                "go: { core: Core { nope: v, .. }, k: [Go(), ..] } => { k: [Done { n: v }, ..] };",
            ),
        ),
        // A record of another struct than its cell's group (an instance record's: readable_records).
        (
            "group-record-other-struct",
            &fixed_regs,
            rules(
                "Smt",
                "go: { core: Regs { r0: v }, k: [Go(), ..] } => { k: [Done { n: v }, ..] };",
            ),
        ),
    ];
    let outcomes = cases
        .iter()
        .map(|(name, configuration, sentences)| {
            let manifest = instance_definitions(
                &temporary.path().join(name),
                "",
                &[("smt", &format!("{configuration}{sentences}"))],
            )
            .remove(0);
            let (success, _, _) = krs_on(target.path(), &manifest, "smt", "check", &[]);
            let mut report = vec![(*name).to_owned()];
            if success {
                let flat = emitted(target.path(), &manifest, "smt");
                report.push(sentence(&flat, "rule [go]:").to_owned());
            } else {
                report.extend(check_report(target.path(), &manifest, "smt"));
            }
            report
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            [
                "group-flat",
                "rule [go]: <core> <k> go => done ( V:Int ) ... </k> <thread> <tenv> 0 |-> V:Int ... </tenv> ... </thread> ... </core>",
            ],
            [
                "configuration-flat",
                "rule [go]: <core> <k> go => done ( V:Int ) ... </k> <thread> <tenv> 0 |-> V:Int ... </tenv> ... </thread> ... </core>",
            ],
            [
                "instance-record",
                "error[krs::analysis::invalid-term]: the instance cell `Core` has no child `tenv`: a record names its struct's own children, each as that child's entry, and `tenv` lies in an instance of the Map collection `thread` inside `Core`, whose entry a record does not name yet; a sentence's own record names a cell at any depth by its name, so name `tenv`, or `thread`, which holds it, there, beside `Core`'s other cells, as a rule for `Core` does",
                "--> smt/src/lib.rs: `tenv: { 0 -> v,`",
            ],
            [
                "instance-record-cells",
                "error[krs::analysis::invalid-term]: the instance cell `Core` has no child `tenv`: a record names its struct's own children, each as that child's entry, and `tenv` lies in an instance of the Map collection `thread` inside `Core`, whose entry a record does not name yet; a sentence's own record names a cell at any depth by its name, so name `tenv`, or `thread`, which holds it, there, beside `Core`'s other cells, as a rule for `Core` does",
                "--> smt/src/lib.rs: `tenv: k::map![0`",
            ],
            [
                "instance-record-claim",
                "error[krs::analysis::invalid-term]: the instance cell `Core` has no child `tenv`: a record names its struct's own children, each as that child's entry, and `tenv` lies in an instance of the Map collection `thread` inside `Core`, whose entry a record does not name yet; a sentence's own record names a cell at any depth by its name, so name `tenv`, or `thread`, which holds it, there, beside `Core`'s other cells, as a rule for `Core` does",
                "--> smt/src/lib.rs: `tenv: { 0 -> v,`",
            ],
            [
                "instance-record-list",
                "error[krs::analysis::invalid-term]: the instance cell `Core` has no child `tenv`: a record names its struct's own children, each as that child's entry, and `tenv` lies in an instance of the List collection `thread` inside `Core`, whose entry a record does not name yet; a sentence's own record names a cell at any depth by its name, so name `tenv`, or `thread`, which holds it, there, beside `Core`'s other cells, as a rule for `Core` does",
                "--> smt/src/lib.rs: `tenv: { 0 -> v,`",
            ],
            [
                "instance-record-list-holder",
                "error[krs::analysis::invalid-term]: the instance cell `Core` has no child `thread`: a record names its struct's own children, each as that child's entry, and `thread` is the List collection `thread` inside `Core`, whose entry a record does not name yet; a sentence's own record names a cell at any depth by its name, so name `thread` there, beside `Core`'s other cells, as a rule for `Core` does",
                "--> smt/src/lib.rs: `thread: [Thread`",
            ],
            [
                "configuration-list-holder",
                "rule [go]: <core> <k> go => done ( V:Int ) ... </k> <threads> <thread> <tenv> 0 |-> V:Int _ </tenv> ... </thread> ... </threads> ... </core>",
            ],
            [
                "instance-record-two-levels",
                "error[krs::analysis::invalid-term]: the instance cell `Core` has no child `sv`: a record names its struct's own children, each as that child's entry, and `sv` lies in an instance of the Map collection `thread` inside `Core`, whose entry a record does not name yet; a sentence's own record names a cell at any depth by its name, so name `sv`, or `thread`, which holds it, there, beside `Core`'s other cells, as a rule for `Core` does",
                "--> smt/src/lib.rs: `sv: v, .. }, ..`",
            ],
            [
                "configuration-two-levels",
                "rule [go]: <core> <k> go => done ( V:Int ) ... </k> <thread> <slot> <sv> V:Int </sv> ... </slot> ... </thread> ... </core>",
            ],
            [
                "instance-record-optional",
                "error[krs::analysis::invalid-term]: the instance cell `Core` has no child `busy`: a record names its struct's own children, each as that child's entry, and `busy` lies in the optional cell `fpu` inside `Core`, whose entry a record does not name yet; a sentence's own record names a cell at any depth by its name, so name `busy`, or `fpu`, which holds it, there, beside `Core`'s other cells, as a rule for `Core` does",
                "--> smt/src/lib.rs: `busy: v, .. }, .`",
            ],
            [
                "configuration-optional-holder",
                "rule [go]: <core> <k> go => done ( V:Int ) ... </k> <fpu> <busy> V:Int </busy> <fa> _ </fa> </fpu> ... </core>",
            ],
            [
                "instance-record-group-child",
                "error[krs::analysis::invalid-term]: the instance cell `Core` has no child `r0`: a record names its struct's own children, each as that child's entry, and `r0` is a cell of its child `regs`, so write it inside that child's record, `regs: Regs { r0: .., .. }`",
                "--> smt/src/lib.rs: `r0: v, .. }, ..`",
            ],
            [
                "instance-record-group-record",
                "rule [go]: <core> <k> go ~> Tail0:K => done ( V:Int ) ~> Tail0:K </k> <regs> <r0> V:Int </r0> </regs> ... </core>",
            ],
            [
                "group-flat-group-child",
                "rule [go]: <core> <k> go => done ( V:Int ) ... </k> <r0> V:Int </r0> ... </core>",
            ],
            [
                "group-record-tenv",
                "error[krs::analysis::invalid-term]: the group `Core` has no child `tenv`: a record names its struct's own children, each as that child's entry, and `tenv` lies in an instance of the Map collection `thread` inside `Core`, whose entry a record does not name yet; a sentence's own record names a cell at any depth by its name, so name `tenv`, or `thread`, which holds it, there, beside `Core`'s other cells, as a rule for `Core` does",
                "--> smt/src/lib.rs: `tenv: { 0 -> v,`",
            ],
            [
                "group-record-group-child",
                "error[krs::analysis::invalid-term]: the group `Core` has no child `r0`: a record names its struct's own children, each as that child's entry, and `r0` is a cell of its child `regs`, so write it inside that child's record, `regs: Regs { r0: .., .. }`",
                "--> smt/src/lib.rs: `r0: v, .. }, k:`",
            ],
            [
                "instance-record-no-such-cell",
                "error[krs::analysis::invalid-term]: the instance cell `Core` has no child `nope`",
                "--> smt/src/lib.rs: `nope: v, .. }, .`",
            ],
            [
                "group-record-no-such-cell",
                "error[krs::analysis::invalid-term]: the group `Core` has no child `nope`",
                "--> smt/src/lib.rs: `nope: v, .. }, k`",
            ],
            [
                "group-record-other-struct",
                "error[krs::analysis::invalid-term]: the record names `Regs`, and `core` holds `Core`",
                "--> smt/src/lib.rs: `Regs { r0: v },`",
            ],
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// Two harts each step by rules for the configuration that name a hart's cells flat: the boot
/// rule spawns hart 1 beside hart 0, and from there `inc` steps hart 0 and `dec` hart 1, each
/// rule matching the one hart whose computation it matches. `krs search --mode all` reaches a
/// state for each hart's step alone, then the one where both stepped.
#[test]
fn a_rule_for_the_configuration_naming_a_harts_cells_steps_each_hart() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rules = format!(
        "{SMP_BOOT}\nk::rules! {{\n    for Smp;\n    use lib::Op::*;\n\n    inc: {{ k: [Inc(), ..], pc }} => {{ k: [..], pc: k::builtin::int::add(pc, 1) }};\n    dec: {{ k: [Dec(), ..], pc }} => {{ k: [..], pc: k::builtin::int::add(pc, 3) }};\n}}\n"
    );
    let manifest =
        instance_definitions(temporary.path(), "", &[("smp", &smp("Map", &rules))]).remove(0);
    let flat = emitted(target.path(), &manifest, "smp");
    let emitted_rules =
        ["rule [inc]:", "rule [dec]:"].map(|start| sentence(&flat, start).to_owned());
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "spawn").unwrap();
    let whitespace = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    let (success, stdout, stderr) = krs_on(
        target.path(),
        &manifest,
        "smp",
        "search",
        &[program.to_str().unwrap(), "--mode", "all"],
    );
    assert!(success, "{stdout}\n{stderr}");
    let states = whitespace(&stdout)
        .split("<generatedTop> ")
        .skip(1)
        .map(|state| harts(&state[..state.find(" </generatedTop>").unwrap()]).join(" | "))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        (
            [
                "rule [inc]: <hart> <k> inc => .K ... </k> <pc> Pc:Int => Pc:Int +Int 1 </pc> ... </hart>",
                "rule [dec]: <hart> <k> dec => .K ... </k> <pc> Pc:Int => Pc:Int +Int 3 </pc> ... </hart>",
            ],
            [
                "<id> 0 </id> <k> spawn ~> .K </k> <pc> 0 </pc>",
                "<id> 0 </id> <k> inc ~> .K </k> <pc> 0 </pc> | <id> 1 </id> <k> dec ~> .K </k> <pc> 10 </pc>",
                "<id> 0 </id> <k> inc ~> .K </k> <pc> 0 </pc> | <id> 1 </id> <k> .K </k> <pc> 13 </pc>",
                "<id> 0 </id> <k> .K </k> <pc> 1 </pc> | <id> 1 </id> <k> dec ~> .K </k> <pc> 10 </pc>",
                "<id> 0 </id> <k> .K </k> <pc> 1 </pc> | <id> 1 </id> <k> .K </k> <pc> 13 </pc>",
            ],
        )
    "#]].assert_debug_eq(&(emitted_rules, states));
}
