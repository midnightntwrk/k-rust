//! Record updates `Ctor { f: e, ..t }` end to end: constructor and group
//! updates in readable rules, equation tables, and equation fns, run with
//! `krs run`, written in full by `krs expand`, and the diagnostics of a base
//! that is no matched record.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, List, int, list};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Wrap, Pair, Step, Inc, Swapped, Jump, Save, Restore, Peek, Cycle))]
pub enum Cmd {
    #[k::syntax("wrap({a}, {b})")]
    Wrap { a: Int, b: Int },
    #[k::syntax("pair({x}, {y})")]
    Pair { x: Exp, y: Exp },
    #[k::syntax("step({e})")]
    Step { e: Exp },
    #[k::syntax("inc({e})")]
    Inc { e: Exp },
    #[k::syntax("swapped({e})")]
    Swapped { e: Exp },
    #[k::syntax("jump")]
    Jump(),
    #[k::syntax("save")]
    Save(),
    #[k::syntax("restore")]
    Restore(),
    #[k::syntax("peek")]
    Peek(),
    #[k::syntax("cycle")]
    Cycle(),
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub fuel: Int,
    #[k::cell]
    pub depth: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub gas: Int,
    #[k::cell]
    pub stack: List,
    #[k::cell(nested)]
    pub frame: Frame,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            gas: 5,
            stack: list::empty(),
            frame: Frame { pc: 1, fuel: 2, depth: 3 },
        }
    }
}

#[k::function(total, internal)]
pub fn Bump(value: Term<Exp>) -> Term<Exp>;

#[k::function(total, internal)]
pub fn Swap(value: Term<Exp>) -> Term<Exp>;
"#;

/// A constructor update in a rule, nested updates and a group pattern in a
/// table, an update listing every field in an equation fn, and group
/// updates of the frame cell and of a frame saved on the stack.
const UPDATES: &str = r"
k::rules! {
    for Machine;
    use Cmd::*;

    step: { k: [Step { e: w @ Wrap { a: x, .. } }, ..] } => { k: [Wrap { a: int::add(x, 1), ..w }, ..] };
    keep: { k: [Step { e: p @ Pair { x: w @ Wrap { a: 0, .. }, .. } }, ..] } => { k: [Pair { y: w, ..p }, ..] };
    inc: { k: [Inc { e }, ..] } => { k: [crate::Bump(e), ..] };
    swapped: { k: [Swapped { e }, ..] } => { k: [crate::Swap(e), ..] };
    jump: { k: [Jump(), ..], frame: saved @ Frame { pc: p, .. } } => { k: [..], frame: Frame { pc: int::add(p, 10), ..saved } };
    save: { k: [Save(), ..], stack: s, frame: f } => { k: [..], stack: list::concat(list::item(f), s) };
    restore: {
        k: [Restore(), ..],
        gas: g,
        stack: k::term![list::concat(list::item(saved @ k::fragment![Frame { fuel: fl, .. }]), s)],
        frame: _,
    } => {
        k: [..],
        gas: fl,
        stack: s,
        frame: Frame { fuel: 0, depth: int::add(g, 1), ..saved },
    };
    peek: { k: [Peek(), ..], gas: g, frame: Frame { depth: d, .. } } => { k: [..], gas: d };
    cycle: { k: [Cycle(), ..] } => { k: [Save(), Jump(), Restore(), ..] };
}

k::equations! {
    for Bump;
    use Cmd::*;
    bump_wrap: w @ Wrap { a: x, .. } => Wrap { a: int::add(x, 1), ..w };
    bump_pair: o @ Pair { x: i @ Wrap { b: y, .. }, .. } => Pair { x: Wrap { b: int::add(y, 1), ..i }, ..o };
    #[k::equation(owise)]
    bump_other: e => e;
}

#[k::equation]
fn swap_wrap(k::term![Swap(w @ Cmd::Wrap { a: x, b: y })]: Term<Exp>) -> Term<Exp> {
    Cmd::Wrap { a: y, b: x, ..w }
}

#[k::equation(owise)]
fn swap_other(k::term![Swap(e)]: Term<Exp>) -> Term<Exp> {
    e
}
";

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
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-UPDATES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The final configuration's `k`, `gas`, `stack`, and `frame` contents
/// after `krs run` of `program`, one line each.
fn run(target: &Path, manifest: &Path, program: &str) -> String {
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, program).unwrap();
    let (success, stdout, stderr) = krs(target, manifest, "run", &[file.to_str().unwrap()]);
    assert!(success, "`krs run {program}` failed:\n{stdout}\n{stderr}");
    let lines = stdout.lines().map(str::trim).collect::<Vec<_>>();
    let cell = |name: &str| {
        let open = format!("<{name}>");
        let close = format!("</{name}>");
        let start = lines
            .iter()
            .position(|line| *line == open)
            .unwrap_or_else(|| panic!("no <{name}> cell:\n{stdout}"));
        let end = start
            + lines[start..]
                .iter()
                .position(|line| *line == close)
                .unwrap();
        lines[start + 1..end].join(" ")
    };
    format!(
        "{program} => k: {} | gas: {} | stack: {} | frame: {}",
        cell("k"),
        cell("gas"),
        cell("stack"),
        cell("frame")
    )
}

const PROGRAMS: [&str; 9] = [
    "step(wrap(1, 7))",
    "step(pair(wrap(0, 4), 9))",
    "inc(wrap(1, 7))",
    "inc(pair(wrap(1, 2), 3))",
    "swapped(wrap(1, 2))",
    "jump",
    "peek",
    "save",
    "cycle",
];

/// Each update keeps the fields it does not list: `krs run` shows the
/// matched record with the listed fields replaced, for constructors and
/// for the frame group, in the frame cell and saved on the stack.
#[test]
fn an_update_keeps_the_fields_it_does_not_list() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "updates", &format!("{PREAMBLE}{UPDATES}"));
    let outcomes = PROGRAMS.map(|program| run(target.path(), &manifest, program));
    expect_test::expect![[r#"
        [
            "step(wrap(1, 7)) => k: wrap(2, 7) ~> .K | gas: 5 | stack: .List | frame: <pc> 1 </pc> <fuel> 2 </fuel> <depth> 3 </depth>",
            "step(pair(wrap(0, 4), 9)) => k: pair(wrap(0, 4), wrap(0, 4)) ~> .K | gas: 5 | stack: .List | frame: <pc> 1 </pc> <fuel> 2 </fuel> <depth> 3 </depth>",
            "inc(wrap(1, 7)) => k: wrap(2, 7) ~> .K | gas: 5 | stack: .List | frame: <pc> 1 </pc> <fuel> 2 </fuel> <depth> 3 </depth>",
            "inc(pair(wrap(1, 2), 3)) => k: pair(wrap(1, 3), 3) ~> .K | gas: 5 | stack: .List | frame: <pc> 1 </pc> <fuel> 2 </fuel> <depth> 3 </depth>",
            "swapped(wrap(1, 2)) => k: wrap(2, 1) ~> .K | gas: 5 | stack: .List | frame: <pc> 1 </pc> <fuel> 2 </fuel> <depth> 3 </depth>",
            "jump => k: .K | gas: 5 | stack: .List | frame: <pc> 11 </pc> <fuel> 2 </fuel> <depth> 3 </depth>",
            "peek => k: .K | gas: 3 | stack: .List | frame: <pc> 1 </pc> <fuel> 2 </fuel> <depth> 3 </depth>",
            "save => k: .K | gas: 5 | stack: ListItem ( <frame> <pc> 1 </pc> <fuel> 2 </fuel> <depth> 3 </depth> </frame> ) | frame: <pc> 1 </pc> <fuel> 2 </fuel> <depth> 3 </depth>",
            "cycle => k: .K | gas: 2 | stack: .List | frame: <pc> 1 </pc> <fuel> 0 </fuel> <depth> 6 </depth>",
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}

/// `krs expand` writes each update in full: the hidden binders become named
/// binders, and an alias used only as a base loses its `@`. The expanded
/// package runs every program to the same configuration.
#[test]
fn expand_writes_an_update_as_every_field() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "readable",
        &format!("{PREAMBLE}{UPDATES}"),
    );
    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let rule = |label: &str| {
        let start = expanded
            .find(&format!("fn {label}("))
            .unwrap_or_else(|| panic!("`{label}` is written:\n{expanded}"));
        let start = expanded[..start].rfind("#[k::").unwrap();
        let end = start + expanded[start..].find("\n}\n").unwrap() + 2;
        expanded[start..end].to_owned()
    };
    expect_test::expect![[r#"
        #[k::rule(label = "step")]
        pub fn step(
            x: k::Term<k::builtin::Int>,
            w_b: k::Term<k::builtin::Int>,
            k::cells! {
                k : k::configuration::KCell(crate ::Cmd::Step(crate ::Cmd::Wrap(x, w_b)), tail @
                ..), state @ ..
            }: crate::Machine,
        ) -> crate::Machine {
            k::cells! {
                k : k::configuration::KCell(crate ::Cmd::Wrap(k::builtin::int::add(x, 1), w_b),
                ..tail), ..state
            }
        }
        #[k::rule(label = "restore")]
        pub fn restore(
            g: k::Term<k::builtin::Int>,
            saved_pc: k::Term<k::builtin::Int>,
            fl: k::Term<k::builtin::Int>,
            s: k::Term<k::builtin::List>,
            k::cells! {
                k : k::configuration::KCell(crate ::Cmd::Restore(), tail @ ..), gas :
                k::configuration::Cell(g), stack :
                k::configuration::Cell(k::builtin::list::concat(k::builtin::list::item(k::fragment![crate
                ::Frame { pc : saved_pc, fuel : fl, depth : _ }]), s)), frame : _, state @ ..
            }: crate::Machine,
        ) -> crate::Machine {
            k::cells! {
                k : k::configuration::KCell(..tail), gas : k::configuration::Cell(fl), stack :
                k::configuration::Cell(s), frame : k::fragment![crate ::Frame { pc : saved_pc,
                fuel : 0, depth : k::builtin::int::add(g, 1) }], ..state
            }
        }
        #[k::equation]
        fn bump_pair(
            k::term![
                crate ::Bump(crate ::Cmd::Pair(crate ::Cmd::Wrap(i_a, y), o_y))
            ]: k::Term<crate::Exp>,
        ) -> k::Term<crate::Exp> {
            crate::Cmd::Pair(crate::Cmd::Wrap(i_a, k::builtin::int::add(y, 1)), o_y)
        }"#]].assert_eq(&format!(
        "{}\n{}\n{}",
        rule("step"),
        rule("restore"),
        rule("bump_pair")
    ));
    let reference = package(temporary.path(), "reference", &expanded);
    for program in PROGRAMS {
        assert_eq!(
            run(target.path(), &reference, program),
            run(target.path(), &manifest, program)
        );
    }
}

/// The diagnostics of a base that is no matched record of the update's
/// constructor, and of an update in a reference `cells!` term.
#[test]
fn a_base_that_is_no_matched_record_is_rejected() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let errors = [
        ("whole", "w: { k: [Step { e: w }, ..] } => { k: [Wrap { a: 1, ..w }, ..] };"),
        (
            "other",
            "w: { k: [Step { e: w @ Pair { .. } }, ..] } => { k: [Wrap { a: 1, ..w }, ..] };",
        ),
        (
            "twice",
            "w: { k: [Step { e: Pair { x: w @ Wrap { a: 1, .. }, y: w @ Wrap { a: 2, .. } } }, ..] } => { k: [Wrap { a: 1, ..w }, ..] };",
        ),
        (
            "alternative",
            "w: { k: [Step { e: (w @ Wrap { a: 1, .. }) | Pair { x: w @ Wrap { a: 2, .. }, .. } }, ..] } => { k: [Wrap { a: 3, ..w }, ..] };",
        ),
        ("unbound", "w: { k: [Jump(), ..] } => { k: [Wrap { a: 1, ..w }, ..] };"),
    ]
    .map(|(name, clause)| {
        let manifest = package(
            temporary.path(),
            &format!("invalid-{name}"),
            &format!("{PREAMBLE}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    {clause}\n}}\n"),
        );
        check_errors(target.path(), &manifest)
    });
    let cells = package(
        temporary.path(),
        "invalid-cells",
        &format!(
            "{PREAMBLE}
#[k::rule(label = \"cells-update\")]
pub fn cells_update(
    w: Exp,
    x: Term<Int>,
    s: Term<List>,
    k::cells! {{ k: k::configuration::KCell(Cmd::Step {{ e: w @ Cmd::Wrap {{ a: x, b: _ }} }}, tail @ ..), stack: k::configuration::Cell(s), state @ .. }}: Machine,
) -> Machine {{
    k::cells! {{ k: k::configuration::KCell(..tail), stack: k::configuration::Cell(list::item(Cmd::Wrap {{ a: 1, ..w }})), ..state }}
}}
"
        ),
    );
    let cells = check_errors(target.path(), &cells);
    expect_test::expect![[r#"
        (
            [
                [
                    "error[krs::analysis::invalid-record-update]: `..w` takes the fields it does not list from a record matched as `w @ Ctor { .. }` in the left-hand side, but `w` is no such alias; a binder of the whole term names no fields K can read",
                    "--> src/lib.rs:78:59",
                ],
                [
                    "error[krs::analysis::invalid-record-update]: `..w` builds a `Wrap` from `w`, which matched a `Pair`; an update keeps the constructor of its base",
                    "--> src/lib.rs:78:73",
                ],
                [
                    "error[krs::analysis::invalid-record-update]: `..w` needs one record to take its fields from, but the left-hand side binds `w` with `@` more than once",
                    "--> src/lib.rs:78:117",
                ],
                [
                    "error[krs::analysis::invalid-record-update]: `..w` needs one record to take its fields from, but the left-hand side binds `w` with `@` more than once",
                    "--> src/lib.rs:78:121",
                ],
                [
                    "error[krs::expand::invalid-record-update]: `..w` takes the other fields from a record the left-hand side matched, but `w` is not a binder of this rule; bind the record with `w @ Ctor { .. }`",
                    "--> src/lib.rs:78:52",
                ],
            ],
            [
                "error[krs::expand::invalid-record-update]: a `cells!` term names every field: write each one (`_` for a field a pattern leaves unconstrained); `Ctor { f: e, ..t }` and a `..` group pattern are readable-record notation",
                "--> src/lib.rs:83:114",
            ],
        )
    "#]].assert_debug_eq(&(errors, cells));
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
