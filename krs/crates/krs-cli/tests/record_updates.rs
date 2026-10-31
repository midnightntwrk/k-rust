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
                    "error[krs::analysis::invalid-record-update]: in a result or a condition, a record update's base must be a name the subject matches: `..w` takes the fields it does not list from a record matched as `w @ Ctor { .. }` in the left-hand side, and `w` is no such alias; a binder of the whole term names no fields K can read. To update a value the sentence computes, destructure it with `let`: write `{ let Cmd::Wrap { a: _, b } = e; Cmd::Wrap { a: .., b } }`, `e` the value and `..` each field the update lists, guarded by `#[k::requires(k::matches!(e, Cmd::Wrap { .. }))]`, since the `let` has no value where `e` is another constructor's, and a result without one ends the run undefined",
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
                "error[krs::analysis::invalid-record-update]: a `cells!` term, the reference notation, names every field of a record, `_` for one a pattern leaves unconstrained; `..base` and `..` are readable-record notation; here it stands in the result of a `cells!` rule",
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

/// Records that name no field, `Ctor { .. }`, in a readable rule, an alias
/// a record update reads, a group, an equation table, and an equation fn;
/// with `explicit`, the same patterns with every field written `_`.
fn fieldless(explicit: bool) -> String {
    let [pair, wrap, frame] = if explicit {
        [
            "Pair { x: _, y: _ }",
            "Wrap { a: _, b: _ }",
            "Frame { pc: _, fuel: _, depth: _ }",
        ]
    } else {
        ["Pair { .. }", "Wrap { .. }", "Frame { .. }"]
    };
    format!(
        r"
k::rules! {{
    for Machine;
    use Cmd::*;

    step: {{ k: [Step {{ e: {pair} }}, ..] }} => {{ k: [Peek(), ..] }};
    swapped: {{ k: [Swapped {{ e: p @ {pair} }}, ..] }} => {{ k: [Pair {{ x: Jump(), ..p }}, ..] }};
    save: {{ k: [Save(), ..], gas: _, frame: {frame} }} => {{ k: [..], gas: 0 }};
}}

k::equations! {{
    for Bump;
    use Cmd::*;
    bump_wrap: {wrap} => Jump();
    #[k::equation(owise)]
    bump_other: e => e;
}}

#[k::equation]
fn swap_pair(k::term![Swap(Cmd::{pair})]: Term<Exp>) -> Term<Exp> {{
    Cmd::Cycle()
}}

#[k::equation(owise)]
fn swap_other(k::term![Swap(e)]: Term<Exp>) -> Term<Exp> {{
    e
}}
"
    )
}

/// `Ctor { .. }` names no field and leaves every one unconstrained, as in
/// Rust: it emits the K of the pattern that writes each field `_`, and
/// `krs expand` writes it that way where it restates a clause. `Ctor()` and `Ctor {}` still name every
/// field.
#[test]
fn a_record_pattern_may_name_no_field() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let emitted = |name: &str, explicit: bool| {
        let manifest = package(
            temporary.path(),
            name,
            &format!("{PREAMBLE}{}", fieldless(explicit)),
        );
        let output = manifest.with_file_name("emitted");
        let (success, _, stderr) = krs(
            target.path(),
            &manifest,
            "emit-k",
            &["--output", output.to_str().unwrap()],
        );
        assert!(success, "{stderr}");
        let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
        assert!(success, "{stderr}");
        (
            fs::read_to_string(output.join("definition.k")).unwrap(),
            expanded,
        )
    };
    let (fieldless_k, expanded) = emitted("fieldless", false);
    let (explicit_k, _) = emitted("explicit", true);
    assert_eq!(fieldless_k, explicit_k);
    let rule = |label: &str| {
        let start = fieldless_k.find(&format!("[{label}]")).unwrap();
        let end = start + fieldless_k[start..].find('\n').unwrap();
        let next = end + fieldless_k[end + 1..].find('\n').unwrap() + 1;
        fieldless_k[end..next].trim().to_owned()
    };
    expect_test::expect![[r#"
        [
            "<k> step ( pair ( _ , _ ) ) => peek ... </k>",
            "<k> swapped ( pair ( _ , Krs_UpdatePY:Exp ) ) => pair ( jump , Krs_UpdatePY:Exp ) ... </k>",
        ]
    "#]]
    .assert_debug_eq(&[rule("step"), rule("swapped")]);
    assert!(
        expanded.contains("k::term![crate ::Bump(crate ::Cmd::Wrap(_, _))]"),
        "{expanded}"
    );
    assert!(
        expanded.contains("KCell(crate ::Cmd::Step(crate ::Cmd::Pair(_, _)), tail @"),
        "{expanded}"
    );

    let errors = ["Pair()", "Pair {}"].map(|pattern| {
        let manifest = package(
            temporary.path(),
            if pattern == "Pair()" { "call" } else { "braces" },
            &format!(
                "{PREAMBLE}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    step: {{ k: [Step {{ e: {pattern} }}, ..] }} => {{ k: [Peek(), ..] }};\n}}\n"
            ),
        );
        check_errors(target.path(), &manifest)
    });
    expect_test::expect![[r#"
        [
            [
                "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-UPDATES::step (rule): application expects 2 arguments but received 0",
                "--> src/lib.rs:78:27",
            ],
            [
                "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-UPDATES::step (rule): application expects 2 arguments but received 0",
                "--> src/lib.rs:78:27",
            ],
        ]
    "#]]
    .assert_debug_eq(&errors);
}

/// Rules that use an alias over a group record whole (N7): `save` pushes
/// the matched frame with `use_spelling`, `restore` writes a frame popped
/// from the stack back, and `peek` matches a stacked frame equal to the
/// current one. `Pair` sequences two programs.
fn whole_group_rules(use_spelling: &str) -> String {
    format!(
        r"
k::rules! {{
    for Machine;
    use Cmd::*;

    step: {{ k: [Pair {{ x, y }}, ..] }} => {{ k: [x, y, ..] }};
    save: {{ k: [Save(), ..], stack: s, frame: saved @ Frame {{ pc: 1, .. }} }} => {{ k: [..], stack: [{use_spelling}, ..s] }};
    restore: {{ k: [Restore(), ..], stack: [saved @ Frame {{ .. }}, s @ ..], frame: _ }} => {{ k: [..], stack: s, frame: saved }};
    peek: {{ k: [Peek(), ..], gas: _, stack: [saved, ..], frame: saved @ Frame {{ .. }} }} => {{ k: [..], gas: 0 }};
    jump: {{ k: [Jump(), ..], frame: f @ Frame {{ pc: p, .. }} }} => {{ k: [..], frame: Frame {{ pc: int::add(p, 10), ..f }} }};
}}

k::claims! {{
    for Machine;
    use Cmd::*;

    #[k::claim(all_paths)]
    saves: {{ k: [Save()], stack: s, frame: saved @ Frame {{ pc: 1, .. }} }} => {{ k: [], stack: [saved, ..s] }};
}}
"
    )
}

/// The emitted rule or claim `label`, up to the next sentence or the end of
/// its module.
fn sentence(k: &str, label: &str) -> String {
    let start = k
        .find(&format!("[{label}]"))
        .unwrap_or_else(|| panic!("`{label}` is emitted:\n{k}"));
    let end = ["\n  rule ", "\n  claim ", "\nendmodule"]
        .iter()
        .filter_map(|next| k[start..].find(next))
        .min()
        .map_or(k.len(), |end| start + end);
    k[start..end].to_owned()
}

/// `definition.k` and `spec.k` of the package.
fn emitted(target: &Path, manifest: &Path) -> (String, String) {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    (
        fs::read_to_string(output.join("definition.k")).unwrap(),
        fs::read_to_string(output.join("spec.k")).unwrap_or_default(),
    )
}

/// The final `k`, `gas`, and `frame` contents after `krs run` of `program`,
/// or of the configuration it is stuck in.
fn frame_outcome(target: &Path, manifest: &Path, program: &str) -> String {
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, program).unwrap();
    let (_, stdout, stderr) = krs(target, manifest, "run", &[file.to_str().unwrap()]);
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    let cell = |name: &str| {
        let open = format!("<{name}> ");
        let start = flat
            .find(&open)
            .unwrap_or_else(|| panic!("{stdout}\n{stderr}"));
        let end = start + flat[start..].find(&format!(" </{name}>")).unwrap();
        flat[start + open.len()..end].to_owned()
    };
    format!(
        "{program} => k: {} | gas: {} | frame: {}",
        cell("k"),
        cell("gas"),
        cell("frame")
    )
}

/// A whole use of `saved @ Frame { .. }` is the update listing no field,
/// `Frame { ..saved }`: the matched frame rebuilt from its children's
/// binders, with no `#as` among a cell's children (N7). The three spellings
/// emit the same K, the rules run (a subject use matches only an equal
/// frame), the readable claim proves, and `krs expand` writes the rebuilt
/// frame in full, which runs the same.
#[test]
fn a_whole_use_of_a_group_alias_is_the_group_rebuilt() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let spellings = [
        "saved",
        "k::fragment![Frame { ..saved }]",
        "Frame { ..saved }",
    ];
    let manifests = spellings.map(|spelling| {
        let name = match spelling {
            "saved" => "whole",
            "Frame { ..saved }" => "record",
            _ => "fragment",
        };
        package(
            temporary.path(),
            name,
            &format!("{PREAMBLE}{}", whole_group_rules(spelling)),
        )
    });
    let [whole, fragment, record] = manifests
        .each_ref()
        .map(|manifest| emitted(target.path(), manifest));
    assert_eq!(whole.0, fragment.0);
    assert_eq!(whole.0, record.0);
    assert!(!whole.0.contains("#as Saved"), "{}", whole.0);
    expect_test::expect![[r"
        [save]:
            <k> save => .K ... </k>
            <stack> S:List => ListItem(<frame> <pc> Krs_UpdateSavedPc:Int </pc> <fuel> Krs_UpdateSavedFuel:Int </fuel> <depth> Krs_UpdateSavedDepth:Int </depth> </frame>) S:List </stack>
            <frame> <pc> ( 1 #as Krs_UpdateSavedPc:Int ) </pc> <fuel> Krs_UpdateSavedFuel:Int </fuel> <depth> Krs_UpdateSavedDepth:Int </depth> </frame>
        [restore]:
            <k> restore => .K ... </k>
            <stack> ListItem(<frame> <pc> Krs_UpdateSavedPc:Int </pc> <fuel> Krs_UpdateSavedFuel:Int </fuel> <depth> Krs_UpdateSavedDepth:Int </depth> </frame>) S:List => S:List </stack>
            (_:FrameCell => <frame> <pc> Krs_UpdateSavedPc:Int </pc> <fuel> Krs_UpdateSavedFuel:Int </fuel> <depth> Krs_UpdateSavedDepth:Int </depth> </frame>)
        [peek]:
            <k> peek => .K ... </k>
            <gas> _ => 0 </gas>
            <stack> ListItem(<frame> <pc> Krs_UpdateSavedPc:Int </pc> <fuel> Krs_UpdateSavedFuel:Int </fuel> <depth> Krs_UpdateSavedDepth:Int </depth> </frame>) Krs_RestStack:List </stack>
            <frame> <pc> Krs_UpdateSavedPc:Int </pc> <fuel> Krs_UpdateSavedFuel:Int </fuel> <depth> Krs_UpdateSavedDepth:Int </depth> </frame>
        [saves]:
            <k> save => .K </k>
            <stack> S:List => ListItem(<frame> <pc> Krs_UpdateSavedPc:Int </pc> <fuel> Krs_UpdateSavedFuel:Int </fuel> <depth> Krs_UpdateSavedDepth:Int </depth> </frame>) S:List </stack>
            <frame> <pc> ( 1 #as Krs_UpdateSavedPc:Int ) </pc> <fuel> Krs_UpdateSavedFuel:Int </fuel> <depth> Krs_UpdateSavedDepth:Int </depth> </frame>"]].assert_eq(&format!(
        "{}\n{}\n{}\n{}",
        sentence(&whole.0, "save"),
        sentence(&whole.0, "restore"),
        sentence(&whole.0, "peek"),
        sentence(&whole.1, "saves")
    ));
    let manifest = &manifests[0];
    let programs = [
        "pair(save, pair(jump, restore))",
        "pair(save, peek)",
        "pair(save, pair(jump, peek))",
    ];
    let outcomes = programs.map(|program| frame_outcome(target.path(), manifest, program));
    expect_test::expect![[r#"
        [
            "pair(save, pair(jump, restore)) => k: .K | gas: 5 | frame: <pc> 1 </pc> <fuel> 2 </fuel> <depth> 3 </depth>",
            "pair(save, peek) => k: .K | gas: 0 | frame: <pc> 1 </pc> <fuel> 2 </fuel> <depth> 3 </depth>",
            "pair(save, pair(jump, peek)) => k: peek ~> .K | gas: 5 | frame: <pc> 1 </pc> <fuel> 2 </fuel> <depth> 3 </depth>",
        ]
    "#]].assert_debug_eq(&outcomes);
    let (success, stdout, stderr) = krs(target.path(), manifest, "prove", &[]);
    assert!(success, "{stdout}\n{stderr}");
    assert!(stdout.contains("SPEC.saves: proven"), "{stdout}");

    let (success, expanded, stderr) = krs(target.path(), manifest, "expand", &[]);
    assert!(success, "{stderr}");
    assert!(!expanded.contains("saved @"), "{expanded}");
    let reference = package(temporary.path(), "reference", &expanded);
    assert_eq!(
        programs.map(|program| frame_outcome(target.path(), &reference, program)),
        outcomes
    );
    let start = expanded.find("pub fn save(").unwrap();
    let end = start + expanded[start..].find("\n}\n").unwrap() + 2;
    expect_test::expect![[r"
        pub fn save(
            s: k::Term<k::builtin::List>,
            saved_pc: k::Term<k::builtin::Int>,
            saved_fuel: k::Term<k::builtin::Int>,
            saved_depth: k::Term<k::builtin::Int>,
            k::cells! {
                k : k::configuration::KCell(crate ::Cmd::Save(), tail @ ..), stack :
                k::configuration::Cell(s), frame : k::fragment![crate ::Frame { pc : saved_pc @
                1, fuel : saved_fuel, depth : saved_depth }], state @ ..
            }: crate::Machine,
        ) -> crate::Machine {
            k::cells! {
                k : k::configuration::KCell(..tail), stack :
                k::configuration::Cell(k::builtin::list::concat(k::builtin::list::item(k::fragment![crate
                ::Frame { pc : saved_pc, fuel : saved_fuel, depth : saved_depth }]), s)), ..state
            }
        }"]].assert_eq(&expanded[start..end]);
}

/// An alias over a group record bound inside `|` matches one of several
/// records, so it has no one set of children to rebuild from: a whole use
/// keeps `#as`, at a list element where the term layer reads it.
#[test]
fn a_group_alias_inside_an_alternative_keeps_its_as() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "alternative",
        &format!(
            "{PREAMBLE}
k::rules! {{
    for Machine;
    use Cmd::*;

    restore: {{ k: [Restore(), ..], stack: list::concat(list::item(saved @ Frame {{ pc: 0, .. }} | saved @ Frame {{ pc: 1, .. }}), s) }} => {{ k: [saved, ..], stack: s }};
}}
"
        ),
    );
    let (definition, _) = emitted(target.path(), &manifest);
    expect_test::expect![[r"
        [restore]:
            <k> restore => Saved:FrameCell ... </k>
            <stack> ListItem(( ( <frame> <pc> 0 </pc> <fuel> _ </fuel> <depth> _ </depth> </frame> #as Saved:FrameCell ) #Or ( <frame> <pc> 1 </pc> <fuel> _ </fuel> <depth> _ </depth> </frame> #as Saved:FrameCell ) )) S:List => S:List </stack>"]].assert_eq(&sentence(&definition, "restore"));
}

/// Hidden binders are named by their alias and field path, and two paths
/// whose underscores join to the same name get distinct binders: `a.x_y`
/// and `a_x.y` are two fields, not one.
#[test]
fn hidden_binders_of_distinct_paths_are_distinct() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "paths",
        &format!(
            "{PREAMBLE}
#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Both, Left, Right))]
pub enum Pr {{
    #[k::syntax(\"both({{l}}, {{r}})\")]
    Both {{ l: Exp, r: Exp }},
    #[k::syntax(\"left({{x_y}}, {{w}})\")]
    Left {{ x_y: Int, w: Int }},
    #[k::syntax(\"right({{y}}, {{w}})\")]
    Right {{ y: Int, w: Int }},
}}

k::rules! {{
    for Machine;
    use Pr::*;

    both: {{ k: [Both {{ l: a @ Left {{ w: 0, .. }}, r: a_x @ Right {{ w: 1, .. }} }}, ..] }} => {{ k: [Both {{ l: Left {{ w: 5, ..a }}, r: Right {{ w: 6, ..a_x }} }}, ..] }};
}}
"
        ),
    );
    let (definition, _) = emitted(target.path(), &manifest);
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, "both(left(7, 0), right(9, 1))").unwrap();
    let (_, stdout, _) = krs(target.path(), &manifest, "run", &[file.to_str().unwrap()]);
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    expect_test::expect![[r"
        [both]:
            <k> both ( left ( Krs_UpdateAXY:Int , 0 ) , right ( Krs_UpdateAXY2:Int , 1 ) ) => both ( left ( Krs_UpdateAXY:Int , 5 ) , right ( Krs_UpdateAXY2:Int , 6 ) ) ... </k>
        <k> both(left(7, 5), right(9, 6)) ~> .K </k>"]].assert_eq(&format!(
        "{}\n{}",
        sentence(&definition, "both"),
        &flat[flat.find("<k>").unwrap()..flat.find("</k>").unwrap() + 4]
    ));
}

/// A configuration whose `outer` group nests the `frame` group, and rules
/// that save, change, and restore them through aliases over group records.
const TWO_LEVEL: &str = r#"
use k::builtin::{Int, KSequence, List, int, list};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Seq, Push, Pop, Bump, Flag, Report))]
pub enum Cmd {
    #[k::syntax("seq({a}, {b})")]
    Seq { a: Stmt, b: Stmt },
    #[k::syntax("push")]
    Push(),
    #[k::syntax("pop")]
    Pop(),
    #[k::syntax("bump")]
    Bump(),
    #[k::syntax("flag")]
    Flag(),
    #[k::syntax("report")]
    Report(),
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub gas: Int,
}

#[k::cell]
pub struct Outer {
    #[k::cell(nested)]
    pub frame: Frame,
    #[k::cell]
    pub flag: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub stack: List,
    #[k::cell(nested)]
    pub outer: Outer,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            stack: list::empty(),
            outer: Outer { frame: Frame { pc: 0, gas: 100 }, flag: 0 },
        }
    }
}

k::rules! {
    for Machine;
    use Cmd::*;

    seq: { k: [Seq { a, b }, ..] } => { k: [a, b, ..] };
    push: { k: [Push(), ..], stack: s, outer: o @ Outer { flag: 0, .. } } => { k: [..], stack: [o, ..s] };
    pop: { k: [Pop(), ..], stack: [saved @ Outer { .. }, s @ ..], outer: _ } => { k: [..], stack: s, outer: saved };
    bump: { k: [Bump(), ..], frame: Frame { pc: p, gas: g } } => { k: [..], frame: Frame { pc: int::add(p, 1), gas: int::add(g, 1000) } };
    flag: { k: [Flag(), ..], outer: o @ Outer { frame: Frame { pc: 0, .. }, .. } } => { k: [..], outer: Outer { flag: 7, ..o } };
    report: { k: [Report(), ..], frame: Frame { pc: p, gas: g }, flag: f } => { k: [int::add(int::add(p, g), f), ..] };
}
"#;

/// Below a base, a group child its pattern constrains with a group record
/// is rebuilt from that record's own children, so an update that takes it
/// keeps the matched child (`flag` keeps `<frame>`); a whole use of an
/// alias over the outer group rebuilds it, nested child included (N7).
#[test]
fn a_group_child_below_a_base_is_rebuilt_from_its_children() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "nested", TWO_LEVEL);
    let (definition, _) = emitted(target.path(), &manifest);
    expect_test::expect![[r"
        [push]:
            <k> push => .K ... </k>
            <stack> S:List => ListItem(<outer> Krs_UpdateOFrame:FrameCell <flag> Krs_UpdateOFlag:Int </flag> </outer>) S:List </stack>
            <outer> Krs_UpdateOFrame:FrameCell <flag> ( 0 #as Krs_UpdateOFlag:Int ) </flag> </outer>
        [pop]:
            <k> pop => .K ... </k>
            <stack> ListItem(<outer> Krs_UpdateSavedFrame:FrameCell <flag> Krs_UpdateSavedFlag:Int </flag> </outer>) S:List => S:List </stack>
            (_:OuterCell => <outer> Krs_UpdateSavedFrame:FrameCell <flag> Krs_UpdateSavedFlag:Int </flag> </outer>)
        [flag]:
            <k> flag => .K ... </k>
            (<outer> <frame> <pc> ( 0 #as Krs_UpdateOFramePc:Int ) </pc> <gas> Krs_UpdateOFrameGas:Int </gas> </frame> <flag> _ </flag> </outer> => <outer> <frame> <pc> Krs_UpdateOFramePc:Int </pc> <gas> Krs_UpdateOFrameGas:Int </gas> </frame> <flag> 7 </flag> </outer>)"]].assert_eq(&format!(
        "{}\n{}\n{}",
        sentence(&definition, "push"),
        sentence(&definition, "pop"),
        sentence(&definition, "flag")
    ));
    let outcomes = [
        "seq(push, seq(bump, seq(pop, report)))",
        "seq(push, seq(bump, report))",
        "seq(flag, report)",
    ]
    .map(|program| {
        let file = manifest.with_file_name("program.txt");
        fs::write(&file, program).unwrap();
        let (success, stdout, stderr) =
            krs(target.path(), &manifest, "run", &[file.to_str().unwrap()]);
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(
            flat.contains("<k>"),
            "{program}: {success}\n{stdout}\n{stderr}"
        );
        format!(
            "{program} => {}",
            &flat[flat.find("<k>").unwrap()..flat.find("</k>").unwrap() + 4]
        )
    });
    expect_test::expect![[r#"
        [
            "seq(push, seq(bump, seq(pop, report))) => <k> 100 ~> .K </k>",
            "seq(push, seq(bump, report)) => <k> 1101 ~> .K </k>",
            "seq(flag, report) => <k> 107 ~> .K </k>",
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}
