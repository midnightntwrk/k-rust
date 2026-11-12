//! One pattern grammar end to end: a pattern needs no `k::term![..]`
//! wrapper for the islands it holds (`k::fragment!` in a list element, a
//! constructor argument, an alias target, or a readable value's root), a
//! hand-written fn subject may end a record in `..`, and a single-body rule
//! may write `k::rewrite!` without the wrapper. A record naming a
//! `#[k::cell]` struct is that group's cell term at any depth. Each spelling
//! is checked against its wrapped or `k::fragment!` twin through `krs
//! emit-k`, which runs the macro and the collector on the same source.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, List, int, list};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Go, Save, Restore, Swap, Bump, Held, Mark))]
pub enum Cmd {
    #[k::syntax("go")]
    Go(),
    #[k::syntax("save")]
    Save(),
    #[k::syntax("restore")]
    Restore(),
    #[k::syntax("swap")]
    Swap(),
    #[k::syntax("bump")]
    Bump(),
    #[k::syntax("held({saved})")]
    Held { saved: k::KItem },
    #[k::syntax("mark({value})")]
    Mark { value: Int },
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub gas: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub stack: List,
    #[k::cell(nested)]
    pub frame: Frame,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            stack: list::empty(),
            frame: Frame { pc: 0, gas: 0 },
        }
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

/// Writes a one-package workspace whose library is the preamble and
/// `source`. Every package shares one K namespace, so two spellings of one
/// definition emit the same K.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    library_package(root, name, &format!("{PREAMBLE}{source}"))
}

/// Writes a one-package workspace whose library is `library`.
fn library_package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-NESTED\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The K source `krs emit-k` writes for the package.
fn emitted_k(target: &Path, manifest: &Path) -> String {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    krs_test_support::without_source_comments(
        &fs::read_to_string(output.join("definition.k")).unwrap(),
    )
}

/// The `error[..]` headlines and messages of `krs check`.
fn check_errors(target: &Path, manifest: &Path) -> String {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    stderr
        .lines()
        .filter(|line| line.starts_with("error"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The emitted rule labelled `label`, up to the next rule.
fn rule<'a>(k: &'a str, label: &str) -> &'a str {
    let start = k
        .find(&format!("rule [{label}]:"))
        .unwrap_or_else(|| panic!("rule `{label}` is emitted:\n{k}"));
    let end = ["rule [", "endmodule"]
        .iter()
        .filter_map(|next| k[start + 1..].find(next))
        .min()
        .map_or(k.len(), |end| start + 1 + end);
    k[start..end].trim_end()
}

/// The fixture's rules in three spellings: inside `k::term![..]` (the only
/// one accepted before), with `k::fragment!` and no wrapper, and with bare
/// group records.
fn machine_rules(spelling: Spelling) -> String {
    let frame = |fields: &str| match spelling {
        Spelling::Bare => format!("Frame {{ {fields} }}"),
        Spelling::Wrapped | Spelling::Fragment => format!("k::fragment![Frame {{ {fields} }}]"),
    };
    let wrap = |pattern: String| match spelling {
        Spelling::Wrapped => format!("k::term![{pattern}]"),
        Spelling::Fragment | Spelling::Bare => pattern,
    };
    let restore = wrap(format!(
        "list::concat(list::item({}), s)",
        frame("pc: p, gas: g")
    ));
    let swap = wrap(format!(
        "list::concat(list::item(saved @ {}), s)",
        frame("pc: p, ..")
    ));
    let held = wrap(format!("Held {{ saved: {} }}", frame("pc: p, ..")));
    // The root of a readable value: `k::fragment!` and the bare record read
    // the configuration's own cell; inside `k::term!` it is the fragment.
    let root = match spelling {
        Spelling::Wrapped => "k::term![k::fragment![Frame { pc: p, gas: g }]]".to_owned(),
        Spelling::Fragment | Spelling::Bare => frame("pc: p, gas: g"),
    };
    let pushed = frame("pc: int::add(p, 1), ..saved");
    format!(
        r"
k::rules! {{
    for Machine;
    use Cmd::*;

    save: {{ k: [Save(), ..], stack: s, frame: f }} => {{
        k: [..],
        stack: list::concat(list::item(f), s),
    }};
    restore: {{ k: [Restore(), ..], stack: {restore}, frame: _ }} => {{
        k: [..],
        stack: s,
        frame: Frame {{ pc: p, gas: g }},
    }};
    swap: {{ k: [Swap(), ..], stack: {swap}, frame: f }} => {{
        k: [..],
        stack: list::concat(list::item({pushed}), list::concat(list::item(f), s)),
    }};
    unhold: {{ k: [{held}, ..], frame: Frame {{ gas: g, .. }} }} => {{
        k: [..],
        frame: Frame {{ pc: p, gas: g }},
    }};
    bump: {{ k: [Bump(), ..], frame: {root} }} => {{
        k: [..],
        frame: Frame {{ pc: g, gas: p }},
    }};
}}
"
    )
}

#[derive(Clone, Copy)]
enum Spelling {
    Wrapped,
    Fragment,
    Bare,
}

/// `k::fragment!` in a list element, as an alias target that a result
/// updates (F5), inside a computation item, and at a readable value's root
/// needs no `k::term!` wrapper, and a bare group record means the fragment
/// at each of those places: all three spellings emit the same K.
#[test]
fn a_pattern_needs_no_wrapper_and_a_group_record_is_its_cell_term() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let wrapped = package(
        temporary.path(),
        "nested-wrapped",
        &machine_rules(Spelling::Wrapped),
    );
    let fragment = package(
        temporary.path(),
        "nested-fragment",
        &machine_rules(Spelling::Fragment),
    );
    let bare = package(
        temporary.path(),
        "nested-bare",
        &machine_rules(Spelling::Bare),
    );
    let k = emitted_k(target.path(), &wrapped);
    assert_eq!(k, emitted_k(target.path(), &fragment));
    assert_eq!(k, emitted_k(target.path(), &bare));
    expect_test::expect![[r"
        rule [restore]:
            <k> restore => .K ... </k>
            <stack> ListItem(<frame> <pc> P:Int </pc> <gas> G:Int </gas> </frame>) S:List => S:List </stack>
            (_:FrameCell => <frame> <pc> P:Int </pc> <gas> G:Int </gas> </frame>)"]]
    .assert_eq(rule(&k, "restore"));
    expect_test::expect![[r"
        rule [swap]:
            <k> swap => .K ... </k>
            <stack> ListItem(<frame> <pc> P:Int </pc> <gas> SavedGas:Int </gas> </frame>) S:List => ListItem(<frame> <pc> P:Int +Int 1 </pc> <gas> SavedGas:Int </gas> </frame>) ListItem(F:FrameCell) S:List </stack>
            F:FrameCell"]]
    .assert_eq(rule(&k, "swap"));
    expect_test::expect![[r"
        rule [unhold]:
            <k> held ( <frame> <pc> P:Int </pc> <gas> _ </gas> </frame> ) => .K ... </k>
            (<frame> <pc> _ </pc> <gas> G:Int </gas> </frame> => <frame> <pc> P:Int </pc> <gas> G:Int </gas> </frame>)"]]
    .assert_eq(rule(&k, "unhold"));
}

/// A group record as a value is a complete cell term: a pattern leaves a
/// child unconstrained only with `..`, as a record at a configuration
/// cell's own position does (`frame: Frame { gas: g, .. }` above, or a group
/// nested in one, see [`a_group_record_at_a_configuration_cell_leaves_children_out_only_with_rest`]).
#[test]
fn a_nested_group_record_names_every_child_or_ends_in_rest() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let missing = package(
        temporary.path(),
        "nested-missing-child",
        r"
k::rules! {
    for Machine;
    use Cmd::*;

    restore: { k: [Restore(), ..], stack: list::concat(list::item(Frame { pc: p }), s) } => {
        k: [p, ..],
        stack: s,
    };
}
",
    );
    let errors = check_errors(target.path(), &missing);
    assert!(
        errors.contains("krs::analysis::invalid-term")
            && errors.contains("must name every child field exactly once"),
        "{errors}"
    );
}

/// Built terms outside a cell's entry for RDRA item 1: an equation's result, a constructor
/// argument in it, and an alias's result. `{record}` is the `Frame` record each one holds.
const BUILT_FRAMES: [(&str, &str, &str); 3] = [
    (
        "equation",
        "the result of an equation",
        "#[k::function(total, internal)]\npub fn Pushed(s: k::Term<List>) -> k::Term<List> {\n    k::term![list::concat(list::item({record}), s)]\n}\n",
    ),
    (
        "argument",
        "the result of an equation",
        "#[k::function(total, internal)]\npub fn Wrapped(s: k::Term<Stmt>) -> k::Term<Stmt> {\n    k::term![Cmd::Held { saved: {record} }]\n}\n",
    ),
    (
        "alias",
        "the result of a `#[k::alias]` fn",
        "#[k::constructors(sort = Stmt, result = KResult)]\npub enum Short {\n    #[k::syntax(\"short()\")]\n    #[k::alias]\n    Short(),\n}\n\n#[k::alias]\nfn short(k::term![Short::Short()]: k::Term<Stmt>) -> k::Term<Stmt> {\n    Cmd::Held { saved: {record} }\n}\n",
    ),
];

/// A bare `..` (no base) means something only where a pattern leaves fields unconstrained or a
/// cell's entry leaves them to the entry: where a term is built anywhere else it names no
/// value for the fields, so a record holding one is refused there even with every field named,
/// as written bare or in `k::fragment!`, with one class and one text (RDRA item 1, AUDIT-R
/// A1-1: the fragment's `..` was dropped by the reader, so `k::fragment![Frame { pc: 1, gas: 2,
/// .. }]` in an equation passed where its bare twin was refused).
#[test]
fn a_built_record_outside_an_entry_holds_no_bare_rest_in_either_spelling() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    for (label, position, template) in BUILT_FRAMES {
        for fields in ["pc: 1, gas: 2, ..", "pc: 1, .."] {
            let refusals = ["bare", "fragment"].map(|spelling| {
                let record = if spelling == "bare" {
                    format!("Frame {{ {fields} }}")
                } else {
                    format!("k::fragment![Frame {{ {fields} }}]")
                };
                let named = if fields.contains("gas") {
                    "all"
                } else {
                    "some"
                };
                let manifest = package(
                    temporary.path(),
                    &format!("built-{label}-{spelling}-{named}"),
                    &template.replace("{record}", &record),
                );
                check_errors(target.path(), &manifest)
            });
            let [bare, fragment] = &refusals;
            assert_eq!(
                bare, fragment,
                "{label}, `{fields}`: one class and text for both spellings"
            );
            assert!(
                bare.starts_with("error[krs::syntax::invalid-record-update]: ")
                    && bare.contains(&format!(
                        "so it holds no `..`, even with every field named; here it stands in {position}"
                    )),
                "{label}, `{fields}`: {bare}"
            );
        }
    }
}

/// Terms a result's entry builds, for DOTS: `{record}` is the `Frame` record each one holds, as a
/// list element, a constructor's argument in one, and a computation's item in a readable rule,
/// and as a list element in a `cells!` rule; the cell is the entry's.
const BUILT_IN_ENTRIES: [(&str, &str, &str); 4] = [
    (
        "element",
        "stack",
        "k::rules! {\n    for Machine;\n    use Cmd::*;\n\n    save: { k: [Save(), ..], stack: s } => { k: [..], stack: [{record}, ..s] };\n}\n",
    ),
    (
        "argument",
        "stack",
        "k::rules! {\n    for Machine;\n    use Cmd::*;\n\n    save: { k: [Save(), ..], stack: s } => { k: [..], stack: [Held { saved: {record} }, ..s] };\n}\n",
    ),
    (
        "item",
        "k",
        "k::rules! {\n    for Machine;\n    use Cmd::*;\n\n    save: { k: [Save(), ..] } => { k: [{record}, ..] };\n}\n",
    ),
    (
        "cells",
        "stack",
        "#[k::rule(label = \"save\")]\npub fn save(\n    s: k::Term<List>,\n    k::cells! { k: k::configuration::KCell(Cmd::Save(), tail @ ..), stack: k::configuration::Cell(s), state @ .. }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(..tail), stack: k::configuration::Cell(list::concat(list::item({record}), s)), ..state }\n}\n",
    ),
];

/// `..` means that the fields a record leaves unnamed are what they would otherwise be: in a
/// pattern anything, and in the record a result's entry writes for its cell what the cell holds
/// (or a created instance's template). A term a result's entry builds is made from nothing, so
/// there is no otherwise: its record's `..` is refused even with every field named, bare or in
/// `k::fragment!`, with the one class and text an equation's result gets, at the record (DOTS:
/// the all-named `..` passed there while its twin in an equation was refused). Where `..` has a
/// meaning an all-named `..` stays the exact record: at the entry's own record and in a pattern.
#[test]
fn a_term_a_result_entry_builds_holds_no_bare_rest_in_either_spelling() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    for (label, cell, template) in BUILT_IN_ENTRIES {
        let head = if label == "cells" {
            "crate::Frame"
        } else {
            "Frame"
        };
        let refusals = ["pc: 1, gas: 2, ..", "pc: 1, .."].map(|fields| {
            ["bare", "fragment"].map(|spelling| {
                let record = if spelling == "bare" {
                    format!("{head} {{ {fields} }}")
                } else {
                    format!("k::fragment![{head} {{ {fields} }}]")
                };
                let named = if fields.contains("gas") {
                    "all"
                } else {
                    "some"
                };
                let manifest = package(
                    temporary.path(),
                    &format!("in-entry-{label}-{spelling}-{named}"),
                    &template.replace("{record}", &record),
                );
                check_errors(target.path(), &manifest)
            })
        });
        let first = &refusals[0][0];
        for (named, spellings) in ["all", "some"].iter().zip(&refusals) {
            for (spelling, errors) in ["bare", "fragment"].iter().zip(spellings) {
                assert_eq!(
                    errors, first,
                    "{label}, {named} named, {spelling}: one class and text"
                );
            }
        }
        assert!(
            first.starts_with("error[krs::syntax::invalid-record-update]: ")
                && first.contains(&format!(
                    "so it holds no `..`, even with every field named; here it stands in a term the entry of the cell `{cell}` builds"
                )),
            "{label}: {first}"
        );
    }
    // Where `..` has a meaning, after every field it is the exact record: the record the entry
    // writes for its cell, and a pattern.
    for (label, exact, open) in [
        (
            "entry",
            "save: { k: [Save(), ..], frame: _ } => { k: [..], frame: Frame { pc: 1, gas: 2 } };",
            "save: { k: [Save(), ..], frame: _ } => { k: [..], frame: Frame { pc: 1, gas: 2, .. } };",
        ),
        (
            "pattern",
            "save: { k: [Save(), ..], stack: [Frame { pc: p, gas: g }, ..] } => { k: [int::add(p, g), ..], stack: [..] };",
            "save: { k: [Save(), ..], stack: [Frame { pc: p, gas: g, .. }, ..] } => { k: [int::add(p, g), ..], stack: [..] };",
        ),
    ] {
        let [exact, open] = [("exact", exact), ("open", open)].map(|(kind, sentence)| {
            let manifest = package(
                temporary.path(),
                &format!("in-entry-{label}-{kind}"),
                &format!("k::rules! {{\n    for Machine;\n    use Cmd::*;\n\n    {sentence}\n}}\n"),
            );
            rule(&emitted_k(target.path(), &manifest), "save").to_owned()
        });
        assert_eq!(open, exact, "{label}");
    }
}

/// A `TWO_LEVEL` `cells!` rule writing `outer` whole in its result as `outer`.
fn cells_outer_rule(outer: &str) -> String {
    format!(
        "{TWO_LEVEL}#[k::rule(label = \"reset\")]\npub fn reset(\n    k::cells! {{ k: k::configuration::KCell(Cmd::Bump(), tail @ ..), outer: _, state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), outer: {outer}, ..state }}\n}}\n"
    )
}

/// In a `cells!` result a `..` after every child leaves nothing open, so the record is the exact
/// one, at a fragment's root and at a group child inside it, bare or in `k::fragment!`
/// (`language.mdx`, group records); one that leaves a child out keeps that child's content.
#[test]
fn a_cells_result_record_ends_in_rest_after_every_child_or_keeps_the_others() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let exact = library_package(
        temporary.path(),
        "cells-exact",
        &cells_outer_rule(
            "k::fragment![crate::Outer { frame: crate::Frame { pc: 1, gas: 2 }, flag: 0 }]",
        ),
    );
    let expected = rule(&emitted_k(target.path(), &exact), "reset").to_owned();
    for (label, outer) in [
        (
            "root",
            "k::fragment![crate::Outer { frame: crate::Frame { pc: 1, gas: 2 }, flag: 0, .. }]",
        ),
        (
            "bare-child",
            "k::fragment![crate::Outer { frame: crate::Frame { pc: 1, gas: 2, .. }, flag: 0 }]",
        ),
        (
            "fragment-child",
            "k::fragment![crate::Outer { frame: k::fragment![crate::Frame { pc: 1, gas: 2, .. }], flag: 0, .. }]",
        ),
    ] {
        let manifest = library_package(
            temporary.path(),
            &format!("cells-{label}"),
            &cells_outer_rule(outer),
        );
        assert_eq!(
            rule(&emitted_k(target.path(), &manifest), "reset"),
            expected,
            "{label}"
        );
    }
    // A `..` that leaves a child out keeps that child's content: the group is there, so the
    // record writes only the children it names, each as its own cell (EDOTS item 1), for both
    // spellings of the child alike.
    let kept = [
        ("root", "k::fragment![crate::Outer { frame: crate::Frame { pc: 1, gas: 2 }, .. }]"),
        (
            "bare-child",
            "k::fragment![crate::Outer { frame: crate::Frame { pc: 1, .. }, flag: 0 }]",
        ),
        (
            "fragment-child",
            "k::fragment![crate::Outer { frame: k::fragment![crate::Frame { pc: 1, .. }], flag: 0 }]",
        ),
    ]
    .map(|(label, outer)| {
        let manifest = library_package(
            temporary.path(),
            &format!("cells-open-{label}"),
            &cells_outer_rule(outer),
        );
        (label, rule(&emitted_k(target.path(), &manifest), "reset").to_owned())
    });
    expect_test::expect![[r#"
        [
            (
                "root",
                "rule [reset]:\n    <k> bump ~> Tail:K => .K ~> Tail:K </k>\n    (_:FrameCell => <frame> <pc> 1 </pc> <gas> 2 </gas> </frame>)",
            ),
            (
                "bare-child",
                "rule [reset]:\n    <k> bump ~> Tail:K => .K ~> Tail:K </k>\n    <pc> _ => 1 </pc>\n    <flag> _ => 0 </flag>",
            ),
            (
                "fragment-child",
                "rule [reset]:\n    <k> bump ~> Tail:K => .K ~> Tail:K </k>\n    <pc> _ => 1 </pc>\n    <flag> _ => 0 </flag>",
            ),
        ]
    "#]].assert_debug_eq(&kept);
    assert_eq!(
        kept[1].1, kept[2].1,
        "one K for both spellings of the child"
    );
}

/// A record whose path names a constructor stays the constructor, even when
/// a `#[k::cell]` struct of the same name exists: the path resolves as
/// rustc resolves it.
#[test]
fn a_constructor_named_like_a_group_stays_a_constructor() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let shadowed = package(
        temporary.path(),
        "nested-shadowed",
        r#"
pub mod shapes {
    use k::builtin::Int;

    k::sorts! {
        Shape: k::KItem + k::KResult;
    }

    #[k::constructors(sort = Shape, result = k::KResult)]
    pub enum Frame {
        #[k::syntax("frame({pc})")]
        Frame { pc: Int },
    }
}

k::rules! {
    for Machine;
    use Cmd::*;

    restore: {
        k: [Restore(), ..],
        stack: list::concat(list::item(shapes::Frame::Frame { pc: p }), s),
        frame: Frame { pc: _, gas: g },
    } => {
        k: [..],
        stack: s,
        frame: Frame { pc: p, gas: g },
    };
}
"#,
    );
    let k = emitted_k(target.path(), &shadowed);
    expect_test::expect![[r"
        rule [restore]:
            <k> restore => .K ... </k>
            <stack> ListItem(frame ( P:Int )) S:List => S:List </stack>
            (<frame> <pc> _ </pc> <gas> G:Int </gas> </frame> => <frame> <pc> P:Int </pc> <gas> G:Int </gas> </frame>)"]]
    .assert_eq(rule(&k, "restore"));
}

const TERM_RULES: &str = r#"
k::sorts! {
    Exp: k::KItem;
    Pr: k::KItem;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum Expr {
    #[k::syntax("marked({inner})")]
    Marked { inner: Exp },
    #[k::syntax("done")]
    Done(),
}

#[k::constructors(sort = Pr, result = KResult)]
pub enum Pairs {
    #[k::syntax("pair({left}, {right})")]
    Pair { left: Exp, right: Exp },
}

#[k::function(total, syntax = "first({p})")]
pub fn First(p: k::Term<Pr>) -> k::Term<Exp>;

#[k::equation]
fn first_pair(left: k::Term<Exp>, SUBJECT: k::Term<Exp>) -> k::Term<Exp> {
    left
}

#[k::rule]
fn unmark(v: k::Term<Exp>, REWRITE: k::Term<Pr>) {}
"#;

/// A hand-written fn subject reads a record rest `..` and a local
/// `k::rewrite!` without `k::term![..]`, and means what the wrapped subject
/// means.
#[test]
fn fn_subjects_read_record_rest_and_rewrites_without_the_wrapper() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let source = |subject: &str, rewrite: &str| {
        TERM_RULES
            .replace("SUBJECT", subject)
            .replace("REWRITE", rewrite)
    };
    let native = package(
        temporary.path(),
        "subjects-native",
        &source(
            "First(Pairs::Pair { left, .. })",
            "Pairs::Pair { left: k::rewrite!(Expr::Marked { inner: v } => v), right: Expr::Done() }",
        ),
    );
    let wrapped = package(
        temporary.path(),
        "subjects-wrapped",
        &source(
            "k::term![First(Pairs::Pair { left, .. })]",
            "k::term![Pairs::Pair { left: k::rewrite!(Expr::Marked { inner: v } => v), right: Expr::Done() }]",
        ),
    );
    let k = emitted_k(target.path(), &native);
    assert_eq!(k, emitted_k(target.path(), &wrapped));
    assert!(
        k.contains("rule first ( pair ( Left:Exp , _ ) ) => Left:Exp"),
        "{k}"
    );
    assert!(
        k.contains("rule pair ( (marked ( V:Exp ) => V:Exp) , done )"),
        "{k}"
    );
}

/// A configuration whose `outer` group nests the `frame` group, beside a
/// `KItem` leaf cell `slot`.
const TWO_LEVEL: &str = r#"
use k::builtin::{Int, KSequence, List, int, list};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Seq, Push, Pop, Bump, Look, Report))]
pub enum Cmd {
    #[k::syntax("seq({a}, {b})")]
    Seq { a: Stmt, b: Stmt },
    #[k::syntax("push")]
    Push(),
    #[k::syntax("pop")]
    Pop(),
    #[k::syntax("bump")]
    Bump(),
    #[k::syntax("look")]
    Look(),
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
    #[k::cell]
    pub slot: k::KItem,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt, item: k::KItem) -> Self {
        Self {
            k: k::k![pgm],
            stack: list::empty(),
            outer: Outer { frame: Frame { pc: 0, gas: 100 }, flag: 0 },
            slot: item,
        }
    }
}
"#;

/// Rules and a claim that read `outer`'s nested `frame` through `outer`,
/// naming only `pc`, each record ending in `..` where it leaves children out.
const LEAVING_OUT: &str = r"
k::rules! {
    for Machine;
    use Cmd::*;

    look: { k: [Look(), ..], outer: Outer { frame: Frame { pc: p, .. }, flag: f } } => { k: [int::add(p, f), ..] };
    report: { k: [Report(), ..], stack: s, outer: o @ Outer { frame: Frame { pc: p, .. }, .. } } => { k: [p, ..], stack: [o, ..s] };
}

k::claims! {
    for Machine;
    use Cmd::*;

    #[k::claim(all_paths)]
    looks: { k: [Look()], outer: Outer { frame: Frame { pc: p, .. }, flag: f } } => { k: [int::add(p, f)] };
}
";

/// A group record at a configuration position that names some of its
/// children and no `..` is refused as `record-missing-children` (L4), in a
/// rule and in a claim, whether it is the entry's own record or a group
/// child's record inside it.
#[test]
fn a_group_record_at_a_configuration_cell_naming_some_children_and_no_rest_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let missing = [
        (
            "inner",
            "rules",
            "look: { k: [Look(), ..], outer: Outer { frame: Frame { pc: p }, flag: f } } => { k: [int::add(p, f), ..] };",
            ("`frame`", "Frame { pc: p }"),
        ),
        (
            "outer",
            "rules",
            "report: { k: [Report(), ..], stack: s, outer: o @ Outer { frame: Frame { pc: p, .. } } } => { k: [p, ..], stack: [o, ..s] };",
            ("`outer`", "Outer { frame: Frame { pc: p, .. } }"),
        ),
        (
            "claim",
            "claims",
            "#[k::claim(all_paths)]\n    looks: { k: [Look()], outer: Outer { frame: Frame { pc: p }, flag: f } } => { k: [int::add(p, f)] };",
            ("`frame`", "Frame { pc: p }"),
        ),
    ];
    // The refusal names the cell whose record leaves children out, at that record: `Outer`
    // names both of `outer`'s children, and it is `frame`'s record that leaves `gas` out, a
    // child of `outer`'s record being an entry of its own cell (P1, P7).
    for (label, block, clause, (cell, record)) in missing {
        let source = format!(
            "{TWO_LEVEL}k::{block}! {{\n    for Machine;\n    use Cmd::*;\n    {clause}\n}}\n"
        );
        let manifest = library_package(temporary.path(), &format!("missing-{label}"), &source);
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(
            !success,
            "{label}: krs check unexpectedly passed:\n{stderr}"
        );
        assert!(
            stderr.contains(&format!(
                "error[krs::analysis::record-missing-children]: the group record of the cell {cell} "
            )),
            "{label}: {stderr}"
        );
        // At the record, line and column, 1-based.
        let offset = source.find(record).expect("the clause holds the record");
        let line = source[..offset].matches('\n').count() + 1;
        let column = offset
            - source[..offset]
                .rfind('\n')
                .map_or(0, |newline| newline + 1)
            + 1;
        assert!(
            stderr.contains(&format!("src/lib.rs:{line}:{column}")),
            "{label}: the refusal stands at `{record}` ({line}:{column}):\n{stderr}"
        );
    }
}

/// Where a group record matches a cell of the running configuration, it
/// leaves children unconstrained only with `..` (L4), as a Rust struct
/// pattern does: the value of the entry that names the group, and each
/// fixed group child of a record there (`frame` inside `outer`), which is
/// the configuration's `<frame>` reached through `outer`. Everywhere else (a
/// `KItem` leaf cell's content, a list element, a group nested in a value)
/// the record is a value and complete, and `k::fragment!` is exact at every
/// position (U5).
#[test]
fn a_group_record_at_a_configuration_cell_leaves_children_out_only_with_rest() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = library_package(
        temporary.path(),
        "leaving-out",
        &format!("{TWO_LEVEL}{LEAVING_OUT}"),
    );
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = krs_test_support::without_source_comments(
        &fs::read_to_string(output.join("definition.k")).unwrap(),
    );
    expect_test::expect![[r"
        rule [look]:
            <k> look => P:Int +Int F:Int ... </k>
            <outer> <frame> <pc> P:Int </pc> <gas> _ </gas> </frame> <flag> F:Int </flag> </outer>
        rule [report]:
            <k> report => P:Int ... </k>
            <stack> S:List => ListItem(<outer> <frame> <pc> P:Int </pc> <gas> OFrameGas:Int </gas> </frame> <flag> OFlag:Int </flag> </outer>) S:List </stack>
            <outer> <frame> <pc> P:Int </pc> <gas> OFrameGas:Int </gas> </frame> <flag> OFlag:Int </flag> </outer>"]]
    .assert_eq(&format!("{}\n{}", rule(&definition, "look"), rule(&definition, "report")));

    // A record as a value (a `KItem` leaf's content, a list element) is a complete term; a
    // fragment at a configuration position is that position's record, so L4's class answers it.
    let strict = [
        (
            "slot: { k: [Look(), ..], slot: Frame { pc: p } } => { k: [p, ..] };",
            "invalid-term",
        ),
        (
            "value: { k: [Look(), ..], stack: [Outer { frame: Frame { pc: p }, .. }, ..] } => { k: [p, ..] };",
            "invalid-term",
        ),
        (
            "fragment: { k: [Look(), ..], frame: k::fragment![Frame { pc: p }] } => { k: [p, ..] };",
            "record-missing-children",
        ),
    ];
    for (clause, code) in strict {
        let label = &clause[..clause.find(':').unwrap()];
        let manifest = library_package(
            temporary.path(),
            &format!("strict-{label}"),
            &format!(
                "{TWO_LEVEL}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    {clause}\n}}\n"
            ),
        );
        let error = check_errors(target.path(), &manifest);
        let explains = match code {
            "invalid-term" => "must name every child field exactly once",
            _ => "names some of its children and no `..`",
        };
        assert!(
            error.contains(&format!("krs::analysis::{code}")) && error.contains(explains),
            "{label}: {error}"
        );
    }
    let manifest = library_package(
        temporary.path(),
        "slot-rest",
        &format!(
            "{TWO_LEVEL}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    slot: {{ k: [Look(), ..], slot: Frame {{ pc: p, .. }} }} => {{ k: [p, ..] }};\n}}\n"
        ),
    );
    expect_test::expect![[r"
        rule [slot]:
            <k> look => P:Int ... </k>
            <slot> <frame> <pc> P:Int </pc> <gas> _ </gas> </frame> </slot>"]]
    .assert_eq(rule(&emitted_k(target.path(), &manifest), "slot"));
}

/// Rules that bind `frame` inside `outer` by a binder, `_`, and an alias
/// over a group record, save it on the stack, update it in place, and write
/// it back.
const CHILD_BINDERS: &str = r"
k::rules! {
    for Machine;
    use Cmd::*;

    seq: { k: [Seq { a, b }, ..] } => { k: [a, b, ..] };
    push: { k: [Push(), ..], stack: s, outer: Outer { frame: fr, .. } } => { k: [..], stack: [fr, ..s] };
    pop: { k: [Pop(), ..], stack: [fr, s @ ..], outer: Outer { frame: _, flag: x } } => { k: [..], stack: s, outer: Outer { frame: fr, flag: x } };
    bump: { k: [Bump(), ..], outer: o @ Outer { frame: fr @ Frame { pc: p, .. }, .. } } => { k: [..], outer: Outer { frame: Frame { pc: int::add(p, 1), ..fr }, ..o } };
    look: { k: [Look(), ..], stack: s, outer: Outer { frame: fr @ Frame { pc: 1, .. }, flag: _ } } => { k: [..], stack: [fr, ..s] };
    report: { k: [Report(), ..], stack: [Frame { pc: p, gas: g }, ..], outer: Outer { frame: Frame { pc: q, .. }, flag: f } } => { k: [int::add(int::add(p, q), int::add(g, f)), ..] };
}
";

/// A group child of a cell term may be a binder or `_` at the child's cell
/// sort, as a group entry may (U5): `Outer { frame: fr, .. }` binds the
/// `<frame>` cell, a result writes it back, and an update of a group may
/// nest inside an update of its parent. An alias over a group child names
/// the matched child and is rebuilt where it is used (N7); one bound twice
/// is rejected. `krs expand` writes a record that leaves a group child out with `..` as written,
/// and the print checks to the same rule.
#[test]
fn a_group_child_may_be_a_binder_or_wildcard() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = library_package(
        temporary.path(),
        "children",
        &format!("{TWO_LEVEL}{CHILD_BINDERS}"),
    );
    let k = emitted_k(target.path(), &manifest);
    expect_test::expect![[r"
        rule [push]:
            <k> push => .K ... </k>
            <stack> S:List => ListItem(Fr:FrameCell) S:List </stack>
            <outer> Fr:FrameCell <flag> _ </flag> </outer>
        rule [pop]:
            <k> pop => .K ... </k>
            <stack> ListItem(Fr:FrameCell) S:List => S:List </stack>
            (<outer> _ <flag> X:Int </flag> </outer> => <outer> Fr:FrameCell <flag> X:Int </flag> </outer>)
        rule [bump]:
            <k> bump => .K ... </k>
            (<outer> <frame> <pc> P:Int </pc> <gas> FrGas:Int </gas> </frame> <flag> OFlag:Int </flag> </outer> => <outer> <frame> <pc> P:Int +Int 1 </pc> <gas> FrGas:Int </gas> </frame> <flag> OFlag:Int </flag> </outer>)
        rule [look]:
            <k> look => .K ... </k>
            <stack> S:List => ListItem(<frame> <pc> FrPc:Int </pc> <gas> FrGas:Int </gas> </frame>) S:List </stack>
            <outer> <frame> <pc> ( 1 #as FrPc:Int ) </pc> <gas> FrGas:Int </gas> </frame> <flag> _ </flag> </outer>"]].assert_eq(&["push", "pop", "bump", "look"].map(|label| rule(&k, label)).join("\n"));
    let run = |manifest: &Path, program: &str| {
        let file = manifest.with_file_name("program.txt");
        fs::write(&file, program).unwrap();
        let (success, stdout, stderr) = krs(
            target.path(),
            manifest,
            "run",
            &[file.to_str().unwrap(), "-c", "ITEM=0"],
        );
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(
            flat.contains("<k>"),
            "{program}: {success}\n{stdout}\n{stderr}"
        );
        format!(
            "{program} => {}",
            &flat[flat.find("<k>").unwrap()..flat.find("</outer>").unwrap() + 8]
        )
    };
    let programs = [
        "seq(push, seq(bump, seq(bump, pop)))",
        "seq(bump, seq(look, report))",
    ];
    expect_test::expect![[r#"
        [
            "seq(push, seq(bump, seq(bump, pop))) => <k> .K </k> <stack> .List </stack> <outer> <frame> <pc> 0 </pc> <gas> 100 </gas> </frame> <flag> 0 </flag> </outer>",
            "seq(bump, seq(look, report)) => <k> 102 ~> .K </k> <stack> ListItem ( <frame> <pc> 1 </pc> <gas> 100 </gas> </frame> ) </stack> <outer> <frame> <pc> 1 </pc> <gas> 100 </gas> </frame> <flag> 0 </flag> </outer>",
        ]
    "#]].assert_debug_eq(&programs.map(|program| run(&manifest, program)));

    let twice = library_package(
        temporary.path(),
        "twice",
        &format!(
            "{TWO_LEVEL}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    look: {{ k: [Look(), ..], stack: [fr @ Frame {{ .. }}, ..], outer: Outer {{ frame: fr @ Frame {{ pc: 1, .. }}, flag: _ }} }} => {{ k: [..] }};\n}}\n"
        ),
    );
    expect_test::expect![[r#"error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::look (rule): the alias `fr` over the group child "frame" names one matched cell, so it must be bound once and outside `|`"#]].assert_eq(&check_errors(target.path(), &twice));

    let omitted = library_package(
        temporary.path(),
        "omitted",
        &format!(
            "{TWO_LEVEL}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    look: {{ k: [Look(), ..], outer: Outer {{ flag: f, .. }} }} => {{ k: [f, ..] }};\n}}\n"
        ),
    );
    let (success, expanded, stderr) = krs(target.path(), &omitted, "expand", &[]);
    assert!(success, "{stderr}");
    // The open record prints as written: the child it names, then `..`.
    assert!(expanded.contains("Outer { flag : f, .. }"), "{expanded}");
    let reference = library_package(temporary.path(), "omitted-expanded", &expanded);
    assert_eq!(run(&reference, "look"), run(&omitted, "look"));
}

/// Two `cells!` rules on `push`, one binding the group child `frame` whole
/// as a `FrameCell` binder and one matching a `Frame` record there.
const CHILD_PAIR: &str = r#"
#[k::rule(label = "child_binder")]
pub fn child_binder(
    fr: Frame,
    k::cells! {
        k: k::configuration::KCell(Cmd::Push(), ..),
        outer: k::fragment![Outer { frame: fr, .. }],
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..), ..state }
}

#[k::rule(label = "child_record")]
pub fn child_record(
    k::cells! {
        k: k::configuration::KCell(Cmd::Push(), ..),
        outer: k::fragment![Outer { frame: k::fragment![Frame { pc: 1, .. }], .. }],
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..), ..state }
}

"#;

/// Two `cells!` rules on `pop`, one binding a `stack` element as a
/// `FrameCell` binder and one matching a `Frame` record there.
const ELEMENT_PAIR: &str = r#"
#[k::rule(label = "element_binder")]
pub fn element_binder(
    fr: Frame,
    s: k::Term<List>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Pop(), ..),
        stack: k::configuration::Cell(list::concat(list::item(fr), s)),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..), ..state }
}

#[k::rule(label = "element_record")]
pub fn element_record(
    s: k::Term<List>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Pop(), ..),
        stack: k::configuration::Cell(list::concat(list::item(k::fragment![Frame { pc: 1, .. }]), s)),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..), ..state }
}
"#;

/// A `Frame` record denotes a `<frame>` cell, a `FrameCell`, wherever it
/// stands, so a `FrameCell` binder at the same place matches every term the
/// record matches: each pair of rules both apply to one configuration.
#[test]
fn a_group_record_overlaps_a_binder_of_its_cell_sort() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let errors =
        [("child-pair", CHILD_PAIR), ("element-pair", ELEMENT_PAIR)].map(|(name, rules)| {
            let manifest = library_package(temporary.path(), name, &format!("{TWO_LEVEL}{rules}"));
            check_errors(target.path(), &manifest)
        });
    expect_test::expect![[r"
        error[krs::analysis::overlapping-rule-heads]: rules `child_binder` and `child_record` can both apply to the same configuration at the same priority; K would take either one (nondeterminism). If that is intended, put both in one group with `#[k::rule(nondet = NAME)]`; otherwise refine a pattern, add disjoint `where` sorts or complementary requires guards, or order them with `owise` or `priority = N`.
        error[krs::analysis::overlapping-rule-heads]: rules `element_binder` and `element_record` can both apply to the same configuration at the same priority; K would take either one (nondeterminism). If that is intended, put both in one group with `#[k::rule(nondet = NAME)]`; otherwise refine a pattern, add disjoint `where` sorts or complementary requires guards, or order them with `owise` or `priority = N`."]].assert_eq(&errors.join("\n"));
}

/// Optional cells: a leaf `counter` and a group `mark`.
const OPTIONAL: &str = r#"
use k::builtin::{Int, KSequence};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Peek, Read))]
pub enum Cmd {
    #[k::syntax("peek")]
    Peek(),
    #[k::syntax("read")]
    Read(),
}

#[k::cell]
pub struct Mark {
    #[k::cell]
    pub seen: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(multiplicity = "?")]
    pub counter: Option<Int>,
    #[k::cell(multiplicity = "?", nested)]
    pub mark: Option<Mark>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm], counter: k::absent!(0), mark: k::absent!(Mark { seen: 0 }) }
    }
}
"#;

/// `krs check`'s first error and where it points, `line:column` in the
/// package's `src/lib.rs`, or `passed`.
fn first_error(target: &Path, manifest: &Path) -> String {
    let (success, stdout, stderr) = krs(target, manifest, "check", &[]);
    if success {
        return format!("passed: {}", stdout.trim());
    }
    let headline = stderr
        .lines()
        .find(|line| line.starts_with("error"))
        .unwrap_or_else(|| panic!("no error:\n{stderr}"));
    let location = stderr
        .lines()
        .find_map(|line| line.trim_start().strip_prefix("--> "))
        .and_then(|path| path.split_once("src/lib.rs:"))
        .map_or("unlocated", |(_, location)| location);
    format!("{headline} @ {location}")
}

/// The `line:column` of `needle`'s last line in the package's `src/lib.rs`.
fn location(manifest: &Path, needle: &str) -> String {
    let source = fs::read_to_string(manifest.with_file_name("src/lib.rs")).unwrap();
    source
        .lines()
        .collect::<Vec<_>>()
        .into_iter()
        .enumerate()
        .rev()
        .find_map(|(line, text)| {
            text.find(needle)
                .map(|column| format!("{}:{}", line + 1, column + 1))
        })
        .unwrap_or_else(|| panic!("`{needle}` is in the source"))
}

/// The two-level package with one machine rule.
fn two_level_rules(rule: &str) -> String {
    format!("{TWO_LEVEL}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    {rule}\n}}\n")
}

/// The rules and claim [`alternatives_over_a_whole_group_cell_are_refused_at_the_bar`]
/// refuses: a name, a library, and where its `|` term starts.
fn refused_alternatives() -> Vec<(&'static str, String, &'static str)> {
    vec![
        (
            "entry",
            two_level_rules(
                "pick: { k: [Push(), ..], outer: Outer { flag: 0, .. } | Outer { flag: 1, .. } } => { k: [..] };",
            ),
            "Outer { flag: 0",
        ),
        (
            "nested-entry",
            two_level_rules(
                "pick: { k: [Push(), ..], frame: Frame { pc: 0, .. } | Frame { gas: 0, .. } } => { k: [..] };",
            ),
            "Frame { pc: 0",
        ),
        (
            "shared-binder",
            two_level_rules(
                "pick: { k: [Push(), ..], outer: Outer { flag: x, frame: Frame { pc: 0, .. } } | Outer { flag: x, frame: Frame { gas: 0, .. } } } => { k: [x, ..] };",
            ),
            "Outer { flag: x",
        ),
        (
            "whole-result",
            two_level_rules(
                "pick: { k: [Push(), ..], outer: Outer { flag: 0, .. } | Outer { flag: 1, .. } } => { k: [..], outer: Outer { frame: Frame { pc: 0, gas: 0 }, flag: 2 } };",
            ),
            "Outer { flag: 0",
        ),
        (
            "alias-over",
            two_level_rules(
                "pick: { k: [Push(), ..], outer: o @ (Outer { flag: 0, .. } | Outer { flag: 1, .. }) } => { k: [..] };",
            ),
            "Outer { flag: 0",
        ),
        (
            "alias-inside",
            two_level_rules(
                "pick: { k: [Push(), ..], outer: (o @ Outer { flag: 0, .. } | o @ Outer { flag: 1, .. }) } => { k: [..] };",
            ),
            "o @ Outer { flag: 0",
        ),
        (
            "claim",
            format!(
                "{TWO_LEVEL}k::claims! {{\n    for Machine;\n    use Cmd::*;\n    #[k::claim(all_paths)]\n    pick: {{ k: [Push()], outer: Outer {{ flag: 0, .. }} | Outer {{ flag: 1, .. }} }} => {{ k: [] }};\n}}\n"
            ),
            "Outer { flag: 0",
        ),
        (
            "group-child",
            two_level_rules(
                "pick: { k: [Push(), ..], outer: Outer { frame: Frame { pc: 0, .. } | Frame { gas: 0, .. }, .. } } => { k: [..] };",
            ),
            "Frame { pc: 0",
        ),
        (
            "group-child-fragments",
            two_level_rules(
                "pick: { k: [Push(), ..], outer: Outer { frame: k::fragment![Frame { pc: 0, gas: _ }] | k::fragment![Frame { pc: 1, gas: _ }], .. } } => { k: [..] };",
            ),
            "k::fragment![Frame { pc: 0",
        ),
        (
            "group-child-alias",
            two_level_rules(
                "pick: { k: [Push(), ..], outer: Outer { frame: f @ (Frame { pc: 0, .. } | Frame { gas: 0, .. }), .. } } => { k: [..] };",
            ),
            "Frame { pc: 0",
        ),
        (
            "optional-group",
            format!(
                "{OPTIONAL}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    peek: {{ k: [Peek(), ..], mark: Some(Mark {{ seen: 0 }} | Mark {{ seen: 1 }}) }} => {{ k: [..] }};\n}}\n"
            ),
            "Mark { seen: 0",
        ),
        (
            "cells-entry",
            format!("{TWO_LEVEL}{CELLS_ENTRY_ALTERNATIVES}"),
            "k::fragment![Outer { flag: 0",
        ),
    ]
}

/// A `cells!` rule joining alternatives of the whole `outer` cell, one set of cells or another:
/// the macro refuses it as it is written. An elaborated readable rule, which no macro reads, is
/// refused where the `cells!` lowering reads a group entry, at the readable entry's code.
const CELLS_ENTRY_ALTERNATIVES: &str = r#"
#[k::rule(label = "pick")]
pub fn pick(
    k::cells! {
        k: k::configuration::KCell(Cmd::Push(), ..),
        outer: k::fragment![Outer { flag: 0, .. } | Outer { flag: 1, .. }],
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..), ..state }
}
"#;

/// `|` whose alternatives are whole group cells (a record entry naming a
/// group, at any depth, an optional group's `Some(..)`, or a group child of
/// a cell term) is refused where it is written, also below an alias, in
/// a claim, and in a `cells!` rule.
#[test]
fn alternatives_over_a_whole_group_cell_are_refused_at_the_bar() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = refused_alternatives();
    let mut refused = Vec::new();
    for (name, source, start) in &cases {
        let manifest = library_package(temporary.path(), &format!("bar-{name}"), source);
        let error = first_error(target.path(), &manifest);
        assert!(
            error.ends_with(&format!(" @ {}", location(&manifest, start))),
            "{name}: the error stands at the `|` term:\n{error}"
        );
        refused.push(format!("{name}: {}", error.split(" @ ").next().unwrap()));
    }
    expect_test::expect![[r#"
        [
            "entry: error[krs::analysis::invalid-pattern-or]: `|` cannot join alternatives of the whole `outer` cell: a group cell's entry is a set of cells, each placed by its label, and no single rule matches one set or another; write the alternatives inside the record, at the child they test (`Outer { child: A | B, .. }`), or write one rule per alternative; the alternatives differ only in `flag`: write `Outer { flag: A | B, .. }`",
            "nested-entry: error[krs::analysis::invalid-pattern-or]: `|` cannot join alternatives of the whole `frame` cell: a group cell's entry is a set of cells, each placed by its label, and no single rule matches one set or another; write the alternatives inside the record, at the child they test (`Frame { child: A | B, .. }`), or write one rule per alternative",
            "shared-binder: error[krs::analysis::invalid-pattern-or]: `|` cannot join alternatives of the whole `outer` cell: a group cell's entry is a set of cells, each placed by its label, and no single rule matches one set or another; write the alternatives inside the record, at the child they test (`Outer { child: A | B, .. }`), or write one rule per alternative",
            "whole-result: error[krs::analysis::invalid-pattern-or]: `|` cannot join alternatives of the whole `outer` cell: a group cell's entry is a set of cells, each placed by its label, and no single rule matches one set or another; write the alternatives inside the record, at the child they test (`Outer { child: A | B, .. }`), or write one rule per alternative; the alternatives differ only in `flag`: write `Outer { flag: A | B, .. }`",
            "alias-over: error[krs::analysis::invalid-pattern-or]: `|` cannot join alternatives of the whole `outer` cell: a group cell's entry is a set of cells, each placed by its label, and no single rule matches one set or another; write the alternatives inside the record, at the child they test (`Outer { child: A | B, .. }`), or write one rule per alternative; the alternatives differ only in `flag`: write `Outer { flag: A | B, .. }`",
            "alias-inside: error[krs::analysis::invalid-pattern-or]: `|` cannot join alternatives of the whole `outer` cell: a group cell's entry is a set of cells, each placed by its label, and no single rule matches one set or another; write the alternatives inside the record, at the child they test (`Outer { child: A | B, .. }`), or write one rule per alternative",
            "claim: error[krs::analysis::invalid-pattern-or]: `|` cannot join alternatives of the whole `outer` cell: a group cell's entry is a set of cells, each placed by its label, and no single rule matches one set or another; write the alternatives inside the record, at the child they test (`Outer { child: A | B, .. }`), or write one rule per alternative; the alternatives differ only in `flag`: write `Outer { flag: A | B, .. }`",
            "group-child: error[krs::analysis::invalid-pattern-or]: `|` cannot join alternatives of the whole `frame` cell: a group cell's entry is a set of cells, each placed by its label, and no single rule matches one set or another; write the alternatives inside the record, at the child they test (`Frame { child: A | B, .. }`), or write one rule per alternative",
            "group-child-fragments: error[krs::analysis::invalid-pattern-or]: `|` cannot join alternatives of the whole `frame` cell: a group cell's entry is a set of cells, each placed by its label, and no single rule matches one set or another; write the alternatives inside the record, at the child they test (`Frame { child: A | B, .. }`), or write one rule per alternative; the alternatives differ only in `pc`: write `Frame { pc: A | B, .. }`",
            "group-child-alias: error[krs::analysis::invalid-pattern-or]: `|` cannot join alternatives of the whole `frame` cell: a group cell's entry is a set of cells, each placed by its label, and no single rule matches one set or another; write the alternatives inside the record, at the child they test (`Frame { child: A | B, .. }`), or write one rule per alternative",
            "optional-group: error[krs::analysis::invalid-pattern-or]: `|` cannot join alternatives of the whole `mark` cell: a group cell's entry is a set of cells, each placed by its label, and no single rule matches one set or another; write the alternatives inside the record, at the child they test (`Mark { child: A | B, .. }`), or write one rule per alternative; the alternatives differ only in `seen`: write `Mark { seen: A | B, .. }`",
            "cells-entry: error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: an entry without a wrapper is a nested cell's: a binder, `_` in a pattern, or `k::fragment![..]`; a leaf cell's content is written inside its wrapper, `Cell(..)`, and the computation's inside `KCell(..)`",
        ]
    "#]]
    .assert_debug_eq(&refused);
}

/// The alternatives a cell term distributes over, inside a leaf, a group
/// record, or a list element, stand as before.
#[test]
fn alternatives_a_cell_term_distributes_over_stand() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let accepted = [
        (
            "child-alternatives",
            two_level_rules(
                "pick: { k: [Push(), ..], outer: Outer { flag: 0 | 1, .. } } => { k: [..] };",
            ),
        ),
        (
            "leaf-alternatives",
            two_level_rules("pick: { k: [Push(), ..], flag: 0 | 1 } => { k: [..] };"),
        ),
        (
            "list-element",
            two_level_rules(
                "pick: { k: [Push(), ..], stack: [Frame { pc: 0, .. } | Frame { gas: 0, .. }, s @ ..] } => { k: [..], stack: s };",
            ),
        ),
        (
            "optional-leaf",
            format!(
                "{OPTIONAL}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    read: {{ k: [Read(), ..], counter: Some(0 | 1) }} => {{ k: [..] }};\n}}\n"
            ),
        ),
    ];
    for (name, source) in &accepted {
        let manifest = library_package(temporary.path(), &format!("bar-{name}"), source);
        let result = first_error(target.path(), &manifest);
        assert!(result.starts_with("passed"), "{name}: {result}");
    }
    let manifest = library_package(temporary.path(), "bar-child-emitted", &accepted[0].1);
    expect_test::expect![[r"
        rule [pick]:
            <k> push => .K ... </k>
            <outer> _ <flag> ( 0 #Or 1 ) </flag> </outer>"]]
    .assert_eq(rule(&emitted_k(target.path(), &manifest), "pick"));
}

const SORTED_HEAD_WILDCARD: &str = r#"
use k::KResult;
use k::builtin::KSequence;

k::sorts! {
    Stmt;
    Tag;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {
    #[k::syntax("go")]
    Go(),
}

#[k::constructors(sort = Tag, result = KResult)]
pub enum Marker {
    #[k::syntax("marked")]
    Marked(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm, Marker::Marked()],
        }
    }
}

k::rules! {
    for Stmt;
    drop: _ => ();
}
"#;

/// A head `_` of a `for Sort` clause is any one item of that sort, and no
/// item of another: `drop` erases the program's `go` and leaves the `Tag`
/// behind it.
#[test]
fn a_head_wildcard_matches_only_its_clauses_sort() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = library_package(temporary.path(), "sorted-wildcard", SORTED_HEAD_WILDCARD);
    expect_test::expect![[r"
        rule [drop]:
            <k> _:Stmt => .K ... </k>"]]
    .assert_eq(rule(&emitted_k(target.path(), &manifest), "drop"));
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "go").unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{stdout}\n{stderr}");
    expect_test::expect!["<k> marked ~> .K </k>"]
        .assert_eq(&stdout.split_whitespace().collect::<Vec<_>>().join(" "));

    // The print names the head `_` by a binder of the clause's sort used once, so the printed
    // rule matches a `Stmt` and nothing else, as the clause does: its run keeps the `Tag` too.
    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let printed = expanded.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        printed.contains("_stmt: crate::Stmt")
            && printed.contains("k::configuration::KCell(_stmt, ..)"),
        "{expanded}"
    );
    let reference = library_package(temporary.path(), "sorted-wildcard-expanded", &expanded);
    expect_test::expect![[r"
        rule [drop]:
            <k> _Stmt:Stmt => .K ... </k>"]]
    .assert_eq(rule(&emitted_k(target.path(), &reference), "drop"));
    let program = reference.with_file_name("program.txt");
    fs::write(&program, "go").unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &reference,
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{stdout}\n{stderr}");
    expect_test::expect!["<k> marked ~> .K </k>"]
        .assert_eq(&stdout.split_whitespace().collect::<Vec<_>>().join(" "));
}

/// Groups with `?` children: `O` beside its plain `on`, `W` holding `Gw` (a `?` child one level
/// down), `Core` holding a `?` group, and the plain leaf `stack`.
const PRESENCES: &str = r#"
use k::builtin::{Int, KSequence, List, list};
use k::{KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Go, Hold))]
pub enum Cmd {
    #[k::syntax("go")]
    Go(),
    #[k::syntax("hold({s})")]
    Hold { s: Int },
}

#[k::cell]
pub struct O {
    #[k::cell(multiplicity = "?")]
    pub oo: Option<Int>,
    #[k::cell(multiplicity = "?")]
    pub op: Option<Int>,
    #[k::cell]
    pub on: Int,
}

#[k::cell]
pub struct Gw {
    #[k::cell(multiplicity = "?")]
    pub wo: Option<Int>,
    #[k::cell]
    pub wa: Int,
}

#[k::cell]
pub struct W {
    #[k::cell(nested)]
    pub wg: Gw,
    #[k::cell]
    pub wn: Int,
}

#[k::cell]
pub struct Fpu {
    #[k::cell]
    pub fx: Int,
}

#[k::cell]
pub struct Core {
    #[k::cell]
    pub pc: Int,
    #[k::cell(multiplicity = "?", nested)]
    pub fpu: Option<Fpu>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub stack: List,
    #[k::cell(nested)]
    pub ocell: O,
    #[k::cell(nested)]
    pub wcell: W,
    #[k::cell(nested)]
    pub core: Core,
    #[k::cell]
    pub slot: k::KItem,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt, item: k::KItem) -> Self {
        Self {
            k: k::k![pgm],
            stack: list::empty(),
            ocell: O { oo: k::absent!(0), op: k::absent!(0), on: 0 },
            wcell: W { wg: Gw { wo: k::absent!(0), wa: 0 }, wn: 0 },
            core: Core { pc: 0, fpu: k::absent!(Fpu { fx: 0 }) },
            slot: item,
        }
    }
}
"#;

/// The readable rule `{ subject } => { result }` over [`PRESENCES`].
fn readable_presence(subject: &str, result: &str) -> String {
    format!(
        "{PRESENCES}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    go: {{ k: [Go(), ..], {subject} }} => {{ k: [{result}..] }};\n}}\n"
    )
}

/// The readable rule writing `result` over [`PRESENCES`].
fn readable_written(result: &str) -> String {
    format!(
        "{PRESENCES}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    go: {{ k: [Go(), ..] }} => {{ k: [..], {result} }};\n}}\n"
    )
}

/// The `cells!` rule matching `subject` over [`PRESENCES`], whose result puts `x` first when
/// `reads`.
fn cells_presence(subject: &str, reads: bool) -> String {
    let (parameter, item) = if reads {
        ("x: Term<Int>, ", "x, ")
    } else {
        ("", "")
    };
    format!(
        "{PRESENCES}#[k::rule(label = \"go\")]\nfn go({parameter}k::cells! {{ k: k::configuration::KCell(Cmd::Go(), tail @ ..), {subject}, state @ .. }}: Machine) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell({item}..tail), ..state }}\n}}\n"
    )
}

/// The `cells!` rule writing `result` over [`PRESENCES`].
fn cells_written(result: &str) -> String {
    format!(
        "{PRESENCES}#[k::rule(label = \"go\")]\nfn go(k::cells! {{ k: k::configuration::KCell(Cmd::Go(), tail @ ..), state @ .. }}: Machine) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), {result}, ..state }}\n}}\n"
    )
}

/// The witnesses [`a_group_records_presence_child_waits_for_its_entry_on_every_route`] checks: a
/// name, a library, and the spelling its refusal starts at.
#[expect(
    clippy::too_many_lines,
    reason = "One table of witnesses, each route beside its twin."
)]
fn presence_witnesses() -> Vec<(&'static str, String, &'static str)> {
    vec![
        (
            "p2b-readable",
            readable_presence("ocell: O { oo: Some(x), .. }", "x, "),
            "Some(x)",
        ),
        (
            "p2a-cells",
            cells_presence("ocell: k::fragment![crate::O { oo: Some(x), .. }]", true),
            "Some(x)",
        ),
        (
            "p2c-readable",
            readable_presence("ocell: O { oo: Some(x), .. }", ""),
            "Some(x)",
        ),
        (
            "p2c-cells",
            cells_presence("ocell: k::fragment![crate::O { oo: Some(_), .. }]", false),
            "Some(_)",
        ),
        (
            "second-subject-readable",
            readable_presence("ocell: O { oo: Some(x), op: None, .. }", "x, "),
            "None",
        ),
        (
            "second-subject-cells",
            cells_presence(
                "ocell: k::fragment![crate::O { oo: Some(x), op: None, .. }]",
                true,
            ),
            "None",
        ),
        (
            "p1b-readable",
            readable_written("ocell: O { oo: Some(1), op: None, on: 0 }"),
            "Some(1)",
        ),
        (
            "p1b-cells",
            cells_written("ocell: k::fragment![crate::O { oo: Some(1), op: None, on: 0 }]"),
            "Some(1)",
        ),
        (
            "depth-2-subject-readable",
            readable_presence("wcell: W { wg: Gw { wo: Some(x), .. }, .. }", "x, "),
            "Some(x)",
        ),
        (
            "depth-2-subject-cells",
            cells_presence(
                "wcell: k::fragment![crate::W { wg: k::fragment![crate::Gw { wo: Some(x), .. }], .. }]",
                true,
            ),
            "Some(x)",
        ),
        (
            "depth-2-result-readable",
            readable_written("wcell: W { wg: Gw { wo: Some(1), wa: 0 }, wn: 0 }"),
            "Some(1)",
        ),
        (
            "depth-2-result-cells",
            cells_written(
                "wcell: k::fragment![crate::W { wg: k::fragment![crate::Gw { wo: Some(1), wa: 0 }], wn: 0 }]",
            ),
            "Some(1)",
        ),
        (
            "bare-subject-readable",
            readable_presence("ocell: O { oo: x, .. }", "x, "),
            "x, ..",
        ),
        (
            "bare-subject-cells",
            cells_presence("ocell: k::fragment![crate::O { oo: x, .. }]", true),
            "x, ..",
        ),
        (
            "bare-result-readable",
            readable_written("ocell: O { oo: 1, op: None, on: 0 }"),
            "1, op",
        ),
        (
            "bare-result-cells",
            cells_written("ocell: k::fragment![crate::O { oo: 1, op: None, on: 0 }]"),
            "1, op",
        ),
        (
            "plain-presence-readable",
            readable_presence("ocell: O { on: Some(x), .. }", "x, "),
            "Some(x)",
        ),
        (
            "plain-presence-cells",
            cells_presence("ocell: k::fragment![crate::O { on: Some(x), .. }]", true),
            "Some(x)",
        ),
        (
            "depth-2-bare-cells",
            cells_presence(
                "wcell: k::fragment![crate::W { wg: crate::Gw { wo: x, .. }, .. }]",
                true,
            ),
            "x, ..",
        ),
        (
            "leaf-readable",
            readable_presence("stack: Core { fpu: Some(_), .. }", ""),
            "Core {",
        ),
        (
            "leaf-result-readable",
            readable_written("stack: Core { pc: 0, fpu: None }"),
            "Core {",
        ),
        (
            "kitem-leaf-readable",
            readable_presence("slot: Core { fpu: Some(_), .. }", ""),
            "Some(_)",
        ),
        (
            "constructor-record-readable",
            readable_presence("slot: Hold { s: Some(_) }", ""),
            "Some(_)",
        ),
        (
            "constructor-call-readable",
            readable_presence("slot: Hold(Some(_))", ""),
            "Some(_)",
        ),
        (
            "constructor-in-group-cells",
            cells_presence(
                "wcell: k::fragment![crate::W { wg: crate::Gw { wo: Some(_), wa: Cmd::Hold { s: None } }, .. }]",
                false,
            ),
            "None",
        ),
        (
            "leaf-cells",
            cells_presence(
                "stack: k::fragment![crate::Core { fpu: Some(_), .. }]",
                false,
            ),
            "k::fragment![crate::Core",
        ),
    ]
}

/// A group record's `?` child written `Some(..)` or `None`, at a configuration position, is that
/// child's presence, an entry no record names yet (`collection-entry`): a fault of a part, which
/// waits for the judgement of the whole entry. So it is one class on both routes and both sides,
/// with any number of such children and at any depth: the limit where the entries are admitted
/// (P2a-c), a principle first where one refuses the whole (the result writes an optional cell its
/// subject does not match, P1b; the subject's `None` is not created), and a subject's presence
/// keeps the names it binds for the result that reads them (P2b). A fragment's children are
/// entries as a record's are, judged by each child's kind on both routes: a `?` child written
/// as a bare term lacks its presence, and a plain child's `Some(..)` is a presence it has none
/// of (TABLE item 1: a `cells!` subject's `oo: x` passed and matched a present `oo` only, and
/// `on: Some(x)` met the limit). On a leaf a `cells!` fragment
/// meets the leaf's refusal, its wrapper (`cell-wrapper`), before the limit, and a readable group
/// record on a leaf whose sort holds no cell term is no term of the leaf (`invalid-term`, TABLE
/// item 3); on a `KItem` leaf it is a value, whose `?` child is the limit's. A constructor's
/// record is a term, so `Some(..)` or `None` in its field names no declaration
/// (`not-a-declaration`), as in the call `Hold(Some(_))`, inside group records too.
#[test]
fn a_group_records_presence_child_waits_for_its_entry_on_every_route() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = presence_witnesses();
    let mut outcomes = Vec::new();
    for (name, source, at) in &cases {
        let manifest = library_package(temporary.path(), &format!("presence-{name}"), source);
        let error = first_error(target.path(), &manifest);
        let (headline, location) = error.split_once(" @ ").expect("refused");
        let class = headline.split(']').next().unwrap_or(headline);
        let library = fs::read_to_string(manifest.with_file_name("src/lib.rs")).unwrap();
        let (line, column) = location.split_once(':').unwrap();
        let line: usize = line.parse().unwrap();
        let column: usize = column.parse().unwrap();
        let written = &library.lines().nth(line - 1).unwrap()[column - 1..];
        assert!(
            written.starts_with(at),
            "{name}: at `{at}`, found `{written}`:\n{error}"
        );
        outcomes.push(format!("{name}: {class}]"));
    }
    expect_test::expect![[r#"
        [
            "p2b-readable: error[krs::analysis::collection-entry]",
            "p2a-cells: error[krs::analysis::collection-entry]",
            "p2c-readable: error[krs::analysis::collection-entry]",
            "p2c-cells: error[krs::analysis::collection-entry]",
            "second-subject-readable: error[krs::analysis::optional-presence]",
            "second-subject-cells: error[krs::analysis::optional-presence]",
            "p1b-readable: error[krs::analysis::optional-presence]",
            "p1b-cells: error[krs::analysis::optional-presence]",
            "depth-2-subject-readable: error[krs::analysis::collection-entry]",
            "depth-2-subject-cells: error[krs::analysis::collection-entry]",
            "depth-2-result-readable: error[krs::analysis::optional-presence]",
            "depth-2-result-cells: error[krs::analysis::optional-presence]",
            "bare-subject-readable: error[krs::analysis::optional-presence]",
            "bare-subject-cells: error[krs::analysis::optional-presence]",
            "bare-result-readable: error[krs::analysis::optional-presence]",
            "bare-result-cells: error[krs::analysis::optional-presence]",
            "plain-presence-readable: error[krs::analysis::optional-presence]",
            "plain-presence-cells: error[krs::analysis::optional-presence]",
            "depth-2-bare-cells: error[krs::analysis::optional-presence]",
            "leaf-readable: error[krs::analysis::invalid-term]",
            "leaf-result-readable: error[krs::analysis::invalid-term]",
            "kitem-leaf-readable: error[krs::analysis::collection-entry]",
            "constructor-record-readable: error[krs::expand::not-a-declaration]",
            "constructor-call-readable: error[krs::expand::not-a-declaration]",
            "constructor-in-group-cells: error[krs::expand::not-a-declaration]",
            "leaf-cells: error[krs::analysis::cell-wrapper]",
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}

/// A function an equation's function context is written for, appended to [`PRESENCES`].
const PEEK: &str = r#"
#[k::function(partial, sort = Int, syntax = "peek({a})")]
pub struct Peek {
    pub a: Term<Int>,
}
"#;

/// The `cells!` sentences over [`PRESENCES`] that match `entry` beside the computation, with the
/// typed parameters `parameters`: a rule, a claim, a context alias and an equation's function
/// context, each by its form's name.
fn sentence_forms(entry: &str, parameters: &str) -> [(&'static str, String); 4] {
    let rule = format!(
        "#[k::rule(label = \"go\")]\nfn go({parameters}, k::cells! {{ k: k::configuration::KCell(Cmd::Go(), tail @ ..), {entry}, state @ .. }}: Machine) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), ..state }}\n}}\n"
    );
    let claim = format!(
        "#[k::claim(all_paths, label = \"go-claim\")]\nfn go_claim({parameters}, k::cells! {{ k: k::configuration::KCell(Cmd::Go(), tail @ ..), {entry}, state @ .. }}: Machine) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), ..state }}\n}}\n"
    );
    let alias = format!(
        "#[k::context_alias(name = at_go, here = site)]\nfn at_go({parameters}, k::cells! {{ k: k::configuration::KCell(site, tail @ ..), {entry}, state @ .. }}: Machine) {{}}\n"
    );
    let context = format!(
        "#[k::equation]\nfn peek(\n    a: Term<Int>,\n    {parameters},\n    k::term![Peek(a)]: Term<Int>,\n    k::cells! {{ {entry}, .. }}: Machine,\n) -> Term<Int> {{\n    a\n}}\n"
    );
    [
        ("rule", rule),
        ("claim", claim),
        ("context-alias", alias),
        ("function-context", context),
    ]
    .map(|(form, sentence)| (form, format!("{PRESENCES}{PEEK}{sentence}")))
}

/// A `cells!` entry's kind is judged by the entry table in every sentence form that holds one,
/// a claim's, a context alias's and a function context's as a rule's (TABLE item 2), so a
/// mistake is told with one class and one text, at one spelling, and in the same order: a
/// presence on a plain leaf; `KCell(..)` on a leaf with an item after its rest, where the
/// wrapper is the first mistake; a by-kind mistake beside a fragment's `?` child presence,
/// whose limit waits for the entries. A claim was judged by the compiler's copy only (another
/// text, at the cell's name), and a claim, a context alias and a function context met the item
/// after the rest and the limit before the kind.
#[test]
fn a_cells_entry_is_judged_alike_by_every_sentence_form() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let witnesses = [
        (
            "presence-on-a-plain-leaf",
            "stack: Some(k::configuration::Cell(s))",
            "s: Term<List>",
            "Some(k::configuration::Cell(s))",
        ),
        (
            "item-after-rest-on-a-leaf",
            "stack: k::configuration::KCell(.., z)",
            "z: Term<Int>",
            "k::configuration::KCell(.., z)",
        ),
        (
            "kind-beside-a-limit",
            "ocell: k::fragment![crate::O { oo: Some(z), .. }], stack: Some(k::configuration::Cell(s))",
            "z: Term<Int>, s: Term<List>",
            "Some(k::configuration::Cell(s))",
        ),
    ];
    let mut outcomes = Vec::new();
    for (name, entry, parameters, at) in witnesses {
        let mut refusals = Vec::new();
        for (form, source) in sentence_forms(entry, parameters) {
            let manifest =
                library_package(temporary.path(), &format!("forms-{name}-{form}"), &source);
            let error = first_error(target.path(), &manifest);
            let (headline, location) = error.split_once(" @ ").expect("refused");
            let library = fs::read_to_string(manifest.with_file_name("src/lib.rs")).unwrap();
            let (line, column) = location.split_once(':').unwrap();
            let line: usize = line.parse().unwrap();
            let column: usize = column.parse().unwrap();
            let written = &library.lines().nth(line - 1).unwrap()[column - 1..];
            assert!(
                written.starts_with(at),
                "{name}, {form}: at `{at}`, found `{written}`:\n{error}"
            );
            refusals.push((form, headline.to_owned()));
        }
        let (_, first) = &refusals[0];
        for (form, headline) in &refusals {
            assert_eq!(headline, first, "{name}: the {form} is told as the rule is");
        }
        outcomes.push(format!("{name}: {first}"));
    }
    expect_test::expect![[r#"
        [
            "presence-on-a-plain-leaf: error[krs::analysis::optional-presence]: the cell `stack` holds a `List` leaf and is not optional (it is declared without `multiplicity = \"?\"`), so it is always there: `Some(..)` and `None` are the presence of an optional cell, which `stack` has none of",
            "item-after-rest-on-a-leaf: error[krs::analysis::cell-wrapper]: the cell `stack` holds a `List` leaf, and the entry's wrapper is not that content's: `KCell(..)` wraps a computation's items and `Cell(..)` a leaf's value, on the cell that holds one; write its entry as `k::configuration::Cell(..)`",
            "kind-beside-a-limit: error[krs::analysis::optional-presence]: the cell `stack` holds a `List` leaf and is not optional (it is declared without `multiplicity = \"?\"`), so it is always there: `Some(..)` and `None` are the presence of an optional cell, which `stack` has none of",
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}

/// Pattern alternatives a mark holds, `Some(s | s)` in a readable record and
/// `Some(k::configuration::Cell(s | s))` in `cells!`, are the one term pattern they make: the
/// marks around them are the entry's, judged by its cell's kind as around any term, with the
/// table's line at the presence on both routes (TABLE follow-up (c): the `cells!` entry was
/// left unread, and the compiler's copy answered with its own text at the cell's name).
#[test]
fn a_presence_around_pattern_alternatives_is_judged_as_around_any_term() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let routes = [
        (
            "readable",
            readable_presence("stack: Some(s | s)", ""),
            "Some(s | s)",
        ),
        (
            "cells",
            format!(
                "{PRESENCES}#[k::rule(label = \"go\")]\nfn go(s: Term<List>, k::cells! {{ k: k::configuration::KCell(Cmd::Go(), tail @ ..), stack: Some(k::configuration::Cell(s | s)), state @ .. }}: Machine) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), ..state }}\n}}\n"
            ),
            "Some(k::configuration::Cell(s | s))",
        ),
        (
            "cells-claim",
            format!(
                "{PRESENCES}#[k::claim(all_paths, label = \"go-claim\")]\nfn go_claim(s: Term<List>, k::cells! {{ k: k::configuration::KCell(Cmd::Go(), tail @ ..), stack: Some(k::configuration::Cell(s | s)), state @ .. }}: Machine) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), ..state }}\n}}\n"
            ),
            "Some(k::configuration::Cell(s | s))",
        ),
    ];
    let mut headlines = Vec::new();
    for (route, source, at) in routes {
        let manifest = library_package(temporary.path(), &format!("alternatives-{route}"), &source);
        let error = first_error(target.path(), &manifest);
        let (headline, place) = error.split_once(" @ ").expect("refused");
        assert_eq!(place, location(&manifest, at), "{route}: {error}");
        headlines.push(headline.to_owned());
    }
    for headline in &headlines {
        assert_eq!(headline, &headlines[0], "one line on every route");
    }
    assert!(
        headlines[0].starts_with(
            "error[krs::analysis::optional-presence]: the cell `stack` holds a `List` leaf"
        ),
        "{}",
        headlines[0]
    );
}

/// A `cells!` leaf's `Cell(k::fragment![..])` holds the group's cell term as the readable
/// record does, so the fragment's `?` children's presences are carried out of it as the entry
/// reader carries a record's (TABLE follow-up (b): rustc's `Option` answered `not-a-declaration`
/// inside `Cell(..)`). The leaf's verdict then comes first, with the readable twin's line: a
/// group record on a `List` leaf is `invalid-term`, and on a `KItem` leaf, which holds it, the
/// `?` child's presence is the group record's limit, both at the same spelling as the twin's.
#[test]
fn a_fragment_inside_a_leaf_s_cell_carries_its_presence_children_as_the_readable_record_does() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let twins = [
        (
            "list-leaf",
            cells_presence(
                "stack: k::configuration::Cell(k::fragment![crate::Core { fpu: Some(_), .. }])",
                false,
            ),
            "k::fragment![crate::Core { fpu: Some(_), .. }]",
            readable_presence("stack: Core { fpu: Some(_), .. }", ""),
            "Core { fpu: Some(_), .. }",
        ),
        (
            "item-leaf",
            cells_presence(
                "slot: k::configuration::Cell(k::fragment![crate::Core { fpu: Some(_), .. }])",
                false,
            ),
            "Some(_), .. }])",
            readable_presence("slot: Core { fpu: Some(_), .. }", ""),
            "Some(_), .. }",
        ),
    ];
    let mut lines = Vec::new();
    for (name, cells, cells_at, readable, readable_at) in twins {
        let mut headlines = Vec::new();
        for (route, source, at) in [
            ("cells", cells, cells_at),
            ("readable", readable, readable_at),
        ] {
            let manifest = library_package(
                temporary.path(),
                &format!("fragment-{name}-{route}"),
                &source,
            );
            let error = first_error(target.path(), &manifest);
            let (headline, place) = error.split_once(" @ ").expect("refused");
            assert_eq!(place, location(&manifest, at), "{name} {route}: {error}");
            headlines.push(headline.to_owned());
        }
        assert_eq!(
            headlines[0], headlines[1],
            "{name}: one line on both routes"
        );
        lines.push(format!("{name}: {}", headlines[0]));
    }
    expect_test::expect![[r#"
        [
            "list-leaf: error[krs::analysis::invalid-term]: the cell `stack` holds a `List` leaf, and the entry gives it a `Core` record, the `Core` group's cell term, whose sort is not below the leaf's: a group's cell sort is below `KItem` only, so a leaf holds a group's record only where its sort is `KItem`",
            "item-leaf: error[krs::analysis::collection-entry]: the record's field `fpu` holds `Some(..)`, a `?` cell's presence, and no term: KRS has no `Option` term; in a group record it is the `?` child's entry, which a group record does not name yet, as an instance record does not name a `?` or `*` child yet",
        ]
    "#]].assert_debug_eq(&lines);
}

/// A group record that is a value, the group's cell term in a list element, means the cell a
/// record at a configuration position means, so its `?` child's place holds the cell or its
/// absence there too, and a bare value, binder, `_` or group record states neither: each is
/// the entry's `optional-presence`, with the entry's text, at the child's value, in a subject
/// and a result, readable and `cells!` alike.
#[test]
fn a_value_records_presence_child_states_its_presence_as_an_entry_does() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "leaf-readable",
            readable_presence("stack: [O { oo: x, .. }, ..]", "x, "),
            "x, ..",
        ),
        (
            "leaf-cells",
            cells_presence(
                "stack: k::configuration::Cell([k::fragment![crate::O { oo: x, .. }], ..])",
                true,
            ),
            "x, ..",
        ),
        (
            "leaf-wildcard",
            readable_presence("stack: [O { oo: _, .. }, ..]", ""),
            "_, ..",
        ),
        (
            "group-record",
            readable_presence("stack: [Core { fpu: Fpu { fx: y }, .. }, ..]", "y, "),
            "Fpu {",
        ),
        (
            "group-binder",
            readable_presence("stack: [Core { fpu: f, .. }, ..]", ""),
            "f, ..",
        ),
        (
            "group-wildcard",
            readable_presence("stack: [Core { fpu: _, pc: y }, ..]", "y, "),
            "_, pc",
        ),
        (
            "result-leaf",
            readable_written("stack: [O { oo: 1, op: 2, on: 3 }]"),
            "1, op",
        ),
    ];
    let mut outcomes = Vec::new();
    for (name, source, at) in &cases {
        let manifest = library_package(temporary.path(), &format!("value-{name}"), source);
        let error = first_error(target.path(), &manifest);
        let (headline, location) = error.split_once(" @ ").expect("refused");
        let library = fs::read_to_string(manifest.with_file_name("src/lib.rs")).unwrap();
        let (line, column) = location.split_once(':').unwrap();
        let line: usize = line.parse().unwrap();
        let column: usize = column.parse().unwrap();
        let written = &library.lines().nth(line - 1).unwrap()[column - 1..];
        assert!(
            written.starts_with(at),
            "{name}: at `{at}`, found `{written}`:\n{error}"
        );
        let cell = if name.starts_with("group") {
            "fpu"
        } else {
            "oo"
        };
        outcomes.push((*name, headline.replace(&format!("`{cell}`"), "`CELL`")));
    }
    // The entry's own refusal of the same spelling at a configuration position, whose text the
    // values share.
    let entry = library_package(
        temporary.path(),
        "value-entry",
        &readable_presence("core: Core { fpu: f, .. }", ""),
    );
    let entry = first_error(target.path(), &entry);
    let entry = entry
        .split_once(" @ ")
        .expect("refused")
        .0
        .replace("`fpu`", "`CELL`");
    for (name, headline) in &outcomes {
        assert_eq!(headline, &entry, "{name}");
    }
    expect_test::expect![[r#"error[krs::analysis::optional-presence]: the cell `CELL` is optional (`multiplicity = "?"`), so its entry states whether it is there: `Some(..)` holds its content when it is, and `None` stands for its absence; write its entry inside `Some(..)`, or as `None` for its absence"#]].assert_eq(&entry);
    // Only a child the author writes states a presence: an update keeps what its base holds
    // there, and a base alias's pattern leaves out what it does not name, so `oo` and `op`,
    // which neither record writes, ask nothing.
    let kept = library_package(
        temporary.path(),
        "value-update-kept",
        &format!(
            "{PRESENCES}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    go: {{ k: [Go(), ..], stack: [o @ O {{ on: x, .. }}, s @ ..] }} => {{ k: [..], stack: [O {{ on: 1, ..o }}, ..s] }};\n}}\n"
        ),
    );
    let kept = first_error(target.path(), &kept);
    assert!(kept.starts_with("passed"), "{kept}");
}

/// Groups a result may create with every child unmatched: an optional group `ogroup` of two
/// children, an optional group `ohcell` holding the group `hg`, and the group child `aframe` of
/// the Map collection `acct`'s instances.
const CREATED: &str = r#"
use k::builtin::{Int, KSequence};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {
    #[k::syntax("make({x})")]
    Make { x: Int },
}

#[k::cell]
pub struct Gp {
    #[k::cell]
    pub pa: Int,
    #[k::cell]
    pub pb: Int,
}

#[k::cell]
pub struct G {
    #[k::cell]
    pub a: Int,
    #[k::cell]
    pub b: Int,
}

#[k::cell]
pub struct Hp {
    #[k::cell(nested)]
    pub hg: G,
    #[k::cell]
    pub hn: Int,
}

#[k::cell]
pub struct Ag {
    #[k::cell]
    pub aa: Int,
    #[k::cell]
    pub ab: Int,
}

#[k::cell]
pub struct Acct {
    #[k::cell]
    pub id: Int,
    #[k::cell(nested)]
    pub aframe: Ag,
}

#[k::cell]
pub struct Bank {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub acct: Acct,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(multiplicity = "?", nested)]
    pub ogroup: Option<Gp>,
    #[k::cell(multiplicity = "?", nested)]
    pub ohcell: Option<Hp>,
    #[k::cell(nested)]
    pub bank: Bank,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            ogroup: k::absent!(Gp { pa: 0, pb: 0 }),
            ohcell: k::absent!(Hp { hg: G { a: 0, b: 0 }, hn: 0 }),
            bank: Bank { acct: Acct { id: 0, aframe: Ag { aa: 0, ab: 0 } } },
        }
    }
}
"#;

/// A result's `..` keeps the children of a group its subject matched; where no group was
/// matched, it names no value for them. A `?` group a result creates with `Some(..)` over
/// `None`, a group child inside one, and a group child of an instance the result creates have no
/// matched group, so a record there that leaves a child out is refused, bare or in
/// `k::fragment!`, readable or `cells!`, with one text (RDRA fix of BUILT-DOTS: once the
/// fragment's `..` was read, `Some(k::fragment![crate::Gp { pa: x, .. }])` emitted
/// `<pb> _ </pb>` on the rule's right side, as the bare group children below already did). The
/// same record naming every child is admitted.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of places and spellings, each with its refusal."
)]
fn a_record_of_a_group_no_subject_matched_names_every_child() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = |subject: &str, result: &str| {
        format!(
            "{CREATED}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    make: {{ k: [Make {{ x }}, ..], {subject} }} => {{ k: [..], {result} }};\n}}\n"
        )
    };
    let cells = |subject: &str, result: &str| {
        format!(
            "{CREATED}#[k::rule(label = \"make\")]\npub fn make(\n    x: Int,\n    k::cells! {{ k: k::configuration::KCell(Cmd::Make {{ x }}, tail @ ..), {subject}, state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), {result}, ..state }}\n}}\n"
        )
    };
    let exact = library_package(
        temporary.path(),
        "created-exact",
        &cells(
            "ogroup: None",
            "ogroup: Some(k::fragment![crate::Gp { pa: x, pb: 0, .. }])",
        ),
    );
    expect_test::expect![[r"
        rule [make]:
            <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k>
            (.Bag => <ogroup> <pa> X:Int </pa> <pb> 0 </pb> </ogroup>)"]]
    .assert_eq(rule(&emitted_k(target.path(), &exact), "make"));
    let refused = [
        (
            "optional",
            "Gp",
            readable("ogroup: None", "ogroup: Some(Gp { pa: x, .. })"),
        ),
        (
            "optional",
            "Gp",
            readable(
                "ogroup: None",
                "ogroup: Some(k::fragment![Gp { pa: x, .. }])",
            ),
        ),
        (
            "optional",
            "Gp",
            cells(
                "ogroup: None",
                "ogroup: Some(k::fragment![crate::Gp { pa: x, .. }])",
            ),
        ),
        (
            "optional-child",
            "G",
            readable(
                "ohcell: None",
                "ohcell: Some(Hp { hg: G { a: x, .. }, hn: 0 })",
            ),
        ),
        (
            "optional-child",
            "G",
            readable(
                "ohcell: None",
                "ohcell: Some(Hp { hg: k::fragment![G { a: x, .. }], hn: 0 })",
            ),
        ),
        (
            "optional-child",
            "G",
            cells(
                "ohcell: None",
                "ohcell: Some(k::fragment![crate::Hp { hg: crate::G { a: x, .. }, hn: 0 }])",
            ),
        ),
        (
            "optional-child",
            "G",
            cells(
                "ohcell: None",
                "ohcell: Some(k::fragment![crate::Hp { hg: k::fragment![crate::G { a: x, .. }], hn: 0 }])",
            ),
        ),
        (
            "instance-child",
            "Ag",
            readable(
                "acct: { .. }",
                "acct: { Acct { id: x, aframe: Ag { aa: x, .. } }, .. }",
            ),
        ),
        (
            "instance-child",
            "Ag",
            readable(
                "acct: { .. }",
                "acct: { Acct { id: x, aframe: k::fragment![Ag { aa: x, .. }] }, .. }",
            ),
        ),
        (
            "instance-child",
            "Ag",
            cells(
                "Bank::acct: { instances0 @ .. }",
                "Bank::acct: { k::fragment![crate::Acct { id: x, aframe: crate::Ag { aa: x, .. } }], ..instances0 }",
            ),
        ),
        (
            "instance-child",
            "Ag",
            cells(
                "Bank::acct: { instances0 @ .. }",
                "Bank::acct: { k::fragment![crate::Acct { id: x, aframe: k::fragment![crate::Ag { aa: x, .. }] }], ..instances0 }",
            ),
        ),
    ];
    for (index, (place, group, source)) in refused.into_iter().enumerate() {
        let manifest = library_package(temporary.path(), &format!("created-{index}"), &source);
        let errors = check_errors(target.path(), &manifest);
        assert_eq!(
            errors,
            format!(
                "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::make (rule): the cell term for \"{group}\" (a `k::fragment!` or a group record) must name every child field exactly once; a pattern ends in `..` to leave the others unconstrained, and a result takes them from a matched group with `..base`"
            ),
            "{place} {index}"
        );
    }
}

/// Groups for the record witnesses: `Mg` holds a typed Map child, a group child and a leaf;
/// `stack` is a List leaf, `slot` a `KItem` leaf, `tmem` a typed Map leaf.
const RECORDS: &str = r#"
use k::builtin::{Int, KSequence, List, Map, int, list, map};
use k::{KItem, KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Go, Hold))]
pub enum Cmd {
    #[k::syntax("go")]
    Go(),
    #[k::syntax("hold({s})")]
    Hold { s: Int },
}

#[k::cell]
pub struct Gw {
    #[k::cell]
    pub wa: Int,
    #[k::cell]
    pub wb: Int,
}

#[k::cell]
pub struct Fpu {
    #[k::cell]
    pub fx: Int,
}

#[k::cell]
pub struct Mg {
    #[k::cell]
    pub mm: Map<Int, Int>,
    #[k::cell(nested)]
    pub mg: Gw,
    #[k::cell]
    pub mn: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub stack: List,
    #[k::cell]
    pub slot: KItem,
    #[k::cell]
    pub mem: Map,
    #[k::cell]
    pub tmem: Map<Int, Int>,
    #[k::cell(nested)]
    pub mcell: Mg,
    #[k::cell(nested)]
    pub fpu: Fpu,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt, #[k::config_var(name = "SLOT")] slot: KItem) -> Self {
        Self {
            k: k::k![pgm],
            stack: list::empty(),
            slot,
            mem: map::empty(),
            tmem: map::empty(),
            mcell: Mg { mm: map::empty(), mg: Gw { wa: 0, wb: 0 }, mn: 0 },
            fpu: Fpu { fx: 0 },
        }
    }
}
"#;

/// The readable rule `{ subject } => { result }` over [`RECORDS`].
fn records_rule(subject: &str, result: &str) -> String {
    let command = if result.is_empty() {
        "Go()"
    } else {
        "Hold { s: x }"
    };
    let entry = |entry: &str| {
        if entry.is_empty() {
            String::new()
        } else {
            format!(", {entry}")
        }
    };
    let (subject, result) = (entry(subject), entry(result));
    format!(
        "{RECORDS}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    go: {{ k: [{command}, ..]{subject} }} => {{ k: [..]{result} }};\n}}\n"
    )
}

/// The `cells!` rule matching `subject` over [`RECORDS`].
fn records_cells(subject: &str) -> String {
    format!(
        "{RECORDS}#[k::rule(label = \"go\")]\nfn go(k::cells! {{ k: k::configuration::KCell(Cmd::Go(), tail @ ..), {subject}, state @ .. }}: Machine) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), ..state }}\n}}\n"
    )
}

/// The witnesses [`a_records_mistake_has_one_refusal_on_every_route`] checks: a name, a library,
/// and the spelling its refusal starts at.
fn record_witnesses() -> Vec<(&'static str, String, &'static str)> {
    vec![
        // On a leaf that is no `KItem` the table answers first: a group's cell term is no term of
        // the leaf's sort, whatever its children. A `KItem` leaf holds a cell term, so there the
        // record's map child is the mistake (`leaf-kitem`).
        (
            "leaf-list",
            records_rule("stack: Mg { mm: { 1 -> v, .. }, .. }", ""),
            "Mg {",
        ),
        (
            "leaf-kitem",
            records_rule("slot: Mg { mm: { 1 -> v, .. }, .. }", ""),
            "Mg {",
        ),
        (
            "foreign-cell",
            records_rule("fpu: Gw { wa: 1, .. }", ""),
            "Gw {",
        ),
        (
            "foreign-cell-cells",
            records_cells("fpu: k::fragment![crate::Gw { wa: 1, .. }]"),
            "crate::Gw",
        ),
        (
            "foreign-child",
            records_rule("mcell: Mg { mn: 1, mg: Fpu { fx: 1 }, .. }", ""),
            "Fpu {",
        ),
        (
            "foreign-child-entries",
            records_rule(
                "mcell: Mg { mm: { 1 -> v, .. }, mg: Fpu { fx: 1 }, .. }",
                "",
            ),
            "Fpu {",
        ),
        (
            "foreign-child-cells-entries",
            records_cells(
                "mcell: k::fragment![crate::Mg { mm: k::map![1 -> _, ..], mg: crate::Fpu { fx: 1 }, .. }]",
            ),
            "crate::Fpu",
        ),
        (
            "foreign-child-alias",
            records_rule("mcell: Mg { mg: g @ Fpu { fx: 1 }, .. }", ""),
            "Fpu {",
        ),
        (
            "foreign-child-value",
            records_rule("slot: Mg { mg: Fpu { fx: 1 }, .. }", ""),
            "Fpu {",
        ),
        (
            "no-child-closed",
            records_rule("slot: Mg { mm: m, mg: g, mn: 1, zz: 2 }", ""),
            "zz:",
        ),
        (
            "no-child-before-map",
            records_rule("mcell: Mg { mm: { true -> v, .. }, zz: 1, .. }", ""),
            "zz:",
        ),
        (
            "call-at-typed-map",
            records_rule("", "tmem: int::add(x, 1)"),
            "int::add",
        ),
        (
            "constructor-at-typed-map",
            records_rule("", "tmem: Hold { s: x }"),
            "Hold {",
        ),
    ]
}

/// A record's mistakes each have one refusal, whichever spelling or position reads the record:
/// a record on a leaf is refused at the record (the table's sort refusal on a leaf that is no
/// `KItem`, and on a `KItem` leaf the record's map child, which no term spells); a record of
/// another struct is a term of another cell sort than its cell's, at
/// the cell, at a group child, through an alias, and beside a map child; a field that names no
/// child is told before how many children the record names; and a call of another sort than a
/// typed Map cell's is a term of another sort, not an untyped map.
#[test]
fn a_records_mistake_has_one_refusal_on_every_route() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = record_witnesses();
    let mut outcomes = Vec::new();
    for (name, source, at) in &cases {
        let manifest = library_package(temporary.path(), &format!("records-{name}"), source);
        let error = first_error(target.path(), &manifest);
        let (headline, location) = error.split_once(" @ ").expect("refused");
        let library = fs::read_to_string(manifest.with_file_name("src/lib.rs")).unwrap();
        let (line, column) = location.split_once(':').unwrap();
        let line: usize = line.parse().unwrap();
        let column: usize = column.parse().unwrap();
        let written = &library.lines().nth(line - 1).unwrap()[column - 1..];
        assert!(
            written.starts_with(at),
            "{name}: at `{at}`, found `{written}`:\n{error}"
        );
        outcomes.push(format!("{name}: {headline}"));
    }
    expect_test::expect![[r#"
        [
            "leaf-list: error[krs::analysis::invalid-term]: the cell `stack` holds a `List` leaf, and the entry gives it a `Mg` record, the `Mg` group's cell term, whose sort is not below the leaf's: a group's cell sort is below `KItem` only, so a leaf holds a group's record only where its sort is `KItem`",
            "leaf-kitem: error[krs::analysis::invalid-term]: `slot` is a leaf cell, whose content is a term, and this record writes a child as a map's entries or a map read (`{ k -> v, .. }`, `k::map![..]`), which no term spells, so it is no term: such a child is the entry of its own cell, which only the group's cell holds",
            "foreign-cell: error[krs::analysis::invalid-term]: the record names `Gw`, and `fpu` holds `Fpu`",
            "foreign-cell-cells: error[krs::analysis::invalid-term]: the record names `Gw`, and `fpu` holds `Fpu`",
            "foreign-child: error[krs::analysis::invalid-term]: the record names `Fpu`, and `mg` holds `Gw`",
            "foreign-child-entries: error[krs::analysis::invalid-term]: the record names `Fpu`, and `mg` holds `Gw`",
            "foreign-child-cells-entries: error[krs::analysis::invalid-term]: the record names `Fpu`, and `mg` holds `Gw`",
            "foreign-child-alias: error[krs::analysis::invalid-term]: the record names `Fpu`, and `mg` holds `Gw`",
            "foreign-child-value: error[krs::analysis::invalid-term]: the record names `Fpu`, and `mg` holds `Gw`",
            "no-child-closed: error[krs::analysis::invalid-term]: the group `Mg` has no child `zz`",
            "no-child-before-map: error[krs::analysis::invalid-term]: the group `Mg` has no child `zz`",
            "call-at-typed-map: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::go (rule): application result sort Int is not admissible at sort Map",
            "constructor-at-typed-map: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::go (rule): application result sort ORG-KRS-NESTED::Stmt (sort) is not admissible at sort Map",
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// [`PRESENCES`] without its `KItem` input, so a program runs with no input bound, started with
/// its `?` leaves absent, or with `oo` and `wo` present when `present`.
fn places(present: bool) -> String {
    let base = PRESENCES
        .replace("    #[k::cell]\n    pub slot: k::KItem,\n", "")
        .replace("pgm: Stmt, item: k::KItem", "pgm: Stmt")
        .replace("            slot: item,\n", "");
    if present {
        base.replace("oo: k::absent!(0)", "oo: Some(5)")
            .replace("wo: k::absent!(0)", "wo: Some(6)")
    } else {
        base
    }
}

/// The final configuration of `go`'s run, on one line.
fn run_go(target: &Path, manifest: &Path) -> String {
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "go").unwrap();
    let (success, stdout, stderr) = krs(target, manifest, "run", &[program.to_str().unwrap()]);
    assert!(success, "{stdout}\n{stderr}");
    stdout.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// A `?` leaf child's place holds the cell or its absence (`<oo> 5 </oo>` or `.OoCell`), both
/// values of the cell's generated sort `OoCell`. So a group record that leaves the child out
/// matches it by `_:OoCell` at its place, a base alias's hidden binder there is `OOo:OoCell`,
/// and the update that takes the child from the base writes that binder back: each rule steps
/// whether the child is absent or present, on every route and at every depth, at a configuration
/// position and in a value (`stack`). `<oo> _ </oo>` there matched the present cell only, so
/// every rule below was stuck with `oo` absent. A plain leaf left out stays `<wn> _ </wn>`: its
/// place always holds the cell, which that matches exactly. The print of a rule that leaves the
/// child out re-checks with the same K; a hidden binder at the place has no `k::cells!`
/// spelling, so `krs expand` refuses to print the rule that holds one.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of places and spellings, each run absent and present."
)]
fn a_left_out_optional_leaf_child_is_a_variable_of_its_cell_sort_at_its_place() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = |rules: &str, present: bool| {
        format!(
            "{}k::rules! {{\n    for Machine;\n    use Cmd::*;\n{rules}}}\n",
            places(present)
        )
    };
    let cases = [
        (
            "readable",
            "    go: { k: [Go(), ..], ocell: O { on: x, .. } } => { k: [..] };\n",
            "go",
            r"rule [go]:
    <k> go => .K ... </k>
    <ocell> _:OoCell _:OpCell <on> X:Int </on> </ocell>",
            "<ocell> {oo} .OpCell <on> 0 </on> </ocell>",
        ),
        (
            "depth-2",
            "    go: { k: [Go(), ..], wcell: W { wg: Gw { wa: x, .. }, .. } } => { k: [..] };\n",
            "go",
            r"rule [go]:
    <k> go => .K ... </k>
    <wcell> <wg> _:WoCell <wa> X:Int </wa> </wg> <wn> _ </wn> </wcell>",
            "<wg> {wo} <wa> 0 </wa> </wg>",
        ),
        (
            "alias",
            "    go: { k: [Go(), ..], ocell: o @ O { on: x, .. } } => { k: [..], ocell: O { on: x + 1, ..o } };\n",
            "go",
            r"rule [go]:
    <k> go => .K ... </k>
    (<ocell> OOo:OoCell OOp:OpCell <on> X:Int </on> </ocell> => <ocell> OOo:OoCell OOp:OpCell <on> X:Int +Int 1 </on> </ocell>)",
            "<ocell> {oo} .OpCell <on> 1 </on> </ocell>",
        ),
        (
            "value",
            "    go: { k: [Go(), ..], ocell: o, stack: s } => { k: [Hold { s: 0 }, ..], stack: [o, ..s] };\n    hold: { k: [Hold { s: _ }, ..], stack: [v @ O { on: x, .. }, r @ ..] } => { k: [..], stack: [O { on: x + 1, ..v }, ..r] };\n",
            "hold",
            r"rule [hold]:
    <k> hold ( _ ) => .K ... </k>
    <stack> ListItem(<ocell> VOo:OoCell VOp:OpCell <on> X:Int </on> </ocell>) R:List => ListItem(<ocell> VOo:OoCell VOp:OpCell <on> X:Int +Int 1 </on> </ocell>) R:List </stack>",
            "<stack> ListItem ( <ocell> {oo} .OpCell <on> 1 </on> </ocell> ) </stack>",
        ),
    ];
    for (name, rules, label, expected, after) in cases {
        for present in [false, true] {
            let manifest = library_package(
                temporary.path(),
                &format!("place-{name}-{present}"),
                &readable(rules, present),
            );
            assert_eq!(
                rule(&emitted_k(target.path(), &manifest), label),
                expected,
                "{name} {present}"
            );
            let (oo, wo) = if present {
                ("<oo> 5 </oo>", "<wo> 6 </wo>")
            } else {
                (".OoCell", ".WoCell")
            };
            let run = run_go(target.path(), &manifest);
            let after = after.replace("{oo}", oo).replace("{wo}", wo);
            assert!(
                run.starts_with("<generatedTop> <k> .K </k>") && run.contains(&after),
                "{name} {present}: {run}"
            );
        }
    }

    // The `cells!` twin of the readable rule: the fragment's `..` leaves the children out.
    let cells = format!(
        "{}#[k::rule(label = \"go\")]\nfn go(x: Term<Int>, k::cells! {{ k: k::configuration::KCell(Cmd::Go(), tail @ ..), ocell: k::fragment![crate::O {{ on: x, .. }}], state @ .. }}: Machine) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(x, ..tail), ..state }}\n}}\n",
        places(false)
    );
    let manifest = library_package(temporary.path(), "place-cells", &cells);
    expect_test::expect![[r"
        rule [go]:
            <k> go ~> Tail:K => X:Int ~> Tail:K </k>
            <ocell> _:OoCell _:OpCell <on> X:Int </on> </ocell>"]]
    .assert_eq(rule(&emitted_k(target.path(), &manifest), "go"));
    assert!(run_go(target.path(), &manifest).starts_with("<generatedTop> <k> 0 ~> .K </k>"));

    // The readable rule's print leaves the children out with the fragment's `..` and re-checks
    // with the same K.
    let manifest = library_package(
        temporary.path(),
        "place-printed",
        &readable(
            "    go: { k: [Go(), ..], ocell: O { on: x, .. } } => { k: [..] };\n",
            false,
        ),
    );
    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    assert!(
        expanded
            .split_whitespace()
            .collect::<String>()
            .contains("ocell:k::fragment![crate::O{on:x,..}]"),
        "{expanded}"
    );
    let reprinted = library_package(temporary.path(), "place-reprinted", &expanded);
    assert_eq!(
        rule(&emitted_k(target.path(), &reprinted), "go"),
        rule(&emitted_k(target.path(), &manifest), "go")
    );

    // A hidden binder holds the `?` child whole, present or absent, which no `cells!` entry
    // writes yet: the print is refused, where it printed a bare binder the table refuses.
    let manifest = library_package(
        temporary.path(),
        "place-alias-printed",
        &readable(cases[2].1, false),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(!success);
    expect_test::expect!["error[krs::reference::unsupported-state]: no `k::cells!` entry: a binder that holds a `?` leaf cell or a `*` cell's instances whole, which no `k::cells!` spelling writes yet"]
        .assert_eq(stderr.lines().find(|line| line.starts_with("error")).unwrap());
}

/// [`CREATED`] with a `look` command, its `acct` collection starting with one instance when
/// `initial`.
fn collection_base(initial: bool) -> String {
    let base = CREATED.replace(
        "    #[k::syntax(\"make({x})\")]\n    Make { x: Int },\n",
        "    #[k::syntax(\"make({x})\")]\n    Make { x: Int },\n    #[k::syntax(\"look\")]\n    Look(),\n",
    );
    if initial {
        base.replace(
            "cell_type = \"Map\", nested)]",
            "cell_type = \"Map\", nested, initial)]",
        )
    } else {
        base
    }
}

/// A `*` cell is its parent's only child, and the parent's content is the collection of the
/// cell's instances, `.AcctCellMap` or one `<acct>` or several: values of K's generated sort
/// `AcctCellMap`. So a group record that leaves the `*` child out matches it by a variable of
/// that sort at its place, and a base alias's hidden binder there is `BAcct:AcctCellMap`. Each
/// rule steps with no instance, one and two (`make` creates one first), where the instance's
/// sort `AcctCell` matched exactly one. The left-out child's `_` stays bare in K, the parent's
/// whole content.
#[test]
fn a_left_out_collection_child_is_a_variable_of_its_collection_sort_at_its_place() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "left-out",
            "    look: { k: [Look(), ..], bank: Bank { .. } } => { k: [..] };\n",
            r"rule [look]:
    <k> look => .K ... </k>
    <bank> _ </bank>",
        ),
        (
            "alias",
            "    look: { k: [Look(), ..], bank: b @ Bank { .. } } => { k: [..], bank: Bank { ..b } };\n",
            r"rule [look]:
    <k> look => .K ... </k>
    (<bank> BAcct:AcctCellMap </bank> => <bank> BAcct:AcctCellMap </bank>)",
        ),
    ];
    let instance = |id: u8| {
        format!("<acct> <id> {id} </id> <aframe> <aa> 0 </aa> <ab> 0 </ab> </aframe> </acct>")
    };
    for (name, look, expected) in cases {
        for initial in [false, true] {
            let source = format!(
                "{}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    make: {{ k: [Make {{ x }}, ..], acct: {{ .. }} }} => {{ k: [Look(), ..], acct: {{ Acct {{ id: x, .. }}, .. }} }};\n{look}}}\n",
                collection_base(initial)
            );
            let manifest = library_package(
                temporary.path(),
                &format!("collection-{name}-{initial}"),
                &source,
            );
            assert_eq!(
                rule(&emitted_k(target.path(), &manifest), "look"),
                expected,
                "{name}"
            );
            for (program, instances) in [
                (
                    "look",
                    if initial {
                        instance(0)
                    } else {
                        ".AcctCellMap".to_owned()
                    },
                ),
                (
                    "make(5)",
                    if initial {
                        format!("{} {}", instance(0), instance(5))
                    } else {
                        instance(5)
                    },
                ),
            ] {
                let file = manifest.with_file_name("program.txt");
                fs::write(&file, program).unwrap();
                let (success, stdout, stderr) =
                    krs(target.path(), &manifest, "run", &[file.to_str().unwrap()]);
                assert!(success, "{stdout}\n{stderr}");
                assert_eq!(
                    stdout.split_whitespace().collect::<Vec<_>>().join(" "),
                    format!(
                        "<generatedTop> <k> .K </k> .OgroupCell .OhcellCell <bank> {instances} </bank> </generatedTop>"
                    ),
                    "{name} {initial} {program}"
                );
            }
        }
    }
}

/// Groups for the kept-children witnesses: a plain group, a group holding a group, an optional
/// group and a Map collection whose instances hold a group.
const KEPT: &str = r#"
use k::builtin::{Int, KSequence};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {
    #[k::syntax("make({x})")]
    Make { x: Int },
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub gas: Int,
}

#[k::cell]
pub struct Inner {
    #[k::cell]
    pub x: Int,
    #[k::cell]
    pub y: Int,
}

#[k::cell]
pub struct Outer {
    #[k::cell(nested)]
    pub inner: Inner,
    #[k::cell]
    pub flag: Int,
}

#[k::cell]
pub struct Gp {
    #[k::cell]
    pub pa: Int,
    #[k::cell]
    pub pb: Int,
}

#[k::cell]
pub struct Ag {
    #[k::cell]
    pub aa: Int,
    #[k::cell]
    pub ab: Int,
}

#[k::cell]
pub struct Acct {
    #[k::cell]
    pub id: Int,
    #[k::cell(nested)]
    pub aframe: Ag,
}

#[k::cell]
pub struct Bank {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub acct: Acct,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub frame: Frame,
    #[k::cell(nested)]
    pub outer: Outer,
    #[k::cell(multiplicity = "?", nested)]
    pub ogroup: Option<Gp>,
    #[k::cell(nested)]
    pub bank: Bank,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            frame: Frame { pc: 0, gas: 0 },
            outer: Outer { inner: Inner { x: 0, y: 0 }, flag: 0 },
            ogroup: k::absent!(Gp { pa: 0, pb: 0 }),
            bank: Bank { acct: Acct { id: 0, aframe: Ag { aa: 0, ab: 0 } } },
        }
    }
}
"#;

/// A `KEPT` readable rule (`claim` false) or claim `make` whose subject's and result's records
/// hold `subject` and `result` beside the computation cell.
fn kept_readable(claim: bool, subject: &str, result: &str) -> String {
    let (block, attribute) = if claim {
        ("claims", "#[k::claim(one_path)]\n    ")
    } else {
        ("rules", "")
    };
    let entries = |head: &str, entries: &str| {
        if entries.is_empty() {
            head.to_owned()
        } else {
            format!("{head}, {entries}")
        }
    };
    format!(
        "{KEPT}k::{block}! {{\n    for Machine;\n    use Cmd::*;\n    {attribute}make: {{ {} }} => {{ {} }};\n}}\n",
        entries("k: [Make { x }, ..]", subject),
        entries("k: [..]", result),
    )
}

/// A `KEPT` `cells!` rule `make` whose subject and result hold `subject` and `result` beside the
/// computation cell, with the parameters `parameters` besides `x`.
fn kept_cells(parameters: &str, subject: &str, result: &str) -> String {
    let subject = if subject.is_empty() {
        String::new()
    } else {
        format!("{subject}, ")
    };
    format!(
        "{KEPT}#[k::rule(label = \"make\")]\npub fn make(\n    x: Int,{parameters}\n    k::cells! {{ k: k::configuration::KCell(Cmd::Make {{ x }}, tail @ ..), {subject}state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), {result}, ..state }}\n}}\n"
    )
}

/// The rule or claim `label` that `krs emit-k` writes for the package, on one line.
fn emitted_sentence(target: &Path, manifest: &Path, label: &str) -> String {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let k = ["definition.k", "spec.k"]
        .iter()
        .filter_map(|file| fs::read_to_string(output.join(file)).ok())
        .map(|k| krs_test_support::without_source_comments(&k))
        .collect::<Vec<_>>()
        .join("\n");
    let start = ["rule", "claim"]
        .iter()
        .find_map(|kind| k.find(&format!("{kind} [{label}]:")))
        .unwrap_or_else(|| panic!("`{label}` is emitted:\n{k}"));
    let end = ["rule [", "claim [", "endmodule"]
        .iter()
        .filter_map(|next| k[start + 1..].find(next))
        .min()
        .map_or(k.len(), |end| start + 1 + end);
    k[start..end]
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

/// EDOTS item 1 and WHOLEKEEP: the record a result's entry writes for a group that is there,
/// matched or overwritten, means by its `..` that the children it leaves unnamed are unchanged.
/// Over a subject record of the group's children, `_`, or no match, it writes only the children
/// it names, each as its own cell: `frame: Frame { pc: x, .. }` is `<pc> _ => X </pc>`, `<gas>`
/// as it was. Elsewhere it is the update of the subject's match of the same place, written whole:
/// beside a binder or an alias of the group (`frame: f` is `f @ Frame { .. }`, the result
/// `Frame { pc: x, ..f }`), inside a `?` group's `Some(..)`, and as an updated instance's group
/// child. Readable rules, claims and `cells!` rules agree, and the bare record and its fragment
/// are one record. A group the result creates keeps its own stated limit
/// (`a_record_of_a_group_no_subject_matched_names_every_child`).
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of places and spellings, each with its K or its refusal."
)]
fn a_result_entrys_record_keeps_the_children_its_rest_leaves_unnamed() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let admitted = [
        (
            "matched",
            kept_readable(
                false,
                "frame: Frame { pc: p, .. }",
                "frame: Frame { pc: x, .. }",
            ),
        ),
        (
            "matched-fragment",
            kept_readable(
                false,
                "frame: Frame { pc: p, .. }",
                "frame: k::fragment![Frame { pc: x, .. }]",
            ),
        ),
        (
            "matched-whole",
            kept_readable(
                false,
                "frame: Frame { pc: p, gas: g }",
                "frame: Frame { pc: x, .. }",
            ),
        ),
        (
            "overwritten",
            kept_readable(false, "", "frame: Frame { pc: x, .. }"),
        ),
        (
            "wildcard",
            kept_readable(false, "frame: _", "frame: Frame { pc: x, .. }"),
        ),
        (
            "none-named",
            kept_readable(false, "frame: Frame { pc: p, .. }", "frame: Frame { .. }"),
        ),
        (
            "group-child",
            kept_readable(
                false,
                "outer: Outer { inner: Inner { x: p, .. }, .. }",
                "outer: Outer { inner: Inner { x: x, .. }, flag: 0 }",
            ),
        ),
        (
            "root-and-child",
            kept_readable(
                false,
                "outer: _",
                "outer: Outer { inner: Inner { x: x, .. }, .. }",
            ),
        ),
        (
            "claim-matched",
            kept_readable(
                true,
                "frame: Frame { pc: p, .. }",
                "frame: Frame { pc: x, .. }",
            ),
        ),
        (
            "claim-overwritten",
            kept_readable(true, "", "frame: Frame { pc: x, .. }"),
        ),
        (
            "cells-matched",
            kept_cells(
                " p: Int,",
                "frame: k::fragment![crate::Frame { pc: p, .. }]",
                "frame: k::fragment![crate::Frame { pc: x, .. }]",
            ),
        ),
        (
            "cells-wildcard",
            kept_cells(
                "",
                "frame: _",
                "frame: k::fragment![crate::Frame { pc: x, .. }]",
            ),
        ),
        (
            "cells-group-child",
            kept_cells(
                "",
                "outer: _",
                "outer: k::fragment![crate::Outer { inner: crate::Inner { x: x, .. }, flag: 0 }]",
            ),
        ),
        (
            "binder",
            kept_readable(false, "frame: f", "frame: Frame { pc: x, .. }"),
        ),
        (
            "alias",
            kept_readable(
                false,
                "frame: f @ Frame { pc: p, .. }",
                "frame: Frame { pc: x, .. }",
            ),
        ),
        (
            "child-binder",
            kept_readable(
                false,
                "outer: Outer { inner: i, .. }",
                "outer: Outer { inner: Inner { x: x, .. }, flag: 0 }",
            ),
        ),
        (
            "optional-present",
            kept_readable(
                false,
                "ogroup: Some(Gp { pa: p, .. })",
                "ogroup: Some(Gp { pa: x, .. })",
            ),
        ),
        (
            "cells-optional-present",
            kept_cells(
                " p: Int,",
                "ogroup: Some(k::fragment![crate::Gp { pa: p, .. }])",
                "ogroup: Some(k::fragment![crate::Gp { pa: x, .. }])",
            ),
        ),
        (
            "instance-child",
            kept_readable(
                false,
                "acct: { me @ Acct { id: i, .. }, .. }",
                "acct: { Acct { aframe: Ag { aa: x, .. }, ..me }, .. }",
            ),
        ),
    ]
    .map(|(name, source)| {
        let manifest = library_package(temporary.path(), &format!("kept-{name}"), &source);
        (name, emitted_sentence(target.path(), &manifest, "make"))
    });
    expect_test::expect![[r#"
        [
            (
                "matched",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> <pc> P:Int => X:Int </pc>",
            ),
            (
                "matched-fragment",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> <pc> P:Int => X:Int </pc>",
            ),
            (
                "matched-whole",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> <pc> P:Int => X:Int </pc> <gas> G:Int </gas>",
            ),
            (
                "overwritten",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> <pc> _ => X:Int </pc>",
            ),
            (
                "wildcard",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> <pc> _ => X:Int </pc>",
            ),
            (
                "none-named",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> <pc> P:Int </pc>",
            ),
            (
                "group-child",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> <x> P:Int => X:Int </x> <flag> _ => 0 </flag>",
            ),
            (
                "root-and-child",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> <x> _ => X:Int </x>",
            ),
            (
                "claim-matched",
                "claim [make]: <k> make ( X:Int ) => .K ... </k> <pc> P:Int => X:Int </pc> [one-path]",
            ),
            (
                "claim-overwritten",
                "claim [make]: <k> make ( X:Int ) => .K ... </k> <pc> _ => X:Int </pc> [one-path]",
            ),
            (
                "cells-matched",
                "rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <pc> P:Int => X:Int </pc>",
            ),
            (
                "cells-wildcard",
                "rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <pc> _ => X:Int </pc>",
            ),
            (
                "cells-group-child",
                "rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <x> _ => X:Int </x> <flag> _ => 0 </flag>",
            ),
            (
                "binder",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> (<frame> <pc> _ </pc> <gas> FGas:Int </gas> </frame> => <frame> <pc> X:Int </pc> <gas> FGas:Int </gas> </frame>)",
            ),
            (
                "alias",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> (<frame> <pc> P:Int </pc> <gas> FGas:Int </gas> </frame> => <frame> <pc> X:Int </pc> <gas> FGas:Int </gas> </frame>)",
            ),
            (
                "child-binder",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> (<outer> <inner> <x> _ </x> <y> IY:Int </y> </inner> <flag> _ </flag> </outer> => <outer> <inner> <x> X:Int </x> <y> IY:Int </y> </inner> <flag> 0 </flag> </outer>)",
            ),
            (
                "optional-present",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> (<ogroup> <pa> P:Int </pa> <pb> OgroupPb:Int </pb> </ogroup> => <ogroup> <pa> X:Int </pa> <pb> OgroupPb:Int </pb> </ogroup>)",
            ),
            (
                "cells-optional-present",
                "rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> (<ogroup> <pa> P:Int </pa> <pb> OgroupPb:Int </pb> </ogroup> => <ogroup> <pa> X:Int </pa> <pb> OgroupPb:Int </pb> </ogroup>)",
            ),
            (
                "instance-child",
                "rule [make]: <k> make ( X:Int ) => .K ... </k> <acct> <id> I:Int </id> (<aframe> <aa> _ </aa> <ab> MeAframeAb:Int </ab> </aframe> => <aframe> <aa> X:Int </aa> <ab> MeAframeAb:Int </ab> </aframe>) ... </acct>",
            ),
        ]
    "#]].assert_debug_eq(&admitted);
}

/// A machine for `a_result_s_dots_over_a_whole_match_keep_the_children_it_leaves_unnamed`: fixed
/// groups `frame`, `outer` (with the group child `inner`) and `two` (two group children), and
/// the `?` group `ogroup`, every child starting other than its default; `{RULES}` is the rules.
const KEEPS: &str = r#"
use k::builtin::{Int, KSequence};
use k::KResult;

k::sorts! {
    Stmt;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (B, A, C, R, S, G, T, H) > right seq (Seq))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("b {x}")] B { x: Int },
    #[k::syntax("a {x}")] A { x: Int },
    #[k::syntax("c {x}")] C { x: Int },
    #[k::syntax("r {x}")] R { x: Int },
    #[k::syntax("s {x}")] S { x: Int },
    #[k::syntax("g {x}")] G { x: Int },
    #[k::syntax("t {x}")] T { x: Int },
    #[k::syntax("h {x}")] H { x: Int },
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub gas: Int,
}

#[k::cell]
pub struct Inner {
    #[k::cell]
    pub x: Int,
    #[k::cell]
    pub y: Int,
}

#[k::cell]
pub struct Outer {
    #[k::cell(nested)]
    pub inner: Inner,
    #[k::cell]
    pub flag: Int,
}

#[k::cell]
pub struct Gp {
    #[k::cell]
    pub pa: Int,
    #[k::cell]
    pub pb: Int,
}

#[k::cell]
pub struct Lg {
    #[k::cell]
    pub lv: Int,
    #[k::cell]
    pub lw: Int,
}

#[k::cell]
pub struct Rg {
    #[k::cell]
    pub rv: Int,
    #[k::cell]
    pub rw: Int,
}

#[k::cell]
pub struct Two {
    #[k::cell(nested)]
    pub left: Lg,
    #[k::cell(nested)]
    pub right: Rg,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub frame: Frame,
    #[k::cell(nested)]
    pub outer: Outer,
    #[k::cell(multiplicity = "?", nested)]
    pub ogroup: Option<Gp>,
    #[k::cell(nested)]
    pub two: Two,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            frame: Frame { pc: 1, gas: 7 },
            outer: Outer { inner: Inner { x: 2, y: 9 }, flag: 3 },
            ogroup: Some(Gp { pa: 4, pb: 8 }),
            two: Two { left: Lg { lv: 5, lw: 6 }, right: Rg { rv: 10, rw: 11 } },
        }
    }
}

k::rules! {
    for Stmt;
    use Cmd::*;

    seq: Seq { first, second } => k::k![first, second];
}

{RULES}
"#;

/// WHOLEKEEP cases 1 and 2: a result's record whose `..` leaves children unnamed over a group
/// the subject matches whole, by a binder (`frame: f`, `f @ Frame { .. }`) or an alias, or
/// inside a `?` group's `Some(..)`, is the update of that match: `Frame { pc: x, ..f }`, the
/// children it leaves unnamed as they were. The rule is the one its explicit update writes, the
/// base named as the lowering names it where the author names none (a group child of `o` is
/// `o_inner`, an unnamed `?` group's match `ogroup`), so the two packages' K is one; a group child
/// of a whole match takes its base from that match's same child, two children of one group
/// apart, and a binder that reads like a hidden binder's name (`f_gas`) stays apart from it.
/// `cells!` rules give the same K. Runs over a machine whose children all start off their
/// defaults keep each child no record names.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of places, each with its explicit twin, and the runs."
)]
fn a_result_s_dots_over_a_whole_match_keep_the_children_it_leaves_unnamed() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    // Each rule: its label, its implicit spelling, and its explicit twin.
    let rules = [
        (
            "b",
            "{ k: [B(x), ..], frame: f } => { k: [..], frame: Frame { pc: x, .. } }",
            "{ k: [B(x), ..], frame: f @ Frame { .. } } => { k: [..], frame: Frame { pc: x, ..f } }",
        ),
        (
            "a",
            "{ k: [A(x), ..], frame: f @ Frame { pc: p, .. } } => { k: [..], frame: Frame { pc: x, .. } }",
            "{ k: [A(x), ..], frame: f @ Frame { pc: p, .. } } => { k: [..], frame: Frame { pc: x, ..f } }",
        ),
        (
            "c",
            "{ k: [C(x), ..], outer: Outer { inner: i, .. } } => { k: [..], outer: Outer { inner: Inner { x: x, .. }, flag: 0 } }",
            "{ k: [C(x), ..], outer: Outer { inner: i @ Inner { .. }, .. } } => { k: [..], outer: Outer { inner: Inner { x: x, ..i }, flag: 0 } }",
        ),
        (
            "r",
            "{ k: [R(x), ..], outer: o } => { k: [..], outer: Outer { inner: Inner { x: x, .. }, .. } }",
            "{ k: [R(x), ..], outer: o @ Outer { inner: o_inner @ Inner { .. }, .. } } => { k: [..], outer: Outer { inner: Inner { x: x, ..o_inner }, ..o } }",
        ),
        (
            "s",
            "{ k: [S(x), ..], ogroup: Some(Gp { pa: p, .. }) } => { k: [..], ogroup: Some(Gp { pa: x, .. }) }",
            "{ k: [S(x), ..], ogroup: Some(ogroup @ Gp { pa: p, .. }) } => { k: [..], ogroup: Some(Gp { pa: x, ..ogroup }) }",
        ),
        (
            "g",
            "{ k: [G(x), ..], ogroup: Some(g) } => { k: [..], ogroup: Some(Gp { pa: x, .. }) }",
            "{ k: [G(x), ..], ogroup: Some(g @ Gp { .. }) } => { k: [..], ogroup: Some(Gp { pa: x, ..g }) }",
        ),
        (
            "t",
            "{ k: [T(x), ..], two: t } => { k: [..], two: Two { left: Lg { lv: x, .. }, right: Rg { rv: x, .. } } }",
            "{ k: [T(x), ..], two: t @ Two { left: t_left @ Lg { .. }, right: t_right @ Rg { .. } } } => { k: [..], two: Two { left: Lg { lv: x, ..t_left }, right: Rg { rv: x, ..t_right } } }",
        ),
        (
            "h",
            "{ k: [H(x), ..], frame: f, outer: Outer { flag: f_gas, .. } } => { k: [..], frame: Frame { pc: f_gas, .. }, outer: Outer { flag: x, .. } }",
            "{ k: [H(x), ..], frame: f @ Frame { .. }, outer: Outer { flag: f_gas, .. } } => { k: [..], frame: Frame { pc: f_gas, ..f }, outer: Outer { flag: x, .. } }",
        ),
    ];
    let package = |name: &str, rules: String| {
        library_package(
            temporary.path(),
            name,
            &KEEPS.replace(
                "{RULES}",
                &format!("k::rules! {{\n    for Machine;\n    use Cmd::*;\n\n{rules}}}\n"),
            ),
        )
    };
    let written = |twin: bool| {
        rules
            .iter()
            .map(|(label, implicit, explicit)| {
                format!("    {label}: {};\n", if twin { explicit } else { implicit })
            })
            .collect::<Vec<_>>()
            .concat()
    };
    let implicit = package("keeps-implicit", written(false));
    let explicit = package("keeps-explicit", written(true));
    let [implicit_k, explicit_k] =
        [&implicit, &explicit].map(|manifest| emitted_k(target.path(), manifest));
    let one_line = |k: &str, label: &str| {
        rule(k, label)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    let emitted = rules
        .iter()
        .map(|(label, _, _)| {
            let k = one_line(&implicit_k, label);
            assert_eq!(k, one_line(&explicit_k, label), "{label}");
            k
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "rule [b]: <k> b X:Int => .K ... </k> (<frame> <pc> _ </pc> <gas> FGas:Int </gas> </frame> => <frame> <pc> X:Int </pc> <gas> FGas:Int </gas> </frame>)",
            "rule [a]: <k> a X:Int => .K ... </k> (<frame> <pc> P:Int </pc> <gas> FGas:Int </gas> </frame> => <frame> <pc> X:Int </pc> <gas> FGas:Int </gas> </frame>)",
            "rule [c]: <k> c X:Int => .K ... </k> (<outer> <inner> <x> _ </x> <y> IY:Int </y> </inner> <flag> _ </flag> </outer> => <outer> <inner> <x> X:Int </x> <y> IY:Int </y> </inner> <flag> 0 </flag> </outer>)",
            "rule [r]: <k> r X:Int => .K ... </k> (<outer> <inner> <x> _ </x> <y> OInnerY:Int </y> </inner> <flag> OFlag:Int </flag> </outer> => <outer> <inner> <x> X:Int </x> <y> OInnerY:Int </y> </inner> <flag> OFlag:Int </flag> </outer>)",
            "rule [s]: <k> s X:Int => .K ... </k> (<ogroup> <pa> P:Int </pa> <pb> OgroupPb:Int </pb> </ogroup> => <ogroup> <pa> X:Int </pa> <pb> OgroupPb:Int </pb> </ogroup>)",
            "rule [g]: <k> g X:Int => .K ... </k> (<ogroup> <pa> _ </pa> <pb> GPb:Int </pb> </ogroup> => <ogroup> <pa> X:Int </pa> <pb> GPb:Int </pb> </ogroup>)",
            "rule [t]: <k> t X:Int => .K ... </k> (<two> <left> <lv> _ </lv> <lw> TLeftLw:Int </lw> </left> <right> <rv> _ </rv> <rw> TRightRw:Int </rw> </right> </two> => <two> <left> <lv> X:Int </lv> <lw> TLeftLw:Int </lw> </left> <right> <rv> X:Int </rv> <rw> TRightRw:Int </rw> </right> </two>)",
            "rule [h]: <k> h X:Int => .K ... </k> (<frame> <pc> _ </pc> <gas> FGas1:Int </gas> </frame> => <frame> <pc> FGas:Int </pc> <gas> FGas1:Int </gas> </frame>) <flag> FGas:Int => X:Int </flag>",
        ]
    "#]]
    .assert_debug_eq(&emitted);

    // The `cells!` rules: a binder of the group, a binder of a group child, a `?` group's present
    // record, and a binder of a group with two group children.
    let cells = [
        ("cb", "f: Frame,", "frame: f", "frame: k::fragment![crate::Frame { pc: x, .. }]"),
        (
            "cc",
            "i: Inner,",
            "outer: k::fragment![crate::Outer { inner: i, .. }]",
            "outer: k::fragment![crate::Outer { inner: crate::Inner { x: x, .. }, flag: 0 }]",
        ),
        (
            "cs",
            "p: Int,",
            "ogroup: Some(k::fragment![crate::Gp { pa: p, .. }])",
            "ogroup: Some(k::fragment![crate::Gp { pa: x, .. }])",
        ),
        (
            "ct",
            "t: Two,",
            "two: t",
            "two: k::fragment![crate::Two { left: crate::Lg { lv: x, .. }, right: crate::Rg { rv: x, .. } }]",
        ),
    ]
    .iter()
    .map(|(label, parameters, subject, result)| {
        let command = label[1..].to_uppercase();
        format!(
            "#[k::rule(label = \"{label}\")]\npub fn {label}(\n    x: Int,\n    {parameters}\n    k::cells! {{ k: k::configuration::KCell(Cmd::{command} {{ x }}, tail @ ..), {subject}, state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), {result}, ..state }}\n}}\n"
        )
    })
    .collect::<Vec<_>>()
    .concat();
    let cells_manifest = library_package(
        temporary.path(),
        "keeps-cells",
        &KEEPS.replace("{RULES}", &cells),
    );
    let cells_k = emitted_k(target.path(), &cells_manifest);
    let emitted = ["cb", "cc", "cs", "ct"].map(|label| one_line(&cells_k, label));
    expect_test::expect![[r#"
        [
            "rule [cb]: <k> b X:Int ~> Tail:K => .K ~> Tail:K </k> (<frame> <pc> _ </pc> <gas> FGas:Int </gas> </frame> => <frame> <pc> X:Int </pc> <gas> FGas:Int </gas> </frame>)",
            "rule [cc]: <k> c X:Int ~> Tail:K => .K ~> Tail:K </k> (<outer> <inner> <x> _ </x> <y> IY:Int </y> </inner> <flag> _ </flag> </outer> => <outer> <inner> <x> X:Int </x> <y> IY:Int </y> </inner> <flag> 0 </flag> </outer>)",
            "rule [cs]: <k> s X:Int ~> Tail:K => .K ~> Tail:K </k> (<ogroup> <pa> P:Int </pa> <pb> OgroupPb:Int </pb> </ogroup> => <ogroup> <pa> X:Int </pa> <pb> OgroupPb:Int </pb> </ogroup>)",
            "rule [ct]: <k> t X:Int ~> Tail:K => .K ~> Tail:K </k> (<two> <left> <lv> _ </lv> <lw> TLeftLw:Int </lw> </left> <right> <rv> _ </rv> <rw> TRightRw:Int </rw> </right> </two> => <two> <left> <lv> X:Int </lv> <lw> TLeftLw:Int </lw> </left> <right> <rv> X:Int </rv> <rw> TRightRw:Int </rw> </right> </two>)",
        ]
    "#]]
    .assert_debug_eq(&emitted);

    // Each rule keeps every child its record leaves unnamed: `gas` 7, `y` 9, `pb` 8, `lw` 6 and
    // `rw` 11, as the machine starts.
    let program = implicit.with_file_name("program.txt");
    fs::write(&program, "b 20 c 21 s 22 t 23").unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &implicit,
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{stdout}\n{stderr}");
    expect_test::expect!["<generatedTop> <k> .K </k> <frame> <pc> 20 </pc> <gas> 7 </gas> </frame> <outer> <inner> <x> 21 </x> <y> 9 </y> </inner> <flag> 0 </flag> </outer> <ogroup> <pa> 22 </pa> <pb> 8 </pb> </ogroup> <two> <left> <lv> 23 </lv> <lw> 6 </lw> </left> <right> <rv> 23 </rv> <rw> 11 </rw> </right> </two> </generatedTop>"]
    .assert_eq(&stdout.split_whitespace().collect::<Vec<_>>().join(" "));
    fs::write(
        cells_manifest.with_file_name("program.txt"),
        "b 20 c 21 s 22 t 23",
    )
    .unwrap();
    let program = cells_manifest.with_file_name("program.txt");
    let (success, cells_stdout, stderr) = krs(
        target.path(),
        &cells_manifest,
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{cells_stdout}\n{stderr}");
    assert_eq!(cells_stdout, stdout);
}

/// A machine for `a_result_record_s_map_child_is_the_map_it_builds`: the fixed group `mg` and the
/// `?` group `og`, each a map child beside an `Int` child, and a Map collection of accounts whose
/// group child `aframe` holds a map; `{RULES}` is the rules.
const MAP_CHILDREN: &str = r#"
use k::builtin::{Int, KSequence, Map};
use k::KResult;

k::sorts! {
    Stmt;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (M1, M2, M3, M4, O1, O2, O3, O4, O5, O6, O7, A1, Mk) > right seq (Seq))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("m1 {x}")] M1 { x: Int },
    #[k::syntax("m2 {x}")] M2 { x: Int },
    #[k::syntax("m3 {x}")] M3 { x: Int },
    #[k::syntax("m4 {x}")] M4 { x: Int },
    #[k::syntax("o1 {x}")] O1 { x: Int },
    #[k::syntax("o2 {x}")] O2 { x: Int },
    #[k::syntax("o3 {x}")] O3 { x: Int },
    #[k::syntax("o4 {x}")] O4 { x: Int },
    #[k::syntax("o5 {x}")] O5 { x: Int },
    #[k::syntax("o6 {x}")] O6 { x: Int },
    #[k::syntax("o7 {x}")] O7 { x: Int },
    #[k::syntax("a1 {x}")] A1 { x: Int },
    #[k::syntax("mk")] Mk(),
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::cell]
pub struct Og {
    #[k::cell]
    pub om: Map<Int, Int>,
    #[k::cell]
    pub ov: Int,
}

#[k::cell]
pub struct Mg {
    #[k::cell]
    pub mm: Map<Int, Int>,
    #[k::cell]
    pub mv: Int,
}

#[k::cell]
pub struct M2g {
    #[k::cell]
    pub ma: Map<Int, Int>,
    #[k::cell]
    pub mb: Map<Int, Int>,
    #[k::cell]
    pub mc: Int,
}

#[k::cell]
pub struct Ag {
    #[k::cell]
    pub am: Map<Int, Int>,
    #[k::cell]
    pub aa: Int,
}

#[k::cell]
pub struct Acct {
    #[k::cell]
    pub id: Int,
    #[k::cell(nested)]
    pub aframe: Ag,
}

#[k::cell]
pub struct Bank {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub acct: Acct,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub mg: Mg,
    #[k::cell(multiplicity = "?", nested)]
    pub og: Option<Og>,
    #[k::cell(nested)]
    pub bank: Bank,
    #[k::cell]
    pub slot: k::KItem,
    #[k::cell(multiplicity = "?", nested)]
    pub o2g: Option<M2g>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            o2g: k::absent!(M2g { ma: k::map![], mb: k::map![], mc: 0 }),
            mg: Mg { mm: k::map![1 -> 2], mv: 5 },
            og: Some(Og { om: k::map![1 -> 2], ov: 6 }),
            bank: Bank { acct: Acct { id: 0, aframe: Ag { am: k::map![], aa: 0 } } },
            slot: 0,
        }
    }
}

k::rules! {
    for Stmt;
    use Cmd::*;

    seq: Seq { first, second } => k::k![first, second];
}

k::rules! {
    for Machine;
    use Cmd::*;

    mk: { k: [Mk(), ..], acct: { .. } } => { k: [..], acct: { Acct { id: 0, aframe: Ag { am: k::map![0 -> 3], aa: 1 } }, .. } };
}

{RULES}
"#;

/// WHOLEKEEP round 2: a result record's `..` keeps the children it leaves unnamed where it writes
/// a map child too. A map child's exact entries are the map they build, a term of the child's
/// content, so the record is the update of the subject's match, as it is without the map: a
/// binder of the fixed group `mg` (read elsewhere too) and a `?` group's present match each
/// emit the K a readable record writes for the same rule, and a `cells!` account's group child
/// whose subject reads its map (`k::map![0 -> v, ..]`) keeps that map by an alias of its
/// pattern. A map written over a rest is no term, so a present group's record that writes one
/// stays a stated limit. Runs keep `mv`, `ov` and the account's map.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "Two routes of the same rules, the limit's text, and the runs."
)]
fn a_result_record_s_map_child_is_the_map_it_builds() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = "k::rules! {
    for Machine;
    use Cmd::*;

    m1: { k: [M1(x), ..], mg: m } => { k: [..], mg: Mg { mm: k::map![0 -> x], .. } };
    m2: { k: [M2(x), ..], mg: m, slot: _ } => { k: [..], mg: Mg { mm: k::map![0 -> x], .. }, slot: m };
    o1: { k: [O1(x), ..], og: Some(Og { .. }) } => { k: [..], og: Some(Og { om: k::map![0 -> x], .. }) };
    m3: { k: [M3(x), ..], mg: m } => { k: [..], mg: Mg { mm: k::map![0 -> x], mv: 1 } };
    m4: { k: [M4(x), ..], mg: Mg { mm: { 0 -> v, .. }, mv: w }, slot: n } => { k: [..], mg: n };
}
";
    let cells = r#"
#[k::rule(label = "m1")]
fn m1(x: Int, m: Mg, k::cells! { k: k::configuration::KCell(Cmd::M1 { x }, tail @ ..), mg: m, state @ .. }: Machine) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), mg: k::fragment![crate::Mg { mm: k::map![0 -> x], .. }], ..state }
}

#[k::rule(label = "m2")]
fn m2(x: Int, m: Mg, k::cells! { k: k::configuration::KCell(Cmd::M2 { x }, tail @ ..), mg: m, slot: k::configuration::Cell(_), state @ .. }: Machine) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), mg: k::fragment![crate::Mg { mm: k::map![0 -> x], .. }], slot: k::configuration::Cell(m), ..state }
}

#[k::rule(label = "o1")]
fn o1(x: Int, k::cells! { k: k::configuration::KCell(Cmd::O1 { x }, tail @ ..), og: Some(k::fragment![crate::Og { .. }]), state @ .. }: Machine) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), og: Some(k::fragment![crate::Og { om: k::map![0 -> x], .. }]), ..state }
}

#[k::rule(label = "m3")]
fn m3(x: Int, m: Mg, k::cells! { k: k::configuration::KCell(Cmd::M3 { x }, tail @ ..), mg: m, state @ .. }: Machine) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), mg: k::fragment![crate::Mg { mm: k::map![0 -> x], mv: 1 }], ..state }
}

#[k::rule(label = "m4")]
fn m4(x: Int, v: Int, w: Int, n: Mg, k::cells! { k: k::configuration::KCell(Cmd::M4 { x }, tail @ ..), mg: k::fragment![crate::Mg { mm: k::map![0 -> v, ..], mv: w }], slot: k::configuration::Cell(n), state @ .. }: Machine) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), mg: n, ..state }
}

#[k::rule(label = "o2")]
fn o2(x: Int, v: Int, k::cells! { k: k::configuration::KCell(Cmd::O2 { x }, tail @ ..), og: Some(k::fragment![crate::Og { om: k::map![0 -> v], .. }]), state @ .. }: Machine) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), og: None, ..state }
}

#[k::rule(label = "o3")]
fn o3(x: Int, k::cells! { k: k::configuration::KCell(Cmd::O3 { x }, tail @ ..), og: Some(k::fragment![crate::Og { om: k::map![..], .. }]), state @ .. }: Machine) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), og: None, ..state }
}

#[k::rule(label = "o4")]
fn o4(x: Int, k::cells! { k: k::configuration::KCell(Cmd::O4 { x }, tail @ ..), og: Some(k::fragment![crate::Og { om: k::map![r @ ..], .. }]), state @ .. }: Machine) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), og: Some(k::fragment![crate::Og { om: k::map![..r], ov: x }]), ..state }
}

#[k::rule(label = "o5")]
fn o5(x: Int, v: Int, k::cells! { k: k::configuration::KCell(Cmd::O5 { x }, tail @ ..), og: Some(k::fragment![crate::Og { om: k::map![0 -> v, r @ ..], .. }]), state @ .. }: Machine) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), og: Some(k::fragment![crate::Og { om: k::map![0 -> x, ..r], .. }]), ..state }
}

#[k::rule(label = "o6")]
fn o6(x: Int, v: Int, k::cells! { k: k::configuration::KCell(Cmd::O6 { x }, tail @ ..), og: Some(k::fragment![crate::Og { om: k::map![1 -> v, r @ ..], .. }]), state @ .. }: Machine) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), og: Some(k::fragment![crate::Og { om: k::map![1 -> v, 0 -> x, ..r], .. }]), ..state }
}

#[k::rule(label = "o7")]
fn o7(x: Int, v: Int, w: Int, c: Int, k::cells! { k: k::configuration::KCell(Cmd::O7 { x }, tail @ ..), o2g: Some(k::fragment![crate::M2g { ma: k::map![0 -> v], mb: k::map![1 -> w, r @ ..], mc: c }]), state @ .. }: Machine) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), o2g: Some(k::fragment![crate::M2g { ma: k::map![0 -> x], mb: k::map![1 -> x, ..r], mc: c }]), ..state }
}

#[k::rule(label = "a1")]
fn a1(
    x: Int,
    v: Int,
    k::cells! {
        k: k::configuration::KCell(Cmd::A1 { x }, tail @ ..),
        Bank::acct: { me @ k::fragment![crate::Acct { aframe: crate::Ag { am: k::map![0 -> v, ..], .. }, .. }], instances0 @ .. },
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Bank::acct: { k::fragment![crate::Acct { aframe: crate::Ag { aa: x, .. }, ..me }], ..instances0 },
        ..state
    }
}
"#;
    let [readable, cells] =
        [("map-children", readable), ("map-children-cells", cells)].map(|(name, rules)| {
            library_package(
                temporary.path(),
                name,
                &MAP_CHILDREN.replace("{RULES}", rules),
            )
        });
    let [readable_k, cells_k] =
        [&readable, &cells].map(|manifest| emitted_k(target.path(), manifest));
    // The computation cell aside, each `cells!` rule is its readable twin.
    let without_k = |k: &str, label: &str| {
        let rule = rule(k, label)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        let end = rule.find("</k>").map_or(0, |end| end + "</k>".len());
        rule[end..].trim().to_owned()
    };
    for label in ["m1", "m2", "o1", "m3", "m4"] {
        assert_eq!(
            without_k(&readable_k, label),
            without_k(&cells_k, label),
            "{label}"
        );
    }
    let emitted = [
        "m1", "m2", "o1", "m3", "m4", "o2", "o3", "o4", "o5", "o6", "o7", "a1",
    ]
    .map(|label| without_k(&cells_k, label));
    expect_test::expect![[r#"
        [
            "(<mg> <mm> _ </mm> <mv> MMv:Int </mv> </mg> => <mg> <mm> .Map [ 0 <- X:Int ] </mm> <mv> MMv:Int </mv> </mg>)",
            "(<mg> <mm> MMm:Map </mm> <mv> MMv:Int </mv> </mg> => <mg> <mm> .Map [ 0 <- X:Int ] </mm> <mv> MMv:Int </mv> </mg>) <slot> _ => <mg> <mm> MMm:Map </mm> <mv> MMv:Int </mv> </mg> </slot>",
            "(<og> <om> _ </om> <ov> OgOv:Int </ov> </og> => <og> <om> .Map [ 0 <- X:Int ] </om> <ov> OgOv:Int </ov> </og>)",
            "(M:MgCell => <mg> <mm> .Map [ 0 <- X:Int ] </mm> <mv> 1 </mv> </mg>)",
            "(<mg> <mm> 0 |-> V:Int _ </mm> <mv> W:Int </mv> </mg> => N:MgCell) <slot> N:MgCell </slot>",
            "(<og> <om> 0 |-> V:Int </om> <ov> _ </ov> </og> => .Bag)",
            "(<og> <om> _ </om> <ov> _ </ov> </og> => .Bag)",
            "(<og> <om> R:Map </om> <ov> _ </ov> </og> => <og> <om> R:Map </om> <ov> X:Int </ov> </og>)",
            "(<og> <om> 0 |-> V:Int R:Map </om> <ov> OgOv:Int </ov> </og> => <og> <om> R:Map [ 0 <- X:Int ] </om> <ov> OgOv:Int </ov> </og>)",
            "(<og> <om> 1 |-> V:Int R:Map </om> <ov> OgOv:Int </ov> </og> => <og> <om> R:Map [ 1 <- V:Int ] [ 0 <- X:Int ] </om> <ov> OgOv:Int </ov> </og>)",
            "(<o2g> <ma> 0 |-> V:Int </ma> <mb> 1 |-> W:Int R:Map </mb> <mc> C:Int </mc> </o2g> => <o2g> <ma> .Map [ 0 <- X:Int ] </ma> <mb> R:Map [ 1 <- X:Int ] </mb> <mc> C:Int </mc> </o2g>)",
            "<acct> (<aframe> <am> ( 0 |-> V:Int _ #as MeAframeAm:Map ) </am> <aa> _ </aa> </aframe> => <aframe> <am> MeAframeAm:Map </am> <aa> X:Int </aa> </aframe>) ... </acct>",
        ]
    "#]]
    .assert_debug_eq(&emitted);
    for (manifest, program) in [(&readable, "m1 7 o1 8"), (&cells, "m1 7 o1 8 mk a1 9")] {
        let file = manifest.with_file_name("program.txt");
        fs::write(&file, program).unwrap();
        let (success, stdout, stderr) =
            krs(target.path(), manifest, "run", &[file.to_str().unwrap()]);
        assert!(success, "{stdout}\n{stderr}");
        let end = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(
            end.contains("<mg> <mm> 0 |-> 7 </mm> <mv> 5 </mv> </mg>"),
            "{end}"
        );
        assert!(
            end.contains("<og> <om> 0 |-> 8 </om> <ov> 6 </ov> </og>"),
            "{end}"
        );
        if program.ends_with("a1 9") {
            assert!(end.contains("<am> 0 |-> 3 </am> <aa> 9 </aa>"), "{end}");
        }
    }
    // A result's entries over the rest the subject names are written over it: `o6 3` writes key 0
    // over the rest beside the matched key 1, and `o5 9` writes key 0 again over the rest it leaves,
    // which keeps key 1, and the group's other child.
    let file = cells.with_file_name("program.txt");
    fs::write(&file, "o6 3 o5 9").unwrap();
    let (success, stdout, stderr) = krs(target.path(), &cells, "run", &[file.to_str().unwrap()]);
    assert!(success, "{stdout}\n{stderr}");
    let end = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        end.contains("<og> <om> 0 |-> 9 1 |-> 2 </om> <ov> 6 </ov> </og>"),
        "{end}"
    );
    // A result's map over an anonymous `..` names no map, as on the child's own cell; a map on a
    // child of another sort is the author's mistake.
    let refused = [
        (
            "unnamed-rest",
            "og: Some(k::fragment![crate::Og { om: k::map![0 -> v, ..], .. }])",
            "og: Some(k::fragment![crate::Og { om: k::map![..], ov: 1 }])",
        ),
        (
            "sort",
            "og: Some(k::fragment![crate::Og { .. }])",
            "og: Some(k::fragment![crate::Og { ov: k::map![0 -> x], .. }])",
        ),
    ]
    .map(|(name, subject, result)| {
        let parameters = if subject.contains(" v") { " v: Int," } else { "" };
        let manifest = library_package(
            temporary.path(),
            &format!("map-children-{name}"),
            &MAP_CHILDREN.replace(
                "{RULES}",
                &format!(
                    "#[k::rule(label = \"o9\")]\nfn o9(x: Int,{parameters} k::cells! {{ k: k::configuration::KCell(Cmd::O1 {{ x }}, tail @ ..), {subject}, state @ .. }}: Machine) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), {result}, ..state }}\n}}\n"
                ),
            ),
        );
        (name, check_errors(target.path(), &manifest))
    });
    expect_test::expect![[r#"
        [
            (
                "unnamed-rest",
                "error[krs::syntax::invalid-expression-notation]: in a term, `map![..]` is a literal, and its rest is the map its entries are written over, `map![k -> v, ..m]`; an anonymous `..` names no map. A pattern reads a map's entries with `map![k -> v, ..]`, and a readable record with `{ k -> v, .. }`",
            ),
            (
                "sort",
                "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::o9 (rule): the child `ov` is written as a map's entries, but its sort is not the builtin `Map`: map notation denotes the entries of a cell whose sort is `Map`",
            ),
        ]
    "#]]
    .assert_debug_eq(&refused);
}

/// EDOTS item 2: a readable record's own `..` stands for the cells it does not name, which a
/// subject leaves unconstrained and a result unchanged, as leaving them out already does, so a
/// rule or claim with it is the one without it. A named rest, `rest @ ..` or `..rest`, would
/// name those cells as one value, which they are not; and `..` ends the record.
#[test]
fn a_records_own_rest_is_the_record_without_it() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    for (name, claim, with, without) in [
        (
            "claim-subject",
            true,
            ("frame: Frame { pc: p, .. }, ..", ""),
            ("frame: Frame { pc: p, .. }", ""),
        ),
        (
            "claim-result",
            true,
            ("", "frame: Frame { pc: x, gas: 0 }, .."),
            ("", "frame: Frame { pc: x, gas: 0 }"),
        ),
        (
            "rule-subject",
            false,
            ("frame: Frame { pc: p, .. }, ..", ""),
            ("frame: Frame { pc: p, .. }", ""),
        ),
        (
            "rule-result",
            false,
            ("", "frame: Frame { pc: x, gas: 0 }, .."),
            ("", "frame: Frame { pc: x, gas: 0 }"),
        ),
    ] {
        let [with, without] =
            [("with", with), ("without", without)].map(|(kind, (subject, result))| {
                let manifest = library_package(
                    temporary.path(),
                    &format!("own-rest-{name}-{kind}"),
                    &kept_readable(claim, subject, result),
                );
                emitted_sentence(target.path(), &manifest, "make")
            });
        assert_eq!(with, without, "{name}");
    }
    let refused = [
        ("named-subject", kept_readable(true, "rest @ ..", "")),
        ("named-result", kept_readable(false, "", "..rest")),
        (
            "not-last",
            kept_readable(true, "..,frame: Frame { pc: p, .. }", ""),
        ),
    ]
    .map(|(name, source)| {
        let manifest = library_package(temporary.path(), &format!("own-rest-{name}"), &source);
        (name, first_error(target.path(), &manifest))
    });
    expect_test::expect![[r#"
        [
            (
                "named-subject",
                "error[krs::syntax::rust-syntax]: `rest @ ..` names a record's rest, the cells the record does not name, which a subject leaves unconstrained: it is several cells, and no value a name can stand for; write `..`, or leave it out @ 101:34",
            ),
            (
                "named-result",
                "error[krs::syntax::rust-syntax]: `..rest` puts back a record's rest by name, but a record's rest, the cells the record does not name, is several cells and no value a name can stand for, and a result keeps them unchanged without one; write `..`, or leave it out @ 100:51",
            ),
            (
                "not-last",
                "error[krs::syntax::rust-syntax]: `..` ends a record: it stands for the cells the record does not name, so every cell it names comes before it @ 101:34",
            ),
        ]
    "#]].assert_debug_eq(&refused);
}

/// A machine with a List collection `job` and a Map collection `thread` of `Job` instances, each
/// with a group child `info: Info { mark: ?, level }`, a group `meta: Meta { mmark: ?, mlevel }`
/// beside them, and a plain `List` leaf `stack`.
const INSTANCE_RECORDS: &str = r#"
use k::builtin::{Int, KSequence, List, list};
use k::{KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {
    #[k::syntax("go")]
    Go(),
}

#[k::cell]
pub struct Info {
    #[k::cell(multiplicity = "?")]
    pub mark: Option<Int>,
    #[k::cell]
    pub level: Int,
}

#[k::cell]
pub struct Job {
    #[k::cell]
    pub id: Int,
    #[k::cell(nested)]
    pub info: Info,
}

#[k::cell]
pub struct Jobs {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub job: Job,
}

#[k::cell]
pub struct Threads {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub thread: Job,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub stack: List,
    #[k::cell(nested)]
    pub jobs: Jobs,
    #[k::cell(nested)]
    pub threads: Threads,
    #[k::cell(nested)]
    pub meta: Meta,
}

#[k::cell]
pub struct Meta {
    #[k::cell(multiplicity = "?")]
    pub mmark: Option<Int>,
    #[k::cell]
    pub mlevel: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            stack: list::empty(),
            jobs: Jobs { job: Job { id: 0, info: Info { mark: k::absent!(0), level: 0 } } },
            threads: Threads { thread: Job { id: 0, info: Info { mark: k::absent!(0), level: 0 } } },
            meta: Meta { mmark: k::absent!(0), mlevel: 0 },
        }
    }
}
"#;

/// A `?` cell's `Some(..)` or `None` in a record an instance child writes is the limit
/// `instance-child-multiplicity`, said once the sentence's entries are admitted, as the same
/// record outside an instance waits for them (TABLE follow-up (a)): a clause with another fault
/// gets that fault first, the line the clause gets with the record outside the instance, on the
/// readable braced route and the `cells!` route; alone, the record's presence is the limit at the
/// presence. A readable List collection's brackets are judged alike
/// ([`a_list_collection_s_brackets_are_judged_as_a_map_collection_s_braces`]).
#[test]
fn a_presence_in_an_instance_child_s_record_waits_for_the_entries_as_outside_an_instance() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = |subject: &str| {
        format!(
            "{INSTANCE_RECORDS}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    go: {{ k: [Go(), ..], {subject} }} => {{ k: [..] }};\n}}\n"
        )
    };
    let cells = |subject: &str| {
        format!(
            "{INSTANCE_RECORDS}#[k::rule(label = \"go\")]\nfn go(s: Term<List>, k::cells! {{ k: k::configuration::KCell(Cmd::Go(), tail @ ..), {subject}, state @ .. }}: Machine) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), ..state }}\n}}\n"
        )
    };
    let twins = [
        (
            "readable",
            readable(
                "thread: { Job { info: Info { mark: Some(1), .. }, .. }, .. }, stack: Some(s)",
            ),
            readable("meta: Meta { mmark: Some(1), .. }, stack: Some(s)"),
            "Some(s)",
        ),
        (
            "cells",
            cells(
                "Jobs::job: [k::fragment![crate::Job { info: crate::Info { mark: Some(1), .. }, .. }], rest @ ..], stack: Some(k::configuration::Cell(s))",
            ),
            cells(
                "meta: k::fragment![crate::Meta { mmark: Some(1), .. }], stack: Some(k::configuration::Cell(s))",
            ),
            "Some(k::configuration::Cell(s))",
        ),
    ];
    let mut lines = Vec::new();
    for (route, inside, outside, at) in twins {
        let mut headlines = Vec::new();
        for (place, source) in [("inside", inside), ("outside", outside)] {
            let manifest = library_package(
                temporary.path(),
                &format!("instance-record-{route}-{place}"),
                &source,
            );
            let error = first_error(target.path(), &manifest);
            let (headline, located) = error.split_once(" @ ").expect("refused");
            assert_eq!(located, location(&manifest, at), "{route} {place}: {error}");
            headlines.push(headline.to_owned());
        }
        assert_eq!(
            headlines[0], headlines[1],
            "{route}: inside an instance as outside"
        );
        lines.push(format!("{route}: {}", headlines[0]));
    }
    let alone = readable("thread: { Job { info: Info { mark: Some(1), .. }, .. }, .. }");
    let manifest = library_package(temporary.path(), "instance-record-alone", &alone);
    let error = first_error(target.path(), &manifest);
    let (headline, located) = error.split_once(" @ ").expect("refused");
    assert_eq!(
        located,
        location(&manifest, "Some(1), .. }, .. }, .. }"),
        "{error}"
    );
    lines.push(format!("alone: {headline}"));
    expect_test::expect![[r#"
        [
            "readable: error[krs::analysis::optional-presence]: the cell `stack` holds a `List` leaf and is not optional (it is declared without `multiplicity = \"?\"`), so it is always there: `Some(..)` and `None` are the presence of an optional cell, which `stack` has none of",
            "cells: error[krs::analysis::optional-presence]: the cell `stack` holds a `List` leaf and is not optional (it is declared without `multiplicity = \"?\"`), so it is always there: `Some(..)` and `None` are the presence of an optional cell, which `stack` has none of",
            "alone: error[krs::analysis::collection-entry]: the cell `mark`, inside the instance child `info`, holds `Some(..)`, a `?` cell's presence: an instance record does not name a `?` or `*` child yet",
        ]
    "#]].assert_debug_eq(&lines);
}

/// The configuration of the BRACKETS witness: a `*` collection `job` of `Job` records, a List
/// collection or a Map collection by `CELL_TYPE`, beside a list leaf `stack`.
const COLLECTION_TWINS: &str = r#"
use k::builtin::{Int, KSequence, List, list};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {
    #[k::syntax("go")]
    Go(),
}

#[k::cell]
pub struct Info {
    #[k::cell(multiplicity = "?")]
    pub mark: Option<Int>,
    #[k::cell]
    pub level: Int,
}

#[k::cell]
pub struct Job {
    #[k::cell]
    pub id: Int,
    #[k::cell(nested)]
    pub info: Info,
    #[k::cell]
    pub tk: KSequence,
    #[k::cell]
    pub n: Int,
}

#[k::cell]
pub struct Jobs {
    #[k::cell(multiplicity = "*", cell_type = "CELL_TYPE", nested)]
    pub job: Job,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub stack: List,
    #[k::cell(nested)]
    pub jobs: Jobs,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            stack: list::empty(),
            jobs: Jobs { job: Job { id: 0, info: Info { mark: k::absent!(0), level: 0 }, tk: k::k![], n: 0 } },
        }
    }
}
"#;

/// The rows of [`a_list_collection_s_brackets_are_judged_as_a_map_collection_s_braces`]: a
/// subject entry and a result suffix, `«`/`»` standing for the collection's delimiters, and
/// whether the row is also asked beside another cell's fault, and in a claim.
const COLLECTION_TWIN_ROWS: [(&str, &str, bool, bool); 11] = [
    (
        "job: «Job { info: Info { mark: None, .. }, .. }, ..»",
        "",
        true,
        true,
    ),
    (
        "job: «Job { tk: k::k![Go(), ..], .. }, ..»",
        "",
        false,
        false,
    ),
    ("job: «Job { n: k::k![1], .. }, ..»", "", true, true),
    ("job: «Job { n: Go(), .. }, ..»", "", false, false),
    ("job: «Job { n: x, .. }, ..»", "", false, false),
    (
        "job: «me @ Job { .. }, ..»",
        ", job: «Job { info: Info { mark: Some(1), level: 0 }, ..me }, ..»",
        false,
        true,
    ),
    (
        "job: «me @ Job { .. }, ..»",
        ", job: «Job { tk: k::k![Go()], ..me }, ..»",
        false,
        false,
    ),
    (
        "job: «me @ Job { .. }, ..»",
        ", job: «Job { n: k::k![1], ..me }, ..»",
        false,
        false,
    ),
    (
        "job: «me @ Job { .. }, ..»",
        ", job: «Job { n: 1, ..me }, ..»",
        false,
        false,
    ),
    (
        "job: «me @ Job { tk: [y, ..], n: x, .. }, ..»",
        ", job: «Job { tk: [x, ..], ..me }, ..»",
        false,
        true,
    ),
    ("job: «Job { tk: [y, ..], .. }, ..»", "", false, true),
];

/// The readable rule `go` (or, with `claim`, the claim `c`) over [`COLLECTION_TWINS`] whose
/// subject and result records hold `subject` and `result`.
fn collection_twin_block(subject: &str, result: &str, claim: bool) -> String {
    if claim {
        format!(
            "k::claims! {{\n    for Machine;\n    use Cmd::*;\n    #[k::claim(all_paths)]\n    c: {{ k: [Go()], {subject} }} => {{ k: []{result} }};\n}}\n"
        )
    } else {
        format!(
            "k::rules! {{\n    for Machine;\n    use Cmd::*;\n    go: {{ k: [Go(), ..], {subject} }} => {{ k: [..]{result} }};\n}}\n"
        )
    }
}

/// `krs check`'s first error for `block` over [`COLLECTION_TWINS`] whose `job` is a `cell_type`
/// collection, `«`/`»` written `open`/`close`, or `passed:` and the sentence `label` it emits.
fn collection_twin(
    target: &Path,
    root: &Path,
    name: &str,
    (cell_type, open, close): (&str, &str, &str),
    block: &str,
    label: &str,
) -> String {
    let library = format!(
        "{}{}",
        COLLECTION_TWINS.replace("CELL_TYPE", cell_type),
        block.replace('«', open).replace('»', close)
    );
    let manifest = library_package(root, &format!("{name}-{cell_type}"), &library);
    let line = first_error(target, &manifest);
    if line.starts_with("passed") {
        return format!("passed: {}", emitted_sentence(target, &manifest, label));
    }
    line
}

/// A readable `*` collection's instance records stand in braces, and a List collection's in
/// brackets, which the syntax also reads as a list's elements and the computation's items: only
/// the cell's declaration says which, so each reading is read and the collector judges the one
/// it selects. A List collection's bracketed record is judged as the same record in a Map
/// collection's braces: the same line, at the same place, for a rule and a claim, alone and
/// beside another cell's fault, or both admitted. A presence in an instance child's group record
/// is the entry's (P5, P6), a `k::k![..]` child is judged by the child's sort, a computation
/// child's brackets are its items, each a `KItem` (`tk: [y, ..]` binds `Y:KItem`), whose result
/// `..` keeps the subject's rest, and a clause with another fault gets that fault first; an
/// admitted pair emits the same instance. On a list leaf the same brackets are a list's elements,
/// terms: a record element's presence is the group record child's limit, and a `k::k![..]` in it
/// the term reader's refusal.
#[test]
fn a_list_collection_s_brackets_are_judged_as_a_map_collection_s_braces() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let mut lines = Vec::new();
    for (index, (subject, result, beside, claimed)) in COLLECTION_TWIN_ROWS.into_iter().enumerate()
    {
        let mut forms = vec![("rule", subject.to_owned(), false)];
        if beside {
            forms.push(("rule+", format!("{subject}, stack: Some(s)"), false));
        }
        if claimed {
            forms.push(("claim", subject.to_owned(), true));
        }
        for (form, subject, claim) in forms {
            let block = collection_twin_block(&subject, result, claim);
            let name = format!("brackets-{index}-{}", form.replace('+', "o"));
            let label = if claim { "c" } else { "go" };
            let twin = |delimiters| {
                collection_twin(
                    target.path(),
                    temporary.path(),
                    &name,
                    delimiters,
                    &block,
                    label,
                )
            };
            let bracketed = twin(("List", "[", "]"));
            let braced = twin(("Map", "{", "}"));
            if braced.starts_with("passed") {
                // A List and a Map collection lay their instances out alike; each instance is
                // the same cells.
                let instance = |line: &str| {
                    line.split_once("<job>")
                        .and_then(|(_, rest)| rest.split_once("</job>"))
                        .map(|(instance, _)| instance.to_owned())
                };
                assert_eq!(
                    instance(&bracketed),
                    instance(&braced),
                    "{form} {subject}{result}: {bracketed} | {braced}"
                );
                assert!(instance(&bracketed).is_some(), "{bracketed}");
            } else {
                assert_eq!(bracketed, braced, "{form} {subject}{result}");
            }
            let written = format!("{subject}{result}")
                .replace('«', "[")
                .replace('»', "]");
            lines.push(format!("{form} {written}: {bracketed}"));
        }
    }
    for (index, (subject, result)) in [
        ("stack: [Info { mark: None, .. }, ..]", ""),
        (
            "stack: [Info { level: 1, .. }, ..]",
            ", stack: [Info { mark: None, level: 1 }, ..]",
        ),
        ("stack: [Info { level: k::k![1], .. }, ..]", ""),
    ]
    .into_iter()
    .enumerate()
    {
        let block = collection_twin_block(subject, result, false);
        let name = format!("brackets-leaf-{index}");
        let line = collection_twin(
            target.path(),
            temporary.path(),
            &name,
            ("List", "[", "]"),
            &block,
            "go",
        );
        lines.push(format!("leaf {subject}{result}: {line}"));
    }
    expect_test::expect![[r#"
        [
            "rule job: [Job { info: Info { mark: None, .. }, .. }, ..]: error[krs::analysis::optional-presence]: the subject tests that the optional cell `mark` is absent (`None`), and the result does not create it: K tests a cell's absence only by creating the cell, so a subject's `None` stands where its result creates it with `Some(..)` @ 66:57",
            "rule+ job: [Job { info: Info { mark: None, .. }, .. }, ..], stack: Some(s): error[krs::analysis::optional-presence]: the cell `stack` holds a `List` leaf and is not optional (it is declared without `multiplicity = \"?\"`), so it is always there: `Some(..)` and `None` are the presence of an optional cell, which `stack` has none of @ 66:87",
            "claim job: [Job { info: Info { mark: None, .. }, .. }, ..]: error[krs::analysis::optional-presence]: the subject tests that the optional cell `mark` is absent (`None`), and the result does not create it: K tests a cell's absence only by creating the cell, so a subject's `None` stands where its result creates it with `Some(..)` @ 67:52",
            "rule job: [Job { tk: k::k![Go(), ..], .. }, ..]: passed: rule [go]: <k> go => .K ... </k> <jobs> <job> <tk> go ~> Tail0:K </tk> ... </job> ... </jobs>",
            "rule job: [Job { n: k::k![1], .. }, ..]: error[krs::analysis::invalid-term]: the cell `n` holds a leaf of sort `Int`, and the entry gives it `k::k![..]`, the computation's item notation, a term of sort `K` (its items in order), whose sort is not below the leaf's @ 66:41",
            "rule+ job: [Job { n: k::k![1], .. }, ..], stack: Some(s): error[krs::analysis::optional-presence]: the cell `stack` holds a `List` leaf and is not optional (it is declared without `multiplicity = \"?\"`), so it is always there: `Some(..)` and `None` are the presence of an optional cell, which `stack` has none of @ 66:69",
            "claim job: [Job { n: k::k![1], .. }, ..]: error[krs::analysis::invalid-term]: the cell `n` holds a leaf of sort `Int`, and the entry gives it `k::k![..]`, the computation's item notation, a term of sort `K` (its items in order), whose sort is not below the leaf's @ 67:36",
            "rule job: [Job { n: Go(), .. }, ..]: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::go (rule): application result sort ORG-KRS-NESTED::Stmt (sort) is not admissible at sort Int @ 66:41",
            "rule job: [Job { n: x, .. }, ..]: passed: rule [go]: <k> go => .K ... </k> <jobs> <job> <n> X:Int </n> ... </job> ... </jobs>",
            "rule job: [me @ Job { .. }, ..], job: [Job { info: Info { mark: Some(1), level: 0 }, ..me }, ..]: error[krs::analysis::optional-presence]: the result writes the optional cell `mark`, which the subject does not match, so the rule does not know whether the cell is there: the subject matches it with `Some(..)` or `None` first @ 66:100",
            "claim job: [me @ Job { .. }, ..], job: [Job { info: Info { mark: Some(1), level: 0 }, ..me }, ..]: error[krs::analysis::optional-presence]: the result writes the optional cell `mark`, which the subject does not match, so the rule does not know whether the cell is there: the subject matches it with `Some(..)` or `None` first @ 67:93",
            "rule job: [me @ Job { .. }, ..], job: [Job { tk: k::k![Go()], ..me }, ..]: error[krs::analysis::continuation-in-readable]: the readable entry of the computation cell `tk` captures or drops its continuation (with a named rest, a splice, a whole binder, or a result without the subject's `..`): a readable rule keeps the rest of the computation with its anonymous `..`, and a `cells!` rule's `KCell(.., rest @ ..)` is what captures it @ 66:85",
            "rule job: [me @ Job { .. }, ..], job: [Job { n: k::k![1], ..me }, ..]: error[krs::analysis::invalid-term]: the cell `n` holds a leaf of sort `Int`, and the entry gives it `k::k![..]`, the computation's item notation, a term of sort `K` (its items in order), whose sort is not below the leaf's @ 66:84",
            "rule job: [me @ Job { .. }, ..], job: [Job { n: 1, ..me }, ..]: passed: rule [go]: <k> go => .K ... </k> <jobs> <job> <n> _ => 1 </n> ... </job> ... </jobs>",
            "rule job: [me @ Job { tk: [y, ..], n: x, .. }, ..], job: [Job { tk: [x, ..], ..me }, ..]: passed: rule [go]: <k> go => .K ... </k> <jobs> <job> <tk> Y:KItem ~> Tail0:K => X:Int ~> Tail0:K </tk> <n> X:Int </n> ... </job> ... </jobs>",
            "claim job: [me @ Job { tk: [y, ..], n: x, .. }, ..], job: [Job { tk: [x, ..], ..me }, ..]: passed: claim [c]: <k> go => .K </k> <jobs> <job> <tk> Y:KItem ~> Tail0:K => X:Int ~> Tail0:K </tk> <n> X:Int </n> ... </job> ... </jobs>",
            "rule job: [Job { tk: [y, ..], .. }, ..]: passed: rule [go]: <k> go => .K ... </k> <jobs> <job> <tk> Y:KItem ~> Tail0:K </tk> ... </job> ... </jobs>",
            "claim job: [Job { tk: [y, ..], .. }, ..]: passed: claim [c]: <k> go => .K </k> <jobs> <job> <tk> Y:KItem ~> Tail0:K </tk> ... </job> ... </jobs>",
            "leaf stack: [Info { mark: None, .. }, ..]: error[krs::analysis::collection-entry]: the record's field `mark` holds `None`, a `?` cell's absence, and no term: KRS has no `Option` term; in a group record it is the `?` child's entry, which a group record does not name yet, as an instance record does not name a `?` or `*` child yet @ 66:47",
            "leaf stack: [Info { level: 1, .. }, ..], stack: [Info { mark: None, level: 1 }, ..]: error[krs::analysis::collection-entry]: the record's field `mark` holds `None`, a `?` cell's absence, and no term: KRS has no `Option` term; in a group record it is the `?` child's entry, which a group record does not name yet, as an instance record does not name a `?` or `*` child yet @ 66:98",
            "leaf stack: [Info { level: k::k![1], .. }, ..]: error[krs::syntax::unsupported-term-expression]: unsupported term expression: macros are not terms unless they are compiler-owned `fragment!`, `id!`, `bytes!`, `anonymous!`, `lexeme!`, `is!`, `project!`, `matches!`, `or_bool!`, or `rewrite!` islands @ 66:48",
        ]
    "#]].assert_debug_eq(&lines);
}

/// The configuration of the CELLSX witnesses, `{CONTEXT_ALIAS}` standing for the context alias
/// `ca` its strict production evaluates through.
const WHOLE: &str = r#"
use k::builtin::{Int, KSequence};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {
    #[k::syntax("make({x})")]
    Make { x: Int },
    #[k::syntax("twice({e})")]
    #[k::strict(using = ca)]
    Twice { e: Stmt },
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub gas: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Int,
    #[k::cell(nested)]
    pub frame: Frame,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm], acc: 0, frame: Frame { pc: 0, gas: 0 } }
    }
}

#[k::context_alias(name = ca, here = site)]
fn ca(
    k::cells! { CONTEXT_ALIAS }: Machine,
) {
}
"#;

/// The context alias pattern `WHOLE` holds unless a row writes its own.
const WHOLE_ALIAS: &str = "k: k::configuration::KCell(site, tail @ ..), state @ ..";

/// A `WHOLE` `cells!` rule (`claim` false) or claim `make` over the binders `x: Int` and
/// `a: Int` and those of `parameters`, whose subject and result are `subject` and `result`
/// after the computation cell's entry (`KCell(Make { x }, tail @ ..)` and `KCell(..tail)`).
fn whole_cells(claim: bool, parameters: &str, subject: &str, result: &str) -> String {
    let attribute = if claim {
        "#[k::claim(one_path, label = \"make\")]"
    } else {
        "#[k::rule(label = \"make\")]"
    };
    format!(
        "{}{attribute}\npub fn make(\n    x: Int,\n    a: Int,{parameters}\n    k::cells! {{ k: k::configuration::KCell(Cmd::Make {{ x }}, tail @ ..), {subject} }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), {result} }}\n}}\n",
        WHOLE.replace("CONTEXT_ALIAS", WHOLE_ALIAS)
    )
}

/// CELLSX: a `cells!` record without a rest is the whole state. Naming every cell of the
/// configuration, as a group (`frame: _`) or through its children (`Frame::pc`, `Frame::gas`),
/// it is the rule or claim with every cell, admitted. A subject's named rest `state @ ..` whose
/// result does not put it back keeps the cells the result does not name, as any `cells!` result
/// does: the rule is the one with `..state`.
#[test]
fn a_cells_record_without_a_rest_names_every_cell() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let emitted = |name: &str, source: &str| {
        let manifest = library_package(temporary.path(), &format!("whole-{name}"), source);
        emitted_sentence(target.path(), &manifest, "make")
    };
    let all = "acc: k::configuration::Cell(a), frame: _";
    let written =
        "acc: k::configuration::Cell(x), frame: k::fragment![crate::Frame { pc: x, gas: 0 }]";
    let leaves = "acc: k::configuration::Cell(a), crate::Frame::pc: k::configuration::Cell(p), crate::Frame::gas: k::configuration::Cell(g)";
    let admitted = [
        ("rule-every-cell", whole_cells(false, "", all, written)),
        ("claim-every-cell", whole_cells(true, "", all, written)),
        (
            "rule-every-leaf",
            whole_cells(
                false,
                "\n    p: Int,\n    g: Int,",
                leaves,
                "acc: k::configuration::Cell(x)",
            ),
        ),
        (
            "rule-named-rest-result-every-cell",
            whole_cells(
                false,
                "",
                "acc: k::configuration::Cell(a), state @ ..",
                written,
            ),
        ),
    ]
    .map(|(name, source)| (name, emitted(name, &source)));
    expect_test::expect![[r#"
        [
            (
                "rule-every-cell",
                "rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> (_:FrameCell => <frame> <pc> X:Int </pc> <gas> 0 </gas> </frame>)",
            ),
            (
                "claim-every-cell",
                "claim [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> (_:FrameCell => <frame> <pc> X:Int </pc> <gas> 0 </gas> </frame>) [one-path]",
            ),
            (
                "rule-every-leaf",
                "rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> <pc> P:Int </pc> <gas> G:Int </gas>",
            ),
            (
                "rule-named-rest-result-every-cell",
                "rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> (_:FrameCell => <frame> <pc> X:Int </pc> <gas> 0 </gas> </frame>)",
            ),
        ]
    "#]]
    .assert_debug_eq(&admitted);
    // The readable twin names the same cells; a readable record leaves none out by its form.
    let readable = format!(
        "{}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    make: {{ k: [Make {{ x }}, ..], acc: a, frame: _ }} => {{ k: [..], acc: x, frame: Frame {{ pc: x, gas: 0 }} }};\n}}\n",
        WHOLE.replace("CONTEXT_ALIAS", WHOLE_ALIAS)
    );
    expect_test::expect![[r#"
        "rule [make]: <k> make ( X:Int ) => .K ... </k> <acc> A:Int => X:Int </acc> (_:FrameCell => <frame> <pc> X:Int </pc> <gas> 0 </gas> </frame>)"
    "#]]
    .assert_debug_eq(&emitted("readable-every-cell", &readable));
    // A named rest the result does not put back is the rest put back.
    for claim in [false, true] {
        let subject = "acc: k::configuration::Cell(a), state @ ..";
        let [without, with] = [
            ("without", "acc: k::configuration::Cell(x)"),
            ("with", "acc: k::configuration::Cell(x), ..state"),
        ]
        .map(|(kind, result)| {
            emitted(
                &format!("named-rest-{claim}-{kind}"),
                &whole_cells(claim, "", subject, result),
            )
        });
        assert_eq!(without, with, "claim: {claim}");
    }
}

/// CELLS3 item 1: a `cells!` subject without a rest is judged by the cells its author names. A
/// group named whole, by `_` or by a record of its children, is named, whatever the result writes
/// there: beside a result record that writes `pc` and keeps the other children, the rule is the
/// one with the subject's `..`, `<pc> _ => X </pc>`. A subject that leaves a cell out is refused
/// whether or not the result writes that cell: the result writes over the cell, and the subject
/// still describes no configuration.
#[test]
fn an_exact_cells_subject_is_judged_by_the_cells_its_author_names() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let emitted = |name: &str, source: &str| {
        let manifest = library_package(temporary.path(), &format!("authored-{name}"), source);
        emitted_sentence(target.path(), &manifest, "make")
    };
    let open = "acc: k::configuration::Cell(x), frame: k::fragment![crate::Frame { pc: x, .. }]";
    let open_rest = format!("{open}, ..");
    let wildcard = "acc: k::configuration::Cell(a), frame: _";
    let record = "acc: k::configuration::Cell(a), frame: k::fragment![crate::Frame { .. }]";
    let mut admitted = Vec::new();
    for claim in [false, true] {
        let form = if claim { "claim" } else { "rule" };
        let rest = emitted(
            &format!("{form}-rest"),
            &whole_cells(claim, "", "acc: k::configuration::Cell(a), ..", open),
        );
        for (name, subject, result) in [
            ("wildcard", wildcard, open),
            ("record", record, open),
            ("result-rest", wildcard, open_rest.as_str()),
        ] {
            let sentence = emitted(
                &format!("{form}-{name}"),
                &whole_cells(claim, "", subject, result),
            );
            assert_eq!(sentence, rest, "{form}-{name}");
        }
        admitted.push(rest);
        admitted.push(emitted(
            &format!("{form}-record-read"),
            &whole_cells(
                claim,
                "\n    p: Int,",
                "acc: k::configuration::Cell(a), frame: k::fragment![crate::Frame { pc: p, .. }]",
                open,
            ),
        ));
    }
    expect_test::expect![[r#"
        [
            "rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> <pc> _ => X:Int </pc>",
            "rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> <pc> P:Int => X:Int </pc>",
            "claim [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> <pc> _ => X:Int </pc> [one-path]",
            "claim [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> <pc> P:Int => X:Int </pc> [one-path]",
        ]
    "#]].assert_debug_eq(&admitted);
    let readable = format!(
        "{}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    make: {{ k: [Make {{ x }}, ..], acc: a, frame: _ }} => {{ k: [..], acc: x, frame: Frame {{ pc: x, .. }} }};\n}}\n",
        WHOLE.replace("CONTEXT_ALIAS", WHOLE_ALIAS)
    );
    expect_test::expect![[r#"
        "rule [make]: <k> make ( X:Int ) => .K ... </k> <acc> A:Int => X:Int </acc> <pc> _ => X:Int </pc>"
    "#]].assert_debug_eq(&emitted("readable", &readable));
    let refused = [
        (
            "acc-written",
            whole_cells(
                false,
                "",
                "frame: k::fragment![crate::Frame { pc: a, .. }]",
                "acc: k::configuration::Cell(x)",
            ),
        ),
        (
            "frame-written",
            whole_cells(
                true,
                "",
                "acc: k::configuration::Cell(a)",
                "acc: k::configuration::Cell(x), frame: k::fragment![crate::Frame { pc: x, gas: 0 }]",
            ),
        ),
        (
            "frame-written-open",
            whole_cells(false, "", "acc: k::configuration::Cell(a)", open),
        ),
    ]
    .map(|(name, source)| {
        let manifest = library_package(temporary.path(), &format!("authored-{name}"), &source);
        (name, first_error(target.path(), &manifest))
    });
    expect_test::expect![[r#"
        [
            (
                "acc-written",
                "error[krs::analysis::record-missing-children]: the `cells!` subject has no `..` and leaves out `acc`: a `cells!` record without `..` is the whole state, so it names every cell of its configuration, as a Rust struct pattern without `..` names every field; name it, or end the record with `..` to leave it unconstrained @ 54:5",
            ),
            (
                "frame-written",
                "error[krs::analysis::record-missing-children]: the `cells!` subject has no `..` and leaves out `frame`: a `cells!` record without `..` is the whole state, so it names every cell of its configuration, as a Rust struct pattern without `..` names every field; name it, or end the record with `..` to leave it unconstrained @ 54:5",
            ),
            (
                "frame-written-open",
                "error[krs::analysis::record-missing-children]: the `cells!` subject has no `..` and leaves out `frame`: a `cells!` record without `..` is the whole state, so it names every cell of its configuration, as a Rust struct pattern without `..` names every field; name it, or end the record with `..` to leave it unconstrained @ 54:5",
            ),
        ]
    "#]].assert_debug_eq(&refused);
}

/// A `WHOLE` `cells!` rule (`claim` false) or claim `make` over `x: Int` and `a: Int` whose
/// subject is `subject` and whose result's payload is `result`, as written.
fn whole_payloads(claim: bool, subject: &str, result: &str) -> String {
    let attribute = if claim {
        "#[k::claim(one_path, label = \"make\")]"
    } else {
        "#[k::rule(label = \"make\")]"
    };
    format!(
        "{}{attribute}\npub fn make(\n    x: Int,\n    a: Int,\n    k::cells! {{ {subject} }}: Machine,\n) -> Machine {{\n    k::cells! {{ {result} }}\n}}\n",
        WHOLE.replace("CONTEXT_ALIAS", WHOLE_ALIAS)
    )
}

/// CELLS3 item 2: a `cells!` result that names no cell, `cells! {}` or `cells! { .. }`, leaves
/// every cell as it is, which is what `..state` says: a claim is the claim with `..state`, and a
/// rule changes no cell, refused as the `..state` twin is, whatever the subject's rest.
#[test]
fn a_cells_result_naming_no_cell_leaves_every_cell_as_it_is() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let k = "k: k::configuration::KCell(Cmd::Make { x }, ..), acc: k::configuration::Cell(a)";
    let mut lines = Vec::new();
    for claim in [false, true] {
        let form = if claim { "claim" } else { "rule" };
        let line = |name: &str, subject: &str, result: &str| {
            let manifest = library_package(
                temporary.path(),
                &format!("unchanged-{form}-{name}"),
                &whole_payloads(claim, subject, result),
            );
            if claim {
                emitted_sentence(target.path(), &manifest, "make")
            } else {
                first_error(target.path(), &manifest)
            }
        };
        let twin = line("reuse", &format!("{k}, state @ .."), "..state");
        for (name, subject, result) in [
            ("named-empty", format!("{k}, state @ .."), ""),
            ("named-rest", format!("{k}, state @ .."), ".."),
            ("anonymous-empty", format!("{k}, .."), ""),
            ("anonymous-rest", format!("{k}, .."), ".."),
        ] {
            assert_eq!(line(name, &subject, result), twin, "{form}-{name}");
        }
        lines.push(twin);
        // An exact subject has no `..state` twin; its claim reads `frame` (`_`), and its rule
        // changes no cell, as the twin's does (`frame: _` names the cell, so it owes no lint).
        lines.push(line("exact-empty", &format!("{k}, frame: _"), ""));
    }
    expect_test::expect![[r#"
        [
            "error[krs::analysis::rule-changes-no-cell]: rule `make` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing @ 54:5",
            "error[krs::analysis::rule-changes-no-cell]: rule `make` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing @ 54:5",
            "claim [make]: <k> make ( X:Int ) ... </k> <acc> A:Int </acc> [one-path]",
            "claim [make]: <k> make ( X:Int ) ... </k> <acc> A:Int </acc> _ [one-path]",
        ]
    "#]].assert_debug_eq(&lines);
}

/// CELLSX: a `cells!` record without a rest that leaves a cell out describes no configuration,
/// since every configuration holds each of its cells; it is refused at the record, which says
/// which cells it leaves out, in a rule, a claim, a single-body rule, a context and a context
/// alias alike.
#[test]
fn a_cells_record_without_a_rest_that_leaves_a_cell_out_is_refused_at_the_record() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rewrite = "k: k::configuration::KCell(k::rewrite!(Cmd::Make { x } => ()), ..), acc: k::configuration::Cell(_)";
    let refused = [
        (
            "rule",
            whole_cells(false, "", "acc: k::configuration::Cell(a)", "acc: k::configuration::Cell(x)"),
        ),
        (
            "claim",
            whole_cells(true, "", "acc: k::configuration::Cell(a)", "acc: k::configuration::Cell(x)"),
        ),
        (
            "rule-one-leaf",
            whole_cells(
                false,
                "\n    p: Int,",
                "acc: k::configuration::Cell(a), crate::Frame::pc: k::configuration::Cell(p)",
                "acc: k::configuration::Cell(x)",
            ),
        ),
        (
            "single-body",
            format!(
                "{}#[k::rule(label = \"make\")]\npub fn make(\n    x: Int,\n    k::cells! {{ {rewrite} }}: Machine,\n) {{}}\n",
                WHOLE.replace("CONTEXT_ALIAS", WHOLE_ALIAS)
            ),
        ),
        (
            "context",
            format!(
                "{}#[k::context(hole = h)]\nfn make(\n    h: Int,\n    k::cells! {{ k: k::configuration::KCell(Cmd::Make {{ x: h }}, ..) }}: Machine,\n) {{}}\n",
                WHOLE.replace("CONTEXT_ALIAS", WHOLE_ALIAS)
            ),
        ),
        (
            "context-alias",
            WHOLE.replace(
                "CONTEXT_ALIAS",
                "k: k::configuration::KCell(site, tail @ ..), acc: k::configuration::Cell(0)",
            ),
        ),
    ]
    .map(|(name, source)| {
        let manifest = library_package(temporary.path(), &format!("whole-{name}"), &source);
        (name, first_error(target.path(), &manifest))
    });
    expect_test::expect![[r#"
        [
            (
                "rule",
                "error[krs::analysis::record-missing-children]: the `cells!` subject has no `..` and leaves out `frame`: a `cells!` record without `..` is the whole state, so it names every cell of its configuration, as a Rust struct pattern without `..` names every field; name it, or end the record with `..` to leave it unconstrained @ 54:5",
            ),
            (
                "claim",
                "error[krs::analysis::record-missing-children]: the `cells!` subject has no `..` and leaves out `frame`: a `cells!` record without `..` is the whole state, so it names every cell of its configuration, as a Rust struct pattern without `..` names every field; name it, or end the record with `..` to leave it unconstrained @ 54:5",
            ),
            (
                "rule-one-leaf",
                "error[krs::analysis::record-missing-children]: the `cells!` subject has no `..` and leaves out `Frame::gas`: a `cells!` record without `..` is the whole state, so it names every cell of its configuration, as a Rust struct pattern without `..` names every field; name it, or end the record with `..` to leave it unconstrained @ 55:5",
            ),
            (
                "single-body",
                "error[krs::analysis::record-missing-children]: the `cells!` subject has no `..` and leaves out `frame`: a `cells!` record without `..` is the whole state, so it names every cell of its configuration, as a Rust struct pattern without `..` names every field; name it, or end the record with `..` to leave it unconstrained @ 53:5",
            ),
            (
                "context",
                "error[krs::analysis::record-missing-children]: the `cells!` subject has no `..` and leaves out `acc` and `frame`: a `cells!` record without `..` is the whole state, so it names every cell of its configuration, as a Rust struct pattern without `..` names every field; name them, or end the record with `..` to leave them unconstrained @ 53:5",
            ),
            (
                "context-alias",
                "error[krs::analysis::record-missing-children]: the `cells!` pattern has no `..` and leaves out `frame`: a `cells!` record without `..` is the whole state, so it names every cell of its configuration, as a Rust struct pattern without `..` names every field; name it, or end the record with `..` to leave it unconstrained @ 47:5",
            ),
        ]
    "#]].assert_debug_eq(&refused);
}

/// A configuration with a cell of each kind a single-body rule's rewrite can stand in: plain
/// leaves of several sorts, a group's leaf, optional leaves, and a Map collection's instances.
const SINGLE_BODY: &str = r#"
use k::builtin::{Int, KSequence, List, Map, list, map};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {
    #[k::syntax("make({x})")]
    Make { x: Int },
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub gas: Int,
}

#[k::cell]
pub struct Obj {
    #[k::cell]
    pub oid: Int,
    #[k::cell]
    pub val: Int,
    #[k::cell]
    pub mem: Map,
}

#[k::cell]
pub struct Objs {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub obj: Obj,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Int,
    #[k::cell(nested)]
    pub frame: Frame,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub lst: List,
    #[k::cell(multiplicity = "?")]
    pub opt: Option<Int>,
    #[k::cell(multiplicity = "?")]
    pub omap: Option<Map>,
    #[k::cell(nested)]
    pub objs: Objs,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            acc: 0,
            frame: Frame { pc: 0, gas: 0 },
            env: k::map![],
            lst: list::empty(),
            opt: k::absent!(0),
            omap: k::absent!(k::map![]),
            objs: Objs { obj: Obj { oid: 0, val: 0, mem: k::map![] } },
        }
    }
}
"#;

/// CELLS4 item 3: a single-body rule's subject is its before-state, and its after-state is the
/// same state with each `k::rewrite!` taken to its right side. One that names no cell
/// (`cells! { .. }`), or names cells and marks no change, keeps every cell: it changes none, the
/// meaning of a rule whose result restates its subject, so it gets that rule's class and text,
/// at its subject.
#[test]
fn a_single_body_rule_that_marks_no_change_changes_no_cell() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let unchanged = |entries: &str| {
        format!(
            "{SINGLE_BODY}#[k::rule(label = \"make\")]\npub fn make(\n    k::cells! {{ {entries} }}: Machine,\n) {{}}\n"
        )
    };
    let mut lines = [
        ("empty", unchanged("")),
        ("rest", unchanged("..")),
        ("named-rest", unchanged("state @ ..")),
        ("wildcard", unchanged("acc: k::configuration::Cell(_), ..")),
        ("computation", unchanged("k: k::configuration::KCell(..), ..")),
        (
            "result-twin",
            whole_payloads(
                false,
                "k: k::configuration::KCell(Cmd::Make { x }, ..), acc: k::configuration::Cell(a), state @ ..",
                "..state",
            ),
        ),
    ]
    .map(|(name, source)| {
        let manifest = library_package(temporary.path(), &format!("unchanged-single-{name}"), &source);
        format!("{name}: {}", first_error(target.path(), &manifest))
    });
    lines.sort();
    expect_test::expect![[r"
        computation: error[krs::analysis::rule-changes-no-cell]: rule `make` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing @ 78:5
        empty: error[krs::analysis::rule-changes-no-cell]: rule `make` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing @ 78:5
        named-rest: error[krs::analysis::rule-changes-no-cell]: rule `make` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing @ 78:5
        rest: error[krs::analysis::rule-changes-no-cell]: rule `make` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing @ 78:5
        result-twin: error[krs::analysis::rule-changes-no-cell]: rule `make` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing @ 54:5
        wildcard: error[krs::analysis::rule-changes-no-cell]: rule `make` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing @ 78:5"]].assert_eq(&lines.join("\n"));
}

/// CELLS4 item 2: the `cells!` reader does not know which cells are leaves, so its refusal of an
/// entry written as a term without a wrapper is true of either: such an entry is a nested cell's
/// (a binder, `_` or a fragment), and a leaf's content stands inside its wrapper. A whole entry
/// `k::rewrite!(a => b)` rewrites a content outside its wrapper, which stands inside it,
/// `Cell(k::rewrite!(a => b))`. Each way out is accepted.
#[test]
fn an_entry_without_its_wrapper_is_refused_for_what_it_writes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cell = "k::configuration::Cell";
    let frame = "frame: k::fragment![crate::Frame { pc: a, .. }]";
    let refused = [
        (
            "leaf-literal",
            whole_cells(false, "", &format!("acc: 0, {frame}, .."), ".."),
        ),
        (
            "result-literal",
            whole_cells(true, "", &format!("acc: {cell}(a), .."), "acc: 1, .."),
        ),
        (
            "leaf-call",
            whole_cells(
                false,
                "",
                &format!("acc: {cell}(a), .."),
                "acc: int::add(a, 1), ..",
            ),
        ),
        (
            "group-literal",
            whole_cells(false, "", &format!("acc: {cell}(a), .."), "frame: 0, .."),
        ),
        (
            "group-call",
            whole_cells(
                true,
                "",
                &format!("acc: {cell}(a), .."),
                "frame: int::add(a, 1), ..",
            ),
        ),
        (
            "leaf-rewrite",
            single_body("\n    a: Int,", "acc: k::rewrite!(a => x)"),
        ),
        (
            "group-rewrite",
            single_body(
                "\n    f: Frame,",
                "frame: k::rewrite!(f => k::fragment![crate::Frame { pc: x, gas: 0 }])",
            ),
        ),
    ]
    .map(|(name, source)| {
        let manifest = library_package(temporary.path(), &format!("unwrapped-{name}"), &source);
        format!("{name}: {}", first_error(target.path(), &manifest))
    });
    expect_test::expect![[r"
        leaf-literal: error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: an entry without a wrapper is a nested cell's: a binder, `_` in a pattern, or `k::fragment![..]`; a leaf cell's content is written inside its wrapper, `Cell(..)`, and the computation's inside `KCell(..)` @ 54:78
        result-literal: error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: an entry without a wrapper is a nested cell's: a binder, `_` in a pattern, or `k::fragment![..]`; a leaf cell's content is written inside its wrapper, `Cell(..)`, and the computation's inside `KCell(..)` @ 56:58
        leaf-call: error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: an entry without a wrapper is a nested cell's: a binder, `_` in a pattern, or `k::fragment![..]`; a leaf cell's content is written inside its wrapper, `Cell(..)`, and the computation's inside `KCell(..)` @ 56:58
        group-literal: error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: an entry without a wrapper is a nested cell's: a binder, `_` in a pattern, or `k::fragment![..]`; a leaf cell's content is written inside its wrapper, `Cell(..)`, and the computation's inside `KCell(..)` @ 56:60
        group-call: error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: an entry without a wrapper is a nested cell's: a binder, `_` in a pattern, or `k::fragment![..]`; a leaf cell's content is written inside its wrapper, `Cell(..)`, and the computation's inside `KCell(..)` @ 56:60
        leaf-rewrite: error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: a `k::rewrite!` changes a content where it stands, and a leaf cell's content stands inside its wrapper: `Cell(k::rewrite!(a => b))`, and the computation's `KCell(k::rewrite!(a => b), ..)`; a nested cell's entry is a binder, `_`, or `k::fragment![..]`, inside which a child's content is rewritten @ 80:90
        group-rewrite: error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: a `k::rewrite!` changes a content where it stands, and a leaf cell's content stands inside its wrapper: `Cell(k::rewrite!(a => b))`, and the computation's `KCell(k::rewrite!(a => b), ..)`; a nested cell's entry is a binder, `_`, or `k::fragment![..]`, inside which a child's content is rewritten @ 80:92"]].assert_eq(&refused.join("\n"));
    let accepted = [
        (
            "leaf-literal",
            whole_cells(false, "", &format!("acc: {cell}(0), {frame}, .."), ".."),
        ),
        (
            "leaf-rewrite",
            single_body(
                "\n    a: Int,",
                &format!("acc: {cell}(k::rewrite!(a => x))"),
            ),
        ),
    ]
    .map(|(name, source)| {
        let manifest = library_package(temporary.path(), &format!("wrapped-{name}"), &source);
        format!(
            "{name}: {}",
            emitted_sentence(target.path(), &manifest, "make")
        )
    });
    expect_test::expect![[r"
        leaf-literal: rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> 0 </acc> <frame> <pc> A:Int </pc> <gas> _ </gas> </frame>
        leaf-rewrite: rule [make]: <k> (make ( X:Int ) => .K) ... </k> <acc> A:Int => X:Int </acc>"]].assert_eq(&accepted.join("\n"));
}

/// A `SINGLE_BODY` single-body rule `make` over `x: Int` and the binders of `parameters` that
/// removes `make(x)` from the computation and rewrites the cells of `entries`.
fn single_body(parameters: &str, entries: &str) -> String {
    format!(
        "{SINGLE_BODY}#[k::rule(label = \"make\")]\npub fn make(\n    x: Int,{parameters}\n    k::cells! {{ k: k::configuration::KCell(k::rewrite!(Cmd::Make {{ x }} => ()), ..), {entries}, .. }}: Machine,\n) {{}}\n"
    )
}

/// SBODY: a `k::rewrite!` that is a cell's whole content, `acc: Cell(k::rewrite!(a => x))`,
/// changes the content from what its left side matches to what its right side writes: the cell's
/// before and after, `<acc> A => X </acc>`, which is the rule with the result `acc: Cell(x)`. It
/// was lowered as a rewrite in place whose content is the rewrite, which the Semantic IR refused
/// as an internal error. A leaf of any sort, inside a group too, an optional cell's present
/// content (the cell stays present) and a kept instance's child read so; an instance's key is
/// kept only by a rewrite with the same sides, read as the key, and another is the key change a
/// result is refused for. Below the root of an optional's content or an instance's child a
/// rewrite has no in-place lowering yet, refused as a stated limit; a rule whose rewrites change
/// nothing is told so. The admitted rule runs: `make(5)` writes 5 into `acc` and `pc`.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of cells, each with its K or its refusal, and one run."
)]
fn a_rewrite_of_a_cell_s_whole_content_is_its_before_and_after() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cell = "k::configuration::Cell";
    let admitted = [
        (
            "leaf",
            "\n    a: Int,",
            format!("acc: {cell}(k::rewrite!(a => x))"),
        ),
        ("literal", "", format!("acc: {cell}(k::rewrite!(0 => x))")),
        (
            "group-leaf",
            "\n    p: Int,",
            format!("crate::Frame::pc: {cell}(k::rewrite!(p => x))"),
        ),
        (
            "two-leaves",
            "\n    a: Int,\n    p: Int,",
            format!(
                "acc: {cell}(k::rewrite!(a => x)), crate::Frame::pc: {cell}(k::rewrite!(p => x))"
            ),
        ),
        (
            "map-leaf",
            "\n    e: k::Term<Map>,",
            format!("env: {cell}(k::rewrite!(e => k::map![]))"),
        ),
        (
            "list-leaf",
            "\n    l: k::Term<List>,",
            format!("lst: {cell}(k::rewrite!(l => list::empty()))"),
        ),
        (
            "optional",
            "\n    o: Int,",
            format!("opt: Some({cell}(k::rewrite!(o => x)))"),
        ),
        (
            "optional-map",
            "\n    m: k::Term<Map>,",
            format!("omap: Some({cell}(k::rewrite!(m => k::map![])))"),
        ),
        (
            "instance-child",
            "\n    v: Int,",
            "Objs::obj: { k::fragment![crate::Obj { oid: 1, val: k::rewrite!(v => x), .. }], .. }"
                .to_owned(),
        ),
        (
            "instance-key-kept",
            "",
            "Objs::obj: { k::fragment![crate::Obj { oid: k::rewrite!(1 => 1), .. }], .. }"
                .to_owned(),
        ),
    ]
    .map(|(name, parameters, entries)| {
        let manifest = library_package(
            temporary.path(),
            &format!("sbody-{name}"),
            &single_body(parameters, &entries),
        );
        (name, emitted_sentence(target.path(), &manifest, "make"))
    });
    expect_test::expect![[r#"
        [
            (
                "leaf",
                "rule [make]: <k> (make ( X:Int ) => .K) ... </k> <acc> A:Int => X:Int </acc>",
            ),
            (
                "literal",
                "rule [make]: <k> (make ( X:Int ) => .K) ... </k> <acc> 0 => X:Int </acc>",
            ),
            (
                "group-leaf",
                "rule [make]: <k> (make ( X:Int ) => .K) ... </k> <pc> P:Int => X:Int </pc>",
            ),
            (
                "two-leaves",
                "rule [make]: <k> (make ( X:Int ) => .K) ... </k> <acc> A:Int => X:Int </acc> <pc> P:Int => X:Int </pc>",
            ),
            (
                "map-leaf",
                "rule [make]: <k> (make ( X:Int ) => .K) ... </k> <env> E:Map => .Map </env>",
            ),
            (
                "list-leaf",
                "rule [make]: <k> (make ( X:Int ) => .K) ... </k> <lst> L:List => .List </lst>",
            ),
            (
                "optional",
                "rule [make]: <k> (make ( X:Int ) => .K) ... </k> <opt> O:Int => X:Int </opt>",
            ),
            (
                "optional-map",
                "rule [make]: <k> (make ( X:Int ) => .K) ... </k> <omap> M:Map => .Map </omap>",
            ),
            (
                "instance-child",
                "rule [make]: <k> (make ( X:Int ) => .K) ... </k> <obj> <oid> 1 </oid> <val> V:Int => X:Int </val> ... </obj>",
            ),
            (
                "instance-key-kept",
                "rule [make]: <k> (make ( X:Int ) => .K) ... </k> <obj> <oid> 1 </oid> ... </obj>",
            ),
        ]
    "#]]
    .assert_debug_eq(&admitted);
    let refused = [
        (
            "optional-below-root",
            format!("omap: Some({cell}(map![1 -> k::rewrite!(_ => x), ..]))"),
        ),
        (
            "instance-child-below-root",
            "Objs::obj: { k::fragment![crate::Obj { oid: 1, mem: map![1 -> k::rewrite!(_ => x), ..], .. }], .. }"
                .to_owned(),
        ),
        (
            "instance-key-changed",
            "Objs::obj: { k::fragment![crate::Obj { oid: k::rewrite!(1 => 2), .. }], .. }"
                .to_owned(),
        ),
    ]
    .map(|(name, entries)| {
        let manifest = library_package(
            temporary.path(),
            &format!("sbody-{name}"),
            &single_body("", &entries),
        );
        (name, first_error(target.path(), &manifest))
    });
    expect_test::expect![[r#"
        [
            (
                "optional-below-root",
                "error[krs::analysis::optional-presence]: the present content of the optional cell `omap` holds a `k::rewrite!` below its root, and a single-body rule rewrites in place only inside a cell that is neither optional nor in a collection instance, which KRS does not lower yet: rewrite the whole content, `k::rewrite!(.. => ..)`, or write the rule with a result @ 79:85",
            ),
            (
                "instance-child-below-root",
                "error[krs::analysis::collection-entry]: the child `mem` of an instance of the collection `obj` holds a `k::rewrite!` below its root, and a single-body rule rewrites in place only inside a cell that is neither optional nor in a collection instance, which KRS does not lower yet: rewrite the whole content, `k::rewrite!(.. => ..)`, or write the rule with a result @ 79:132",
            ),
            (
                "instance-key-changed",
                "error[krs::analysis::map-collection-key]: a rewrite changes a cell of an instance of the Map collection `obj` in place, and `oid` is the instance's key, its identity: a key not provably the one matched is the instance moved, removed and created under the new key, which a rewrite in place does not state; write a rule with a result whose record writes the new key and takes the other children with `..me` from the instance its subject labels `me @` @ 79:124",
            ),
        ]
    "#]]
    .assert_debug_eq(&refused);
    // Rewrites that change nothing are no step.
    let unchanged = library_package(
        temporary.path(),
        "sbody-unchanged",
        &format!(
            "{SINGLE_BODY}#[k::rule(label = \"make\")]\npub fn make(\n    x: Int,\n    a: Int,\n    k::cells! {{ k: k::configuration::KCell(Cmd::Make {{ x }}, ..), acc: {cell}(k::rewrite!(a => a)), .. }}: Machine,\n) {{}}\n"
        ),
    );
    expect_test::expect!["error[krs::analysis::rule-changes-no-cell]: rule `make` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing @ 80:5"].assert_eq(&first_error(target.path(), &unchanged));
    // The rule steps: `make(5)` leaves the computation and writes 5 into `acc` and `pc`.
    let manifest = library_package(
        temporary.path(),
        "sbody-run",
        &single_body(
            "\n    a: Int,\n    p: Int,",
            &format!(
                "acc: {cell}(k::rewrite!(a => x)), crate::Frame::pc: {cell}(k::rewrite!(p => x))"
            ),
        ),
    );
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "make(5)").unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{stdout}\n{stderr}");
    expect_test::expect!["<generatedTop> <k> .K </k> <acc> 5 </acc> <frame> <pc> 5 </pc> <gas> 0 </gas> </frame> <env> .Map </env> <lst> .List </lst> .OptCell .OmapCell <objs> .ObjCellMap </objs> </generatedTop>"].assert_eq(&stdout.split_whitespace().collect::<Vec<_>>().join(" "));
}

/// CELLS2 item 1: a `cells!` result's record-level `..` stands for the cells the record does not
/// name, which a `cells!` result leaves as they are with or without it, so the rule or claim with
/// the `..` is the one without it, whatever the subject's rest: `..`, `state @ ..`, or none
/// (every cell named). `..` ends the record, as the subject's does.
#[test]
fn a_cells_results_own_rest_is_the_result_without_it() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let emitted = |name: &str, source: &str| {
        let manifest = library_package(temporary.path(), &format!("result-rest-{name}"), source);
        emitted_sentence(target.path(), &manifest, "make")
    };
    let written =
        "acc: k::configuration::Cell(x), frame: k::fragment![crate::Frame { pc: x, gas: 0 }]";
    let mut lines = Vec::new();
    for claim in [false, true] {
        for (name, subject, result) in [
            (
                "anonymous",
                "acc: k::configuration::Cell(a), ..",
                "acc: k::configuration::Cell(x)",
            ),
            (
                "named",
                "acc: k::configuration::Cell(a), state @ ..",
                "acc: k::configuration::Cell(x)",
            ),
            (
                "exact",
                "acc: k::configuration::Cell(a), frame: _",
                "acc: k::configuration::Cell(x)",
            ),
            (
                "exact-written",
                "acc: k::configuration::Cell(a), frame: _",
                written,
            ),
        ] {
            let name = format!("{name}-{}", if claim { "claim" } else { "rule" });
            let [without, with, comma] = [
                ("without", result.to_owned()),
                ("with", format!("{result}, ..")),
                ("comma", format!("{result}, ..,")),
            ]
            .map(|(kind, result)| {
                emitted(
                    &format!("{name}-{kind}"),
                    &whole_cells(claim, "", subject, &result),
                )
            });
            assert_eq!(with, without, "{name}");
            assert_eq!(comma, without, "{name}");
            lines.push(format!("{name}: {with}"));
        }
    }
    expect_test::expect![[r#"
        [
            "anonymous-rule: rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc>",
            "named-rule: rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc>",
            "exact-rule: rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> _",
            "exact-written-rule: rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> (_:FrameCell => <frame> <pc> X:Int </pc> <gas> 0 </gas> </frame>)",
            "anonymous-claim: claim [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> [one-path]",
            "named-claim: claim [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> [one-path]",
            "exact-claim: claim [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> _ [one-path]",
            "exact-written-claim: claim [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <acc> A:Int => X:Int </acc> (_:FrameCell => <frame> <pc> X:Int </pc> <gas> 0 </gas> </frame>) [one-path]",
        ]
    "#]]
    .assert_debug_eq(&lines);
    let refused = [
        (
            "not-last",
            whole_cells(
                false,
                "",
                "acc: k::configuration::Cell(a), ..",
                "..,acc: k::configuration::Cell(x)",
            ),
        ),
        (
            "twice",
            whole_cells(
                true,
                "",
                "acc: k::configuration::Cell(a), ..",
                "acc: k::configuration::Cell(x), .., ..",
            ),
        ),
    ]
    .map(|(name, source)| {
        let manifest = library_package(temporary.path(), &format!("result-rest-{name}"), &source);
        (name, first_error(target.path(), &manifest))
    });
    expect_test::expect![[r#"
        [
            (
                "not-last",
                "error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: the configuration remainder must be last @ 56:55",
            ),
            (
                "twice",
                "error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: the configuration remainder must be last @ 56:87",
            ),
        ]
    "#]]
    .assert_debug_eq(&refused);
}

/// A machine with a Map leaf `env` and a group `objs` holding a Map collection `obj` of `Obj`
/// instances.
const OVERWRITE: &str = r#"
use k::builtin::{Int, KSequence, Map, map};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {
    #[k::syntax("make({x})")]
    Make { x: Int },
}

#[k::cell]
pub struct Obj {
    #[k::cell]
    pub oid: Int,
    #[k::cell]
    pub val: Int,
}

#[k::cell]
pub struct Objs {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub obj: Obj,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell(nested)]
    pub objs: Objs,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm], env: k::map![], objs: Objs { obj: Obj { oid: 0, val: 0 } } }
    }
}
"#;

/// An `OVERWRITE` `cells!` rule (`claim` false) or claim `make`, whose subject holds `subject`
/// after the computation cell's entry and the record's `..`, and whose result writes `result`.
fn overwrite_cells(claim: bool, subject: &str, result: &str) -> String {
    let attribute = if claim {
        "#[k::claim(one_path, label = \"make\")]"
    } else {
        "#[k::rule(label = \"make\")]"
    };
    format!(
        "{OVERWRITE}{attribute}\npub fn make(\n    x: Int,\n    k::cells! {{ k: k::configuration::KCell(Cmd::Make {{ x }}, tail @ ..), {subject}.. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), {result} }}\n}}\n"
    )
}

/// An `OVERWRITE` readable rule (`claim` false) or claim `make` writing `result`.
fn overwrite_readable(claim: bool, result: &str) -> String {
    let (block, attribute) = if claim {
        ("claims", "#[k::claim(one_path)]\n    ")
    } else {
        ("rules", "")
    };
    format!(
        "{OVERWRITE}k::{block}! {{\n    for Machine;\n    use Cmd::*;\n    {attribute}make: {{ k: [Make {{ x }}, ..] }} => {{ k: [..], {result} }};\n}}\n"
    )
}

/// CELLS2 item 2: a result entry over a cell the subject does not match overwrites it. A `cells!`
/// result writing a whole map on a Map leaf is that overwrite, the rule whose subject reads the
/// leaf with `_`. A result writing a `*` collection's instances replaces every instance it holds,
/// which is not lowered yet: a readable and a `cells!` result give it one refusal, at the entry.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of routes and spellings, each with its K or its refusal."
)]
fn a_cells_result_over_a_cell_its_subject_leaves_out_overwrites_it_as_a_readable_one_does() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let emitted = |name: &str, source: &str| {
        let manifest = library_package(temporary.path(), &format!("overwrite-{name}"), source);
        emitted_sentence(target.path(), &manifest, "make")
    };
    let mut admitted = Vec::new();
    for (name, map) in [("map", "map![1 -> 2]"), ("empty", "map![]")] {
        let result = format!("env: k::configuration::Cell({map})");
        let [unmatched, wildcard] = [
            ("unmatched", ""),
            ("wildcard", "env: k::configuration::Cell(_), "),
        ]
        .map(|(kind, subject)| {
            emitted(
                &format!("{name}-{kind}"),
                &overwrite_cells(false, subject, &result),
            )
        });
        assert_eq!(unmatched, wildcard, "{name}");
        admitted.push(format!("{name}: {unmatched}"));
    }
    expect_test::expect![[r#"
        [
            "map: rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <env> _ => 1 |-> 2 </env>",
            "empty: rule [make]: <k> make ( X:Int ) ~> Tail:K => .K ~> Tail:K </k> <env> _ => .Map </env>",
        ]
    "#]]
    .assert_debug_eq(&admitted);
    let instances = "{ crate::Obj { oid: 1, val: 2 } }";
    let mut refused = Vec::new();
    for claim in [false, true] {
        let form = if claim { "claim" } else { "rule" };
        for (name, source) in [
            (
                "readable",
                overwrite_readable(claim, "obj: { Obj { oid: 1, val: 2 } }"),
            ),
            (
                "cells",
                overwrite_cells(claim, "", &format!("crate::Objs::obj: {instances}")),
            ),
            (
                "cells-fragment",
                overwrite_cells(
                    claim,
                    "",
                    "crate::Objs::obj: { k::fragment![crate::Obj { oid: 1, val: 2 }] }",
                ),
            ),
            (
                "cells-beside-a-map",
                overwrite_cells(
                    claim,
                    "",
                    &format!(
                        "env: k::configuration::Cell(map![1 -> 2]), crate::Objs::obj: {instances}"
                    ),
                ),
            ),
        ] {
            let manifest = library_package(
                temporary.path(),
                &format!("overwrite-{form}-{name}"),
                &source,
            );
            refused.push((
                format!("{form}-{name}"),
                first_error(target.path(), &manifest),
            ));
        }
    }
    let headline = |line: &str| line.split_once(" @ ").unwrap().0.to_owned();
    for (name, line) in &refused {
        assert_eq!(headline(line), headline(&refused[0].1), "{name}");
    }
    expect_test::expect![[r#"
        [
            (
                "rule-readable",
                "error[krs::analysis::collection-entry]: the result writes the collection `obj`, whose instances the subject does not match, so the rule replaces every instance `obj` holds, whatever they are; a collection's instances are matched one by one, the others kept by `..`, so a rule that drops instances it never matched is not lowered yet: match the instances the rule replaces in the subject @ 50:54",
            ),
            (
                "rule-cells",
                "error[krs::analysis::collection-entry]: the result writes the collection `obj`, whose instances the subject does not match, so the rule replaces every instance `obj` holds, whatever they are; a collection's instances are matched one by one, the others kept by `..`, so a rule that drops instances it never matched is not lowered yet: match the instances the rule replaces in the subject @ 52:71",
            ),
            (
                "rule-cells-fragment",
                "error[krs::analysis::collection-entry]: the result writes the collection `obj`, whose instances the subject does not match, so the rule replaces every instance `obj` holds, whatever they are; a collection's instances are matched one by one, the others kept by `..`, so a rule that drops instances it never matched is not lowered yet: match the instances the rule replaces in the subject @ 52:71",
            ),
            (
                "rule-cells-beside-a-map",
                "error[krs::analysis::collection-entry]: the result writes the collection `obj`, whose instances the subject does not match, so the rule replaces every instance `obj` holds, whatever they are; a collection's instances are matched one by one, the others kept by `..`, so a rule that drops instances it never matched is not lowered yet: match the instances the rule replaces in the subject @ 52:114",
            ),
            (
                "claim-readable",
                "error[krs::analysis::collection-entry]: the result writes the collection `obj`, whose instances the subject does not match, so the rule replaces every instance `obj` holds, whatever they are; a collection's instances are matched one by one, the others kept by `..`, so a rule that drops instances it never matched is not lowered yet: match the instances the rule replaces in the subject @ 51:54",
            ),
            (
                "claim-cells",
                "error[krs::analysis::collection-entry]: the result writes the collection `obj`, whose instances the subject does not match, so the rule replaces every instance `obj` holds, whatever they are; a collection's instances are matched one by one, the others kept by `..`, so a rule that drops instances it never matched is not lowered yet: match the instances the rule replaces in the subject @ 52:71",
            ),
            (
                "claim-cells-fragment",
                "error[krs::analysis::collection-entry]: the result writes the collection `obj`, whose instances the subject does not match, so the rule replaces every instance `obj` holds, whatever they are; a collection's instances are matched one by one, the others kept by `..`, so a rule that drops instances it never matched is not lowered yet: match the instances the rule replaces in the subject @ 52:71",
            ),
            (
                "claim-cells-beside-a-map",
                "error[krs::analysis::collection-entry]: the result writes the collection `obj`, whose instances the subject does not match, so the rule replaces every instance `obj` holds, whatever they are; a collection's instances are matched one by one, the others kept by `..`, so a rule that drops instances it never matched is not lowered yet: match the instances the rule replaces in the subject @ 52:114",
            ),
        ]
    "#]]
    .assert_debug_eq(&refused);
}

/// CELLS3 item 3: a result entry over a collection whose group the subject names whole, `objs`
/// beside `Objs::obj: { .. }`, overwrites no collection the subject leaves out: the subject's
/// entry of `objs` matches every instance there. The rule names the group and a cell inside it,
/// as a leaf written beside its matched group does, and gets that refusal, `group-and-descendant`,
/// on every route, at the collection's entry.
#[test]
fn a_result_collection_inside_a_group_its_subject_names_is_named_twice() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let mut refused = Vec::new();
    for claim in [false, true] {
        let form = if claim { "claim" } else { "rule" };
        let (block, attribute) = if claim {
            ("claims", "#[k::claim(one_path)]\n    ")
        } else {
            ("rules", "")
        };
        for (name, source) in [
            (
                "readable",
                format!(
                    "{OVERWRITE}k::{block}! {{\n    for Machine;\n    use Cmd::*;\n    {attribute}make: {{ k: [Make {{ x }}, ..], objs: o }} => {{ k: [..], obj: {{ Obj {{ oid: 1, val: 2 }} }} }};\n}}\n"
                ),
            ),
            (
                "cells",
                overwrite_cells(
                    claim,
                    "objs: _, ",
                    "crate::Objs::obj: { crate::Obj { oid: 1, val: 2 } }",
                ),
            ),
            (
                "cells-empty",
                overwrite_cells(claim, "objs: _, ", "crate::Objs::obj: { }"),
            ),
        ] {
            let manifest = library_package(
                temporary.path(),
                &format!("named-twice-{form}-{name}"),
                &source,
            );
            refused.push((
                format!("{form}-{name}"),
                first_error(target.path(), &manifest),
            ));
        }
    }
    expect_test::expect![[r#"
        [
            (
                "rule-readable",
                "error[krs::analysis::group-and-descendant]: rule `make` selects the nested cell `objs` and the cell `obj` inside it; the whole-cell entry `objs` already names every cell below it, so select one or the other @ 50:58",
            ),
            (
                "rule-cells",
                "error[krs::analysis::group-and-descendant]: rule `make` selects the nested cell `objs` and the cell `obj` inside it; the whole-cell entry `objs` already names every cell below it, so select one or the other @ 52:66",
            ),
            (
                "rule-cells-empty",
                "error[krs::analysis::group-and-descendant]: rule `make` selects the nested cell `objs` and the cell `obj` inside it; the whole-cell entry `objs` already names every cell below it, so select one or the other @ 52:66",
            ),
            (
                "claim-readable",
                "error[krs::analysis::group-and-descendant]: rule `make` selects the nested cell `objs` and the cell `obj` inside it; the whole-cell entry `objs` already names every cell below it, so select one or the other @ 51:58",
            ),
            (
                "claim-cells",
                "error[krs::analysis::group-and-descendant]: rule `make` selects the nested cell `objs` and the cell `obj` inside it; the whole-cell entry `objs` already names every cell below it, so select one or the other @ 52:66",
            ),
            (
                "claim-cells-empty",
                "error[krs::analysis::group-and-descendant]: rule `make` selects the nested cell `objs` and the cell `obj` inside it; the whole-cell entry `objs` already names every cell below it, so select one or the other @ 52:66",
            ),
        ]
    "#]].assert_debug_eq(&refused);
}

/// CELLS4 item 4: `group-and-descendant` is about the cell the sentence names twice, so it stands
/// at that cell's name in its entry, on the route of a leaf named beside its group (the rule's
/// lowering) as on the route of a collection named beside its group (the collector), wherever
/// the entry is: the subject's or the result's, readable or `cells!`.
#[test]
fn group_and_descendant_stands_at_the_cell_named_twice() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cell = "k::configuration::Cell";
    let mut lines = Vec::new();
    for claim in [false, true] {
        let form = if claim { "claim" } else { "rule" };
        let (block, attribute) = if claim {
            ("claims", "#[k::claim(one_path)]\n    ")
        } else {
            ("rules", "")
        };
        for (name, source) in [
            (
                "leaf-in-result",
                whole_cells(
                    claim,
                    "\n    f: Frame,",
                    &format!("acc: {cell}(a), frame: f, .."),
                    &format!("crate::Frame::pc: {cell}(1), .."),
                ),
            ),
            (
                "leaf-in-subject",
                whole_cells(
                    claim,
                    "\n    f: Frame,\n    p: Int,",
                    &format!("acc: {cell}(a), frame: f, crate::Frame::pc: {cell}(p), .."),
                    "..",
                ),
            ),
            (
                "readable",
                format!(
                    "{}k::{block}! {{\n    for Machine;\n    use Cmd::*;\n    {attribute}make: {{ k: [Make {{ x }}, ..], acc: a, frame: f }} => {{ k: [..], acc: x, pc: 1 }};\n}}\n",
                    WHOLE.replace("CONTEXT_ALIAS", WHOLE_ALIAS)
                ),
            ),
        ] {
            let manifest =
                library_package(temporary.path(), &format!("twice-{form}-{name}"), &source);
            let line = first_error(target.path(), &manifest);
            let (_, at) = line.rsplit_once(" @ ").unwrap();
            let (row, column) = at.split_once(':').unwrap();
            let text = source
                .lines()
                .nth(row.parse::<usize>().unwrap() - 1)
                .unwrap();
            let named = &text[column.parse::<usize>().unwrap() - 1..][..2];
            lines.push(format!("{form}-{name}: {line} ({named})"));
        }
    }
    expect_test::expect![[r"
        rule-leaf-in-result: error[krs::analysis::group-and-descendant]: rule `make` selects the nested cell `frame` and the cell `pc` inside it; the whole-cell entry `frame` already names every cell below it, so select one or the other @ 57:67 (pc)
        rule-leaf-in-subject: error[krs::analysis::group-and-descendant]: rule `make` selects the nested cell `frame` and the cell `pc` inside it; the whole-cell entry `frame` already names every cell below it, so select one or the other @ 56:129 (pc)
        rule-readable: error[krs::analysis::group-and-descendant]: rule `make` selects the nested cell `frame` and the cell `pc` inside it; the whole-cell entry `frame` already names every cell below it, so select one or the other @ 53:75 (pc)
        claim-leaf-in-result: error[krs::analysis::group-and-descendant]: rule `make` selects the nested cell `frame` and the cell `pc` inside it; the whole-cell entry `frame` already names every cell below it, so select one or the other @ 57:67 (pc)
        claim-leaf-in-subject: error[krs::analysis::group-and-descendant]: rule `make` selects the nested cell `frame` and the cell `pc` inside it; the whole-cell entry `frame` already names every cell below it, so select one or the other @ 56:129 (pc)
        claim-readable: error[krs::analysis::group-and-descendant]: rule `make` selects the nested cell `frame` and the cell `pc` inside it; the whole-cell entry `frame` already names every cell below it, so select one or the other @ 54:75 (pc)"]].assert_eq(&lines.join("\n"));
}

/// CELLS3 item 4: a `k::rewrite!` written as a cell's whole entry whose sides are entries rather
/// than contents is refused for what it writes. A side `None` would change whether the cell is
/// present, which a rule states by its subject and its result. `Some(..)`, `Cell(..)` and
/// `KCell(..)` name no content, so they stand outside the rewrite, around the content it
/// changes, which a single-body rule admits (`Some(Cell(k::rewrite!(o => x)))`).
#[test]
fn a_rewrite_whose_side_is_an_entry_is_refused_for_what_it_writes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cell = "k::configuration::Cell";
    let whole_k = format!(
        "{SINGLE_BODY}#[k::rule(label = \"make\")]\npub fn make(\n    x: Int,\n    k::cells! {{ k: k::rewrite!(k::configuration::KCell(..) => k::configuration::KCell(1)), .. }}: Machine,\n) {{}}\n"
    );
    let refused = [
        (
            "presence",
            single_body("", &format!("opt: k::rewrite!(None => Some({cell}(x)))")),
        ),
        (
            "absence",
            single_body(
                "\n    o: Int,",
                &format!("opt: k::rewrite!(Some({cell}(o)) => None)"),
            ),
        ),
        (
            "wrapper-in-presence",
            single_body(
                "\n    o: Int,",
                &format!("opt: Some(k::rewrite!({cell}(o) => {cell}(x)))"),
            ),
        ),
        (
            "presence-on-both-sides",
            single_body(
                "\n    o: Int,",
                &format!("opt: k::rewrite!(Some({cell}(o)) => Some({cell}(x)))"),
            ),
        ),
        ("computation", whole_k),
    ]
    .map(|(name, source)| {
        let manifest = library_package(temporary.path(), &format!("entry-rewrite-{name}"), &source);
        (name, first_error(target.path(), &manifest))
    });
    expect_test::expect![[r#"
        [
            (
                "presence",
                "error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: a `k::rewrite!` from `None` changes whether the cell is present, and a rewrite changes a content where it stands, never whether its cell is there: a rule states that change by its subject and its result, `None` in its subject and `Some(Cell(..))` in its result @ 79:90",
            ),
            (
                "absence",
                "error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: a `k::rewrite!` to `None` changes whether the cell is present, and a rewrite changes a content where it stands, never whether its cell is there: a rule states that change by its subject and its result, `Some(Cell(..))` in its subject and `None` in its result @ 80:90",
            ),
            (
                "wrapper-in-presence",
                "error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: `Cell(..)` on a side of a `k::rewrite!` names no content: it says which cell holds a content, and a rewrite changes a content where it stands; write `Cell(..)` outside the rewrite, around the content it changes: `Cell(k::rewrite!(a => b))` @ 80:95",
            ),
            (
                "presence-on-both-sides",
                "error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: `Some(..)` on a side of a `k::rewrite!` names no content: it says that a `?` cell is present, and a rewrite changes a content where it stands; write `Some(..)` outside the rewrite, around the content it changes: `Some(Cell(k::rewrite!(a => b)))` @ 80:90",
            ),
            (
                "computation",
                "error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: `KCell(..)` on a side of a `k::rewrite!` names no content: it says which cell holds a content, and a rewrite changes a content where it stands; write `KCell(..)` outside the rewrite, around the content it changes: `KCell(k::rewrite!(a => b), ..)` @ 79:20",
            ),
        ]
    "#]].assert_debug_eq(&refused);
    let manifest = library_package(
        temporary.path(),
        "entry-rewrite-content",
        &single_body(
            "\n    o: Int,",
            &format!("opt: Some({cell}(k::rewrite!(o => x)))"),
        ),
    );
    expect_test::expect![[r#"
        "rule [make]: <k> (make ( X:Int ) => .K) ... </k> <opt> O:Int => X:Int </opt>"
    "#]]
    .assert_debug_eq(&emitted_sentence(target.path(), &manifest, "make"));
}

/// A machine whose `?` group `ogroup` (`Gp { pa, pb }`) starts present (`pa` 3, `pb` 4) when
/// `present` and absent otherwise, beside a `KItem` cell `slot` that starts at 0.
fn optional_group(present: bool) -> String {
    let start = if present {
        "Some(Gp { pa: 3, pb: 4 })"
    } else {
        "k::absent!(Gp { pa: 0, pb: 0 })"
    };
    format!(
        r#"
use k::builtin::{{Int, KSequence}};
use k::KResult;

k::sorts! {{
    Stmt;
}}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {{
    #[k::syntax("go")]
    Go(),
}}

#[k::cell]
pub struct Gp {{
    #[k::cell]
    pub pa: Int,
    #[k::cell]
    pub pb: Int,
}}

#[k::configuration]
pub struct Machine {{
    #[k::cell]
    pub k: KSequence,
    #[k::cell(multiplicity = "?", nested)]
    pub ogroup: Option<Gp>,
    #[k::cell]
    pub slot: k::KItem,
}}

impl Machine {{
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {{
        Self {{ k: k::k![pgm], ogroup: {start}, slot: 0 }}
    }}
}}
"#
    )
}

/// FZERO: `Some(..)` on a `?` group states that the group is present. The cell's place holds
/// the present group or its absence (`.OgroupCell`), both values of the group's cell sort, so a
/// bare `X:OgroupCell` or `_:OgroupCell` there matched the absent group too: every rule below
/// stepped with `ogroup` absent, `Some(_) => None` deleted nothing, an overwrite created the
/// group, and `x` carried the absence into `slot`. `Some(_)` and a `Some(x)` nothing else reads
/// are the group with every child unconstrained, `Some(Gp { .. })`; a readable `Some(x)` the rule
/// reads elsewhere is `Some(x @ Gp { .. })`, matched by its children's binders and rebuilt from
/// them where read; a `cells!` rule writes it as the cell's alias where the result leaves the
/// group as it was, and, as a readable rule does, by its children's binders where the result
/// rewrites the group. Each rule is run with the group absent, where it is stuck, and present,
/// where it steps.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of spellings, each with its K and its runs."
)]
fn a_present_optional_group_is_stated_present() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = |present: bool, entries: &str| {
        let (subject, result) = entries.split_once(" => ").unwrap();
        format!(
            "{}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    go: {{ k: [Go(), ..], {subject} }} => {{ k: [..]{result} }};\n}}\n",
            optional_group(present)
        )
    };
    let cells = |present: bool, entries: &str| {
        let (subject, result) = entries.split_once(" => ").unwrap();
        format!(
            "{}#[k::rule(label = \"go\")]\nfn go(x: Gp, k::cells! {{ k: k::configuration::KCell(Cmd::Go(), tail @ ..), {subject}, state @ .. }}: Machine) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail){result}, ..state }}\n}}\n",
            optional_group(present)
        )
    };
    let unconstrained = "<ogroup> <pa> _ </pa> <pb> _ </pb> </ogroup>";
    let rebuilt = "<ogroup> <pa> XPa:Int </pa> <pb> XPb:Int </pb> </ogroup>";
    // Each case: its name, whether it is a `cells!` rule, its entries, its K, and the cells the
    // run with the group present ends with.
    let cases: [(&str, bool, &str, String, &str); 12] = [
        (
            "some-x",
            false,
            "ogroup: Some(x) => ",
            unconstrained.to_owned(),
            "<ogroup> <pa> 3 </pa> <pb> 4 </pb> </ogroup> <slot> 0 </slot>",
        ),
        (
            "some-wildcard",
            false,
            "ogroup: Some(_) => ",
            unconstrained.to_owned(),
            "<ogroup> <pa> 3 </pa> <pb> 4 </pb> </ogroup> <slot> 0 </slot>",
        ),
        (
            "delete",
            false,
            "ogroup: Some(_) => , ogroup: None",
            format!("({unconstrained} => .Bag)"),
            ".OgroupCell <slot> 0 </slot>",
        ),
        (
            "restated",
            false,
            "ogroup: Some(x) => , ogroup: Some(x)",
            unconstrained.to_owned(),
            "<ogroup> <pa> 3 </pa> <pb> 4 </pb> </ogroup> <slot> 0 </slot>",
        ),
        (
            "overwrite",
            false,
            "ogroup: Some(x) => , ogroup: Some(Gp { pa: 1, pb: 1 })",
            format!("({unconstrained} => <ogroup> <pa> 1 </pa> <pb> 1 </pb> </ogroup>)"),
            "<ogroup> <pa> 1 </pa> <pb> 1 </pb> </ogroup> <slot> 0 </slot>",
        ),
        (
            "read-elsewhere",
            false,
            "ogroup: Some(x), slot: _ => , slot: x",
            format!("{rebuilt} <slot> _ => {rebuilt} </slot>"),
            "<ogroup> <pa> 3 </pa> <pb> 4 </pb> </ogroup> <slot> <ogroup> <pa> 3 </pa> <pb> 4 </pb> </ogroup> </slot>",
        ),
        (
            "moved-out",
            false,
            "ogroup: Some(x), slot: _ => , ogroup: None, slot: x",
            format!("({rebuilt} => .Bag) <slot> _ => {rebuilt} </slot>"),
            ".OgroupCell <slot> <ogroup> <pa> 3 </pa> <pb> 4 </pb> </ogroup> </slot>",
        ),
        (
            "cells-some-x",
            true,
            "ogroup: Some(x) => ",
            unconstrained.to_owned(),
            "<ogroup> <pa> 3 </pa> <pb> 4 </pb> </ogroup> <slot> 0 </slot>",
        ),
        (
            "cells-delete",
            true,
            "ogroup: Some(x) => , ogroup: None",
            format!("({unconstrained} => .Bag)"),
            ".OgroupCell <slot> 0 </slot>",
        ),
        (
            "cells-restated",
            true,
            "ogroup: Some(x) => , ogroup: Some(x)",
            unconstrained.to_owned(),
            "<ogroup> <pa> 3 </pa> <pb> 4 </pb> </ogroup> <slot> 0 </slot>",
        ),
        (
            "cells-read-elsewhere",
            true,
            "ogroup: Some(x), slot: k::configuration::Cell(_) => , slot: k::configuration::Cell(x)",
            format!("( {unconstrained} #as X:OgroupCell ) <slot> _ => X:OgroupCell </slot>"),
            "<ogroup> <pa> 3 </pa> <pb> 4 </pb> </ogroup> <slot> <ogroup> <pa> 3 </pa> <pb> 4 </pb> </ogroup> </slot>",
        ),
        (
            "cells-moved-out",
            true,
            "ogroup: Some(x), slot: k::configuration::Cell(_) => , ogroup: None, slot: k::configuration::Cell(x)",
            format!("({rebuilt} => .Bag) <slot> _ => {rebuilt} </slot>"),
            ".OgroupCell <slot> <ogroup> <pa> 3 </pa> <pb> 4 </pb> </ogroup> </slot>",
        ),
    ];
    let mut emitted = Vec::new();
    for (name, cells_rule, entries, cells_k, after) in &cases {
        for present in [false, true] {
            let source = if *cells_rule {
                cells(present, entries)
            } else {
                readable(present, entries)
            };
            let manifest = library_package(
                temporary.path(),
                &format!("ogroup-{name}-{present}"),
                &source,
            );
            let sentence = emitted_sentence(target.path(), &manifest, "go");
            assert!(sentence.ends_with(cells_k.as_str()), "{name}: {sentence}");
            if !present {
                emitted.push(format!("{name}: {sentence}"));
            }
            let run = run_go(target.path(), &manifest);
            if present {
                assert!(
                    run.starts_with("<generatedTop> <k> .K </k>") && run.contains(after),
                    "{name} present: {run}"
                );
            } else {
                assert!(
                    run.starts_with(
                        "<generatedTop> <k> go ~> .K </k> .OgroupCell <slot> 0 </slot>"
                    ),
                    "{name} absent: {run}"
                );
            }
        }
    }
    expect_test::expect![[r#"
        [
            "some-x: rule [go]: <k> go => .K ... </k> <ogroup> <pa> _ </pa> <pb> _ </pb> </ogroup>",
            "some-wildcard: rule [go]: <k> go => .K ... </k> <ogroup> <pa> _ </pa> <pb> _ </pb> </ogroup>",
            "delete: rule [go]: <k> go => .K ... </k> (<ogroup> <pa> _ </pa> <pb> _ </pb> </ogroup> => .Bag)",
            "restated: rule [go]: <k> go => .K ... </k> <ogroup> <pa> _ </pa> <pb> _ </pb> </ogroup>",
            "overwrite: rule [go]: <k> go => .K ... </k> (<ogroup> <pa> _ </pa> <pb> _ </pb> </ogroup> => <ogroup> <pa> 1 </pa> <pb> 1 </pb> </ogroup>)",
            "read-elsewhere: rule [go]: <k> go => .K ... </k> <ogroup> <pa> XPa:Int </pa> <pb> XPb:Int </pb> </ogroup> <slot> _ => <ogroup> <pa> XPa:Int </pa> <pb> XPb:Int </pb> </ogroup> </slot>",
            "moved-out: rule [go]: <k> go => .K ... </k> (<ogroup> <pa> XPa:Int </pa> <pb> XPb:Int </pb> </ogroup> => .Bag) <slot> _ => <ogroup> <pa> XPa:Int </pa> <pb> XPb:Int </pb> </ogroup> </slot>",
            "cells-some-x: rule [go]: <k> go ~> Tail:K => .K ~> Tail:K </k> <ogroup> <pa> _ </pa> <pb> _ </pb> </ogroup>",
            "cells-delete: rule [go]: <k> go ~> Tail:K => .K ~> Tail:K </k> (<ogroup> <pa> _ </pa> <pb> _ </pb> </ogroup> => .Bag)",
            "cells-restated: rule [go]: <k> go ~> Tail:K => .K ~> Tail:K </k> <ogroup> <pa> _ </pa> <pb> _ </pb> </ogroup>",
            "cells-read-elsewhere: rule [go]: <k> go ~> Tail:K => .K ~> Tail:K </k> ( <ogroup> <pa> _ </pa> <pb> _ </pb> </ogroup> #as X:OgroupCell ) <slot> _ => X:OgroupCell </slot>",
            "cells-moved-out: rule [go]: <k> go ~> Tail:K => .K ~> Tail:K </k> (<ogroup> <pa> XPa:Int </pa> <pb> XPb:Int </pb> </ogroup> => .Bag) <slot> _ => <ogroup> <pa> XPa:Int </pa> <pb> XPb:Int </pb> </ogroup> </slot>",
        ]
    "#]]
    .assert_debug_eq(&emitted);

    // A claim states the same presence as a rule.
    let claim = format!(
        "{}k::claims! {{\n    for Machine;\n    use Cmd::*;\n    #[k::claim(one_path)]\n    go: {{ k: [Go(), ..], ogroup: Some(x), slot: _ }} => {{ k: [..], slot: x }};\n}}\n",
        optional_group(false)
    );
    let manifest = library_package(temporary.path(), "ogroup-claim", &claim);
    assert_eq!(
        emitted_sentence(target.path(), &manifest, "go"),
        format!(
            "claim [go]: <k> go => .K ... </k> {rebuilt} <slot> _ => {rebuilt} </slot> [one-path]"
        )
    );
}

/// `SINGLE_BODY` with `hold(x)`, an Int field, `keep(body)`, a field of sort `KSequence`,
/// `wrap(s)`, a Stmt field, and `duo(a, b)`, whose fields' sort is a parameter.
fn dot_k_fixture() -> String {
    SINGLE_BODY.replace(
        "    Make { x: Int },\n",
        "    Make { x: Int },\n    #[k::syntax(\"hold({x})\")]\n    Hold { x: Int },\n    #[k::syntax(\"keep({body})\")]\n    Keep { body: KSequence },\n    #[k::syntax(\"wrap({s})\")]\n    Wrap { s: Stmt },\n",
    ) + "\n#[k::constructor(sort = Stmt, syntax = \"duo({a}, {b})\")]\npub struct Duo<S: ?Sized> {\n    pub a: k::Term<S>,\n    pub b: k::Term<S>,\n}\n\n"
}

/// TERMDOTK: `()` on a rewrite's right is `.K`, a term of sort K, so it stands where K is
/// admissible: as a whole K-sequence item, which the rewrite removes, or at a place of sort K, a
/// field of sort `KSequence`, which it writes empty (`keep((B:K => .K))`). Anywhere else it is no
/// value of its place, the author's mistake that every other wrongly-sorted right side is, with
/// that side's class, text and location, on the `cells!` and the term route, in a rule and in a
/// context. A place whose sort is a parameter (`duo(a, b)`) is judged at the sort the rewrite
/// takes: `.K` is refused at Int, and admitted where the instance is K. Only the item loop says
/// that a place is a whole item; a place that states no sort is not one. It was refused by a structural check that knew only K-sequence items: framed as the
/// configuration descriptor's on the `cells!` route, an internal error on the term route, and a
/// field of sort K refused with them. A readable clause and an equation never hold a rewrite.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of places, routes and sentence kinds, and the admitted rule's run."
)]
fn a_dot_k_right_side_stands_where_k_is_admissible() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let fixture = dot_k_fixture();
    let removal = "k: k::configuration::KCell(k::rewrite!(Cmd::Make { x } => ()), ..)";
    let cells = |parameters: &str, entries: &str| {
        format!(
            "{fixture}#[k::rule(label = \"make\")]\npub fn make(\n    x: Int,{parameters}\n    k::cells! {{ {entries}, .. }}: Machine,\n) {{}}\n"
        )
    };
    let term = |parameters: &str, subject: &str| {
        format!(
            "{fixture}#[k::rule(label = \"make\")]\npub fn make(\n    {parameters}\n    k::term![{subject}]: k::Term<Stmt>,\n) {{}}\n"
        )
    };
    let cells_context = |entry: &str| {
        format!(
            "{fixture}#[k::context(hole = h)]\nfn ctx(\n    h: Int,\n    k::cells! {{ k: k::configuration::KCell({entry}, ..), .. }}: Machine,\n) {{}}\n"
        )
    };
    let term_context = |subject: &str| {
        format!(
            "{fixture}#[k::context(hole = h)]\nfn ctx(\n    h: Int,\n    k::term![{subject}]: k::Term<Stmt>,\n) {{}}\n"
        )
    };
    let refused = [
        ("cells-rule/int-leaf", cells("\n    a: Int,", &format!("{removal}, acc: k::configuration::Cell(k::rewrite!(a => ()))"))),
        ("cells-rule/map-leaf", cells("\n    e: Map,", &format!("{removal}, env: k::configuration::Cell(k::rewrite!(e => ()))"))),
        ("cells-rule/group-child", cells("\n    p: Int,", &format!("{removal}, crate::Frame::pc: k::configuration::Cell(k::rewrite!(p => ()))"))),
        ("cells-rule/map-value", cells("", &format!("{removal}, env: k::configuration::Cell(map![1 -> k::rewrite!(_ => ()), ..])"))),
        ("cells-rule/item-field", cells("", "k: k::configuration::KCell(Cmd::Hold { x: k::rewrite!(x => ()) }, ..)")),
        ("cells-rule/other-term", cells("\n    a: Int,", &format!("{removal}, acc: k::configuration::Cell(k::rewrite!(a => true))"))),
        ("cells-rule/parametric-field", cells("", "k: k::configuration::KCell(Cmd::Make { x }, Duo { a: k::rewrite!(x => ()), b: 1 }, ..)")),
        ("cells-context/item-field", cells_context("Cmd::Hold { x: k::rewrite!(h => ()) }")),
        ("term-rule/field", term("x: Int,", "Cmd::Hold { x: k::rewrite!(x => ()) }")),
        ("term-rule/parametric-field", term("x: Int,", "Cmd::Wrap { s: Duo { a: k::rewrite!(x => ()), b: 1 } }")),
        ("term-rule/other-term", term("x: Int,", "Cmd::Hold { x: k::rewrite!(x => true) }")),
        ("term-rule/root", term("x: Int,", "k::rewrite!(Cmd::Make { x } => ())")),
        ("term-context/field", term_context("Cmd::Hold { x: k::rewrite!(h => ()) }")),
        ("equation", format!("{fixture}#[k::function(total)]\npub fn Peek(a: k::Term<Int>) -> k::Term<Int>;\n\n#[k::equation]\nfn peek(a: Int, k::term![Peek(k::rewrite!(a => ()))]: k::Term<Int>) -> k::Term<Int> {{\n    a\n}}\n")),
        ("readable-rule", format!("{fixture}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    make: {{ k: [k::rewrite!(Make {{ x }} => ()), ..] }} => {{ k: [..] }};\n}}\n")),
    ]
    .map(|(name, source)| {
        let manifest = library_package(temporary.path(), &format!("dot-k-{}", name.replace('/', "-")), &source);
        format!("{name}: {}", first_error(target.path(), &manifest))
    });
    expect_test::expect![[r"
        cells-rule/int-leaf: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::make (rule): `()` (.K) of sort K is not admissible at sort Int @ 93:130
        cells-rule/map-leaf: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::make (rule): `()` (.K) of sort K is not admissible at sort Map @ 93:130
        cells-rule/group-child: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::make (rule): `()` (.K) of sort K is not admissible at sort Int @ 93:143
        cells-rule/map-value: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::make (rule): `()` (.K) of sort K is not admissible at sort KRS-FRAMEWORK::KItem (sort) @ 92:140
        cells-rule/item-field: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::make (rule): `()` (.K) of sort K is not admissible at sort Int @ 92:76
        cells-rule/other-term: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::make (rule): literal `true` of sort Bool is not admissible at sort Int @ 93:130
        cells-rule/parametric-field: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::make (rule): `()` (.K) of sort K is not admissible at sort Int @ 92:87
        cells-context/item-field: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::ctx (context): `()` (.K) of sort K is not admissible at sort Int @ 92:76
        term-rule/field: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::make (rule): `()` (.K) of sort K is not admissible at sort Int @ 92:46
        term-rule/parametric-field: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::make (rule): `()` (.K) of sort K is not admissible at sort Int @ 92:55
        term-rule/other-term: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::make (rule): literal `true` of sort Bool is not admissible at sort Int @ 92:46
        term-rule/root: error[krs::syntax::unsupported-rule-pattern]: unsupported rule pattern: a whole-subject `k::rewrite!(from => to)` is an ordinary rule: write `from` as the subject and `to` as the result, or mark the change below the subject's root @ 92:14
        term-context/field: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-NESTED::ctx (context): `()` (.K) of sort K is not admissible at sort Int @ 92:46
        equation: error[krs::syntax::invalid-local-rewrite]: `k::rewrite!` belongs to a single-body rule, which returns `()`; a rule with a result already states the whole after-state @ 93:31
        readable-rule: error[krs::syntax::invalid-local-rewrite]: `k::rewrite!` (K's local =>) marks what changes inside the subject of a single-body rule or the hole of a context, once and outside any local pattern; here it stands in the subject of a readable rule @ 92:17"]].assert_eq(&refused.join("\n"));
    let admitted = [
        ("cells-rule/item", cells("\n    a: Int,", &format!("{removal}, acc: k::configuration::Cell(k::rewrite!(a => x))"))),
        ("cells-rule/k-field", cells("\n    b: KSequence,", "acc: k::configuration::Cell(x), k: k::configuration::KCell(Cmd::Keep { body: k::rewrite!(b => ()) }, ..)")),
        ("term-rule/k-field", term("b: KSequence,", "Cmd::Keep { body: k::rewrite!(b => ()) }")),
        ("term-rule/parametric-k-field", term("b: KSequence,\n    c: KSequence,", "Cmd::Wrap { s: Duo { a: k::rewrite!(b => ()), b: c } }")),
    ]
    .map(|(name, source)| {
        let manifest = library_package(temporary.path(), &format!("dot-k-{}", name.replace('/', "-")), &source);
        if name.starts_with("term-") {
            // A term-shaped rule carries its label as an attribute.
            let k = emitted_k(target.path(), &manifest);
            let rule = k
                .lines()
                .map(str::trim)
                .find(|line| line.ends_with("[label(make)]"))
                .unwrap_or_else(|| panic!("`make` is emitted:\n{k}"))
                .to_owned();
            format!("{name}: {rule}")
        } else {
            format!("{name}: {}", emitted_sentence(target.path(), &manifest, "make"))
        }
    });
    expect_test::expect![[r"
        cells-rule/item: rule [make]: <k> (make ( X:Int ) => .K) ... </k> <acc> A:Int => X:Int </acc>
        cells-rule/k-field: rule [make]: <acc> X:Int </acc> <k> keep ( (B:K => .K) ) ... </k>
        term-rule/k-field: rule keep ( (B:K => .K) ) [label(make)]
        term-rule/parametric-k-field: rule wrap ( duo ( (B:K => .K) , C:K ) ) [label(make)]"]].assert_eq(&admitted.join("\n"));
    // The admitted field rule runs: `split` and `wrap` turn `make(1)` into `keep(hold(1))`, and
    // `make` empties its field once, `acc` going from 0 to 1.
    let manifest = library_package(
        temporary.path(),
        "dot-k-run",
        &format!(
            "{fixture}#[k::rule(label = \"make\")]\npub fn make(\n    b: KSequence,\n    k::cells! {{ k: k::configuration::KCell(Cmd::Keep {{ body: k::rewrite!(b => ()) }}, ..), acc: k::configuration::Cell(k::rewrite!(0 => 1)), .. }}: Machine,\n) {{}}\n\nk::rules! {{\n    for Stmt;\n    use Cmd::*;\n    split: Make {{ x }} => k::k![Hold {{ x }}, Hold {{ x }}];\n}}\n\n#[k::rule(label = \"wrap\")]\npub fn wrap(\n    k::cells! {{ k: k::configuration::KCell(Cmd::Hold {{ x: _ }}, rest @ ..), .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(Cmd::Keep {{ body: rest }}), .. }}\n}}\n"
        ),
    );
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "make(1)").unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{stdout}\n{stderr}");
    expect_test::expect!["<generatedTop> <k> keep(.K) ~> .K </k> <acc> 1 </acc> <frame> <pc> 0 </pc> <gas> 0 </gas> </frame> <env> .Map </env> <lst> .List </lst> .OptCell .OmapCell <objs> .ObjCellMap </objs> </generatedTop>"].assert_eq(&stdout.split_whitespace().collect::<Vec<_>>().join(" "));
}
