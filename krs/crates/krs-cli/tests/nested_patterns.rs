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
            "cells-entry: error[krs::syntax::invalid-state-macro]: invalid `cells!` payload: nested cell entries are a binder, `_`, or fragment!",
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

/// EDOTS item 1: the record a result's entry writes for a group that is there, matched or
/// overwritten, means by its `..` that the children it leaves unnamed are unchanged, so it
/// writes only the children it names, each as its own cell: `frame: Frame { pc: x, .. }` is
/// `<pc> _ => X </pc>`, `<gas>` as it was. Readable rules, claims and `cells!` rules agree, and
/// the bare record and its fragment are one record. Two places have no lowering yet and refuse
/// with what the `..` means there: beside a subject that matches the group whole, and where the
/// result writes the group whole (a `?` group's `Some(..)`, an updated instance's group child).
/// A group the result creates keeps its own stated limit
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
        ]
    "#]].assert_debug_eq(&admitted);
    let refused = [
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
        let manifest = library_package(temporary.path(), &format!("kept-refused-{name}"), &source);
        (name, first_error(target.path(), &manifest))
    });
    expect_test::expect![[r#"
        [
            (
                "binder",
                "error[krs::syntax::invalid-record-update]: the result's record of the group `frame` leaves children unnamed with `..`, which there keep their content, so it writes only the children it names, each as its own cell; the subject matches the group whole, as a binder or an alias, and writing some of its children beside that match is not supported yet: match the group with a record of its children, or update the matched record with `..base` @ 100:66",
            ),
            (
                "alias",
                "error[krs::syntax::invalid-record-update]: the result's record of the group `frame` leaves children unnamed with `..`, which there keep their content, so it writes only the children it names, each as its own cell; the subject matches the group whole, as a binder or an alias, and writing some of its children beside that match is not supported yet: match the group with a record of its children, or update the matched record with `..base` @ 100:88",
            ),
            (
                "child-binder",
                "error[krs::syntax::invalid-record-update]: the result's record of the group `inner` leaves children unnamed with `..`, which there keep their content, so it writes only the children it names, each as its own cell; the subject matches the group whole, as a binder or an alias, and writing some of its children beside that match is not supported yet: match the group with a record of its children, or update the matched record with `..base` @ 100:102",
            ),
            (
                "optional-present",
                "error[krs::syntax::invalid-record-update]: the result's record of the group `ogroup` leaves children unnamed with `..`, which there keep their content; it stands where the result writes the group whole, as one term naming every child (an optional group's `Some(..)`, an instance record's group child), which has no form yet for children that keep their content: name every child, or take the others from a matched record with `..base` @ 100:94",
            ),
            (
                "cells-optional-present",
                "error[krs::syntax::invalid-record-update]: the result's record of the group `ogroup` leaves children unnamed with `..`, which there keep their content; it stands where the result writes the group whole, as one term naming every child (an optional group's `Some(..)`, an instance record's group child), which has no form yet for children that keep their content: name every child, or take the others from a matched record with `..base` @ 102:66",
            ),
            (
                "instance-child",
                "error[krs::syntax::invalid-record-update]: the result's record of the group `aframe` leaves children unnamed with `..`, which there keep their content; it stands where the result writes the group whole, as one term naming every child (an optional group's `Some(..)`, an instance record's group child), which has no form yet for children that keep their content: name every child, or take the others from a matched record with `..base` @ 100:111",
            ),
        ]
    "#]].assert_debug_eq(&refused);
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
