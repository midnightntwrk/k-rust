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
    fs::read_to_string(output.join("definition.k")).unwrap()
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
    unhold: {{ k: [{held}, ..], frame: Frame {{ gas: g }} }} => {{
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
            <stack> ListItem(<frame> <pc> P:Int </pc> <gas> Krs_UpdateSavedGas:Int </gas> </frame>) S:List => ListItem(<frame> <pc> P:Int +Int 1 </pc> <gas> Krs_UpdateSavedGas:Int </gas> </frame>) ListItem(F:FrameCell) S:List </stack>
            F:FrameCell"]]
    .assert_eq(rule(&k, "swap"));
    expect_test::expect![[r"
        rule [unhold]:
            <k> held ( <frame> <pc> P:Int </pc> <gas> _ </gas> </frame> ) => .K ... </k>
            (<frame> <pc> _ </pc> <gas> G:Int </gas> </frame> => <frame> <pc> P:Int </pc> <gas> G:Int </gas> </frame>)"]]
    .assert_eq(rule(&k, "unhold"));
}

/// A group record as a value is a complete cell term: a pattern leaves a
/// child unconstrained only with `..`, while a record at a configuration
/// cell's own position (`frame: Frame { gas: g }` above, or a group nested
/// in one, see [`a_group_record_may_omit_children_where_it_matches_a_configuration_cell`])
/// may omit children silently.
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
/// naming only `pc`; with `rest`, the inner record ends in `..`.
fn omitting(rest: bool) -> String {
    let frame = if rest {
        "Frame { pc: p, .. }"
    } else {
        "Frame { pc: p }"
    };
    format!(
        r"
k::rules! {{
    for Machine;
    use Cmd::*;

    look: {{ k: [Look(), ..], outer: Outer {{ frame: {frame}, flag: f }} }} => {{ k: [int::add(p, f), ..] }};
    report: {{ k: [Report(), ..], stack: s, outer: o @ Outer {{ frame: {frame} }} }} => {{ k: [p, ..], stack: [o, ..s] }};
}}

k::claims! {{
    for Machine;
    use Cmd::*;

    #[k::claim(all_paths)]
    looks: {{ k: [Look()], outer: Outer {{ frame: {frame}, flag: f }} }} => {{ k: [int::add(p, f)] }};
}}
"
    )
}

/// Where a group record matches a cell of the running configuration, it
/// may omit children: the value of the entry that names the group, and
/// each fixed group child of a record there (`frame` inside `outer`), which
/// is the configuration's `<frame>` reached through `outer`. Everywhere
/// else (a `KItem` leaf cell's content, a list element, a group nested in
/// a value) the record is a value and complete, and `k::fragment!` is
/// exact at every position (U5).
#[test]
fn a_group_record_may_omit_children_where_it_matches_a_configuration_cell() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let emitted = |name: &str, rest: bool| {
        let manifest = library_package(
            temporary.path(),
            name,
            &format!("{TWO_LEVEL}{}", omitting(rest)),
        );
        let output = manifest.with_file_name("emitted");
        let (success, _, stderr) = krs(
            target.path(),
            &manifest,
            "emit-k",
            &["--output", output.to_str().unwrap()],
        );
        assert!(success, "{stderr}");
        ["definition.k", "spec.k"].map(|file| fs::read_to_string(output.join(file)).unwrap())
    };
    let lenient = emitted("omitting", false);
    assert_eq!(lenient, emitted("rest", true));
    expect_test::expect![[r"
        rule [look]:
            <k> look => P:Int +Int F:Int ... </k>
            <outer> <frame> <pc> P:Int </pc> <gas> _ </gas> </frame> <flag> F:Int </flag> </outer>
        rule [report]:
            <k> report => P:Int ... </k>
            <stack> S:List => ListItem(<outer> <frame> <pc> P:Int </pc> <gas> Krs_UpdateOFrameGas:Int </gas> </frame> <flag> Krs_UpdateOFlag:Int </flag> </outer>) S:List </stack>
            <outer> <frame> <pc> P:Int </pc> <gas> Krs_UpdateOFrameGas:Int </gas> </frame> <flag> Krs_UpdateOFlag:Int </flag> </outer>"]]
    .assert_eq(&format!("{}\n{}", rule(&lenient[0], "look"), rule(&lenient[0], "report")));

    let errors = [
        "slot: { k: [Look(), ..], slot: Frame { pc: p } } => { k: [p, ..] };",
        "value: { k: [Look(), ..], stack: [Outer { frame: Frame { pc: p }, .. }, ..] } => { k: [p, ..] };",
        "fragment: { k: [Look(), ..], frame: k::fragment![Frame { pc: p }] } => { k: [p, ..] };",
    ]
    .map(|clause| {
        let label = &clause[..clause.find(':').unwrap()];
        let manifest = library_package(
            temporary.path(),
            &format!("strict-{label}"),
            &format!("{TWO_LEVEL}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    {clause}\n}}\n"),
        );
        check_errors(target.path(), &manifest)
    });
    for error in &errors {
        assert!(
            error.contains("krs::analysis::invalid-term")
                && error.contains("must name every child field exactly once"),
            "{error}"
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
