//! Bracket notation for K's builtin `List` end to end: at a `List` position
//! brackets are the list of their elements, `[a, ..mid, z]` the term
//! `ListItem(a) mid ListItem(z)`, with at most one rest anywhere. A package
//! written with brackets emits exactly the K of the same package written with
//! the `list::item`/`list::concat` terms they denote, in a function body and
//! its `match` arms, `k::equations!` rows, a constructor field, a function
//! argument, `k::term!`, readable records, a readable claim, and a `cells!`
//! claim; a closed list is its items, without `.List`. A readable record's
//! anonymous `..` is one shared rest wherever it stands, the rules run
//! natively, a stdin read keeps its shape, `krs expand` writes the explicit
//! terms, and malformed lists are errors.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A package with one placeholder `{NAME}` per list; [`SPELLINGS`] fills each
/// with brackets or with the explicit terms they denote.
const SOURCE: &str = r#"
use k::builtin::{Int, KSequence, List, int, list};
use k::{KItem, KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Pop, Last, Swap, Rot, Push, Log, Clear, Wrap) > right seq (Seq))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("pop")] Pop(),
    #[k::syntax("last")] Last(),
    #[k::syntax("swap")] Swap(),
    #[k::syntax("rot")] Rot(),
    #[k::syntax("push({v})")] Push { v: Int },
    #[k::syntax("log({v})")] Log { v: Int },
    #[k::syntax("clear")] Clear(),
    #[k::syntax("wrap({items})")] Wrap { items: List },
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub queue: List<Int>,
    #[k::cell]
    pub logs: List<Int>,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "QUEUE")] queue: List<Int>,
    ) -> Self {
        Self { k: k::k![pgm], queue, logs: list::empty(), acc: 0 }
    }
}

#[k::function(total, internal)]
pub fn Pair(a: Term<Int>, b: Term<Int>) -> Term<List> {
    {PAIR}
}

#[k::function(total, internal)]
pub fn LastOf(l: Term<List>) -> Term<Int> {
    match l {
        {LAST_ARM} => z,
        _ => 0,
    }
}

#[k::function(total, internal)]
pub fn Ends(l: Term<List>) -> Term<Int> {
    match l {
        {ENDS_ARM} => int::add(a, z),
        _ => 0,
    }
}

#[k::function(partial, internal)]
pub fn FirstOf(l: Term<List>) -> Term<Int>;

k::equations! {
    for FirstOf;
    first_of: ({FIRST_ROW}) => x;
}

#[k::function(total, internal)]
pub fn Wrapped(v: Term<Int>) -> Term<Stmt> {
    Cmd::Wrap { items: {WRAPPED} }
}

#[k::function(total, internal)]
pub fn Around(v: Term<Int>, l: Term<List>) -> Term<Int> {
    Ends({AROUND})
}

#[k::function(total, internal)]
pub fn Triple(v: Term<Int>) -> Term<List> {
    k::term![{TRIPLE}]
}

k::rules! {
    for Stmt;
    use Cmd::*;
    seq: Seq(s1, s2) => k::k![s1, s2];
}

k::rules! {
    for Machine;
    use Cmd::*;

    pop: { k: [Pop(), ..], queue: {POP_BEFORE}, acc: _ } => { k: [..], queue: rest, acc: v };
    last: { k: [Last(), ..], queue: {LAST_BEFORE}, acc: _ } => { k: [..], queue: rest, acc: v };
    swap: { k: [Swap(), ..], queue: {SWAP_BEFORE} } => { k: [..], queue: {SWAP_AFTER} };
    rot: { k: [Rot(), ..], queue: {ROT_BEFORE} } => { k: [..], queue: {ROT_AFTER} };
    push: { k: [Push(v), ..], queue: q } => { k: [..], queue: {PUSHED} };
    log: { k: [Log(e), ..], logs } => { k: [..], logs: {LOGGED} };
    clear: { k: [Clear(), ..], queue: {ONE} } => { k: [..], queue: {EMPTY} };
}

k::claims! {
    for Machine;
    use Cmd::*;

    #[k::claim(all_paths)]
    pop_claim: { k: [Pop()], queue: {CLAIM_BEFORE}, acc: _ } => { k: [], queue: {CLAIM_AFTER}, acc: 1 };
}

#[k::claim(all_paths, label = "rot-claim")]
fn rot_claim(
    k::cells! {
        k: k::configuration::KCell(Cmd::Rot()),
        queue: k::configuration::Cell({CELLS_BEFORE}),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        queue: k::configuration::Cell({CELLS_AFTER}),
        ..state
    }
}
"#;

/// Each placeholder of [`SOURCE`], the explicit terms it is written with,
/// and the brackets that denote them.
const SPELLINGS: &[(&str, &str, &str)] = &[
    (
        "PAIR",
        "list::concat(list::item(a), list::item(b))",
        "[a, b]",
    ),
    ("LAST_ARM", "list::concat(_, list::item(z))", "[.., z]"),
    (
        "ENDS_ARM",
        "list::concat(list::item(a), list::concat(_, list::item(z)))",
        "[a, .., z]",
    ),
    ("FIRST_ROW", "list::concat(list::item(x), _)", "[x, ..]"),
    (
        "WRAPPED",
        "list::concat(list::item(v), list::item(1))",
        "[v, 1]",
    ),
    (
        "AROUND",
        "list::concat(list::item(v), list::concat(l, list::item(v)))",
        "[v, ..l, v]",
    ),
    (
        "TRIPLE",
        "list::concat(list::item(v), list::concat(list::item(2), list::item(v)))",
        "[v, 2, v]",
    ),
    (
        "POP_BEFORE",
        "list::concat(list::item(v), rest)",
        "[v, rest @ ..]",
    ),
    (
        "LAST_BEFORE",
        "list::concat(rest, list::item(v))",
        "[rest @ .., v]",
    ),
    (
        "SWAP_BEFORE",
        "list::concat(list::item(a), list::concat(mid, list::item(z)))",
        "[a, mid @ .., z]",
    ),
    (
        "SWAP_AFTER",
        "list::concat(list::item(z), list::concat(mid, list::item(a)))",
        "[z, ..mid, a]",
    ),
    (
        "ROT_BEFORE",
        "list::concat(list::item(a), rest)",
        "[a, rest @ ..]",
    ),
    (
        "ROT_AFTER",
        "list::concat(rest, list::item(a))",
        "[..rest, a]",
    ),
    ("PUSHED", "list::concat(list::item(v), q)", "[v, ..q]"),
    ("LOGGED", "list::concat(logs, list::item(e))", "[..logs, e]"),
    ("ONE", "list::item(_)", "[_]"),
    ("EMPTY", "list::empty()", "[]"),
    (
        "CLAIM_BEFORE",
        "list::concat(list::item(1), list::concat(list::item(2), list::item(3)))",
        "[1, 2, 3]",
    ),
    (
        "CLAIM_AFTER",
        "list::concat(list::item(2), list::item(3))",
        "[2, 3]",
    ),
    (
        "CELLS_BEFORE",
        "list::concat(list::item(1), list::item(2))",
        "[1, 2]",
    ),
    (
        "CELLS_AFTER",
        "list::concat(list::item(2), list::item(1))",
        "[2, 1]",
    ),
];

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes the package `name` with `source`.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(
        directory.join("src/lib.rs"),
        format!("#![allow(unused_imports)]\n{source}"),
    )
    .unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-LIST-BRACKETS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// [`SOURCE`] with each placeholder written as brackets or as the explicit
/// terms.
fn spelled(brackets: bool) -> String {
    SPELLINGS
        .iter()
        .fold(SOURCE.to_owned(), |source, (name, explicit, bracket)| {
            let placeholder = format!("{{{name}}}");
            assert!(source.contains(&placeholder), "{placeholder} is unused");
            source.replace(&placeholder, if brackets { bracket } else { explicit })
        })
}

/// The emitted `.k` files of a package, the definition and its spec
/// module, by name.
fn definition_k(target: &Path, root: &Path, name: &str, source: &str) -> String {
    let manifest = package(root, name, source);
    let output = root.join("emitted");
    let (success, _, stderr) = krs(
        target,
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let mut files = fs::read_dir(&output)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "k"))
        .collect::<Vec<_>>();
    files.sort();
    files.iter().fold(String::new(), |mut emitted, path| {
        let name = path.file_name().unwrap().to_string_lossy();
        writeln!(emitted, "// {name}").unwrap();
        emitted.push_str(&fs::read_to_string(path).unwrap());
        emitted
    })
}

#[test]
fn brackets_emit_the_k_of_the_list_terms_they_denote() {
    let target = shared_fixture_target();
    let explicit = temp_dir();
    let brackets = temp_dir();
    let explicit_k = definition_k(target.path(), explicit.path(), "lists", &spelled(false));
    let bracket_k = definition_k(target.path(), brackets.path(), "lists", &spelled(true));
    assert_eq!(bracket_k, explicit_k);
    for sentence in [
        "rule pair ( A:Int , B:Int ) => ListItem(A:Int) ListItem(B:Int)",
        "rule lastOf ( _ ListItem(Z:Int) ) => Z:Int",
        "rule ends ( ListItem(A:Int) _ ListItem(Z:Int) ) => A:Int +Int Z:Int",
        "rule firstOf ( ListItem(X:Int) _ ) => X:Int",
        "rule wrapped ( V:Int ) => wrap ( ListItem(V:Int) ListItem(1) )",
        "rule around ( V:Int , L:List ) => ends ( ListItem(V:Int) L:List ListItem(V:Int) )",
        "rule triple ( V:Int ) => ListItem(V:Int) ListItem(2) ListItem(V:Int)",
        "<queue> Rest:List ListItem(V:Int) => Rest:List </queue>",
        "<queue> ListItem(A:Int) Mid:List ListItem(Z:Int) => ListItem(Z:Int) Mid:List ListItem(A:Int) </queue>",
        "<queue> ListItem(A:Int) Rest:List => Rest:List ListItem(A:Int) </queue>",
        "<logs> Logs:List => Logs:List ListItem(E:Int) </logs>",
        "<queue> ListItem(_) => .List </queue>",
        "<queue> ListItem(1) ListItem(2) ListItem(3) => ListItem(2) ListItem(3) </queue>",
        "<queue> ListItem(1) ListItem(2) => ListItem(2) ListItem(1) </queue>",
    ] {
        assert!(bracket_k.contains(sentence), "{sentence}:\n{bracket_k}");
    }
}

/// A readable record's anonymous `..` on a `List` cell is one rest, the same
/// on both sides wherever each side holds it.
const ANONYMOUS: &str = r"
k::rules! {
    for Machine;
    use Cmd::*;

    pop: { k: [Pop(), ..], queue: [v, ..], acc: _ } => { k: [..], queue: [..], acc: v };
    last: { k: [Last(), ..], queue: [.., v], acc: _ } => { k: [..], queue: [..], acc: v };
    swap: { k: [Swap(), ..], queue: [a, .., z] } => { k: [..], queue: [z, .., a] };
    rot: { k: [Rot(), ..], queue: [a, ..] } => { k: [..], queue: [.., a] };
    push: { k: [Push(v), ..], queue: q } => { k: [..], queue: [v, ..q] };
    log: { k: [Log(e), ..], logs } => { k: [..], logs: [..logs, e] };
    clear: { k: [Clear(), ..], queue: [_] } => { k: [..], queue: [] };
}
";

/// [`SOURCE`] with its machine rules written with anonymous rests.
fn anonymous() -> String {
    let source = spelled(true);
    let start = source.find("k::rules! {\n    for Machine;").unwrap();
    let end = start + source[start..].find("\n}\n").unwrap() + 3;
    format!("{}{ANONYMOUS}{}", &source[..start], &source[end..])
}

#[test]
fn a_record_cells_anonymous_rest_is_one_shared_rest_anywhere() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let definition = definition_k(target.path(), temporary.path(), "lists", &anonymous());
    for sentence in [
        "<queue> ListItem(V:Int) Krs_RestQueue:List => Krs_RestQueue:List </queue>",
        "<queue> Krs_RestQueue:List ListItem(V:Int) => Krs_RestQueue:List </queue>",
        "<queue> ListItem(A:Int) Krs_RestQueue:List ListItem(Z:Int) => ListItem(Z:Int) Krs_RestQueue:List ListItem(A:Int) </queue>",
        "<queue> ListItem(A:Int) Krs_RestQueue:List => Krs_RestQueue:List ListItem(A:Int) </queue>",
    ] {
        assert!(definition.contains(sentence), "{sentence}:\n{definition}");
    }
}

/// The final `queue`, `logs`, and `acc` after `krs run` of `program` on the
/// queue `1 2 3`.
fn run(target: &Path, manifest: &Path, program: &str) -> String {
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, program).unwrap();
    let (success, stdout, stderr) = krs(
        target,
        manifest,
        "run",
        &[
            file.to_str().unwrap(),
            "-c",
            "QUEUE=ListItem(1) ListItem(2) ListItem(3)",
        ],
    );
    assert!(success, "`krs run {program}` failed:\n{stdout}\n{stderr}");
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    let cell = |name: &str| {
        let open = format!("<{name}> ");
        let start = flat
            .find(&open)
            .unwrap_or_else(|| panic!("no <{name}>:\n{stdout}"))
            + open.len();
        let end = start + flat[start..].find(&format!(" </{name}>")).unwrap();
        flat[start..end]
            .replace("ListItem ( ", "")
            .replace(" )", "")
    };
    format!(
        "{program} => queue: {} | logs: {} | acc: {}",
        cell("queue"),
        cell("logs"),
        cell("acc")
    )
}

#[test]
fn the_rules_run_natively() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "lists", &anonymous());
    let runs = [
        "pop",
        "last",
        "swap",
        "rot",
        "push(9) log(4) log(5)",
        "pop pop clear",
    ]
    .map(|program| run(target.path(), &manifest, program));
    expect_test::expect![[r#"
        [
            "pop => queue: 2 3 | logs: .List | acc: 1",
            "last => queue: 1 2 | logs: .List | acc: 3",
            "swap => queue: 3 2 1 | logs: .List | acc: 0",
            "rot => queue: 2 3 1 | logs: .List | acc: 0",
            "push(9) log(4) log(5) => queue: 9 1 2 3 | logs: 4 5 | acc: 0",
            "pop pop clear => queue: .List | logs: .List | acc: 2",
        ]
    "#]]
    .assert_debug_eq(&runs);
}

#[test]
fn the_claims_are_proven() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "lists", &spelled(true));
    let (success, stdout, stderr) = krs(target.path(), &manifest, "prove", &[]);
    assert!(success, "{stdout}\n{stderr}");
    assert!(
        format!("{stdout}{stderr}").contains("2 of 2 claims proven"),
        "{stdout}\n{stderr}"
    );
}

#[test]
fn expand_writes_the_list_terms_brackets_denote() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "lists", &anonymous());
    let (success, stdout, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let start = stdout
        .find("pub fn swap(")
        .expect("the readable rule is written");
    let start = stdout[..start].rfind("#[k::rule(").unwrap();
    let end = start + stdout[start..].find("\n}\n").unwrap() + 3;
    expect_test::expect![[r#"
        #[k::rule(label = "swap")]
        pub fn swap(
            a: k::Term<k::builtin::Int>,
            rest: k::Term<k::builtin::List>,
            z: k::Term<k::builtin::Int>,
            k::cells! {
                k : k::configuration::KCell(crate ::Cmd::Swap(), tail @ ..), queue :
                k::configuration::Cell(k::builtin::list::concat(k::builtin::list::item(a),
                k::builtin::list::concat(rest, k::builtin::list::item(z)))), state @ ..
            }: crate::Machine,
        ) -> crate::Machine {
            k::cells! {
                k : k::configuration::KCell(..tail), queue :
                k::configuration::Cell(k::builtin::list::concat(k::builtin::list::item(z),
                k::builtin::list::concat(rest, k::builtin::list::item(a)))), ..state
            }
        }
    "#]]
    .assert_eq(&stdout[start..end]);
    let start = stdout.find("fn first_of(").unwrap();
    let end = start + stdout[start..].find("\n}\n").unwrap() + 3;
    expect_test::expect![[r"
        fn first_of(
            k::term![
                crate ::FirstOf(k::builtin::list::concat(k::builtin::list::item(x), _))
            ]: k::Term<k::builtin::Int>,
        ) -> k::Term<k::builtin::Int> {
            x
        }
    "]]
    .assert_eq(&stdout[start..end]);
}

/// The first `error[..]` headline and its message of `krs check` on a
/// package whose last item is `item`.
fn check_error(target: &Path, item: &str) -> String {
    let temporary = temp_dir();
    let source = spelled(true) + item;
    let manifest = package(temporary.path(), "lists", &source);
    let (success, _, stderr) = krs(target, &manifest, "check", &[]);
    assert!(!success, "{item} was accepted");
    stderr
        .lines()
        .find(|line| line.starts_with("error["))
        .unwrap_or_else(|| panic!("no error headline:\n{stderr}"))
        .to_owned()
}

#[test]
fn malformed_lists_are_errors() {
    let target = shared_fixture_target();
    let errors = [
        // One rest per bracket, in patterns and results.
        "#[k::function(total, internal)]
         pub fn Both(l: Term<List>) -> Term<Int> { match l { [a, .., b, ..] => a + b, _ => 0 } }",
        "#[k::function(total, internal)]
         pub fn Join(a: Term<List>, b: Term<List>) -> Term<List> { [..a, ..b] }",
        "#[k::function(total, internal)]
         pub fn Any(l: Term<List>) -> Term<Int> { match l { [..] => 1 } }",
        // A position whose sort is no list.
        "#[k::function(total, internal)]
         pub fn NotAList(n: Term<Int>) -> Term<Int> { k::term![[n, n]] }",
        // The computation cell is matched from its front.
        "k::rules! {
             for Machine;
             back: { k: [.., Cmd::Pop()] } => { k: [..] };
         }",
    ]
    .map(|item| check_error(target.path(), item));
    expect_test::expect![[r#"
        [
            "error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`",
            "error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`",
            "error[krs::syntax::invalid-list-notation]: `[..]` and `[rest @ ..]` name no element: the first matches any list, so write `_`, and the second is the binder `rest` itself",
            "error[krs::analysis::invalid-list-notation]: list notation builds a list, but this position has sort `Int`, which is not one: a list is the builtin `List`, a `#[k::syntax_list]` sort, or the sort of a `#[k::cons_list]` constructors enum",
            "error[krs::collect::invalid-configuration]: `..` may only end the computation cell `k`'s items: it is matched from its front, the next step first, so name the items before the rest",
        ]
    "#]].assert_debug_eq(&errors);
}

/// A bracketed value that reads both as a List collection's instances and as
/// list elements is read by the cell's declared type: on a `List` leaf cell
/// its records are constructor patterns, the list's elements.
#[test]
fn records_on_a_list_leaf_are_elements() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let source = r#"
use k::builtin::{Int, KSequence, List, list};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("entry({a})")] Entry { a: Int },
    #[k::syntax("back")] Back(),
    #[k::syntax("front")] Front(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub entries: List<Stmt>,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm], entries: list::empty(), acc: 0 }
    }
}

k::rules! {
    for Machine;
    use Cmd::*;

    back: { k: [Back(), ..], entries: [.., Entry { a: x }], acc: _ } => { k: [..], entries: [..], acc: x };
    front: { k: [Front(), ..], entries: [first @ Entry { a: x }, ..], acc: _ } => { k: [first, ..], entries: [..], acc: x };
}
"#;
    let definition = definition_k(target.path(), temporary.path(), "entries", source);
    for sentence in [
        "<entries> Krs_RestEntries:List ListItem(entry ( X:Int )) => Krs_RestEntries:List </entries>",
        "<entries> ListItem(( entry ( X:Int ) #as First:Stmt )) Krs_RestEntries:List => Krs_RestEntries:List </entries>",
    ] {
        assert!(definition.contains(sentence), "{sentence}:\n{definition}");
    }
}
