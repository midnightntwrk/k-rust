//! An instance child is a cell, so its brackets in a pattern mean what they mean at a cell of
//! the child's kind outside every instance: a builtin `List` child's `[.., x]` and `[x, .., y]`
//! match its back, a named rest (`[r @ .., x]`) binds the list it matches, a computation child
//! refuses an item after its rest or a named one, a `Set` child refuses brackets, and a second
//! rest is refused as at its own cell. The verdict is the same whether the collection's instances
//! are written in braces (a Map collection) or brackets (a List collection), in a rule, a claim
//! and a `k::patterns!` step, and an instance rule matching a list child's back runs.
//!
//! A result that keeps such a child's unnamed rest, `[..]` or `[y, ..]` over a subject
//! `[.., x]`, or over an aliased `l @ [x, ..]`, is a stated limit (`collection-entry`): the rest
//! an instance child keeps is the one its subject's own brackets end with. A named rest is kept
//! by its name, `[r @ .., x]` then `[x, ..r]`, as at the child's own cell.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A machine with a Map collection `th` and a List collection `job` whose instances hold a
/// builtin `List`, a computation and a `Set` child, and top cells of the same kinds (`ll`, `aux`,
/// `ss`); `{SENTENCES}` is the sentences under test.
const SOURCE: &str = r#"
use k::KResult;
use k::builtin::{Int, KSequence, List, Set, list, set};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Go, Open, Push, Last) > right seq (Seq))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("open {n}")] Open { n: Int },
    #[k::syntax("push {n}")] Push { n: Int },
    #[k::syntax("last")] Last(),
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::cell]
pub struct Th {
    #[k::cell]
    pub tid: Int,
    #[k::cell]
    pub tl: List,
    #[k::cell]
    pub tk: KSequence,
    #[k::cell]
    pub ts: Set,
}

#[k::cell]
pub struct Ths {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub th: Th,
}

#[k::cell]
pub struct Job {
    #[k::cell]
    pub jl: List,
    #[k::cell]
    pub jk: KSequence,
    #[k::cell]
    pub js: Set,
}

#[k::cell]
pub struct Jobs {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub job: Job,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub ll: List,
    #[k::cell]
    pub aux: KSequence,
    #[k::cell]
    pub ss: Set,
    #[k::cell]
    pub out: List,
    #[k::cell(nested)]
    pub ths: Ths,
    #[k::cell(nested)]
    pub jobs: Jobs,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            ll: list::empty(),
            aux: k::k![],
            ss: set::empty(),
            out: list::empty(),
            ths: Ths { th: Th { tid: 0, tl: list::empty(), tk: k::k![], ts: set::empty() } },
            jobs: Jobs { job: Job { jl: list::empty(), jk: k::k![], js: set::empty() } },
        }
    }
}

k::rules! {
    for Stmt;
    use Cmd::*;

    seq: Seq(s1, s2) => k::k![s1, s2];
}

{SENTENCES}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is [`SOURCE`] with `sentences`.
fn package(root: &Path, name: &str, sentences: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(
        directory.join("src/lib.rs"),
        SOURCE.replace("{SENTENCES}", sentences),
    )
    .unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CHILD-SEQUENCES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The verdict on one sentence `go`, written as a rule or, with `claim`, as an all-paths claim:
/// the emitted sentence on one line, or the first error line.
fn verdict(target: &Path, root: &Path, name: &str, clause: &str, claim: bool) -> String {
    let (kind, attribute) = if claim {
        ("claims", "#[k::claim(all_paths)] ")
    } else {
        ("rules", "")
    };
    let sentences = format!(
        "k::{kind}! {{\n    for Machine;\n    use Cmd::*;\n\n    {attribute}{clause}\n}}\n"
    );
    let manifest = package(root, name, &sentences);
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    if !success {
        return stderr
            .lines()
            .find(|line| line.starts_with("error["))
            .unwrap_or_else(|| panic!("no error headline:\n{stderr}"))
            .to_owned();
    }
    let file = if claim { "spec.k" } else { "definition.k" };
    let k =
        krs_test_support::without_source_comments(&fs::read_to_string(output.join(file)).unwrap());
    let head = if claim { "claim [go]:" } else { "rule [go]:" };
    let start = k
        .find(head)
        .unwrap_or_else(|| panic!("`go` is emitted:\n{k}"));
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

/// The class of a verdict: the error's code, or `accepted`.
fn class(verdict: &str) -> &str {
    verdict
        .strip_prefix("error[")
        .and_then(|rest| rest.split_once(']'))
        .map_or("accepted", |(code, _)| code)
}

/// For each child kind and pattern shape, the instance child's verdict in braces (a Map
/// collection) and in brackets (a List collection) is its twin's, the same spelling at a top cell
/// of the same kind: the class always, and where accepted the same match of the child's content.
/// A second rest leaves its item unused, as a twin that reads it has no other verdict. A named
/// rest is the child's rest bound to a name, matched where it stands.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of every kind and shape against its twin, its expectation inline."
)]
fn an_instance_child_s_brackets_are_judged_as_its_cell_s() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let shapes = [
        ("back", "[.., x]", ", out: _", ", out: [x]"),
        ("ends", "[x, .., y]", ", out: _", ", out: [x, y]"),
        ("mid", "[.., x, ..]", "", ""),
        ("named-back", "[r @ .., x]", ", out: _", ", out: [x]"),
        ("named-ends", "[x, r @ .., y]", ", out: _", ", out: [x, y]"),
        ("named-front", "[x, r @ ..]", ", out: _", ", out: [x]"),
        ("named-mid", "[r @ .., x, ..]", "", ""),
    ];
    // (kind, Map child, List child, twin cell)
    let kinds = [
        ("list", "tl", "jl", "ll"),
        ("computation", "tk", "jk", "aux"),
        ("set", "ts", "js", "ss"),
    ];
    let mut table = Vec::new();
    for (kind, map_child, list_child, twin) in kinds {
        for (shape, value, subject_out, result_out) in shapes {
            // The twin rewrites no other computation, so its brackets are its own cell's.
            let twin_clause = if twin == "aux" {
                format!("go: {{ aux: {value}{subject_out} }} => {{ aux: [..]{result_out} }};")
            } else {
                format!(
                    "go: {{ k: [Go(), ..], {twin}: {value}{subject_out} }} => {{ k: [..]{result_out} }};"
                )
            };
            let braces = format!(
                "go: {{ k: [Go(), ..], th: {{ Th {{ {map_child}: {value}, .. }}, .. }}{subject_out} }} => {{ k: [..]{result_out} }};"
            );
            let brackets = format!(
                "go: {{ k: [Go(), ..], job: [Job {{ {list_child}: {value}, .. }}, ..]{subject_out} }} => {{ k: [..]{result_out} }};"
            );
            let row = format!("{kind}-{shape}");
            let twin_verdict = verdict(
                target.path(),
                temporary.path(),
                &format!("twin-{row}"),
                &twin_clause,
                false,
            );
            let braces_verdict = verdict(
                target.path(),
                temporary.path(),
                &format!("braces-{row}"),
                &braces,
                false,
            );
            let brackets_verdict = verdict(
                target.path(),
                temporary.path(),
                &format!("brackets-{row}"),
                &brackets,
                false,
            );
            assert_eq!(
                class(&braces_verdict),
                class(&twin_verdict),
                "{row} in braces: {braces_verdict}\ntwin: {twin_verdict}"
            );
            assert_eq!(
                class(&brackets_verdict),
                class(&twin_verdict),
                "{row} in brackets: {brackets_verdict}\ntwin: {twin_verdict}"
            );
            table.push(format!("{row}\n  twin: {twin_verdict}\n  braces: {braces_verdict}\n  brackets: {brackets_verdict}"));
        }
    }
    expect_test::expect![[r"
        list-back
          twin: rule [go]: <k> go => .K ... </k> <ll> Krs_RestLl:List ListItem(X:KItem) </ll> <out> _ => ListItem(X:KItem) </out>
          braces: rule [go]: <k> go => .K ... </k> <th> <tl> _ ListItem(X:KItem) </tl> ... </th> <out> _ => ListItem(X:KItem) </out>
          brackets: rule [go]: <k> go => .K ... </k> <out> _ => ListItem(X:KItem) </out> <jobs> <job> <jl> _ ListItem(X:KItem) </jl> ... </job> ... </jobs>
        list-ends
          twin: rule [go]: <k> go => .K ... </k> <ll> ListItem(X:KItem) Krs_RestLl:List ListItem(Y:KItem) </ll> <out> _ => ListItem(X:KItem) ListItem(Y:KItem) </out>
          braces: rule [go]: <k> go => .K ... </k> <th> <tl> ListItem(X:KItem) _ ListItem(Y:KItem) </tl> ... </th> <out> _ => ListItem(X:KItem) ListItem(Y:KItem) </out>
          brackets: rule [go]: <k> go => .K ... </k> <out> _ => ListItem(X:KItem) ListItem(Y:KItem) </out> <jobs> <job> <jl> ListItem(X:KItem) _ ListItem(Y:KItem) </jl> ... </job> ... </jobs>
        list-mid
          twin: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          braces: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          brackets: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
        list-named-back
          twin: rule [go]: <k> go => .K ... </k> <ll> R:List ListItem(X:KItem) </ll> <out> _ => ListItem(X:KItem) </out>
          braces: rule [go]: <k> go => .K ... </k> <th> <tl> R:List ListItem(X:KItem) </tl> ... </th> <out> _ => ListItem(X:KItem) </out>
          brackets: rule [go]: <k> go => .K ... </k> <out> _ => ListItem(X:KItem) </out> <jobs> <job> <jl> R:List ListItem(X:KItem) </jl> ... </job> ... </jobs>
        list-named-ends
          twin: rule [go]: <k> go => .K ... </k> <ll> ListItem(X:KItem) R:List ListItem(Y:KItem) </ll> <out> _ => ListItem(X:KItem) ListItem(Y:KItem) </out>
          braces: rule [go]: <k> go => .K ... </k> <th> <tl> ListItem(X:KItem) R:List ListItem(Y:KItem) </tl> ... </th> <out> _ => ListItem(X:KItem) ListItem(Y:KItem) </out>
          brackets: rule [go]: <k> go => .K ... </k> <out> _ => ListItem(X:KItem) ListItem(Y:KItem) </out> <jobs> <job> <jl> ListItem(X:KItem) R:List ListItem(Y:KItem) </jl> ... </job> ... </jobs>
        list-named-front
          twin: rule [go]: <k> go => .K ... </k> <ll> ListItem(X:KItem) R:List </ll> <out> _ => ListItem(X:KItem) </out>
          braces: rule [go]: <k> go => .K ... </k> <th> <tl> ListItem(X:KItem) R:List </tl> ... </th> <out> _ => ListItem(X:KItem) </out>
          brackets: rule [go]: <k> go => .K ... </k> <out> _ => ListItem(X:KItem) </out> <jobs> <job> <jl> ListItem(X:KItem) R:List </jl> ... </job> ... </jobs>
        list-named-mid
          twin: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          braces: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          brackets: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
        computation-back
          twin: error[krs::collect::invalid-configuration]: the entry of the computation cell `aux` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it
          braces: error[krs::collect::invalid-configuration]: the entry of the computation cell `tk` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it
          brackets: error[krs::collect::invalid-configuration]: the entry of the computation cell `jk` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it
        computation-ends
          twin: error[krs::collect::invalid-configuration]: the entry of the computation cell `aux` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it
          braces: error[krs::collect::invalid-configuration]: the entry of the computation cell `tk` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it
          brackets: error[krs::collect::invalid-configuration]: the entry of the computation cell `jk` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it
        computation-mid
          twin: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          braces: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          brackets: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
        computation-named-back
          twin: error[krs::analysis::continuation-in-readable]: the readable entry of the computation cell `aux` captures or drops its continuation (with a named rest, a splice, a whole binder, or a result without the subject's `..`): a readable rule keeps the rest of the computation with its anonymous `..`, and a `cells!` rule's `KCell(.., rest @ ..)` is what captures it
          braces: error[krs::analysis::continuation-in-readable]: the readable entry of the computation cell `tk` captures or drops its continuation (with a named rest, a splice, a whole binder, or a result without the subject's `..`): a readable rule keeps the rest of the computation with its anonymous `..`, and a `cells!` rule's `KCell(.., rest @ ..)` is what captures it
          brackets: error[krs::analysis::continuation-in-readable]: the readable entry of the computation cell `jk` captures or drops its continuation (with a named rest, a splice, a whole binder, or a result without the subject's `..`): a readable rule keeps the rest of the computation with its anonymous `..`, and a `cells!` rule's `KCell(.., rest @ ..)` is what captures it
        computation-named-ends
          twin: error[krs::analysis::continuation-in-readable]: the readable entry of the computation cell `aux` captures or drops its continuation (with a named rest, a splice, a whole binder, or a result without the subject's `..`): a readable rule keeps the rest of the computation with its anonymous `..`, and a `cells!` rule's `KCell(.., rest @ ..)` is what captures it
          braces: error[krs::analysis::continuation-in-readable]: the readable entry of the computation cell `tk` captures or drops its continuation (with a named rest, a splice, a whole binder, or a result without the subject's `..`): a readable rule keeps the rest of the computation with its anonymous `..`, and a `cells!` rule's `KCell(.., rest @ ..)` is what captures it
          brackets: error[krs::analysis::continuation-in-readable]: the readable entry of the computation cell `jk` captures or drops its continuation (with a named rest, a splice, a whole binder, or a result without the subject's `..`): a readable rule keeps the rest of the computation with its anonymous `..`, and a `cells!` rule's `KCell(.., rest @ ..)` is what captures it
        computation-named-front
          twin: error[krs::analysis::continuation-in-readable]: the readable entry of the computation cell `aux` captures or drops its continuation (with a named rest, a splice, a whole binder, or a result without the subject's `..`): a readable rule keeps the rest of the computation with its anonymous `..`, and a `cells!` rule's `KCell(.., rest @ ..)` is what captures it
          braces: error[krs::analysis::continuation-in-readable]: the readable entry of the computation cell `tk` captures or drops its continuation (with a named rest, a splice, a whole binder, or a result without the subject's `..`): a readable rule keeps the rest of the computation with its anonymous `..`, and a `cells!` rule's `KCell(.., rest @ ..)` is what captures it
          brackets: error[krs::analysis::continuation-in-readable]: the readable entry of the computation cell `jk` captures or drops its continuation (with a named rest, a splice, a whole binder, or a result without the subject's `..`): a readable rule keeps the rest of the computation with its anonymous `..`, and a `cells!` rule's `KCell(.., rest @ ..)` is what captures it
        computation-named-mid
          twin: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          braces: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          brackets: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
        set-back
          twin: error[krs::analysis::invalid-list-notation]: the cell `ss` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          braces: error[krs::analysis::invalid-list-notation]: the cell `ts` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          brackets: error[krs::analysis::invalid-list-notation]: the cell `js` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
        set-ends
          twin: error[krs::analysis::invalid-list-notation]: the cell `ss` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          braces: error[krs::analysis::invalid-list-notation]: the cell `ts` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          brackets: error[krs::analysis::invalid-list-notation]: the cell `js` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
        set-mid
          twin: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          braces: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          brackets: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
        set-named-back
          twin: error[krs::analysis::invalid-list-notation]: the cell `ss` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          braces: error[krs::analysis::invalid-list-notation]: the cell `ts` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          brackets: error[krs::analysis::invalid-list-notation]: the cell `js` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
        set-named-ends
          twin: error[krs::analysis::invalid-list-notation]: the cell `ss` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          braces: error[krs::analysis::invalid-list-notation]: the cell `ts` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          brackets: error[krs::analysis::invalid-list-notation]: the cell `js` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
        set-named-front
          twin: error[krs::analysis::invalid-list-notation]: the cell `ss` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          braces: error[krs::analysis::invalid-list-notation]: the cell `ts` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          brackets: error[krs::analysis::invalid-list-notation]: the cell `js` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
        set-named-mid
          twin: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          braces: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          brackets: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`"]].assert_eq(&table.join("\n"));
}

/// A claim's subject is read as a rule's: a List child's back is matched, and a computation
/// child's item after its rest refused.
#[test]
fn an_instance_child_s_brackets_in_a_claim_are_judged_as_in_a_rule() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let claims = [
        (
            "claim-list-back",
            "go: { k: [Go(), ..], th: { Th { tl: [.., x], .. }, .. }, out: _ } => { k: [..], out: [x] };",
        ),
        (
            "claim-computation-back",
            "go: { k: [Go(), ..], job: [Job { jk: [.., x], .. }, ..], out: _ } => { k: [..], out: [x] };",
        ),
    ]
    .map(|(name, clause)| {
        format!(
            "{name}: {}",
            verdict(target.path(), temporary.path(), name, clause, true)
        )
    });
    expect_test::expect![[r"
        claim-list-back: claim [go]: <k> go => .K ... </k> <th> <tl> _ ListItem(X:KItem) </tl> ... </th> <out> _ => ListItem(X:KItem) </out>
        claim-computation-back: error[krs::collect::invalid-configuration]: the entry of the computation cell `jk` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it"]].assert_eq(&claims.join("\n"));
}

/// An instance rule that matches the back of its instance's list child runs: `push` puts an
/// element at the front of the list, so `last` reads the first one pushed.
#[test]
fn an_instance_list_child_s_back_is_matched_in_a_run() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rules = r"
k::rules! {
    for Machine;
    use Cmd::*;

    open: { k: [Open(n), ..], th: { .. } } => { k: [..], th: { Th { tid: n, tl: [], tk: [], ts: set::empty() }, .. } };
    push: { k: [Push(n), ..], th: { me @ Th { tl: [..], .. }, .. } } => { k: [..], th: { Th { tl: [n, ..], ..me }, .. } };
    last: { k: [Last(), ..], th: { Th { tl: [.., x], .. }, .. }, out: _ } => { k: [..], out: [x] };
}
";
    let manifest = package(temporary.path(), "run-back", rules);
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "open 1 push 2 push 3 push 4 last\n").unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{stdout}\n{stderr}");
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    let start = flat.find("<out>").unwrap();
    let end = flat.find("</ths>").unwrap() + "</ths>".len();
    expect_test::expect!["<out> ListItem ( 2 ) </out> <ths> <th> <tid> 1 </tid> <tl> ListItem ( 4 ) ListItem ( 3 ) ListItem ( 2 ) </tl> <tk> .K </tk> <ts> .Set </ts> </th> </ths>"].assert_eq(&flat[start..end]);
}

/// A result keeping with `..` the rest of an instance child whose subject matches items after
/// that rest, or matches it below an alias, is the stated limit at the child, by a label or a
/// Map key, in braces and brackets, in a rule and a claim; a named rest is kept by its name, as
/// at the child's own cell.
#[test]
fn a_kept_rest_of_an_instance_child_matched_at_its_back_is_a_stated_limit() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let go = "k: [Go(), ..]";
    let rows = [
        (
            "label-all",
            format!(
                "go: {{ {go}, th: {{ me @ Th {{ tl: [.., x], .. }}, .. }}, out: _ }} => {{ k: [..], th: {{ Th {{ tl: [..], ..me }}, .. }}, out: [x] }};"
            ),
            false,
        ),
        (
            "label-front",
            format!(
                "go: {{ {go}, th: {{ me @ Th {{ tl: [x, .., y], .. }}, .. }}, out: _ }} => {{ k: [..], th: {{ Th {{ tl: [y, ..], ..me }}, .. }}, out: [x] }};"
            ),
            false,
        ),
        (
            "brackets",
            format!(
                "go: {{ {go}, job: [me @ Job {{ jl: [.., x], .. }}, ..], out: _ }} => {{ k: [..], job: [Job {{ jl: [x, ..], ..me }}, ..], out: [x] }};"
            ),
            false,
        ),
        (
            "map-key",
            format!(
                "go: {{ {go}, th: {{ Th {{ tid: i, tl: [.., x], .. }}, .. }}, out: _ }} => {{ k: [..], th: {{ Th {{ tid: i, tl: [x, ..], .. }}, .. }}, out: [x] }};"
            ),
            false,
        ),
        (
            "alias-back",
            format!(
                "go: {{ {go}, th: {{ me @ Th {{ tl: l @ [.., x], .. }}, .. }}, out: _ }} => {{ k: [..], th: {{ Th {{ tl: [..], ..me }}, .. }}, out: [x] }};"
            ),
            false,
        ),
        (
            "alias-front",
            format!(
                "go: {{ {go}, th: {{ me @ Th {{ tl: l @ [x, ..], .. }}, .. }}, out: _ }} => {{ k: [..], th: {{ Th {{ tl: [x, ..], ..me }}, .. }}, out: [x] }};"
            ),
            false,
        ),
        (
            "claim",
            format!(
                "go: {{ {go}, job: [me @ Job {{ jl: [.., x], .. }}, ..], out: _ }} => {{ k: [..], job: [Job {{ jl: [..], ..me }}, ..], out: [x] }};"
            ),
            true,
        ),
        (
            "named",
            format!(
                "go: {{ {go}, th: {{ me @ Th {{ tl: [r @ .., x], .. }}, .. }}, out: _ }} => {{ k: [..], th: {{ Th {{ tl: [x, ..r], ..me }}, .. }}, out: [x] }};"
            ),
            false,
        ),
        (
            "named-twin",
            format!(
                "go: {{ {go}, ll: [r @ .., x], out: _ }} => {{ k: [..], ll: [x, ..r], out: [x] }};"
            ),
            false,
        ),
        (
            "named-brackets",
            format!(
                "go: {{ {go}, job: [me @ Job {{ jl: [x, r @ .., y], .. }}, ..], out: _ }} => {{ k: [..], job: [Job {{ jl: [y, ..r, x], ..me }}, ..], out: [x] }};"
            ),
            false,
        ),
        (
            "named-brackets-twin",
            format!(
                "go: {{ {go}, ll: [x, r @ .., y], out: _ }} => {{ k: [..], ll: [y, ..r, x], out: [x] }};"
            ),
            false,
        ),
    ]
    .map(|(name, clause, claim)| {
        format!(
            "{name}: {}",
            verdict(target.path(), temporary.path(), name, &clause, claim)
        )
    });
    expect_test::expect![[r"
        label-all: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
        label-front: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
        brackets: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `jl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
        map-key: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
        alias-back: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
        alias-front: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
        claim: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `jl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
        named: rule [go]: <k> go => .K ... </k> <th> <tl> R:List ListItem(X:KItem) => ListItem(X:KItem) R:List </tl> ... </th> <out> _ => ListItem(X:KItem) </out>
        named-twin: rule [go]: <k> go => .K ... </k> <ll> R:List ListItem(X:KItem) => ListItem(X:KItem) R:List </ll> <out> _ => ListItem(X:KItem) </out>
        named-brackets: rule [go]: <k> go => .K ... </k> <out> _ => ListItem(X:KItem) </out> <jobs> <job> <jl> ListItem(X:KItem) R:List ListItem(Y:KItem) => ListItem(Y:KItem) R:List ListItem(X:KItem) </jl> ... </job> ... </jobs>
        named-brackets-twin: rule [go]: <k> go => .K ... </k> <ll> ListItem(X:KItem) R:List ListItem(Y:KItem) => ListItem(Y:KItem) R:List ListItem(X:KItem) </ll> <out> _ => ListItem(X:KItem) </out>"]].assert_eq(&rows.join("\n"));
}

/// Each spelling the entry table once could not read, or read past, beside its twin at a top cell
/// of the same kind: a child in parentheses or alternatives, a double alias, alternatives of a
/// computation's item beside a list child's back, an aliased rest kept (the twin's too), a rest
/// the result neither keeps nor names, a result's `..term`, and a result's items after its `..`.
/// Where the result keeps a rest the lowering does not keep, both routes say the stated limit;
/// elsewhere the instance child's verdict is its twin's.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of the review's spellings beside their twins, its expectation inline."
)]
fn every_kept_rest_spelling_of_an_instance_child_is_judged_as_its_twin_s() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let keep = |subject: &str, result: &str| {
        (
            format!(
                "go: {{ k: [Go(), ..], th: {{ me @ Th {{ tl: {subject}, .. }}, .. }}, out: _ }} => {{ k: [..], th: {{ Th {{ tl: {result}, ..me }}, .. }}, out: [x] }};"
            ),
            format!(
                "go: {{ k: [Go(), ..], ll: {subject}, out: _ }} => {{ k: [..], ll: {result}, out: [x] }};"
            ),
        )
    };
    let put = |subject: &str, result: &str| {
        (
            format!(
                "go: {{ k: [Push(a), ..], th: {{ me @ Th {{ tl: {subject}, .. }}, .. }} }} => {{ k: [..], th: {{ Th {{ tl: {result}, ..me }}, .. }} }};"
            ),
            format!("go: {{ k: [Push(a), ..], ll: {subject} }} => {{ k: [..], ll: {result} }};"),
        )
    };
    let rows = [
        ("paren-back", keep("([.., x])", "[..]")),
        ("paren-front", keep("([x, ..])", "[..]")),
        ("paren-exact", keep("([x, ..])", "[x]")),
        ("double-alias", keep("l @ m @ [x, ..]", "[..]")),
        ("alias", keep("l @ [x, ..]", "[..]")),
        ("alternatives", keep("[x, ..] | [x]", "[..]")),
        (
            "item-alternatives",
            (
                "go: { k: [Go(), ..], th: { me @ Th { tk: [Go() | Last(), ..], tl: [.., x], .. }, .. }, out: _ } => { k: [..], th: { Th { tl: [..], ..me }, .. }, out: [x] };".to_owned(),
                "go: { k: [Go() | Last(), ..], ll: [.., x], out: _ } => { k: [..], ll: [..], out: [x] };".to_owned(),
            ),
        ),
        (
            "rest-unkept",
            (
                "go: { k: [Go(), ..], th: { me @ Th { tl: [x, ..], .. }, .. }, out: r } => { k: [..], th: { Th { tl: [x, ..r], ..me }, .. }, out: [x] };".to_owned(),
                "go: { k: [Go(), ..], ll: [x, ..], out: r } => { k: [..], ll: [x, ..r], out: [x] };".to_owned(),
            ),
        ),
        ("splice-term", put("[_, r @ ..]", "[a, ..list::concat(r, r)]")),
        ("items-after-rest", put("[_, ..]", "[.., a]")),
        ("items-around-rest", put("[_, ..]", "[a, .., a]")),
        ("two-rests", put("[_, ..]", "[.., a, ..]")),
        (
            "computation-items-after-rest",
            (
                "go: { k: [Push(a), ..], th: { me @ Th { tk: [_, ..], .. }, .. } } => { k: [..], th: { Th { tk: [.., a], ..me }, .. } };".to_owned(),
                "go: { aux: [_, ..] } => { aux: [.., 1] };".to_owned(),
            ),
        ),
        (
            "set-items-after-rest",
            (
                "go: { k: [Push(a), ..], job: [me @ Job { js: _, .. }, ..] } => { k: [..], job: [Job { js: [.., a], ..me }, ..] };".to_owned(),
                "go: { k: [Push(a), ..], ss: _ } => { k: [..], ss: [.., a] };".to_owned(),
            ),
        ),
    ];
    let table = rows
        .iter()
        .map(|(name, (instance, twin))| {
            let instance = verdict(
                target.path(),
                temporary.path(),
                &format!("instance-{name}"),
                instance,
                false,
            );
            let twin = verdict(
                target.path(),
                temporary.path(),
                &format!("twin-{name}"),
                twin,
                false,
            );
            format!("{name}\n  instance: {instance}\n  twin: {twin}")
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r"
        paren-back
          instance: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
          twin: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `ll` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
        paren-front
          instance: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
          twin: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `ll` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
        paren-exact
          instance: error[krs::syntax::invalid-list-notation]: the entry of the cell `tl` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it writes the whole list, which drops a rest the subject leaves unnamed; write `..` on both sides to keep the rest, or name it in the subject (`rest @ ..`) to drop or move it
          twin: error[krs::syntax::invalid-list-notation]: the entry of the cell `ll` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it writes the whole list, which drops a rest the subject leaves unnamed; write `..` on both sides to keep the rest, or name it in the subject (`rest @ ..`) to drop or move it
        double-alias
          instance: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
          twin: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `ll` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
        alias
          instance: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
          twin: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `ll` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
        alternatives
          instance: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
          twin: error[krs::syntax::rust-syntax]: expected `,` between machine-rule cells
        item-alternatives
          instance: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
          twin: rule [go]: <k> ( go #Or last ) => .K ... </k> <ll> Krs_RestLl:List ListItem(X:KItem) => Krs_RestLl:List </ll> <out> _ => ListItem(X:KItem) </out>
        rest-unkept
          instance: error[krs::syntax::invalid-list-notation]: the entry of the cell `tl` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it writes the whole list, which drops a rest the subject leaves unnamed; write `..` on both sides to keep the rest, or name it in the subject (`rest @ ..`) to drop or move it
          twin: error[krs::syntax::invalid-list-notation]: the entry of the cell `ll` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it writes the whole list, which drops a rest the subject leaves unnamed; write `..` on both sides to keep the rest, or name it in the subject (`rest @ ..`) to drop or move it
        splice-term
          instance: rule [go]: <k> push A:Int => .K ... </k> <th> <tl> ListItem(_) R:List => ListItem(A:Int) R:List R:List </tl> ... </th>
          twin: rule [go]: <k> push A:Int => .K ... </k> <ll> ListItem(_) R:List => ListItem(A:Int) R:List R:List </ll>
        items-after-rest
          instance: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
          twin: rule [go]: <k> push A:Int => .K ... </k> <ll> ListItem(_) Krs_RestLl:List => Krs_RestLl:List ListItem(A:Int) </ll>
        items-around-rest
          instance: error[krs::analysis::collection-entry]: the result's unnamed rest `..` keeps a rest of `tl` that the lowering does not keep yet: the subject matches it inside a term (below an alias, in parentheses or among alternatives), or, in an instance child, with items after it, or the result writes items after it there; a rest is kept only where the subject's own brackets end with it, and an instance child's only after its items, so name the rest in the subject and write it back by its name, or name every item
          twin: rule [go]: <k> push A:Int => .K ... </k> <ll> ListItem(_) Krs_RestLl:List => ListItem(A:Int) Krs_RestLl:List ListItem(A:Int) </ll>
        two-rests
          instance: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
          twin: error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`
        computation-items-after-rest
          instance: error[krs::collect::invalid-configuration]: the entry of the computation cell `tk` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it
          twin: error[krs::collect::invalid-configuration]: the entry of the computation cell `aux` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it
        set-items-after-rest
          instance: error[krs::analysis::invalid-list-notation]: the cell `js` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          twin: error[krs::analysis::invalid-list-notation]: the cell `ss` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)"]].assert_eq(&table.join("\n"));
}

/// A workspace of a specification package, [`SOURCE`] with no sentence, and a `k::patterns!`
/// package `pats` over it holding `steps`; the patterns package's manifest.
fn patterns_workspace(root: &Path, steps: &str) -> PathBuf {
    let spec = package(root, "spec", "");
    let manifest = fs::read_to_string(&spec)
        .unwrap()
        .replace("\n[workspace]\nresolver = \"3\"\n", "");
    fs::write(&spec, manifest).unwrap();
    let pats = root.join("pats");
    fs::create_dir_all(pats.join("src")).unwrap();
    fs::write(
        pats.join("src/lib.rs"),
        format!("k::patterns! {{\n    for spec::Machine;\n\n{steps}\n}}\n"),
    )
    .unwrap();
    fs::write(
        pats.join("Cargo.toml"),
        format!(
            "[package]\nname = \"pats\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\nspec = {{ path = \"../spec\" }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CHILD-SEQUENCE-STEPS\"\n\n[package.metadata.krs.definitions.main]\n",
            krs_path(),
        ),
    )
    .unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"spec\", \"pats\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    pats.join("Cargo.toml")
}

/// The verdict on the steps of a patterns package: each step's K, or the first error line.
fn step_verdicts(target: &Path, root: &Path, steps: &str) -> Result<Vec<(String, String)>, String> {
    let manifest = patterns_workspace(root, steps);
    let output = root.join("emitted");
    let (success, _, stderr) = krs(
        target,
        &manifest,
        "emit-k",
        &[
            "--dependency",
            "spec:main",
            "--ir",
            "--output",
            output.to_str().unwrap(),
        ],
    );
    if !success {
        return Err(stderr
            .lines()
            .find(|line| line.starts_with("error["))
            .unwrap_or_else(|| panic!("no error headline:\n{stderr}"))
            .to_owned());
    }
    let definition: krs_ir_levels::DefinitionIr =
        serde_json::from_str(&fs::read_to_string(output.join("definition-ir.json")).unwrap())
            .unwrap();
    Ok(krs_compiler::emit_patterns(&definition)
        .unwrap()
        .into_iter()
        .map(|pattern| (pattern.id, pattern.steps[0].pattern.clone()))
        .collect())
}

/// The content of the cell `cell` in a step's K, a list rest the step names for the cell's
/// unnamed `..` written `_`: the rest occurs once, so its name matches what `_` matches.
fn content(k: &str, cell: &str) -> String {
    let open = format!("<{cell}> ");
    let start = k.find(&open).unwrap_or_else(|| panic!("<{cell}> in {k}")) + open.len();
    let end = k[start..].find(&format!(" </{cell}>")).unwrap() + start;
    k[start..end]
        .split_whitespace()
        .map(|token| {
            if token.starts_with("Krs_Rest") && token.ends_with(":List") {
                "_"
            } else {
                token
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// A `k::patterns!` step, whose lists may hold several rests, reads an instance child's brackets
/// as its twin's at its own cell: the same match of a List child, in braces and brackets, and the
/// same refusal of a computation child's item after its rest and of a Set child's brackets.
#[test]
fn an_instance_child_s_brackets_in_a_step_are_judged_as_its_cell_s() {
    let target = shared_fixture_target();
    let shapes = [
        ("several", "[.., a, .., b, ..]"),
        ("back", "[.., x]"),
        ("named", "[r @ .., x]"),
        ("ends", "[x, .., y]"),
    ];
    let temporary = temp_dir();
    let mut steps = String::new();
    for (shape, value) in shapes {
        writeln!(
            steps,
            "    twin_{shape}: {{ ll: {value} }};\n    braces_{shape}: {{ th: {{ spec::Th {{ tl: {value}, .. }}, .. }} }};\n    brackets_{shape}: {{ job: [spec::Job {{ jl: {value}, .. }}, ..] }};"
        )
        .unwrap();
    }
    let emitted = step_verdicts(target.path(), temporary.path(), &steps).unwrap();
    let step = |id: String| {
        emitted
            .iter()
            .find(|(emitted, _)| *emitted == id)
            .unwrap_or_else(|| panic!("step {id} in {emitted:?}"))
            .1
            .clone()
    };
    let mut table = Vec::new();
    for (shape, _) in shapes {
        let twin = step(format!("twin-{shape}"));
        let braces = step(format!("braces-{shape}"));
        let brackets = step(format!("brackets-{shape}"));
        assert_eq!(content(&braces, "tl"), content(&twin, "ll"), "{shape}");
        assert_eq!(content(&brackets, "jl"), content(&twin, "ll"), "{shape}");
        table.push(format!("{shape}: {}", content(&twin, "ll")));
    }
    expect_test::expect![[r"
        several: _ ListItem(A:KItem) _ ListItem(B:KItem) _
        back: _ ListItem(X:KItem)
        named: R:List ListItem(X:KItem)
        ends: ListItem(X:KItem) _ ListItem(Y:KItem)"]]
    .assert_eq(&table.join("\n"));

    let mut refusals = Vec::new();
    for (row, twin, braces, brackets) in [
        (
            "computation",
            "{ aux: [.., x, ..] }",
            "{ th: { spec::Th { tk: [.., x, ..], .. }, .. } }",
            "{ job: [spec::Job { jk: [.., x, ..], .. }, ..] }",
        ),
        (
            "set",
            "{ ss: [.., x] }",
            "{ th: { spec::Th { ts: [.., x], .. }, .. } }",
            "{ job: [spec::Job { js: [.., x], .. }, ..] }",
        ),
    ] {
        let verdicts = [("twin", twin), ("braces", braces), ("brackets", brackets)].map(
            |(position, pattern)| {
                let root = temporary.path().join(format!("{row}-{position}"));
                step_verdicts(target.path(), &root, &format!("    p: {pattern};"))
                    .expect_err("refused")
            },
        );
        assert_eq!(class(&verdicts[1]), class(&verdicts[0]), "{row}");
        assert_eq!(class(&verdicts[2]), class(&verdicts[0]), "{row}");
        refusals.push(format!("{row}:\n  {}", verdicts.join("\n  ")));
    }
    expect_test::expect![[r"
        computation:
          error[krs::collect::invalid-configuration]: the entry of the computation cell `aux` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it
          error[krs::collect::invalid-configuration]: the entry of the computation cell `tk` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it
          error[krs::collect::invalid-configuration]: the entry of the computation cell `jk` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it
        set:
          error[krs::analysis::invalid-list-notation]: the cell `ss` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          error[krs::analysis::invalid-list-notation]: the cell `ts` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)
          error[krs::analysis::invalid-list-notation]: the cell `js` holds a `Set` leaf, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's)"]].assert_eq(&refusals.join("\n"));
}
