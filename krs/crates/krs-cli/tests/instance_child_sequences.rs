//! An instance child is a cell, so its brackets in a pattern mean what they mean at a cell of
//! the child's kind outside every instance: a builtin `List` child's `[.., x]` and `[x, .., y]`
//! match its back, a computation child refuses an item after its rest, a `Set` child refuses
//! brackets, and a second rest is refused as at its own cell. The verdict is the same whether
//! the collection's instances are written in braces (a Map collection) or brackets (a List
//! collection), in a rule and in a claim, and an instance rule matching a list child's back
//! runs.

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
/// A second rest leaves its item unused, as a twin that reads it has no other verdict.
#[test]
fn an_instance_child_s_brackets_are_judged_as_its_cell_s() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let shapes = [
        ("back", "[.., x]", ", out: _", ", out: [x]"),
        ("ends", "[x, .., y]", ", out: _", ", out: [x, y]"),
        ("mid", "[.., x, ..]", "", ""),
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
