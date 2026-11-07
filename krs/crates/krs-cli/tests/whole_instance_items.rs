//! An instance-list item that is one name is that whole instance: in a pattern `x` is the
//! instance record `x @ Decl { .. }` of the collection's declared group, labelled `x` and leaving
//! every child open, and `_` is `Decl { .. }`; in a result `x` is the instance the pattern bound
//! to `x`, kept as matched, the update `Decl { ..x }` that writes no child. A List collection's
//! `job: [x, ..]` is its front instance, `[.., x]` its back one, and a Set collection's
//! `acct: { x, .. }` any one it holds. Each readable rule written so checks, emits the K of its
//! `x @ Decl { .. }` twin, and runs.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A machine with a List collection of jobs and a Set collection of accounts, both empty at
/// the start; `{RULES}` is the machine rules in one spelling.
const SOURCE: &str = r#"
use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Spawn, Open, Pop, Last, Keep, Close, Any) > right seq (Seq))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("spawn {payload}")] Spawn { payload: Int },
    #[k::syntax("open {id}")] Open { id: Int },
    #[k::syntax("pop")] Pop(),
    #[k::syntax("last")] Last(),
    #[k::syntax("keep")] Keep(),
    #[k::syntax("close")] Close(),
    #[k::syntax("any")] Any(),
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::cell]
pub struct Queue {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub job: Job,
}

#[k::cell]
pub struct Job {
    #[k::cell]
    pub payload: Int,
}

#[k::cell]
pub struct Accts {
    #[k::cell(multiplicity = "*", cell_type = "Set", nested)]
    pub acct: Acct,
}

#[k::cell]
pub struct Acct {
    #[k::cell]
    pub id: Int,
    #[k::cell]
    pub bal: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub queue: Queue,
    #[k::cell(nested)]
    pub accts: Accts,
    #[k::cell]
    pub count: Int,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            queue: Queue { job: Job { payload: 0 } },
            accts: Accts { acct: Acct { id: 0, bal: 0 } },
            count: 0,
        }
    }
}

k::rules! {
    for Stmt;
    use Cmd::*;

    seq: Seq(s1, s2) => k::k![s1, s2];
}

k::rules! {
    for Machine;
    use Cmd::*;

    spawn: { k: [Spawn(n), ..], job: [..] } => { k: [..], job: [.., Job { payload: n }] };
    open: { k: [Open(n), ..], acct: { .. } } => { k: [..], acct: { Acct { id: n, bal: 0 }, .. } };
}

{RULES}
"#;

/// The rules naming whole instances, each spelled as an item alone.
const ITEMS: &str = r"
k::rules! {
    for Machine;
    use Cmd::*;

    pop: { k: [Pop(), ..], job: [x, ..], count: c } => { k: [..], job: [..], count: int::add(c, 1) };
    last: { k: [Last(), ..], job: [.., x], count: c } => { k: [..], job: [..], count: int::add(c, 10) };
    keep: { k: [Keep(), ..], job: [x, ..], count: c } => { k: [..], job: [x, ..], count: int::add(c, 100) };
    close: { k: [Close(), ..], acct: { x, .. }, count: c } => { k: [..], acct: { .. }, count: int::add(c, 1000) };
    any: { k: [Any(), ..], acct: { _, .. }, count: c } => { k: [..], count: int::add(c, 10000) };
}
";

/// The same rules, each whole instance spelled as its record, `x @ Decl { .. }`.
const RECORDS: &str = r"
k::rules! {
    for Machine;
    use Cmd::*;

    pop: { k: [Pop(), ..], job: [x @ Job { .. }, ..], count: c } => { k: [..], job: [..], count: int::add(c, 1) };
    last: { k: [Last(), ..], job: [.., x @ Job { .. }], count: c } => { k: [..], job: [..], count: int::add(c, 10) };
    keep: { k: [Keep(), ..], job: [x @ Job { .. }, ..], count: c } => { k: [..], job: [Job { ..x }, ..], count: int::add(c, 100) };
    close: { k: [Close(), ..], acct: { x @ Acct { .. }, .. }, count: c } => { k: [..], acct: { .. }, count: int::add(c, 1000) };
    any: { k: [Any(), ..], acct: { Acct { .. }, .. }, count: c } => { k: [..], count: int::add(c, 10000) };
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is [`SOURCE`] with `rules`.
fn package(root: &Path, name: &str, rules: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(
        directory.join("src/lib.rs"),
        SOURCE.replace("{RULES}", rules),
    )
    .unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-WHOLE-INSTANCES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// Each rule naming a whole instance by an item alone checks and emits the K of its twin naming
/// it by its record, `x @ Decl { .. }`, and runs: `pop` removes the front job, `last` the back
/// one, `keep` keeps the front job as matched, `close` removes one account and `any` reads one.
#[test]
fn a_whole_instance_item_is_its_labelled_record() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let items = package(temporary.path(), "items", ITEMS);
    let records = package(temporary.path(), "records", RECORDS);
    let (success, stdout, stderr) = krs(target.path(), &items, "check", &[]);
    assert!(success, "{stdout}\n{stderr}");
    let emitted = emitted_k(target.path(), &items);
    assert_eq!(emitted, emitted_k(target.path(), &records));
    let rules = ["pop", "last", "keep", "close", "any"]
        .map(|label| rule(&emitted, label))
        .join("\n");
    expect_test::expect![[r"
        rule [pop]:
            <k> pop => .K ... </k>
            <count> C:Int => C:Int +Int 1 </count>
            <queue>
                (<job>
                    .Bag ...
                </job> => .Bag)
                ...
            </queue>
        rule [last]:
            <k> last => .K ... </k>
            <count> C:Int => C:Int +Int 10 </count>
            <queue>
                _Instances2:Bag
                (<job>
                    .Bag ...
                </job> => .Bag)
            </queue>
        rule [keep]:
            <k> keep => .K ... </k>
            <count> C:Int => C:Int +Int 100 </count>
            <queue>
                <job>
                    .Bag ...
                </job>
                ...
            </queue>
        rule [close]:
            <k> close => .K ... </k>
            (<acct>
                .Bag ...
            </acct> => .Bag)
            <count> C:Int => C:Int +Int 1000 </count>
        rule [any]:
            <k> any => .K ... </k>
            <acct>
                .Bag ...
            </acct>
            <count> C:Int => C:Int +Int 10000 </count>"]]
    .assert_eq(&rules);

    let program = items.with_file_name("program.txt");
    fs::write(
        &program,
        "spawn 1 spawn 2 spawn 3 keep pop last open 7 open 8 any close\n",
    )
    .unwrap();
    let (success, stdout, stderr) = krs(target.path(), &items, "run", &[program.to_str().unwrap()]);
    assert!(success, "{stdout}\n{stderr}");
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    let start = flat.find("<k>").unwrap();
    let end = flat.find("</count>").unwrap() + "</count>".len();
    expect_test::expect!["<k> .K </k> <queue> <job> <payload> 2 </payload> </job> </queue> <accts> <acct> <id> 7 </id> <bal> 0 </bal> </acct> </accts> <count> 11111 </count>"].assert_eq(&flat[start..end]);
}
