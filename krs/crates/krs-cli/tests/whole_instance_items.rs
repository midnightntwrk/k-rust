//! An instance-list item that is one name is that whole instance: in a pattern `x` is the
//! instance record `x @ Decl { .. }` of the collection's declared group, labelled `x` and leaving
//! every child open, and `_` is `Decl { .. }`; in a result `x` is the instance the pattern bound
//! to `x`, kept as matched, the update `Decl { ..x }` that writes no child. A List collection's
//! `job: [x, ..]` is its front instance, `[.., x]` its back one, and a Set collection's
//! `acct: { x, .. }` any one it holds. Each readable rule written so checks, emits the K of its
//! `x @ Decl { .. }` twin, and runs.
//!
//! An instance record written on both sides without a label is the same instance when its
//! collection identifies it so: a Map collection's instance by its key, a List collection's by
//! its position. It is that instance updated, as its labelled twin `o @ ..` / `..o` is, so the
//! result's `..` keeps the children it does not name rather than reset them to the template's
//! defaults; a Set instance has no such identity, and a List's back instance is not updated in
//! place.

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
    package_of(root, name, &SOURCE.replace("{RULES}", rules))
}

/// Writes a one-package workspace whose library is `source`.
fn package_of(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
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

/// A Map collection of objects keyed by `oid`, a List collection and a Set collection, all empty
/// at the start; `new` and `push` create instances whose unnamed children differ from the
/// template's defaults (`mem: 7`, `lmem: 9`). `{RULES}` is the updates in one spelling.
const TWINS: &str = r#"
use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (New, Upd, Cupd, Swap, Same, Push, Pupd, Sput, Plast) > right seq (Seq))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("new {id}")] New { id: Int },
    #[k::syntax("upd {id} {x}")] Upd { id: Int, x: Int },
    #[k::syntax("cupd {x}")] Cupd { x: Int },
    #[k::syntax("swap")] Swap(),
    #[k::syntax("same {id}")] Same { id: Int },
    #[k::syntax("push {x}")] Push { x: Int },
    #[k::syntax("pupd {x}")] Pupd { x: Int },
    #[k::syntax("sput {x}")] Sput { x: Int },
    #[k::syntax("plast {x}")] Plast { x: Int },
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::cell]
pub struct Objs {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub obj: Obj,
}

#[k::cell]
pub struct Obj {
    #[k::cell]
    pub oid: Int,
    #[k::cell]
    pub val: Int,
    #[k::cell]
    pub mem: Int,
}

#[k::cell]
pub struct Lobs {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub lob: Lob,
}

#[k::cell]
pub struct Lob {
    #[k::cell]
    pub lval: Int,
    #[k::cell]
    pub lmem: Int,
}

#[k::cell]
pub struct Sobs {
    #[k::cell(multiplicity = "*", cell_type = "Set", nested)]
    pub sob: Sob,
}

#[k::cell]
pub struct Sob {
    #[k::cell]
    pub sid: Int,
    #[k::cell]
    pub sval: Int,
    #[k::cell]
    pub smem: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub objs: Objs,
    #[k::cell(nested)]
    pub lobs: Lobs,
    #[k::cell(nested)]
    pub sobs: Sobs,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            objs: Objs { obj: Obj { oid: 0, val: 0, mem: 0 } },
            lobs: Lobs { lob: Lob { lval: 0, lmem: 0 } },
            sobs: Sobs { sob: Sob { sid: 0, sval: 0, smem: 0 } },
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

    new: { k: [New(i), ..], obj: { .. } } => { k: [..], obj: { Obj { oid: i, val: 0, mem: 7 }, .. } };
    push: { k: [Push(x), ..], lob: [..] } => { k: [..], lob: [Lob { lval: x, lmem: 9 }, ..] };
    // A Set instance is no subject instance: removed, and one created with the defaults.
    sput: { k: [Sput(x), ..], sob: { Sob { sid: 1, sval: v, .. }, .. } } => { k: [..], sob: { Sob { sid: 1, sval: int::add(v, x), .. }, .. } };
    // A List's back instance replaced by one that names every child: removed and created.
    plast: { k: [Plast(x), ..], lob: [.., Lob { lval: v, .. }] } => { k: [..], lob: [.., Lob { lval: int::add(v, x), lmem: 0 }] };
}

{RULES}
"#;

/// The updates, each instance written without a label on both sides.
const ANONYMOUS: &str = r#"
k::rules! {
    for Machine;
    use Cmd::*;

    upd: { k: [Upd(i, x), ..], obj: { Obj { oid: i, val: v, .. }, .. } } => { k: [..], obj: { Obj { oid: i, val: int::add(v, x), .. }, .. } };
    swap: { k: [Swap(), ..], obj: { Obj { oid: 1, val: v, .. }, Obj { oid: 2, val: w, .. }, .. } } => { k: [..], obj: { Obj { oid: 2, val: v, .. }, Obj { oid: 1, val: w, .. }, .. } };
    same: { k: [Same(i), ..], obj: { Obj { oid: i, val: v, .. }, .. } } => { k: [..], obj: { Obj { oid: i, val: v, .. }, .. } };
    pupd: { k: [Pupd(x), ..], lob: [Lob { lval: v, .. }, ..] } => { k: [..], lob: [Lob { lval: int::add(v, x), .. }, ..] };
}

#[k::rule(label = "cupd")]
fn cupd(
    x: k::Term<Int>,
    v: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Cupd(x), tail @ ..),
        Objs::obj: { k::fragment![crate::Obj { oid: 1, val: v, .. }], instances0 @ .. },
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Objs::obj: { k::fragment![crate::Obj { oid: 1, val: int::add(v, x), .. }], ..instances0 },
        ..state
    }
}

k::claims! {
    for Machine;
    use Cmd::*;

    #[k::claim(all_paths)]
    upd_claim: { k: [Upd(1, 2), ..], obj: { Obj { oid: 1, val: v, .. }, .. } } => { k: [..], obj: { Obj { oid: 1, val: int::add(v, 2), .. }, .. } };
}
"#;

/// The same updates, each through the label its subject gives the instance, `o @ ..` and `..o`.
const LABELLED: &str = r#"
k::rules! {
    for Machine;
    use Cmd::*;

    upd: { k: [Upd(i, x), ..], obj: { o @ Obj { oid: i, val: v, .. }, .. } } => { k: [..], obj: { Obj { val: int::add(v, x), ..o }, .. } };
    swap: { k: [Swap(), ..], obj: { a @ Obj { oid: 1, val: v, .. }, b @ Obj { oid: 2, val: w, .. }, .. } } => { k: [..], obj: { Obj { val: v, ..b }, Obj { val: w, ..a }, .. } };
    same: { k: [Same(i), ..], obj: { o @ Obj { oid: i, val: v, .. }, .. } } => { k: [..], obj: { Obj { ..o }, .. } };
    pupd: { k: [Pupd(x), ..], lob: [o @ Lob { lval: v, .. }, ..] } => { k: [..], lob: [Lob { lval: int::add(v, x), ..o }, ..] };
}

#[k::rule(label = "cupd")]
fn cupd(
    x: k::Term<Int>,
    v: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Cupd(x), tail @ ..),
        Objs::obj: { o @ k::fragment![crate::Obj { oid: 1, val: v, .. }], instances0 @ .. },
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Objs::obj: { k::fragment![crate::Obj { val: int::add(v, x), ..o }], ..instances0 },
        ..state
    }
}

k::claims! {
    for Machine;
    use Cmd::*;

    #[k::claim(all_paths)]
    upd_claim: { k: [Upd(1, 2), ..], obj: { o @ Obj { oid: 1, val: v, .. }, .. } } => { k: [..], obj: { Obj { val: int::add(v, 2), ..o }, .. } };
}
"#;

/// The K source and the claims `krs emit-k` writes for the package.
fn emitted_k_and_claims(target: &Path, manifest: &Path) -> String {
    let definition = emitted_k(target, manifest);
    let spec = fs::read_to_string(manifest.with_file_name("emitted").join("spec.k")).unwrap();
    format!(
        "{definition}\n{}",
        krs_test_support::without_source_comments(&spec)
    )
}

/// The emitted claim labelled `label`, up to the next sentence.
fn claim<'a>(k: &'a str, label: &str) -> &'a str {
    let start = k
        .find(&format!("claim [{label}]:"))
        .unwrap_or_else(|| panic!("claim `{label}` is emitted:\n{k}"));
    let end = ["claim [", "endmodule"]
        .iter()
        .filter_map(|next| k[start + 1..].find(next))
        .min()
        .map_or(k.len(), |end| start + 1 + end);
    k[start..end].trim_end()
}

/// Each update written without labels emits the K of its labelled twin, readable and `cells!`,
/// rule and claim: the Map instance whose key the result keeps, and the List's front instance at
/// the same position, are kept and rewritten in place, `..` keeping `mem` and `lmem`. A run
/// shows them kept: `mem` stays 7 and `lmem` 9 through the updates. The Set instance and the
/// List's back instance a record naming every child replaces are removed and created.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "The pinned K of every row and the run that shows it are one witness."
)]
fn an_instance_written_on_both_sides_is_updated_in_place() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let anonymous = package_of(
        temporary.path(),
        "anonymous",
        &TWINS.replace("{RULES}", ANONYMOUS),
    );
    let labelled = package_of(
        temporary.path(),
        "labelled",
        &TWINS.replace("{RULES}", LABELLED),
    );
    let (success, stdout, stderr) = krs(target.path(), &anonymous, "check", &[]);
    assert!(success, "{stdout}\n{stderr}");
    let emitted = emitted_k_and_claims(target.path(), &anonymous);
    assert_eq!(emitted, emitted_k_and_claims(target.path(), &labelled));
    let rules = ["upd", "swap", "same", "pupd", "cupd", "sput", "plast"]
        .map(|label| rule(&emitted, label))
        .join("\n");
    expect_test::expect![[r"
        rule [upd]:
            <k> upd I:Int X:Int => .K ... </k>
            <obj>
                <oid> I:Int </oid>
                <val> V:Int => V:Int +Int X:Int </val>
                ...
            </obj>
        rule [swap]:
            <k> swap => .K ... </k>
            <obj>
                <oid> 1 </oid>
                <val> V:Int => W:Int </val>
                ...
            </obj>
            <obj>
                <oid> 2 </oid>
                <val> W:Int => V:Int </val>
                ...
            </obj>
        rule [same]:
            <k> same I:Int => .K ... </k>
            <obj>
                <oid> I:Int </oid>
                <val> V:Int </val>
                ...
            </obj>
        rule [pupd]:
            <k> pupd X:Int => .K ... </k>
            <lobs>
                <lob>
                    <lval> V:Int => V:Int +Int X:Int </lval>
                    ...
                </lob>
                ...
            </lobs>
        rule [cupd]:
            <k> cupd X:Int ~> Tail:K => .K ~> Tail:K </k>
            <obj>
                <oid> 1 </oid>
                <val> V:Int => V:Int +Int X:Int </val>
                ...
            </obj>
        rule [sput]:
            <k> sput X:Int => .K ... </k>
            (<sob>
                <sid> 1 </sid>
                <sval> V:Int </sval>
                ...
            </sob> => .Bag)
            (.Bag => <sob>
                <sid> 1 </sid>
                <sval> V:Int +Int X:Int </sval>
                ...
            </sob>)
        rule [plast]:
            <k> plast X:Int => .K ... </k>
            <lobs>
                _Instances1:Bag
                (<lob>
                    <lval> V:Int </lval>
                    ...
                </lob> => .Bag)
                (.Bag => <lob>
                    <lval> V:Int +Int X:Int </lval>
                    <lmem> 0 </lmem>
                </lob>)
            </lobs>
        claim [upd-claim]:
            <k> upd 1 2 => .K ... </k>
            <obj>
                <oid> 1 </oid>
                <val> V:Int => V:Int +Int 2 </val>
                ...
            </obj>"]]
    .assert_eq(&format!("{rules}\n{}", claim(&emitted, "upd-claim")));

    let program = anonymous.with_file_name("program.txt");
    fs::write(
        &program,
        "new 1 new 2 upd 1 5 swap same 2 cupd 3 push 3 pupd 4\n",
    )
    .unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &anonymous,
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{stdout}\n{stderr}");
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    let start = flat.find("<objs>").unwrap();
    let end = flat.find("</lobs>").unwrap() + "</lobs>".len();
    expect_test::expect!["<objs> <obj> <oid> 1 </oid> <val> 3 </val> <mem> 7 </mem> </obj> <obj> <oid> 2 </oid> <val> 5 </val> <mem> 7 </mem> </obj> </objs> <lobs> <lob> <lval> 7 </lval> <lmem> 9 </lmem> </lob> </lobs>"].assert_eq(&flat[start..end]);
}

/// A List's back instance written on both sides, its result keeping children with `..`, is the
/// instance updated in place, which KRS does not emit at the back: refused, as its labelled twin.
#[test]
fn a_back_instance_updated_in_place_is_refused_as_its_labelled_twin() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let errors = [
        "last: { k: [Pupd(x), ..], lob: [.., Lob { lval: v, .. }] } => { k: [..], lob: [.., Lob { lval: int::add(v, x), .. }] };",
        "last: { k: [Pupd(x), ..], lob: [.., o @ Lob { lval: v, .. }] } => { k: [..], lob: [.., Lob { lval: int::add(v, x), ..o }] };",
    ]
    .iter()
    .enumerate()
    .map(|(index, clause)| {
        let rules = format!("k::rules! {{\n    for Machine;\n    use Cmd::*;\n\n    {clause}\n}}\n");
        let manifest = package_of(
            temporary.path(),
            &format!("back{index}"),
            &TWINS.replace("{RULES}", &rules),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{clause} was accepted");
        stderr
            .lines()
            .find(|line| line.starts_with("error["))
            .unwrap_or_else(|| panic!("no error headline:\n{stderr}"))
            .to_owned()
    })
    .collect::<Vec<_>>();
    assert_eq!(errors[0], errors[1]);
    expect_test::expect!["error[krs::analysis::collection-entry]: a back instance of the List collection `lob` is matched in place; KRS creates or removes instances at the back, and reads and updates them at the front"].assert_eq(&errors[0]);
}
