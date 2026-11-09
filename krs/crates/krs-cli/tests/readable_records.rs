//! Readable-record notation end to end: the cell shorthand `{ pc, gas }`, and
//! the instance child shorthand `Account { balance, .. }`. Each notation is
//! checked against the long form it stands for, through `krs emit-k` and
//! `krs expand`, which run the macro and the collector's reparse on the same
//! source.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{
    fixture_build_env, krs_command, shared_fixture_target, temp_dir, without_source_comments,
};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, List, int, list};
use k::KResult;

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Go, Push, Save, Tag))]
pub enum Cmd {
    #[k::syntax("go")]
    Go(),
    #[k::syntax("push")]
    Push(),
    #[k::syntax("save")]
    Save(),
    #[k::syntax("tag")]
    Tag(),
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub depth: Int,
    #[k::cell]
    pub fuel: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub gas: Int,
    #[k::cell]
    pub stack: List,
    #[k::cell(nested)]
    pub frame: Frame,
    #[k::cell(name = "kind")]
    pub r#type: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            pc: 0,
            gas: 0,
            stack: list::empty(),
            frame: Frame { depth: 0, fuel: 0 },
            r#type: 0,
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
    package_over(root, name, PREAMBLE, source)
}

/// [`package`] over another preamble.
fn package_over(root: &Path, name: &str, preamble: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{preamble}{source}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-RECORDS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The reference source `krs expand` writes for the package.
fn expanded(target: &Path, manifest: &Path) -> String {
    let (success, stdout, stderr) = krs(target, manifest, "expand", &[]);
    assert!(success, "{stderr}");
    stdout
}

/// The `error[..]` headlines of `krs check`, without their locations.
fn check_errors(target: &Path, manifest: &Path) -> Vec<String> {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    stderr
        .lines()
        .filter(|line| line.starts_with("error"))
        .map(ToOwned::to_owned)
        .collect()
}

const SHORTHAND: &str = r"
k::rules! {
    for Machine;
    use Cmd::*;

    step: { k: [Go(), ..], pc, gas } => { k: [..], pc: int::add(pc, 1), gas };
    save: { k: [Save(), ..], frame, stack } => { k: [..], stack: list::concat(list::item(frame), stack) };
    push: { k: [Push(), ..], gas, stack } => { k: [..], stack: list::concat(list::item(gas), stack) };
    tag: { k: [Tag(), ..], r#type } => { k: [..], r#type: int::add(r#type, 1) };
}
";

const LONG: &str = r"
k::rules! {
    for Machine;
    use Cmd::*;

    step: { k: [Go(), ..], pc: pc, gas: gas } => { k: [..], pc: int::add(pc, 1), gas: gas };
    save: { k: [Save(), ..], frame: frame, stack: stack } => { k: [..], stack: list::concat(list::item(frame), stack) };
    push: { k: [Push(), ..], gas: gas, stack: stack } => { k: [..], stack: list::concat(list::item(gas), stack) };
    tag: { k: [Tag(), ..], r#type: r#type } => { k: [..], r#type: int::add(r#type, 1) };
}
";

/// A lone cell name is the entry `cell: cell` on either side: for a leaf
/// cell, a group cell bound whole, a cell written back unchanged (a read),
/// and a raw identifier. Both spellings emit the same K and expand to the
/// same reference rules.
#[test]
fn a_shorthand_entry_is_the_entry_binding_the_cell_name() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let shorthand = package(temporary.path(), "shorthand", SHORTHAND);
    let long = package(temporary.path(), "long", LONG);
    let shorthand_k = emitted_k(target.path(), &shorthand);
    // The packages' names differ, and the source comments name them.
    assert_eq!(
        without_source_comments(&shorthand_k),
        without_source_comments(&emitted_k(target.path(), &long))
    );
    assert!(
        shorthand_k.contains("<gas> Gas:Int </gas>"),
        "the restated cell is a read:\n{shorthand_k}"
    );
    assert!(
        shorthand_k.contains("<kind> Type:Int => Type:Int +Int 1 </kind>"),
        "{shorthand_k}"
    );
    assert_eq!(
        expanded(target.path(), &shorthand),
        expanded(target.path(), &long)
    );
}

/// A shorthand result entry whose binder the subject does not bind fails
/// as the long entry does.
#[test]
fn an_unbound_shorthand_result_fails_as_the_long_entry() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rule = |result: &str| {
        format!(
            "k::rules! {{\n    for Machine;\n    use Cmd::*;\n    step: {{ k: [Go(), ..], gas: g }} => {{ k: [..], {result} }};\n}}\n"
        )
    };
    let shorthand = package(temporary.path(), "unbound-shorthand", &rule("gas"));
    let long = package(temporary.path(), "unbound-long", &rule("gas: gas"));
    let errors = check_errors(target.path(), &shorthand);
    assert!(!errors.is_empty());
    assert_eq!(errors, check_errors(target.path(), &long));
}

/// A configuration with a Map collection of accounts, keyed by `id`, below
/// the plain group `accounts`.
const ACCOUNTS: &str = r#"
use k::builtin::{Int, KSequence, int};
use k::KResult;

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Read, Open, Pay, Reset, Audit))]
pub enum Cmd {
    #[k::syntax("read {id}")]
    Read { id: Int },
    #[k::syntax("open {id} {balance}")]
    Open { id: Int, balance: Int },
    #[k::syntax("pay {id} {amount}")]
    Pay { id: Int, amount: Int },
    #[k::syntax("reset {id} {balance}")]
    Reset { id: Int, balance: Int },
    #[k::syntax("audit {id}")]
    Audit { id: Int },
}

#[k::cell]
pub struct Account {
    #[k::cell(name = "acctID")]
    pub id: Int,
    #[k::cell]
    pub balance: Int,
    #[k::cell]
    pub nonce: Int,
}

#[k::cell]
pub struct Accounts {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub account: Account,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub accounts: Accounts,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            accounts: Accounts { account: Account { id: 0, balance: 0, nonce: 0 } },
        }
    }
}
"#;

const INSTANCE_SHORTHAND: &str = r#"
k::rules! {
    for Machine;
    use Cmd::*;

    #[k::requires(want == id)]
    read: { k: [Read { id: want }, ..], account: { Account { id, balance, .. }, .. } } => { k: [balance, ..] };
    open: { k: [Open { id, balance }, ..], account: { .. } } => { k: [..], account: { Account { id, balance, nonce: 0 }, .. } };
    #[k::requires(want == id)]
    pay: { k: [Pay { id: want, amount }, ..], account: { me @ Account { id, balance, nonce, .. }, .. } } => { k: [..], account: { Account { balance: int::add(balance, amount), nonce: int::add(nonce, 1), ..me }, .. } };
    reset: { k: [Reset { id, balance }, ..], account: { Account { .. }, .. } } => { k: [..], account: { Account { id, balance, nonce: 0 }, .. } };
}

#[k::rule(label = "audit")]
#[k::requires(want == id)]
fn audit(
    want: k::Term<Int>,
    id: k::Term<Int>,
    nonce: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Audit(want), tail @ ..),
        Accounts::account: { me @ k::fragment![crate::Account { id, nonce, .. }], instances0 @ .. },
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(nonce, ..tail),
        Accounts::account: { k::fragment![crate::Account { nonce, ..me }], ..instances0 },
        ..state
    }
}
"#;

const INSTANCE_LONG: &str = r#"
k::rules! {
    for Machine;
    use Cmd::*;

    #[k::requires(want == id)]
    read: { k: [Read { id: want }, ..], account: { Account { id: id, balance: balance, .. }, .. } } => { k: [balance, ..] };
    open: { k: [Open { id, balance }, ..], account: { .. } } => { k: [..], account: { Account { id: id, balance: balance, nonce: 0 }, .. } };
    #[k::requires(want == id)]
    pay: { k: [Pay { id: want, amount }, ..], account: { me @ Account { id: id, balance: balance, nonce: nonce, .. }, .. } } => { k: [..], account: { Account { balance: int::add(balance, amount), nonce: int::add(nonce, 1), ..me }, .. } };
    reset: { k: [Reset { id, balance }, ..], account: { Account { .. }, .. } } => { k: [..], account: { Account { id: id, balance: balance, nonce: 0 }, .. } };
}

#[k::rule(label = "audit")]
#[k::requires(want == id)]
fn audit(
    want: k::Term<Int>,
    id: k::Term<Int>,
    nonce: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Audit(want), tail @ ..),
        Accounts::account: { me @ k::fragment![crate::Account { id: id, nonce: nonce, .. }], instances0 @ .. },
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(nonce, ..tail),
        Accounts::account: { k::fragment![crate::Account { nonce: nonce, ..me }], ..instances0 },
        ..state
    }
}
"#;

/// An instance child that is only a name is `name: name`, in a readable
/// pattern instance (a binder), a created instance and an update (the bound
/// variable), a removed-and-created instance, and a `cells!` rule's
/// instances: both spellings emit the same K, and the readable rules expand
/// to the same reference rules, which write the long children.
#[test]
fn a_shorthand_instance_child_is_the_child_bound_to_its_name() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let shorthand = package_over(
        temporary.path(),
        "instance-shorthand",
        ACCOUNTS,
        INSTANCE_SHORTHAND,
    );
    let long = package_over(temporary.path(), "instance-long", ACCOUNTS, INSTANCE_LONG);
    let shorthand_k = emitted_k(target.path(), &shorthand);
    // The packages' names differ, and the source comments name them.
    assert_eq!(
        without_source_comments(&shorthand_k),
        without_source_comments(&emitted_k(target.path(), &long))
    );
    let words = shorthand_k.split_whitespace().collect::<Vec<_>>().join(" ");
    for written in [
        // The created instance writes the bound variables.
        "(.Bag => <account> <acctID> Id:Int </acctID> <balance> Balance:Int </balance> <nonce> 0 </nonce> </account>)",
        // The update writes through the shorthand's binders.
        "<balance> Balance:Int => Balance:Int +Int Amount:Int </balance> <nonce> Nonce:Int => Nonce:Int +Int 1 </nonce>",
    ] {
        assert!(words.contains(written), "{written}\n{shorthand_k}");
    }
    // `krs expand` prints a readable instance's long children, and copies a
    // `cells!` rule fn as written: the readable rules expand alike.
    let readable = |expansion: String| {
        let end = expansion.find("#[k::rule(label = \"audit\")]").unwrap();
        expansion[..end].to_owned()
    };
    let shorthand_expansion = readable(expanded(target.path(), &shorthand));
    assert_eq!(
        shorthand_expansion,
        readable(expanded(target.path(), &long))
    );
    let words = shorthand_expansion
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert!(
        words.contains("crate ::Account { id : id, balance : balance, nonce : 0 }"),
        "{shorthand_expansion}"
    );
}

/// A shorthand result child whose name the subject does not bind fails as
/// the long child does.
#[test]
fn an_unbound_shorthand_instance_child_fails_as_the_long_child() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rule = |child: &str| {
        format!(
            "k::rules! {{\n    for Machine;\n    use Cmd::*;\n    open: {{ k: [Open {{ id, balance: b }}, ..], account: {{ .. }} }} => {{ k: [..], account: {{ Account {{ id, {child}, nonce: 0 }}, .. }} }};\n}}\n"
        )
    };
    let shorthand = package_over(
        temporary.path(),
        "unbound-instance-shorthand",
        ACCOUNTS,
        &rule("balance"),
    );
    let long = package_over(
        temporary.path(),
        "unbound-instance-long",
        ACCOUNTS,
        &rule("balance: balance"),
    );
    let errors = check_errors(target.path(), &shorthand);
    assert!(!errors.is_empty());
    assert_eq!(errors, check_errors(target.path(), &long));
}

/// An instance label names exactly one subject instance, which at most one result instance
/// updates (`krs::analysis::duplicate-instance-label`): a subject that labels two instances
/// alike, and two result instances that update one label, are each refused with a reason in the
/// terms of the entry.
#[test]
fn a_label_used_twice_is_refused_with_its_reason() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rule = |subject: &str, result: &str| {
        format!(
            "k::rules! {{\n    for Machine;\n    use Cmd::*;\n    pay: {{ k: [Pay {{ id: want, amount }}, ..], account: {{ {subject} }} }} => {{ k: [..], account: {{ {result} }} }};\n}}\n"
        )
    };
    for (name, subject, result, reason) in [
        (
            "label-twice-subject",
            "me @ Account { id: want, .. }, me @ Account { id: amount, .. }, ..",
            "Account { nonce: 1, ..me }, ..",
            "labels two subject instances `me @`: a label names exactly one instance the subject matches",
        ),
        (
            "label-twice-result",
            "me @ Account { id: want, .. }, ..",
            "Account { nonce: 1, ..me }, Account { balance: amount, ..me }, ..",
            "update the subject instance labelled `me` (`..me`): an update rewrites the one instance its label names in place, so that instance is the base of one update at most",
        ),
    ] {
        let manifest = package_over(temporary.path(), name, ACCOUNTS, &rule(subject, result));
        let errors = check_errors(target.path(), &manifest);
        assert!(
            errors.iter().any(|error| {
                error.starts_with("error[krs::analysis::duplicate-instance-label]")
                    && error.contains(reason)
            }),
            "{name}: {errors:#?}"
        );
    }
}

/// Two groups, a Map collection of `Acct`, and commands the record cases match.
const GROUP_RECORDS: &str = r#"
use k::builtin::{Int, KSequence, List, Map, list, map};
use k::{KItem, KResult};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Go, Put, Ct))]
pub enum Cmd {
    #[k::syntax("go")]
    Go(),
    #[k::syntax("put({x})")]
    Put { x: Int },
    #[k::syntax("ct")]
    Ct(),
}

#[k::cell]
pub struct H {
    #[k::cell]
    pub hl: List,
    #[k::cell]
    pub hb: Int,
}

#[k::cell]
pub struct M {
    #[k::cell]
    pub mm: Map,
    #[k::cell]
    pub mn: Int,
}

#[k::cell]
pub struct Acct {
    #[k::cell]
    pub aid: Int,
    #[k::cell]
    pub abal: Int,
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
    pub hcell: H,
    #[k::cell(nested)]
    pub mcell: M,
    #[k::cell(nested)]
    pub bank: Bank,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            hcell: H { hl: list::empty(), hb: 0 },
            mcell: M { mm: map::empty(), mn: 0 },
            bank: Bank { acct: Acct { aid: 0, abal: 0 } },
        }
    }
}
"#;

/// An instance record names its struct (TRI-D2): `acct`'s instances are `Acct`, so a record
/// of `H`, another `#[k::cell]` struct, is refused on both routes, whatever children it names.
#[test]
fn an_instance_record_of_another_struct_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    for (name, rules) in [
        (
            "readable-head",
            "k::rules! {\n    for Machine;\n    use Cmd::*;\n    ct: { k: [Ct(), ..], acct: { H { aid: 1, .. }, .. } } => { k: [..] };\n}\n",
        ),
        (
            "cells-head",
            "#[k::rule(label = \"ct\")]\npub fn ct(\n    k::cells! {\n        k: k::configuration::KCell(Cmd::Ct(), tail @ ..),\n        crate::Bank::acct: { k::fragment![crate::H { aid: 1, .. }], .. },\n        state @ ..\n    }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(..tail), ..state }\n}\n",
        ),
    ] {
        let manifest = package_over(temporary.path(), name, GROUP_RECORDS, rules);
        let errors = check_errors(target.path(), &manifest);
        assert!(
            errors.iter().any(|error| error
                == "error[krs::analysis::collection-entry]: the instance record names `H`, and `acct`'s instances are `Acct`"),
            "{name}: {errors:#?}"
        );
    }
}

/// A group record's Map child at a configuration position is the child's entry (ruling R4,
/// TRI-D2): a map read, an exact map in a subject, and an exact map written over one, in
/// readable rules and their `cells!` twins. Such a record is lowered as its children's own
/// cells, exactly as `M::mm: Cell(map![..])` is, so both routes emit the same K; a record whose
/// children are terms keeps its whole group clause; and `krs expand` writes each record as the
/// `cells!` fragment of its children's entries.
#[test]
fn a_group_record_map_child_is_the_child_entry_on_both_routes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = r"
k::rules! {
    for Machine;
    use Cmd::*;

    go: { k: [Go(), ..], mcell: M { mm: { y -> x, .. }, .. } } => { k: [..] };
    put: { k: [Put { x }, ..], mcell: M { mm: { z -> y }, .. } } => { k: [..], mcell: M { mm: { y -> x }, mn: 0 } };
    ct: { k: [Ct(), ..], hcell: H { hl: h, hb: b } } => { k: [..], hcell: H { hl: h, hb: int::add(b, 1) } };
}
";
    let cells = r#"
#[k::rule(label = "go")]
pub fn go(
    y: KItem,
    x: KItem,
    k::cells! {
        k: k::configuration::KCell(Cmd::Go(), tail @ ..),
        mcell: k::fragment![crate::M { mm: k::map![y -> x, ..], .. }],
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), ..state }
}

#[k::rule(label = "put")]
pub fn put(
    x: Int,
    z: KItem,
    y: KItem,
    k::cells! {
        k: k::configuration::KCell(Cmd::Put { x }, tail @ ..),
        mcell: k::fragment![crate::M { mm: k::map![z -> y], .. }],
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        mcell: k::fragment![crate::M { mm: k::map![y -> x], mn: 0 }],
        ..state
    }
}

#[k::rule(label = "ct")]
pub fn ct(
    h: List,
    b: Int,
    k::cells! {
        k: k::configuration::KCell(Cmd::Ct(), tail @ ..),
        hcell: k::fragment![crate::H { hl: h, hb: b }],
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        hcell: k::fragment![crate::H { hl: h, hb: k::builtin::int::add(b, 1) }],
        ..state
    }
}
"#;
    let preamble = GROUP_RECORDS.replace("list, map};", "int, list, map};");
    let readable = package_over(temporary.path(), "records-readable", &preamble, readable);
    let cells = package_over(temporary.path(), "records-cells", &preamble, cells);
    let flat = |k: &str| k.split_whitespace().collect::<Vec<_>>().join(" ");
    let readable_k = flat(&emitted_k(target.path(), &readable));
    let cells_k = flat(&emitted_k(target.path(), &cells));
    for sentence in [
        "<mm> Y:KItem |-> X:KItem ... </mm>",
        "<mm> Z:KItem |-> Y:KItem => Y:KItem |-> X:Int </mm> <mn> _ => 0 </mn>",
        "(<hcell> <hl> H:List </hl> <hb> B:Int </hb> </hcell> => <hcell> <hl> H:List </hl> <hb> B:Int +Int 1 </hb> </hcell>)",
    ] {
        assert!(
            readable_k.contains(sentence),
            "no `{sentence}` in {readable_k}"
        );
        assert!(cells_k.contains(sentence), "no `{sentence}` in {cells_k}");
    }
    let rules = |k: &str| {
        k[k.find("rule [ct]").unwrap()..]
            .replace("~> Tail:K ", "")
            .replace("records-readable/", "")
            .replace("records-cells/", "")
    };
    let readable_rules = rules(&readable_k).replace("... </k>", "</k>");
    let cells_rules = rules(&cells_k).replace("... </k>", "</k>");
    assert_eq!(readable_rules, cells_rules);
    let expanded = flat(&expanded(target.path(), &readable));
    for record in [
        "mcell : k::fragment![crate ::M { mm : k::map![y -> x, ..], .. }]",
        "mcell : k::fragment![crate ::M { mm : k::map![y -> x], mn : 0 }]",
    ] {
        assert!(expanded.contains(record), "no `{record}` in {expanded}");
    }
}

/// A group, a List collection whose instances hold a computation cell, and the commands the
/// computation-child cases match.
const COMPUTATION_CHILDREN: &str = r#"
use k::builtin::{Int, KSequence};
use k::{KItem, KResult};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Go, Put, Add))]
pub enum Cmd {
    #[k::syntax("go")]
    Go(),
    #[k::syntax("put({x})")]
    Put { x: Int },
    #[k::syntax("add({x})")]
    Add { x: Int },
}

#[k::cell]
pub struct C {
    #[k::cell]
    pub cc: KSequence,
    #[k::cell]
    pub cn: Int,
}

#[k::cell]
pub struct T {
    #[k::cell]
    pub tk: KSequence,
    #[k::cell]
    pub tn: Int,
}

#[k::cell]
pub struct Tqueue {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub tjob: T,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub ccell: C,
    #[k::cell(nested)]
    pub tqueue: Tqueue,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            ccell: C { cc: k::k![], cn: 0 },
            tqueue: Tqueue { tjob: T { tk: k::k![], tn: 0 } },
        }
    }
}
"#;

/// Brackets on a group record's computation child, or on a `cells!` instance record's, are that
/// child's K sequence (ruling R4): the child's entry is read by its declared kind, and brackets
/// on a computation cell are its items wherever it is declared. The readable rules and their
/// `cells!` twins emit the same K, the child's own cell, and `krs expand` writes the brackets
/// back in the record.
#[test]
fn a_record_computation_child_in_brackets_is_its_k_sequence_on_both_routes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = r"
k::rules! {
    for Machine;
    use Cmd::*;

    go: { k: [Go(), ..], ccell: C { cc: [y, ..], .. } } => { k: [..] };
    put: { k: [Put { x }, ..], ccell: C { cc: [z], .. } } => { k: [..], ccell: C { cc: [x], cn: 0 } };
    add: { k: [Add { x }, ..], tjob: [..] } => { k: [..], tjob: [T { tk: [x], tn: 0 }, ..] };
}
";
    let cells = r#"
#[k::rule(label = "go")]
pub fn go(
    y: KItem,
    k::cells! {
        k: k::configuration::KCell(Cmd::Go(), tail @ ..),
        ccell: k::fragment![crate::C { cc: [y, ..], .. }],
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), ..state }
}

#[k::rule(label = "put")]
pub fn put(
    x: Int,
    z: KItem,
    k::cells! {
        k: k::configuration::KCell(Cmd::Put { x }, tail @ ..),
        ccell: k::fragment![crate::C { cc: [z], .. }],
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        ccell: k::fragment![crate::C { cc: [x], cn: 0 }],
        ..state
    }
}

#[k::rule(label = "add")]
pub fn add(
    x: Int,
    k::cells! {
        k: k::configuration::KCell(Cmd::Add { x }, tail @ ..),
        crate::Tqueue::tjob: [..],
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        crate::Tqueue::tjob: [k::fragment![crate::T { tk: [x], tn: 0 }], ..],
        ..state
    }
}
"#;
    let readable = package_over(
        temporary.path(),
        "brackets-readable",
        COMPUTATION_CHILDREN,
        readable,
    );
    let cells = package_over(
        temporary.path(),
        "brackets-cells",
        COMPUTATION_CHILDREN,
        cells,
    );
    let flat = |k: &str| k.split_whitespace().collect::<Vec<_>>().join(" ");
    let readable_k = flat(&emitted_k(target.path(), &readable));
    let cells_k = flat(&emitted_k(target.path(), &cells));
    for sentence in [
        "<cc> Y:KItem ... </cc>",
        "<cc> Z:KItem => X:Int </cc> <cn> _ => 0 </cn>",
        "<tjob> <tk> X:Int </tk> <tn> 0 </tn> </tjob>",
    ] {
        assert!(
            readable_k.contains(sentence),
            "no `{sentence}` in {readable_k}"
        );
        assert!(cells_k.contains(sentence), "no `{sentence}` in {cells_k}");
    }
    let expanded = flat(&expanded(target.path(), &readable));
    for record in [
        "ccell : k::fragment![crate ::C { cc : [y, ..], .. }]",
        "ccell : k::fragment![crate ::C { cc : [x], cn : 0 }]",
    ] {
        assert!(expanded.contains(record), "no `{record}` in {expanded}");
    }
}
