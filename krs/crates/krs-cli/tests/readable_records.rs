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
