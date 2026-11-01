//! A partial construct a sentence evaluates before it knows the construct has a value (a sort
//! projection or a read KRS projects, a lookup, a list read, a `let` statement whose pattern may
//! not match) is tested first: in a condition, its test is the conjunct before the one that
//! evaluates it; in a pattern's key, the key is a fresh name the condition equates with the
//! lookup after its test (NT-37). Each rule applies where the construct has a value and does not
//! apply where it has none, on k-rust as K's matching logic reads it, where an untested
//! construct would leave the condition undefined (and abort Java K's LLVM backend).

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PARTIAL: &str = r#"
use k::builtin::{Bool, Int, KSequence, List, Map};
use k::KResult;

k::sorts! {
    Stmt;
    Arg;
    Value: KResult;
    impl Value for Int;
    impl Arg for Int;
    impl Arg for Bool;
}

#[k::constructors(sort = Arg, result = KResult)]
pub enum ArgSyntax {
    #[k::syntax("pair {a} {b}")]
    Pair { a: Int, b: Int },
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Proj, Guarded, Look, Index, Bind, Key))]
pub enum StmtSyntax {
    #[k::syntax("proj {a}")]
    Proj { a: Arg },
    #[k::syntax("guarded {a}")]
    Guarded { a: Arg },
    #[k::syntax("look {a}")]
    Look { a: Int },
    #[k::syntax("index {a}")]
    Index { a: Int },
    #[k::syntax("bind {a}")]
    Bind { a: Arg },
    #[k::syntax("key {a}")]
    Key { a: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub keys: Map,
    #[k::cell]
    pub items: List,
    #[k::cell]
    pub acc: Value,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: k::builtin::map![1 -> 5],
            keys: k::builtin::map![1 -> 1],
            items: k::builtin::list::item(7),
            acc: 0,
        }
    }
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    #[k::requires(k::project!(Int, a) > 0)]
    proj: { k: [Proj(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(k::is!(Int, a) && k::project!(Int, a) > 0)]
    guarded: { k: [Guarded(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(m[a] > 0)]
    look: { k: [Look(a), ..], env: m, acc: _ } => { k: [..], acc: 1 };
    #[k::requires(l[a] > 0)]
    index: { k: [Index(a), ..], items: l, acc: _ } => { k: [..], acc: 1 };
    #[k::requires({ let ArgSyntax::Pair { a: x, b: _ } = a; x > 0 })]
    bind: { k: [Bind(a), ..], acc: _ } => { k: [..], acc: 1 };
    key: { k: [Key(a), ..], keys: kk, env: { kk[a] -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-PARTIAL\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// Each condition states its constructs' tests before the conjunct that evaluates them, and
/// one the author's condition already states (`guarded`) is not stated again; the key that
/// looks a map up is a name the condition equates with the lookup after its test. Each rule
/// applies where its construct has a value and does not where it has none: a projection at an
/// `Int` and at `true`, a lookup of a present and an absent key, a read inside the list (a
/// negative index counts from its end) and past it, a `let` pattern a pair matches and an `Int`
/// does not.
#[test]
fn a_partial_construct_is_tested_before_the_sentence_evaluates_it() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "partial-conditions", PARTIAL);
    let output = temporary.path().join("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    let lines = definition
        .lines()
        .map(str::trim)
        .filter(|line| line.contains("requires") || line.contains("<env>"))
        .map(|line| line.split(" [label(").next().unwrap_or(line).to_owned())
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "<env> 1 |-> 5 </env>",
            "requires ( pair _ _ :=K A:Arg ) andThenBool ( #let pair X:Int _ = A:Arg #in X:Int >Int 0 )",
            "requires isInt(A:Arg) andThenBool ({A:Arg}:>Int >Int 0)",
            "requires (A:Int <Int size(L:List)) andThenBool (((0 -Int size(L:List)) <=Int A:Int) andThenBool (isInt(L:List [ A:Int ]) andThenBool ({L:List [ A:Int ]}:>Int >Int 0)))",
            "<env> Krs_Instance0:KItem |-> V:Int ... </env>",
            "requires A:Int in_keys(Kk:Map) andThenBool (Krs_Instance0:KItem ==K (Kk:Map [ A:Int ]))",
            "<env> M:Map </env>",
            "requires A:Int in_keys(M:Map) andThenBool (isInt(M:Map [ A:Int ]) andThenBool ({M:Map [ A:Int ]}:>Int >Int 0))",
            "requires isInt(A:Arg) andThenBool ({A:Arg}:>Int >Int 0)",
        ]
    "#]].assert_debug_eq(&lines);

    for (program, acc) in [
        ("proj 3", Some("1")),
        ("proj true", None),
        ("guarded 3", Some("1")),
        ("guarded true", None),
        ("look 1", Some("1")),
        ("look 2", None),
        ("index 0", Some("1")),
        ("index -1", Some("1")),
        ("index 1", None),
        ("bind pair 1 2", Some("1")),
        ("bind 3", None),
        ("key 1", Some("5")),
        ("key 2", None),
    ] {
        let path = temporary.path().join("program.pgm");
        fs::write(&path, program).unwrap();
        let (success, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &[path.to_str().unwrap(), "--output", "kast"],
        );
        let ended = stdout
            .split("`<acc>`(#token(\"")
            .nth(1)
            .and_then(|rest| rest.split('"').next());
        let done = stdout.contains("`<k>`(.K)");
        assert!(
            success && done == acc.is_some() && ended == Some(acc.unwrap_or("0")),
            "{program}:\n{stdout}\n{stderr}"
        );
    }
}
