//! A partial construct a sentence evaluates before it knows the construct has a value (a sort
//! projection or a read KRS projects, a builtin operation outside the domain the catalog states
//! for it, a `let` statement whose pattern may not match) is tested first: in a condition, its
//! test is the conjunct before the one that evaluates it; in a pattern's key, the key is a fresh
//! name the condition equates with the lookup after its test (NT-37). Each rule applies where the
//! construct has a value and does not apply where it has none, on k-rust, where an untested
//! construct would leave the condition undefined, and on Java K's LLVM backend, which aborted
//! there before the tests. A claim's and a static clause's tests, which KRS lifts into functions,
//! are tested in the lifted equations' conditions. A test the author wrote below `!` or `||`
//! protects nothing under KRS's reading of the connectives, which keep every operand's
//! definedness, and is reported (`krs::analysis::dead-guard`).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use krs_test_support::{
    fixture_build_env, kompile_reference, krs_command, shared_fixture_target, temp_dir,
};

const PARTIAL: &str = r#"
use k::builtin::{Bool, Int, KSequence, List, Map};
use k::KResult;
use k::Term;

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
#[k::precedence((Proj, Guarded, Look, Index, Bind, Key, Div, Upd, OrIdiom, NotAnd, Pick, Flag))]
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
    #[k::syntax("div {a}")]
    Div { a: Int },
    #[k::syntax("upd {a}")]
    Upd { a: Int },
    #[k::syntax("oridiom {a}")]
    OrIdiom { a: Arg },
    #[k::syntax("notand {a}")]
    NotAnd { a: Arg },
    #[k::syntax("pick {a}")]
    #[k::desugar]
    Pick { a: Int },
    #[k::syntax("flag {b}")]
    Flag { b: Bool },
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

#[k::desugar]
fn pick(k::term![StmtSyntax::Pick(a)]: Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::Flag(k::matches!(10 / a, 5))
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
    #[k::requires(10 / a > 1)]
    div: { k: [Div(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(l.update(a, 0).len() > 0)]
    upd: { k: [Upd(a), ..], items: l, acc: _ } => { k: [..], acc: 1 };
    #[k::requires(!k::is!(Int, a) || k::project!(Int, a) > 0)]
    oridiom: { k: [OrIdiom(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(!(k::is!(Int, a) && k::project!(Int, a) > 0))]
    notand: { k: [NotAnd(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(b)]
    flag: { k: [Flag(b), ..], acc: _ } => { k: [..], acc: 1 };
}

k::claims! {
    for Machine;
    use StmtSyntax::*;

    #[k::claim(all_paths)]
    #[k::requires(k::matches!(m[a], 5))]
    lookreq: { k: [Look(a)], env: m } => { k: [], env: m };
    #[k::claim(all_paths)]
    #[k::ensures(k::matches!(m[a], 5))]
    lookens: { k: [Look(a)], env: m } => { k: [], env: m };
}
"#;

/// Each program, and the `<acc>` its run ends with when the rule it exercises applies (`None`:
/// the rule does not apply, and the run is stuck with `acc 0`): a projection at an `Int` and at
/// `true`, a lookup of a present and an absent key, a read inside the list (a negative index
/// counts from its end) and past it, a `let` pattern a pair matches and an `Int` does not, a
/// division by a divisor other than zero and by zero, a list update inside and past the list,
/// the author's `||` and `!` guards, which do not protect, and a static clause's lifted test of a
/// division at `2` and `3` (at `0` the clause's result has no value, which is not tested).
const PROGRAMS: &[(&str, Option<&str>)] = &[
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
    ("div 3", Some("1")),
    ("div 0", None),
    ("upd 0", Some("1")),
    ("upd 1", None),
    ("upd -1", None),
    ("oridiom 3", Some("1")),
    ("oridiom true", None),
    ("notand 0", Some("1")),
    ("notand true", None),
    ("pick 2", Some("1")),
    ("pick 3", None),
];

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

/// The final `<acc>` of a run's KAST output, and whether its `<k>` is empty.
fn ended(stdout: &str) -> (Option<&str>, bool) {
    let acc = stdout
        .split("`<acc>`(#token(\"")
        .nth(1)
        .and_then(|rest| rest.split('"').next());
    (acc, stdout.contains("`<k>`(.K)"))
}

/// Each condition states its constructs' tests before the conjunct that evaluates them, and
/// one the author's condition already states (`guarded`) is not stated again; the key that
/// looks a map up is a name the condition equates with the lookup after its test; a claim's
/// `k::matches!` over a lookup and a static clause's over a division are functions whose
/// equations test the construct. Each rule applies where its construct has a value and does
/// not where it has none ([`PROGRAMS`]), on k-rust and on Java K's LLVM backend: a run there is
/// stuck where it aborted before the tests (`div 0`: division by zero; `proj true`: a
/// projection that does not apply). The author's tests below `||` and `!` are reported.
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
    let warnings = stderr
        .lines()
        .filter(|line| line.starts_with("warning["))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "warning[krs::analysis::dead-guard]: this projection is tested below `!` or `||` in the conjunct that evaluates it, which does not protect it: `&&`, `||` and `!` keep the definedness of every operand, evaluated or not, so the condition has no value where the projection has none, and KRS tests the projection before the conjunct, so the sentence applies only where it has a value; to apply where it has none, write that case as a sentence of its own (`#[k::requires(!k::is!(S, t))]`), and to say what the condition means, test before the conjunct (`k::is!(S, t) && ..`)",
            "warning[krs::analysis::dead-guard]: this projection is tested below `!` or `||` in the conjunct that evaluates it, which does not protect it: `&&`, `||` and `!` keep the definedness of every operand, evaluated or not, so the condition has no value where the projection has none, and KRS tests the projection before the conjunct, so the sentence applies only where it has a value; to apply where it has none, write that case as a sentence of its own (`#[k::requires(!k::is!(S, t))]`), and to say what the condition means, test before the conjunct (`k::is!(S, t) && ..`)",
        ]
    "#]]
    .assert_debug_eq(&warnings);
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
            "requires (A:Int =/=Int 0) andThenBool ((10 /Int A:Int) >Int 1)",
            "requires B:Bool",
            "requires isInt(A:Arg) andThenBool ({A:Arg}:>Int >Int 0)",
            "requires (A:Int <Int size(L:List)) andThenBool (((0 -Int size(L:List)) <=Int A:Int) andThenBool (isInt(L:List [ A:Int ]) andThenBool ({L:List [ A:Int ]}:>Int >Int 0)))",
            "<env> Krs_Instance0:KItem |-> V:Int ... </env>",
            "requires A:Int in_keys(Kk:Map) andThenBool (Krs_Instance0:KItem ==K (Kk:Map [ A:Int ]))",
            "requires A:Int in_keys(M:Map) andThenBool (notBool ( 5 :=K (M:Map [ A:Int ]) ))",
            "requires A:Int in_keys(M:Map) andThenBool ( 5 :=K (M:Map [ A:Int ]) )",
            "requires (A:Int =/=Int 0) andThenBool (notBool ( 5 :=K 10 /Int A:Int ))",
            "requires A:Int in_keys(M:Map) andThenBool ( 5 :=K (M:Map [ A:Int ]) )",
            "requires A:Int in_keys(M:Map) andThenBool (notBool ( 5 :=K (M:Map [ A:Int ]) ))",
            "requires (A:Int =/=Int 0) andThenBool ( 5 :=K 10 /Int A:Int )",
            "<env> M:Map </env>",
            "requires A:Int in_keys(M:Map) andThenBool (isInt(M:Map [ A:Int ]) andThenBool ({M:Map [ A:Int ]}:>Int >Int 0))",
            "requires isInt(A:Arg) andThenBool (notBool (isInt(A:Arg) andThenBool ({A:Arg}:>Int >Int 0)))",
            "requires isInt(A:Arg) andThenBool ((notBool isInt(A:Arg)) orElseBool ({A:Arg}:>Int >Int 0))",
            "requires isInt(A:Arg) andThenBool ({A:Arg}:>Int >Int 0)",
            "requires (A:Int <Int size(L:List)) andThenBool ((0 <=Int A:Int) andThenBool (size(L:List [ A:Int <- 0 ]) >Int 0))",
        ]
    "#]].assert_debug_eq(&lines);

    for (program, acc) in PROGRAMS {
        let path = temporary.path().join("program.pgm");
        fs::write(&path, program).unwrap();
        let (success, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &[path.to_str().unwrap(), "--output", "kast"],
        );
        let (ended, done) = ended(&stdout);
        assert!(
            success && done == acc.is_some() && ended == Some(acc.unwrap_or("0")),
            "krs run {program}:\n{stdout}\n{stderr}"
        );
    }

    // The same programs on Java K's LLVM backend, from the emitted definition.
    let compiled =
        kompile_reference(&definition, "ORG-KRS-PARTIAL", "ORG-KRS-PARTIAL-SYNTAX").run();
    let krun = std::env::var_os("KRS_K_BIN").map_or_else(
        || PathBuf::from("krun"),
        |directory| PathBuf::from(directory).join("krun"),
    );
    for (program, acc) in PROGRAMS {
        let path = temporary.path().join("program.pgm");
        fs::write(&path, program).unwrap();
        let output = Command::new(&krun)
            .arg("--definition")
            .arg(compiled.path().join("compiled"))
            .arg(&path)
            .args(["--output", "kast"])
            .output()
            .expect("the pinned krun starts");
        let stdout = String::from_utf8(output.stdout).unwrap();
        let (ended, done) = ended(&stdout);
        assert!(
            output.status.success() && done == acc.is_some() && ended == Some(acc.unwrap_or("0")),
            "krun {program}:\n{stdout}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
