//! Readable map reads whose key is a pattern, end to end: a key name the
//! subject binds nowhere else matches the key of any entry, so the rule
//! applies once per entry; `_` reads any entry, and a value `_` (also
//! `have m[k] -> let _`) any value;
//! the `have` clause, whose
//! `let` marks what it introduces, rejects a key bound nowhere.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Id, Int, KSequence, Map, map};
use k::KResult;

k::sorts! {
    Stmt;
    Value: KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Skip, Pick, Two, Seq))]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("pick")]
    Pick(),
    #[k::syntax("two")]
    Two(),
    #[k::syntax("seq {s}")]
    Seq { s: Stmt },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Value>,
    #[k::cell]
    pub raw: Map,
    #[k::cell]
    pub acc: Value,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "ENV")] env: Map<Id, Value>,
        #[k::config_var(name = "ACC")] acc: Value,
    ) -> Self {
        Self {
            k: k::k![pgm],
            env,
            raw: map::empty(),
            acc,
        }
    }
}
"#;

const RULES: &str = r"
k::rules! {
    for Machine;
    use StmtSyntax::*;

    pick: { k: [Skip(), ..], env: { kk -> vv, .. }, acc: _ } => { k: [..], acc: vv };
    pick_any: { k: [Pick(), ..], env: { _ -> vv, .. }, acc: _ } => { k: [..], acc: vv };
    two: { k: [Two(), ..], env: { a -> x, b -> y, .. }, acc: _ } => { k: [..], acc: x };
    two_any: { k: [Seq(Two()), ..], env: { _ -> x, _ -> y, .. }, acc: _ } => { k: [..], acc: y };
    untyped: { k: [Seq(Skip()), ..], raw: { rk -> rv, .. }, acc: _ } => { k: [..], acc: rv } where rk: Id, rv: Value;
    compound: { k: [Seq(Pick()), ..], raw: { Seq(s) -> rv, .. } } => { k: [s, ..] } where rv: Value;
    same: { k: [Seq(Seq(Skip())), ..], raw: { kv -> kv, .. } } => { k: [..] } where kv: Int;
    wild: { k: [Seq(Seq(Pick())), ..], env: { a -> _, b -> _, .. }, acc: _ } => { k: [..], acc: 1 };
    typed_wild: { k: [Seq(Seq(Two())), ..], raw: { rk -> _, rj -> _, .. }, acc: _ } => { k: [..], acc: 1 } where rk: Id, rj: Id, _: Value;
}

k::claims! {
    for Machine;
    use StmtSyntax::*;

    #[k::claim(one_path)]
    picked: { k: [Skip()], env: { key -> value, .. }, acc: _ } => { k: [], acc: value };
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is `library`.
fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-MAP-READ\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The sentence's body lines in the emitted K, joined.
fn sentence(source: &str, label: &str) -> String {
    let start = source
        .find(&format!(" [{label}]:"))
        .unwrap_or_else(|| panic!("no sentence {label}:\n{source}"));
    source[start..]
        .lines()
        .skip(1)
        .take_while(|line| {
            let line = line.trim_start();
            !line.starts_with("rule") && !line.starts_with("claim") && !line.is_empty()
        })
        .map(str::trim)
        .filter(|line| *line != "endmodule")
        .collect::<Vec<_>>()
        .join(" ")
}

fn emit(target: &Path, manifest: &Path, output: &Path) -> (String, String) {
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    (
        fs::read_to_string(output.join("definition.k")).unwrap(),
        fs::read_to_string(output.join("spec.k")).unwrap_or_default(),
    )
}

/// A key name bound nowhere else is a variable of the map pattern, typed by
/// the map's key type; `_` is an anonymous key; two of either are two
/// distinct entries; a call's arguments bind and its head does not; a key
/// equal to its value keeps that meaning. A value `_` binds a value of its
/// own, at the cell's value sort or the sort `_: S` writes, so two of them
/// read two entries whatever their values. `krs expand` writes the same
/// rules as `cells!` maps, which emit the same K with named frames, a value
/// `_` as a fresh binder.
#[test]
fn a_free_map_read_key_matches_any_entry() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "map-read", &format!("{PREAMBLE}{RULES}"));
    let (definition, spec) = emit(target.path(), &manifest, &temporary.path().join("emitted"));
    let rules = [
        "pick",
        "pick-any",
        "two",
        "two-any",
        "untyped",
        "compound",
        "same",
        "wild",
        "typed-wild",
    ]
    .map(|label| (label, sentence(&definition, label)));
    expect_test::expect![[r#"
        [
            (
                "pick",
                "<k> skip => .K ... </k> <env> Kk:Id |-> Vv:Value ... </env> <acc> _ => Vv:Value </acc>",
            ),
            (
                "pick-any",
                "<k> pick => .K ... </k> <env> _ |-> Vv:Value ... </env> <acc> _ => Vv:Value </acc>",
            ),
            (
                "two",
                "<k> two => .K ... </k> <env> A:Id |-> X:Value B:Id |-> Y:Value ... </env> <acc> _ => X:Value </acc>",
            ),
            (
                "two-any",
                "<k> seq (two) => .K ... </k> <env> _ |-> X:Value _ |-> Y:Value ... </env> <acc> _ => Y:Value </acc>",
            ),
            (
                "untyped",
                "<k> seq (skip) => .K ... </k> <raw> Rk:Id |-> Rv:Value ... </raw> <acc> _ => Rv:Value </acc>",
            ),
            (
                "compound",
                "<k> seq (pick) => S:Stmt ... </k> <raw> seq S:Stmt |-> Rv:Value ... </raw>",
            ),
            (
                "same",
                "<k> seq (seq (skip)) => .K ... </k> <raw> Kv:Int |-> Kv:Int ... </raw>",
            ),
            (
                "wild",
                "<k> seq (seq (pick)) => .K ... </k> <env> A:Id |-> V5F:Value B:Id |-> V5F31:Value ... </env> <acc> _ => 1 </acc>",
            ),
            (
                "typed-wild",
                "<k> seq (seq (two)) => .K ... </k> <raw> Rk:Id |-> V5F:Value Rj:Id |-> V5F31:Value ... </raw> <acc> _ => 1 </acc>",
            ),
        ]
    "#]]
    .assert_debug_eq(&rules);
    assert_eq!(
        sentence(&spec, "picked"),
        "<k> skip => .K </k> <env> Key:Id |-> Value:Value ... </env> <acc> _ => Value:Value </acc> [one-path]"
    );

    // The expansion, pasted back, emits the same rules with named frames.
    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let printed = expanded.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        printed.contains("map![kk -> vv, rest0 @ ..]")
            && printed.contains("map![_ -> x, _ -> y, rest0 @ ..]")
            && printed.contains("map![a -> value, b -> _1, rest0 @ ..]")
            && printed.contains("map![rk -> value, rj -> _1, rest0 @ ..]"),
        "{expanded}"
    );
    let pasted = package(temporary.path(), "map-read-expanded", &expanded);
    let (pasted, _) = emit(target.path(), &pasted, &temporary.path().join("pasted"));
    for (label, body) in &rules {
        // The first value `_` is printed as the binder `value`.
        let framed = sentence(&pasted, label)
            .replace(" ~> Tail:K", "")
            .replace(" Rest0:Map", " ...")
            .replace("|-> Value:", "|-> V5F:");
        assert_eq!(&framed.replace(" </k>", " ... </k>"), body, "{label}");
    }
}

/// Two value `_`s are two binders: the rule reads two entries whatever
/// values they hold, where one binder read twice would need equal values.
#[test]
fn two_value_wildcards_read_entries_of_different_values() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "map-read", &format!("{PREAMBLE}{RULES}"));
    let path = temporary.path().join("wild.pgm");
    fs::write(&path, "seq seq pick").unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[
            path.to_str().unwrap(),
            "-c",
            "ENV=x |-> 1 y |-> 2",
            "-c",
            "ACC=0",
            "--output",
            "kast",
        ],
    );
    assert!(success, "{stderr}");
    assert!(
        stdout.contains("`<k>`(.K)") && stdout.contains("`<acc>`(#token(\"1\",\"Int\"))"),
        "{stdout}"
    );
}

/// The rule applies once for each entry: `krs search` finds one final state
/// per entry, for a named key and for `_`.
#[test]
fn search_reaches_one_state_per_entry() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "map-read", &format!("{PREAMBLE}{RULES}"));
    for program in ["skip", "pick"] {
        let path = temporary.path().join(format!("{program}.pgm"));
        fs::write(&path, program).unwrap();
        let (success, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "search",
            &[
                path.to_str().unwrap(),
                "-c",
                "ENV=x |-> 1 y |-> 2",
                "-c",
                "ACC=0",
                "--output",
                "kast",
            ],
        );
        assert!(success, "{stderr}");
        let mut accumulators = stdout
            .lines()
            .filter_map(|line| {
                line.split("`<acc>`(#token(\"")
                    .nth(1)
                    .and_then(|rest| rest.split('"').next())
            })
            .collect::<Vec<_>>();
        accumulators.sort_unstable();
        assert_eq!(accumulators, ["1", "2"], "{program}:\n{stdout}");
        assert!(
            stderr.contains("krs search: 2 solutions"),
            "{program}:\n{stderr}"
        );
    }
}

/// A language whose sort rules read two map cells with `have .. -> let _`.
const HAVE_WILDCARDS: &str = r#"
use k::builtin::{Id, Int, KSequence, Map, map};
use k::KResult;

k::sorts! {
    Stmt;
    Value: KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Skip, Get, Typed))]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("get {x}")]
    Get { x: Id },
    #[k::syntax("typed {x}")]
    Typed { x: Id },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Value>,
    #[k::cell]
    pub other: Map<Id, Value>,
    #[k::cell]
    pub raw: Map,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "ENV")] env: Map<Id, Value>,
        #[k::config_var(name = "OTHER")] other: Map<Id, Value>,
    ) -> Self {
        Self {
            k: k::k![pgm],
            env,
            other,
            raw: map::empty(),
        }
    }
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    both: Get(x) => Skip() where have env[x -> let _], have other[x -> let _];
    typed: Typed(x) => Skip() where have env[x -> let _], have raw[x -> let _], _: Value;
}
"#;

/// Each `have m[k] -> let _` binds a value of its own, as a record read's
/// value `_` does: two of them read entries of different values, and
/// `_: S` narrows each. `krs expand` writes them as fresh binders, which emit
/// the same K.
#[test]
fn two_have_wildcards_are_two_binders() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "map-read-have-wild", HAVE_WILDCARDS);
    let (definition, _) = emit(target.path(), &manifest, &temporary.path().join("emitted"));
    let rules = ["both", "typed"].map(|label| (label, sentence(&definition, label)));
    assert_eq!(
        rules,
        [
            (
                "both",
                "<k> get X:Id => skip ... </k> <env> X:Id |-> V5F:Value ... </env> <other> X:Id |-> V5F31:Value ... </other>".to_owned(),
            ),
            (
                "typed",
                "<k> typed X:Id => skip ... </k> <env> X:Id |-> V5F:Value ... </env> <raw> X:Id |-> V5F31:Value ... </raw>".to_owned(),
            ),
        ]
    );

    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let printed = expanded.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        printed.contains("map![x -> value, rest0 @ ..]")
            && printed.contains("map![x -> _1, rest1 @ ..]"),
        "{expanded}"
    );
    let pasted = package(temporary.path(), "map-read-have-wild-expanded", &expanded);
    let (pasted, _) = emit(target.path(), &pasted, &temporary.path().join("pasted"));
    for (label, body) in &rules {
        let framed = sentence(&pasted, label)
            .replace(" ~> Tail:K", "")
            .replace(" Rest0:Map", " ...")
            .replace(" Rest1:Map", " ...")
            .replace("|-> Value:", "|-> V5F:");
        assert_eq!(&framed.replace(" </k>", " ... </k>"), body, "{label}");
    }

    // One binder read twice would need equal values; `x` maps to 1 and 2.
    let path = temporary.path().join("get.pgm");
    fs::write(&path, "get x").unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[
            path.to_str().unwrap(),
            "-c",
            "ENV=x |-> 1",
            "-c",
            "OTHER=x |-> 2",
            "--output",
            "kast",
        ],
    );
    assert!(success, "{stderr}");
    assert!(stdout.contains("`<k>`(stmtSyntaxSkip(.KList))"), "{stdout}");
}

/// `have` marks what it introduces with `let`, so its key names a binding of
/// the rule; a key bound nowhere is a KRS error that points to the record
/// read, not a Rust resolution error.
#[test]
fn a_have_clause_rejects_a_key_bound_nowhere() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "map-read-have",
        &format!(
            "{PREAMBLE}
k::rules! {{
    for Stmt;
    use StmtSyntax::*;

    unseq: Seq(s) => s where have env[kk -> let v];
}}
"
        ),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(!success);
    let headlines = stderr
        .lines()
        .filter(|line| line.starts_with("error"))
        .collect::<Vec<_>>();
    assert_eq!(
        headlines,
        [
            "error[krs::syntax::rust-syntax]: `kk` is bound nowhere in this rule; `have` reads the entry at a key the rule already knows; to read any entry, bind the key with a record read `env: { kk -> v, .. }`"
        ],
        "{stderr}"
    );
}

const LOCAL_KEYS: &str = r#"
use k::builtin::{Int, KSequence, Map, Set, map};
use k::KResult;

k::sorts! {
    Stmt;
    Value: KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Look, Test, Pick, Elem, See))]
pub enum StmtSyntax {
    #[k::syntax("look {n}")]
    Look { n: Int },
    #[k::syntax("test {n}")]
    Test { n: Int },
    #[k::syntax("pick {n}")]
    Pick { n: Int },
    #[k::syntax("elem {n} {s}")]
    Elem { n: Int, s: Set },
    #[k::syntax("see {a}")]
    See { a: k::KItem },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub acc: Value,
    #[k::cell]
    pub seen: Set,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "ENV")] env: Map,
    ) -> Self {
        Self {
            k: k::k![pgm],
            env,
            acc: 0,
            seen: k::builtin::set::empty(),
        }
    }
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    look: { k: [Look(n), ..], env: { { let m = n; m + 1 } -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
    test: { k: [Test(n), ..], env: { k::matches!(n, 0) -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
}

#[k::rule(label = "elem")]
fn elem(k::term![StmtSyntax::Elem(n, k::builtin::set::item(n + 1))]: k::Term<Stmt>) -> k::Term<Stmt> {
    StmtSyntax::Look(n)
}

#[k::rule(label = "see")]
fn see(
    a: k::Term<k::KItem>,
    r: k::Term<Set>,
    k::cells! { k: k::configuration::KCell(StmtSyntax::See(a), tail @ ..), seen: k::configuration::Cell(k::builtin::set::concat(k::builtin::set::item(k::project!(Int, a)), r)), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), seen: k::configuration::Cell(r), ..state }
}
"#;

/// A `let` block and `k::matches!` in a key the pattern computes denote their values, functions
/// of the names they read, which KRS lifts into functions of their own: the key applies the
/// function and is looked up, as a key applying any function is (finding NT-3-2). A set's element
/// reads as a key does, notation included, and a projection there is guarded as in a key, in a
/// `#[k::rule]` fn's term and a `cells!` rule's cell alike (NT-3-1). The rules apply where the map
/// holds the computed key, and not elsewhere.
#[test]
fn a_local_function_in_a_key_is_lifted_and_looked_up() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "local-keys", LOCAL_KEYS);
    let (definition, _) = emit(target.path(), &manifest, &temporary.path().join("emitted"));
    let digests = definition
        .split("krsLocal_")
        .skip(1)
        .filter_map(|rest| rest.get(..24))
        .collect::<std::collections::BTreeSet<_>>();
    let mut normalized = definition.clone();
    for (index, digest) in digests.iter().enumerate() {
        normalized =
            normalized.replace(&format!("krsLocal_{digest}"), &format!("krsLocal_{index}"));
    }
    let lines = normalized
        .lines()
        .map(str::trim)
        .filter(|line| {
            line.contains("krsLocal_") || line.contains("SetItem") || line.contains("isInt")
        })
        .map(|line| {
            line.split(" [label(krsRule_")
                .next()
                .unwrap_or(line)
                .to_owned()
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "syntax Int ::= \"krsLocal_0\" \"(\" Int \")\" [symbol(krsLocal_0), function]",
            "syntax Bool ::= \"krsLocal_1\" \"(\" Int \")\" [symbol(krsLocal_1), function]",
            "rule elem N:Int SetItem(N:Int +Int 1) => look N:Int [label(elem)]",
            "rule krsLocal_0 ( N:Int ) => ( #let M:Int = N:Int #in M:Int +Int 1 )",
            "rule krsLocal_1 ( N:Int ) => true",
            "rule krsLocal_1 ( N:Int ) => false",
            "<env> krsLocal_0 ( N:Int ) |-> V:Int ... </env>",
            "<seen> SetItem(A:KItem) R:Set => R:Set </seen>",
            "requires isInt(A:KItem)",
            "<env> krsLocal_1 ( N:Int ) |-> V:Int ... </env>",
        ]
    "#]]
    .assert_debug_eq(&lines);

    for (program, env, acc) in [
        ("look 1", "2 |-> 7 5 |-> 9", Some("7")),
        ("look 4", "2 |-> 7 5 |-> 9", Some("9")),
        ("look 3", "2 |-> 7 5 |-> 9", None),
        ("test 0", "true |-> 3 false |-> 4", Some("3")),
        ("test 5", "true |-> 3 false |-> 4", Some("4")),
        ("test 5", "true |-> 3", None),
    ] {
        let path = temporary.path().join("program.pgm");
        fs::write(&path, program).unwrap();
        let env = format!("ENV={env}");
        let (success, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &[path.to_str().unwrap(), "-c", &env, "--output", "kast"],
        );
        let ended = stdout
            .split("`<acc>`(#token(\"")
            .nth(1)
            .and_then(|rest| rest.split('"').next());
        let done = stdout.contains("`<k>`(.K)");
        match acc {
            Some(acc) => assert!(
                success && done && ended == Some(acc),
                "{program} over {env}:\n{stdout}\n{stderr}"
            ),
            None => assert!(
                !done && ended == Some("0"),
                "{program} over {env}:\n{stdout}\n{stderr}"
            ),
        }
    }
}

/// A key that also holds a name nothing else binds selects an entry by matching the map's
/// evaluated keys, which no `let` block's or test's value is: the construct is refused there,
/// with its class, at the construct.
#[test]
fn a_local_function_in_a_selection_key_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rules = LOCAL_KEYS.replace(
        "{ let m = n; m + 1 } -> v",
        "StmtSyntax::Elem({ let m = n; m + 1 }, z) -> v",
    );
    let manifest = package(temporary.path(), "local-keys-selection", &rules);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(!success);
    let headlines = stderr
        .lines()
        .filter(|line| line.starts_with("error") || line.contains('^'))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "error[krs::expand::let-outside-term]: a `let` block stands in a map key that also holds the name `z`, which nothing else binds, so the key selects an entry by matching the evaluated keys the map holds rather than computing the key looked up; a `let` block is the application of a function generated for it, which no evaluated key is, so the key never matches: a key holds it only where the pattern binds every other name the key holds elsewhere, so that the key is computed and looked up",
            "   |                                                         ^^^^^^^^^^",
        ]
    "#]].assert_debug_eq(&headlines);
}
