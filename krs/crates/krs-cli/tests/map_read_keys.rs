//! Readable map reads whose key is a pattern, end to end: a key name the
//! subject binds nowhere else matches the key of any entry, so the rule
//! applies once per entry; `_` reads any entry; the `have` clause, whose
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
/// equal to its value keeps that meaning. `krs expand` writes the same
/// rules as `cells!` maps, which emit the same K with named frames.
#[test]
fn a_free_map_read_key_matches_any_entry() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "map-read", &format!("{PREAMBLE}{RULES}"));
    let (definition, spec) = emit(target.path(), &manifest, &temporary.path().join("emitted"));
    let rules = [
        "pick", "pick-any", "two", "two-any", "untyped", "compound", "same",
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
    assert!(
        expanded.contains("map![kk -> vv, rest0 @ ..]")
            && expanded.contains("map![_ -> x, _ -> y, rest0 @ ..]"),
        "{expanded}"
    );
    let pasted = package(temporary.path(), "map-read-expanded", &expanded);
    let (pasted, _) = emit(target.path(), &pasted, &temporary.path().join("pasted"));
    for (label, body) in &rules {
        let framed = sentence(&pasted, label)
            .replace(" ~> Tail:K", "")
            .replace(" Rest0:Map", " ...");
        assert_eq!(&framed.replace(" </k>", " ... </k>"), body, "{label}");
    }
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
