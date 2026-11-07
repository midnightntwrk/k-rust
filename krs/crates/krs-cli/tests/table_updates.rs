//! A `for Sort` table clause's `update env = map::update(env, k, v)` writes the whole cell `env`
//! with the term, `env` naming the cell's current value: `<env> Env => Env [ K <- V ] </env>`. So
//! a key already in the map takes the new value and a new key is added, end to end: `krs check`
//! accepts the clause, `krs emit-k` writes the rewrite, and the program runs alike on k-rust and on
//! Java K's LLVM backend. The update's base must be the cell itself; another base is refused.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use krs_test_support::{
    fixture_build_env, kompile_reference, krs_command, shared_fixture_target, temp_dir,
};

const HEAD: &str = r#"
use k::builtin::{Int, KSequence, Map, map};
use k::KResult;

k::sorts! {
    Stmt;
    Value: KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Put) > right seq (Seq))]
pub enum StmtSyntax {
    #[k::syntax("put {key} {value}")]
    Put { key: Int, value: Int },
    #[k::syntax("{a} ; {b}")]
    Seq { a: Stmt, b: Stmt },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Int, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: map::empty(),
        }
    }
}
"#;

const RULES: &str = r"
k::rules! {
    for Stmt;
    use StmtSyntax::*;

    seq: Seq(a, b) => k![a, b];
    put: Put(key, value) => () where update env = map::update(env, key, value);
}
";

/// Writes key 1 twice, so the second write replaces an entry the map holds, and key 2 once, into
/// an empty map: it ends with `<k>` empty and `<env>` `1 |-> 7 2 |-> 3`.
const PROGRAM: &str = "put 1 5 ; put 1 7 ; put 2 3";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is `HEAD` and `rules`.
fn package(root: &Path, name: &str, rules: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{HEAD}{rules}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-TABLE-UPDATE\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The final state's values in a KAST print: whether `<k>` is empty, and which `key |-> value`
/// entries of Ints it holds, sorted, so the backends' entry orders agree.
fn final_values(kast: &str) -> (bool, Vec<String>) {
    let token = |text: &str| format!("#token(\"{text}\",\"Int\")");
    let entries = (1..=2)
        .flat_map(|key| [3, 5, 7].map(move |value| (key, value)))
        .filter(|(key, value)| {
            kast.contains(&format!(
                "`_|->_`({},{})",
                token(&key.to_string()),
                token(&value.to_string())
            ))
        })
        .map(|(key, value)| format!("{key} |-> {value}"))
        .collect();
    (kast.contains("`<k>`(.K)"), entries)
}

#[test]
fn a_table_update_writes_the_whole_cell_on_every_route() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "table-update", RULES);

    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "krs check:\n{stderr}");

    let output = temporary.path().join("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "krs emit-k:\n{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    let put = definition
        .lines()
        .map(str::trim)
        .filter(|line| line.contains("<env>"))
        .map(|line| line.split(" [label(").next().unwrap_or(line))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "<env> .Map </env>",
            "<env> Env:Map => Env:Map [ Key:Int <- Value:Int ] </env>",
        ]
    "#]]
    .assert_debug_eq(&put);

    let program = temporary.path().join("program.pgm");
    fs::write(&program, PROGRAM).unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[program.to_str().unwrap(), "--output", "kast"],
    );
    assert!(success, "krs run:\n{stdout}\n{stderr}");
    let expected = (true, vec!["1 |-> 7".to_owned(), "2 |-> 3".to_owned()]);
    assert_eq!(final_values(&stdout), expected, "krs run:\n{stdout}");

    // The same program on Java K's LLVM backend, from the emitted definition.
    let compiled = kompile_reference(
        &definition,
        "ORG-KRS-TABLE-UPDATE",
        "ORG-KRS-TABLE-UPDATE-SYNTAX",
    )
    .run();
    let krun = std::env::var_os("KRS_K_BIN").map_or_else(
        || PathBuf::from("krun"),
        |directory| PathBuf::from(directory).join("krun"),
    );
    let output = Command::new(&krun)
        .arg("--definition")
        .arg(compiled.path().join("compiled"))
        .arg(&program)
        .args(["--output", "kast"])
        .output()
        .expect("the pinned krun starts");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success(),
        "krun:\n{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(final_values(&stdout), expected, "krun:\n{stdout}");
}

/// The update's base is the cell's current value, so a base naming anything else is refused where
/// it is written.
#[test]
fn a_table_update_of_another_base_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rules = r"
k::rules! {
    for Stmt;
    use StmtSyntax::*;

    put: Put(key, value) => () where update env = map::update(other, key, value);
}
";
    let manifest = package(temporary.path(), "table-update-other", rules);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(
        !success && stderr.contains("the update base must be the cell `env`"),
        "krs check:\n{stderr}"
    );
}
