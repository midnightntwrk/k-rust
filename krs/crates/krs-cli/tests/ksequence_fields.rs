//! A declaration over `KSequence`, K's `K`, emits a production whose module
//! declares the sort: a constructor field and a function parameter or result
//! of type `KSequence` make their module import `SORT-K`, and every route
//! accepts the definition. A rule matches a saved
//! sequence and splices it back into the computation.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const SOURCE: &str = r#"
use k::KResult;
use k::Term;
use k::builtin::{Int, KSequence, List};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Park, Resume, Bump, Report, WrapK) > right seq (Seq))]
pub enum Cmd {
    #[k::syntax("park")]
    Park(),
    #[k::syntax("resume")]
    Resume(),
    #[k::syntax("bump")]
    Bump(),
    #[k::syntax("report")]
    Report(),
    #[k::syntax("wrapk ( {body} )")]
    WrapK { body: KSequence },
    #[k::syntax("{first} ; {second}")]
    Seq { first: Stmt, second: Stmt },
}

#[k::function(partial, internal)]
pub fn Body(w: Term<Stmt>) -> Term<KSequence>;

#[k::function(total, internal)]
pub fn Again(b: Term<KSequence>) -> Term<Stmt>;

#[k::equation]
fn body(k::term![Body(Cmd::WrapK(b))]: Term<KSequence>) -> Term<KSequence> {
    b
}

#[k::equation]
fn again(k::term![Again(b)]: Term<Stmt>) -> Term<Stmt> {
    Cmd::WrapK(b)
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub stack: List,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "ACC")] acc: Int,
    ) -> Self {
        Self {
            k: k::k![pgm],
            stack: k::builtin::list::empty(),
            acc,
        }
    }
}

// Saving the rest of the computation has no KRS surface yet.
k::raw_k!(
    r"rule <k> park ~> T:K => bump ~> resume </k> <stack> S:List => ListItem(wrapk(T)) S </stack>"
);

k::rules! {
    for Stmt;
    use Cmd::*;

    seq: Seq(s1, s2) => k::k![s1, s2];
}

k::rules! {
    for Machine;
    use Cmd::*;

    bump: { k: [Bump(), ..], acc: a } => { k: [..], acc: a + 1 };
    report: { k: [Report(), ..], acc: a } => { k: [..], acc: a * 10 };
    resume: { k: [Resume(), ..], stack: [WrapK { body: b }, s @ ..] } => { k: [b, ..], stack: s };
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is `source`.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CONTINUATIONS\"\nallow-raw-k = true\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The `imports` lines of the emitted module `name`.
fn imports(definition: &str, name: &str) -> Vec<String> {
    let start = definition
        .find(&format!("module {name}\n"))
        .unwrap_or_else(|| panic!("no module {name}:\n{definition}"));
    definition[start..]
        .lines()
        .skip(1)
        .take_while(|line| *line != "endmodule")
        .filter_map(|line| line.trim().strip_prefix("imports "))
        .map(str::to_owned)
        .collect()
}

/// Both modules that declare productions over `K` import `SORT-K`, every
/// route checks the definition, and a computation saved in a `KSequence`
/// field runs when a rule splices it back.
#[test]
fn a_ksequence_declaration_imports_the_sort_k_module() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "continuations", SOURCE);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");

    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    for line in [
        "syntax Stmt ::= \"wrapk\" \"(\" K \")\"",
        "syntax K ::= \"body\" \"(\" Stmt \")\"",
        "syntax Stmt ::= \"again\" \"(\" K \")\"",
    ] {
        assert!(definition.contains(line), "{line}:\n{definition}");
    }
    assert!(
        imports(&definition, "ORG-KRS-CONTINUATIONS-SYNTAX").contains(&"SORT-K".to_owned()),
        "{definition}"
    );
    assert!(
        imports(&definition, "ORG-KRS-CONTINUATIONS").contains(&"SORT-K".to_owned()),
        "{definition}"
    );

    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "park ; report").unwrap();
    let (_, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[program.to_str().unwrap(), "-c", "ACC=0"],
    );
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("<k> .K </k> <stack> .List </stack> <acc> 10 </acc>"),
        "{stdout}\n{stderr}"
    );
}
