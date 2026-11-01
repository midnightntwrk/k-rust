//! Several `#[k::requires]` are one condition, their conjunction in written order
//! (`andThenBool`), whatever their place beside the sentence's marker: a later condition is tested
//! only where the earlier ones hold, so it may rely on their definedness. Here the first condition
//! is `value =/=Int 0` and the second divides by `value`, both written before `#[k::rule]`, which
//! rustc expands after them.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const SOURCE: &str = r#"
use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Go))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("go({value})")] Go { value: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}

/// `go(v)` is 1 where 10 divided by `v` exceeds 1, which is tested only where `v` is not 0.
#[k::requires(int::ne(value, 0))]
#[k::requires(int::gt(int::div(10, value), 1))]
#[k::rule(label = "go")]
fn go(k::term![ExpSyntax::Go { value }]: Term<Exp>) -> Term<Exp> {
    1
}

#[k::rule(owise, label = "go-other")]
fn go_other(k::term![ExpSyntax::Go { .. }]: Term<Exp>) -> Term<Exp> {
    0
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A one-package workspace named `conditions` whose library is [`SOURCE`].
fn package(root: &Path) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), SOURCE).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"conditions\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CONDITIONS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    manifest
}

/// Runs `krs <command>` on the package's `main` definition: whether it passed, its stdout and
/// its stderr.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", "conditions", "--definition", "main"])
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

/// The emitted K tests the conditions in written order, and the run applies `go` only where both
/// hold: at 0 the division is never tested, and `go-other` applies.
#[test]
fn two_conditions_before_the_marker_are_tested_in_written_order() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path());
    let emitted = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", emitted.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let k = fs::read_to_string(emitted.join("definition.k")).unwrap();
    let requires = k
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("requires") && line.contains("/Int"))
        .unwrap_or_else(|| panic!("the rule's condition: {k}"));
    assert_eq!(
        requires,
        "requires (Value:Int =/=Int 0) andThenBool ((10 /Int Value:Int) >Int 1) [label(go)]",
        "{k}"
    );

    let mut results = Vec::new();
    for program in ["go(0)", "go(2)", "go(20)"] {
        let file = manifest.with_file_name("program.txt");
        fs::write(&file, program).unwrap();
        let (_, stdout, stderr) = krs(target.path(), &manifest, "run", &[file.to_str().unwrap()]);
        let state = stdout
            .lines()
            .skip_while(|line| line.trim() != "<k>")
            .skip(1)
            .take_while(|line| line.trim() != "</k>")
            .map(str::trim)
            .collect::<Vec<_>>()
            .join(" ");
        assert!(!state.is_empty(), "{program}: {stdout}\n{stderr}");
        results.push(format!("{program} => {state}"));
    }
    assert_eq!(
        results,
        ["go(0) => 0 ~> .K", "go(2) => 1 ~> .K", "go(20) => 0 ~> .K"]
    );
}
