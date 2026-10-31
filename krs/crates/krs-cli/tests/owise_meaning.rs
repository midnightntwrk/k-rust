//! What `owise` states, on every route.
//!
//! An `owise` equation gives its function's value wherever no other equation of the function
//! applies, and an `owise` transition applies wherever no other rule applies. For an equation
//! that is a statement about every argument, symbolic ones included, so it is emitted as
//! `owise` itself, never as the rank 200 that orders it: both the emitted K and the native
//! KORE carry `owise`, and the native `owise` axiom holds the condition that no other equation
//! of its function applies. A written priority of 200 or more beside an `owise` sentence would
//! order the two against what `owise` states, so it is refused.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Bool, Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
    impl Exp for Bool;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Go, Pick, Toss))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("go({value})")] Go { value: Int },
    #[k::syntax("pick({value})")] Pick { value: Int },
    #[k::syntax("toss({value})")] Toss { value: Int },
}

#[k::function(total, sort = Bool, syntax = "isOne({value})")]
pub struct IsOne {
    pub value: Term<Int>,
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

#[k::rule(label = "go")]
fn go(k::term![ExpSyntax::Go { value }]: Term<Exp>) -> Term<Exp> {
    value
}

#[k::rule(owise, label = "pick-other")]
fn pick_other(k::term![ExpSyntax::Pick { .. }]: Term<Exp>) -> Term<Exp> {
    0
}

#[k::equation(owise)]
fn is_not_one(k::term![IsOne(_)]: Term<Bool>) -> Term<Bool> {
    false
}
"#;

/// The `isOne` equation and the `pick` transition that `owise` falls back from, and claims
/// whose truth depends on `owise` over a symbolic argument.
const SIBLINGS: &str = r#"
#[k::requires(int::eq(value, 1))]
#[k::equation]
fn is_one(k::term![IsOne(value)]: Term<Bool>) -> Term<Bool> {
    true
}

#[k::rule(label = "pick-one")]
#[k::requires(int::eq(value, 1))]
fn pick_one(k::term![ExpSyntax::Pick { value }]: Term<Exp>) -> Term<Exp> {
    1
}

#[k::claim(all_paths, label = "one-reaches-one")]
#[k::requires(IsOne(i))]
pub fn one_reaches_one(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Go(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(1, ..tail), ..state }
}

#[k::claim(all_paths, label = "one-reaches-two")]
#[k::requires(IsOne(i))]
pub fn one_reaches_two(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Go(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(2, ..tail), ..state }
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A one-package workspace named `owise` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"owise\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-OWISE\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .args(["--package", "owise", "--definition", "main"])
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

/// The KORE axioms of `kore` that carry `attribute`, each up to the next axiom.
fn axioms_with<'a>(kore: &'a str, attribute: &str) -> Vec<&'a str> {
    kore.split("axiom{")
        .skip(1)
        .filter(|axiom| axiom.contains(attribute))
        .collect()
}

/// The emitted K and the native KORE state `owise` itself, and the native `owise` equation's
/// axiom holds the condition that no other equation of `isOne` applies; no sentence carries
/// the rank 200.
#[test]
fn owise_is_emitted_as_itself_on_both_routes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), SIBLINGS);
    let emitted = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", emitted.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let k = fs::read_to_string(emitted.join("definition.k")).unwrap();
    let owise = k
        .lines()
        .map(str::trim)
        .filter(|line| line.contains("owise"))
        .map(|line| line.split(", label(").next().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        owise,
        [
            "rule isOne ( _ ) => false [owise",
            "rule pick ( _ ) => 0 [owise"
        ]
    );
    assert!(!k.contains("priority("), "{k}");

    let built = manifest.with_file_name("built");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "build",
        &["--output", built.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let kore = fs::read_to_string(built.join("definition.kore")).unwrap();
    // The builtin modules have `owise` equations of their own; these are the package's.
    let owise = axioms_with(&kore, "owise{}()")
        .into_iter()
        .filter(|axiom| axiom.contains("isOne") || axiom.contains("pick-other"))
        .collect::<Vec<_>>();
    assert_eq!(owise.len(), 2, "{owise:#?}");
    let equation = owise
        .iter()
        .find(|axiom| axiom.contains("\\equals"))
        .expect("the owise equation's axiom");
    assert!(
        equation.contains("\\not"),
        "the owise equation's axiom holds no condition that the other equation does not apply:\n{equation}"
    );
    assert!(
        axioms_with(&kore, "priority{}(\"200\")")
            .iter()
            .all(|axiom| !axiom.contains("isOne") && !axiom.contains("pick")),
        "an `owise` sentence carries the rank 200"
    );
}

/// Over a symbolic argument the `owise` equation gives `false` only where `V =/=Int 1` is
/// known: `isOne(V)` holds only at 1, so `go(V)` reaches 1, and the claim that it reaches 2,
/// which a vacuous `isOne(V) = false` would prove, fails.
#[test]
fn owise_decides_a_claim_over_a_symbolic_argument() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), SIBLINGS);
    let (success, stdout, stderr) = krs(target.path(), &manifest, "prove", &[]);
    assert!(!success, "{stdout}\n{stderr}");
    let statuses = stdout
        .lines()
        .filter(|line| line.starts_with("ORG-KRS-OWISE-SPEC."))
        .collect::<Vec<_>>();
    assert_eq!(
        statuses,
        [
            "ORG-KRS-OWISE-SPEC.one-reaches-one: proven",
            "ORG-KRS-OWISE-SPEC.one-reaches-two: failed"
        ],
        "{stdout}"
    );
}

/// `krs check` of the package: its `error[..]` headlines with the locations they point at and
/// their help lines.
fn check(target: &Path, manifest: &Path) -> Vec<String> {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "{stderr}");
    let directory = format!("{}/", manifest.parent().unwrap().display());
    stderr
        .lines()
        .filter(|line| {
            let line = line.trim_start();
            line.starts_with("error") || line.starts_with("--> ") || line.starts_with("= help: ")
        })
        .map(|line| line.trim().replace(&directory, ""))
        .collect()
}

/// An equation at priority 200 or more beside an `owise` equation of its function is refused,
/// and so is a transition at such a priority that can apply where an `owise` transition does;
/// one that cannot is never ordered against it and is accepted.
#[test]
fn a_priority_at_or_after_owise_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let refused = [
        (
            "equation",
            "#[k::requires(int::eq(value, 1))]\n#[k::equation(priority = 200)]\nfn is_one(k::term![IsOne(value)]: Term<Bool>) -> Term<Bool> {\n    true\n}\n",
        ),
        (
            "transition",
            "#[k::rule(priority = 250, label = \"pick-late\")]\nfn pick_late(k::term![ExpSyntax::Pick { .. }]: Term<Exp>) -> Term<Exp> {\n    1\n}\n",
        ),
    ]
    .map(|(name, source)| {
        let manifest = package(&temporary.path().join(name), source);
        format!("{name}:\n{}", check(target.path(), &manifest).join("\n"))
    })
    .join("\n");
    expect_test::expect![[r"
        equation:
        error[krs::analysis::priority-after-owise]: equation `is_one` of `IsOne` has priority 200, which orders it with or after the `owise` equation `is_not_one` (`owise` is ranked 200); but `owise` gives the value only where no other equation of `IsOne` applies, so every other equation comes first, and the definition would state two orders between them
        --> src/lib.rs:53:26
        = help: give the equation a priority below 200
        transition:
        error[krs::analysis::priority-after-owise]: rule `pick_late` has priority 250, which orders it with or after the `owise` rule `pick_other` (`owise` is ranked 200), and the two can apply to the same configuration; but `owise` applies only where no other rule applies, so every other rule comes first, and the definition would state two orders between them
        --> src/lib.rs:52:22
        = help: give the rule a priority below 200, or make the two rules disjoint"]]
    .assert_eq(&refused);

    let disjoint = package(
        &temporary.path().join("disjoint"),
        "#[k::rule(priority = 250, label = \"toss\")]\nfn toss(k::term![ExpSyntax::Toss { .. }]: Term<Exp>) -> Term<Exp> {\n    1\n}\n",
    );
    let (success, _, stderr) = krs(target.path(), &disjoint, "check", &[]);
    assert!(success, "{stderr}");
}
