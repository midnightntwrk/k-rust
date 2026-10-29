//! Rows of the position table (`krs_syntax::positions`) that a parser once decided, end to end:
//! authored packages through `krs check`, each refusal with its class's one code at the
//! construct.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, Map};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Wrap, Pair, Done, Swap))]
pub enum ExpSyntax {
    #[k::syntax("wrap({e})")]
    Wrap { e: Exp },
    #[k::syntax("pair({a}, {b})")]
    Pair { a: Exp, b: Exp },
    #[k::syntax("done")]
    Done(),
    #[k::syntax("swap({e})")]
    Swap { e: Exp },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            env: k::map![],
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

/// A one-package workspace named `rows` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"rows\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-POSITION-ROWS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .args(["--package", "rows", "--definition", "main"])
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

/// `krs check` of the package: whether it passed, and its `error[..]` headlines with the
/// locations they point at.
fn check(target: &Path, manifest: &Path) -> (bool, Vec<String>) {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    let directory = format!("{}/", manifest.parent().unwrap().display());
    let errors = stderr
        .lines()
        .filter(|line| line.starts_with("error") || line.trim_start().starts_with("--> "))
        .map(|line| line.trim().replace(&directory, ""))
        .collect();
    (success, errors)
}

/// Each case's package and its `krs check` outcome.
fn outcomes<const N: usize>(
    cases: [(&'static str, &str); N],
) -> [(&'static str, (bool, Vec<String>)); N] {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    cases.map(|(name, source)| {
        let manifest = package(&temporary.path().join(name), source);
        (name, check(target.path(), &manifest))
    })
}

/// A `let` pattern reads its value by one shape, so it takes no alias and no alternatives, in a
/// result as in a condition; the refusal points at the alias and at the `|`.
#[test]
fn a_let_pattern_takes_no_alias_and_no_alternatives() {
    let outcomes = outcomes([
        (
            "alias-in-result",
            "#[k::rule(label = \"unwrap\")]\nfn unwrap(k::term![ExpSyntax::Swap { e }]: Term<Exp>) -> Term<Exp> {\n    let w @ ExpSyntax::Wrap { .. } = e;\n    w\n}\n",
        ),
        (
            "alternatives-in-result",
            "#[k::rule(label = \"unwrap\")]\nfn unwrap(k::term![ExpSyntax::Swap { e }]: Term<Exp>) -> Term<Exp> {\n    let (ExpSyntax::Done() | ExpSyntax::Wrap { .. }) = e;\n    e\n}\n",
        ),
        (
            "alias-in-condition",
            "k::rules! {\n    for Exp;\n    use ExpSyntax::*;\n    #[k::requires({ let w @ Wrap { .. } = e; k::matches!(w, Wrap { .. }) })]\n    unwrap: Swap { e } => e;\n}\n",
        ),
    ]);
    expect_test::expect![[r#"
        [
            (
                "alias-in-result",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-let]: a `let` pattern destructures one value, which a bare name already names whole: write `let p = e; let P = p;` for `p @ P`; here it stands in a `let` pattern in the result of a `#[k::rule]` fn",
                        "--> src/lib.rs:43:9",
                    ],
                ),
            ),
            (
                "alternatives-in-result",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-let]: a `let` reads its value by one pattern, whose names the rest of its block uses: test which shape a value has with `k::matches!`, or match each shape in a sentence of its own; here it stands in a `let` pattern in the result of a `#[k::rule]` fn",
                        "--> src/lib.rs:43:10",
                    ],
                ),
            ),
            (
                "alias-in-condition",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-let]: a `let` pattern destructures one value, which a bare name already names whole: write `let p = e; let P = p;` for `p @ P`; here it stands in a `let` pattern in the `requires` condition of a `k::rules!` sort rule",
                        "--> src/lib.rs:44:25",
                    ],
                ),
            ),
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}

/// `..base` builds a record from a matched one, so a pattern refuses it at the base: a `k::term!`
/// subject, a `for Sort` clause's subject, and a readable record's computation item.
#[test]
fn a_record_update_in_a_pattern_is_refused_at_its_base() {
    let outcomes = outcomes([
        (
            "term-subject",
            "#[k::rule(label = \"open\")]\nfn open(k::term![ExpSyntax::Swap { e: ExpSyntax::Pair { a: x, ..p } }]: Term<Exp>) -> Term<Exp> {\n    x\n}\n",
        ),
        (
            "clause-subject",
            "k::rules! {\n    for Exp;\n    use ExpSyntax::*;\n    open: Swap { e: Pair { a: x, ..p } } => x;\n}\n",
        ),
        (
            "readable-item",
            "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    open: { k: [Swap { e: Pair { a: x, ..p } }, ..] } => { k: [x, ..] };\n}\n",
        ),
    ]);
    expect_test::expect![[r#"
        [
            (
                "term-subject",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-record-update]: `..base` builds a record whose unlisted fields are those of the record the alias `base` matched, which only a term a sentence builds can say; a pattern denotes no record by it, and leaves out the fields it does not constrain with `..`; here it stands in the subject of a `#[k::rule]` fn",
                        "--> src/lib.rs:42:65",
                    ],
                ),
            ),
            (
                "clause-subject",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-record-update]: `..base` builds a record whose unlisted fields are those of the record the alias `base` matched, which only a term a sentence builds can say; a pattern denotes no record by it, and leaves out the fields it does not constrain with `..`; here it stands in the subject of a `k::rules!` sort rule",
                        "--> src/lib.rs:44:36",
                    ],
                ),
            ),
            (
                "readable-item",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-record-update]: `..base` builds a record whose unlisted fields are those of the record the alias `base` matched, which only a term a sentence builds can say; a pattern denotes no record by it, and leaves out the fields it does not constrain with `..`; here it stands in the subject of a readable rule",
                        "--> src/lib.rs:44:42",
                    ],
                ),
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// A single-body rule whose subject marks no change is a mistake of the whole sentence, told at
/// the fn's name; a construct its subject's root or its guard may not hold is a mistake told by
/// its spelling and position alone, so it is told first, as it is with a rewrite: alternatives,
/// which the one term rewritten in place cannot be, a record update, a `let` block, and a rewrite
/// in a guard. A binder list that declares a name the subject does not bind is a names mistake,
/// told after it.
#[test]
fn a_single_body_rule_tells_a_misplaced_root_before_its_missing_rewrite() {
    let outcomes = outcomes([
        (
            "no-rewrite",
            "#[k::rule(label = \"idle\")]\nfn idle(k::term![ExpSyntax::Done()]: Term<Exp>) {}\n",
        ),
        (
            "alternatives",
            "#[k::rule(label = \"idle\")]\nfn idle(k::term![ExpSyntax::Done() | ExpSyntax::Wrap { .. }]: Term<Exp>) {}\n",
        ),
        (
            "record-update",
            "#[k::rule(label = \"idle\")]\nfn idle(k::term![ExpSyntax::Pair { a: x, ..x }]: Term<Exp>) {}\n",
        ),
        (
            "let",
            "#[k::rule(label = \"idle\")]\nfn idle(k::term![{ let y = x; y }]: Term<Exp>) {}\n",
        ),
        (
            "rewrite-in-guard",
            "#[k::rule(label = \"idle\")]\n#[k::requires(k::rewrite!(true => false))]\nfn idle(k::term![ExpSyntax::Done()]: Term<Exp>) {}\n",
        ),
        (
            "binder-list",
            "#[k::rule(label = \"idle\")]\nfn idle(y: Term<Int>, k::term![ExpSyntax::Done()]: Term<Exp>) {}\n",
        ),
    ]);
    expect_test::expect![[r#"
        [
            (
                "no-rewrite",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-local-rewrite]: a single-body rule must change something: mark what changes in its subject with `k::rewrite!(from => to)`, or return a result",
                        "--> src/lib.rs:42:4",
                    ],
                ),
            ),
            (
                "alternatives",
                (
                    false,
                    [
                        "error[krs::analysis::invalid-pattern-or]: `A | B` (K's #Or) matches one of several terms, and a subject rewritten as one term in place stands for the one term it matched: write one sentence per alternative; here it stands in the subject of a single-body `#[k::rule]` fn",
                        "--> src/lib.rs:42:18",
                    ],
                ),
            ),
            (
                "record-update",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-record-update]: `..base` builds a record whose unlisted fields are those of the record the alias `base` matched, which only a term a sentence builds can say; a pattern denotes no record by it, and leaves out the fields it does not constrain with `..`; here it stands in the subject of a single-body `#[k::rule]` fn",
                        "--> src/lib.rs:42:44",
                    ],
                ),
            ),
            (
                "let",
                (
                    false,
                    [
                        "error[krs::expand::let-outside-term]: a `let` block (K's #let) computes a term, the application `#fun(P => B)(E)` of a function generated for that block alone, which no term holds, so it stands where a term is built or a condition computed, never in a pattern, which matches terms as they are; a pattern's map key computes its value, but `#let` binds its pattern's names, and in a rule's left side those names would read as the rule's pattern variables; a `cells!` cell value holds none for now, in a result as in a pattern: write the block in a readable rule, a `#[k::rule]` fn's result or a condition; here it stands in the subject of a single-body `#[k::rule]` fn",
                        "--> src/lib.rs:42:20",
                    ],
                ),
            ),
            (
                "rewrite-in-guard",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-local-rewrite]: `k::rewrite!` (K's local =>) marks what changes inside the subject of a single-body rule or the hole of a context, once and outside any local pattern; here it stands in the `requires` condition of a single-body `#[k::rule]` fn",
                        "--> src/lib.rs:42:15",
                    ],
                ),
            ),
            (
                "binder-list",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-local-rewrite]: a single-body rule must change something: mark what changes in its subject with `k::rewrite!(from => to)`, or return a result",
                        "--> src/lib.rs:42:4",
                    ],
                ),
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// A single-body rule's map changes values: a rewrite in a key is refused at the rewrite, and the
/// same rewrite in the value is accepted.
#[test]
fn a_rewrite_in_a_map_key_is_refused_at_the_rewrite() {
    let rule = |entry: &str| {
        format!(
            "#[k::rule(label = \"rekey\")]\npub fn rekey(\n    x: Exp,\n    v: KItem,\n    k::cells! {{\n        k: k::configuration::KCell(k::rewrite!(ExpSyntax::Swap {{ e: x }} => ()), ..),\n        env: k::configuration::Cell(k::map![{entry}, ..]),\n        state @ ..\n    }}: Machine,\n) {{}}\n"
        )
    };
    let outcomes = outcomes([
        (
            "in-key",
            rule("k::rewrite!(x => ExpSyntax::Done()) -> v").as_str(),
        ),
        (
            "in-value",
            rule("x -> k::rewrite!(v => ExpSyntax::Done())").as_str(),
        ),
    ]);
    expect_test::expect![[r#"
        [
            (
                "in-key",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-local-rewrite]: a map key is what the map is looked up by, and a rewrite there would move the entry to another key, a removal and an insertion that may meet a key the map already holds: a rewrite in a map changes a value, `key -> k::rewrite!(old => new)`, and a rule with a result moves an entry with `map::remove` and `map::update`; here it stands in a map key in the subject of a single-body `cells!` rule",
                        "--> src/lib.rs:47:45",
                    ],
                ),
            ),
            (
                "in-value",
                (
                    true,
                    [],
                ),
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// Single-body rules whose rewrites build their right sides with a `let` and a `k::matches!` test:
/// each names its own binders, which the right side reads within their scope.
const RIGHT_SIDE_SCOPES: &str = r#"
#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Step, Test, No, Yes))]
pub enum StepSyntax {
    #[k::syntax("step({e}, {flag})")]
    Step { e: KItem, flag: Exp },
    #[k::syntax("test({e}, {flag})")]
    Test { e: KItem, flag: Exp },
    #[k::syntax("no")]
    No(),
    #[k::syntax("yes")]
    Yes(),
}

#[k::rule(label = "swap")]
fn swap(
    k::term![StepSyntax::Step {
        e: k::rewrite!(p => { let ExpSyntax::Pair { a: x, b: y } = p; ExpSyntax::Pair { a: y, b: x } }),
        flag: k::rewrite!(StepSyntax::No() => StepSyntax::Yes()),
    }]: Term<Exp>,
) {}

#[k::rule(label = "twin")]
fn twin(
    k::term![StepSyntax::Test {
        e: k::rewrite!(p => k::matches!(p, ExpSyntax::Pair { a: x, b: x })),
        flag: k::rewrite!(StepSyntax::No() => StepSyntax::Yes()),
    }]: Term<Exp>,
) {}
"#;

/// The emitted term rule labelled `label`, one line.
fn rule<'a>(k: &'a str, label: &str) -> &'a str {
    k.lines()
        .find(|line| line.ends_with(&format!("[label({label})]")))
        .unwrap_or_else(|| panic!("rule `{label}` is emitted:\n{k}"))
        .trim()
}

/// A rewrite's right side binds names of its own with a `let` and a `k::matches!` pattern; the
/// rules emit those binders local to their constructs, build natively, and run.
#[test]
fn a_right_side_reads_the_names_it_binds() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), RIGHT_SIDE_SCOPES);
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let k = fs::read_to_string(output.join("definition.k")).unwrap();
    expect_test::expect![[r"
        rule step ( (P:KItem => ( #let pair ( X:Exp , Y:Exp ) = P:KItem #in pair ( Y:Exp , X:Exp ) )) , (no => yes) ) [label(swap)]
        rule test ( (P:KItem => ( pair ( X:Exp , X:Exp ) :=K P:KItem )) , (no => yes) ) [label(twin)]"]].assert_eq(&format!("{}\n{}", rule(&k, "swap"), rule(&k, "twin")));
    let program = manifest.with_file_name("program.txt");
    let runs = [
        "step(pair(1, 2), no)",
        "test(pair(1, 1), no)",
        "test(pair(1, 2), no)",
    ]
    .map(|source| {
        fs::write(&program, source).unwrap();
        let (_, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &[program.to_str().unwrap()],
        );
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        let start = flat
            .find("<k>")
            .unwrap_or_else(|| panic!("{source}:\n{stdout}\n{stderr}"));
        let end = flat.find("</k>").unwrap() + "</k>".len();
        format!("{source} => {}", &flat[start..end])
    });
    expect_test::expect![[r#"
        [
            "step(pair(1, 2), no) => <k> step(pair(2, 1), yes) ~> .K </k>",
            "test(pair(1, 1), no) => <k> test(true, yes) ~> .K </k>",
            "test(pair(1, 2), no) => <k> test(false, yes) ~> .K </k>",
        ]
    "#]]
    .assert_debug_eq(&runs);
}
