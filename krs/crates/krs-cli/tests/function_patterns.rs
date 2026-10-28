//! A function application where a rule's or an equation's pattern matches a term
//! (`krs::analysis::function-in-pattern`) end to end: authored packages through `krs check`. The class
//! tests cover the computation cell of every sentence form below its root; these cover the roots
//! of the slots a rule matches, the other places a rule matches, and the places the application is
//! the meaning.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, List, Map};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("load({n})")]
    Load { n: Int },
    #[k::syntax("wrap({e})")]
    Wrap { e: KItem },
    #[k::syntax("done")]
    Done(),
}

#[k::function(partial, sort = Int, syntax = "size({a})")]
pub struct Size {
    pub a: Term<KItem>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Exp,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub stack: List,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            acc: ExpSyntax::Done(),
            env: k::map![],
            stack: k::builtin::list::empty(),
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

/// A one-package workspace named `patterns` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"patterns\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-FUNCTION-PATTERNS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    manifest
}

/// `krs check` of the package: whether it passed, and its `error[..]` headlines with the
/// locations they point at.
fn check(target: &Path, manifest: &Path) -> (bool, Vec<String>) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args(["check", "--manifest-path"])
        .arg(manifest)
        .args(["--package", "patterns", "--definition", "main"])
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    let directory = format!("{}/", manifest.parent().unwrap().display());
    let errors = stderr
        .lines()
        .filter(|line| line.starts_with("error") || line.trim_start().starts_with("--> "))
        .map(|line| line.trim().replace(&directory, ""))
        .collect();
    (output.status.success(), errors)
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

/// A function at the root of each slot a rule or an equation matches: a fn rule's subject (a term
/// rule's, an anywhere rule's, a single-body rule's), a `for Sort` clause's subject, a computation
/// item, a cell's content, and a function-context cell.
const ROOT_CASES: [(&str, &str); 9] = [
    (
        "rule-subject",
        "#[k::rule(label = \"twist\")]\nfn twist(k::term![Size(x)]: Term<Int>) -> Term<Int> {\n    0\n}\n",
    ),
    (
        "anywhere-subject",
        "#[k::rule(anywhere, label = \"twist\")]\nfn twist(k::term![Size(x)]: Term<Int>) -> Term<Int> {\n    0\n}\n",
    ),
    (
        "single-body-subject",
        "#[k::rule(label = \"twist\")]\nfn twist(k::term![Size(k::rewrite!(x => ExpSyntax::Done()))]: Term<Int>) {}\n",
    ),
    (
        "sort-rule-subject",
        "k::rules! {\n    for Exp;\n    use ExpSyntax::*;\n    twist: Size(x) => Done();\n}\n",
    ),
    (
        "readable-item",
        "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    twist: { k: [Size(x), ..] } => { k: [Done(), ..] };\n}\n",
    ),
    (
        "cells-item",
        "#[k::rule(label = \"twist\")]\npub fn twist(\n    x: KItem,\n    k::cells! { k: k::configuration::KCell(Size(x), tail @ ..), state @ .. }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(ExpSyntax::Done(), ..tail), ..state }\n}\n",
    ),
    (
        "readable-cell",
        "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    reset: { k: [Wrap(x), ..], acc: Size(x) } => { k: [..], acc: Done() };\n}\n",
    ),
    (
        "cells-cell",
        "#[k::rule(label = \"clear\")]\npub fn clear(\n    x: KItem,\n    k::cells! { k: k::configuration::KCell(ExpSyntax::Wrap(x), tail @ ..), acc: k::configuration::Cell(Size(x)), state @ .. }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(..tail), acc: k::configuration::Cell(ExpSyntax::Done()), ..state }\n}\n",
    ),
    (
        "function-context",
        "#[k::equation]\nfn probe(\n    x: Term<KItem>,\n    k::term![Size(x)]: Term<Int>,\n    k::cells! { acc: k::configuration::Cell(Size(x)), .. }: Machine,\n) -> Term<Int> {\n    0\n}\n",
    ),
];

#[test]
fn a_function_at_the_root_of_any_slot_a_rule_matches_is_refused() {
    let outcomes = outcomes(ROOT_CASES);
    expect_test::expect![[r#"
        [
            (
                "rule-subject",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable and relate it to the application in a guard (`requires`), or, to define the function, write an equation (`#[k::equation]`, or a `k::equations!` row)",
                        "--> src/lib.rs:50:19",
                    ],
                ),
            ),
            (
                "anywhere-subject",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable and relate it to the application in a guard (`requires`), or, to define the function, write an equation (`#[k::equation]`, or a `k::equations!` row)",
                        "--> src/lib.rs:50:19",
                    ],
                ),
            ),
            (
                "single-body-subject",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:50:19",
                    ],
                ),
            ),
            (
                "sort-rule-subject",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable and relate it to the application in a guard (`requires`), or, to define the function, write an equation (`#[k::equation]`, or a `k::equations!` row)",
                        "--> src/lib.rs:52:12",
                    ],
                ),
            ),
            (
                "readable-item",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:52:18",
                    ],
                ),
            ),
            (
                "cells-item",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:52:44",
                    ],
                ),
            ),
            (
                "readable-cell",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:52:37",
                    ],
                ),
            ),
            (
                "cells-cell",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:52:104",
                    ],
                ),
            ),
            (
                "function-context",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:53:45",
                    ],
                ),
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
}

#[test]
fn a_function_below_the_root_of_any_pattern_a_rule_matches_is_refused() {
    let outcomes = outcomes([
        (
            "readable-cell",
            "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    reset: { k: [Done(), ..], acc: Wrap(Size(x)) } => { k: [..], acc: Done() };\n}\n",
        ),
        (
            "cells-cell",
            "#[k::rule(label = \"clear\")]\npub fn clear(\n    x: KItem,\n    k::cells! { k: k::configuration::KCell(ExpSyntax::Done(), tail @ ..), acc: k::configuration::Cell(ExpSyntax::Wrap(Size(x))), state @ .. }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(..tail), acc: k::configuration::Cell(ExpSyntax::Done()), ..state }\n}\n",
        ),
        (
            "function-context",
            "#[k::equation]\nfn probe(\n    x: Term<KItem>,\n    k::term![Size(x)]: Term<Int>,\n    k::cells! { acc: k::configuration::Cell(ExpSyntax::Wrap(Size(x))), .. }: Machine,\n) -> Term<Int> {\n    0\n}\n",
        ),
        (
            "collection-function",
            "#[k::rule(label = \"count\")]\nfn count(k::term![ExpSyntax::Load(k::builtin::list::size(l))]: Term<Exp>) -> Term<Exp> {\n    ExpSyntax::Done()\n}\n",
        ),
    ]);
    expect_test::expect![[r#"
        [
            (
                "readable-cell",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:52:41",
                    ],
                ),
            ),
            (
                "cells-cell",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:52:119",
                    ],
                ),
            ),
            (
                "function-context",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:53:61",
                    ],
                ),
            ),
            (
                "collection-function",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the builtin function `k::builtin::list::size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:50:35",
                    ],
                ),
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// The application is the meaning at an equation's root (a fn's and a table row's), anywhere in a
/// simplification's and a claim's subject, in a map key, and in a result.
#[test]
fn an_application_that_is_the_meaning_is_accepted() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let source = r"
#[k::equation]
fn size_wrap(k::term![Size(ExpSyntax::Wrap(x))]: Term<Int>) -> Term<Int> {
    Size(x)
}

#[k::simplification]
fn size_of_size(k::term![Size(ExpSyntax::Wrap(Size(x)))]: Term<Int>) -> Term<Int> {
    Size(x)
}

k::rules! {
    for Machine;
    use ExpSyntax::*;
    read: { k: [Load(n), ..], env: { Size(n) -> v, .. } } => { k: [Wrap(v), ..] };
}

k::equations! {
    for Size;

    size_done: (ExpSyntax::Done()) => 0;
}

#[k::simplification]
fn size_root(k::term![Size(x)]: Term<Int>) -> Term<Int> {
    Size(x)
}

k::claims! {
    for Machine;
    use ExpSyntax::*;
    #[k::claim(all_paths)]
    sized: { k: [Wrap(Size(x)), ..] } => { k: [..] };
    #[k::claim(all_paths)]
    sized_root: { k: [Size(x), ..] } => { k: [..] };
}
";
    let manifest = package(&temporary.path().join("accepted"), source);
    let (success, errors) = check(target.path(), &manifest);
    assert!(success, "{errors:#?}");
}
