//! What stands at a subject's root, with and without `k::term![..]`, which is optional around a
//! subject and so reads the root alike.
//!
//! An equation defines one function, so its subject's root is that function's application; a
//! simplification rewrites a function's unevaluated application. A constructor's application or
//! a literal there is a value, which evaluation leaves as written, so it defines or simplifies
//! nothing, and a builtin operation is its builtin domain's to define: each is refused at the
//! root's head, also when root alternatives apply one constructor. A subject's root is the
//! constructor or function the sentence matches, so `_`, an alias and a compiler-owned island
//! stand below it, in each alternative of a root `A | B` too.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, int};
use k::{KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Red, Green, Blue, Show, Duo) > right seq (Seq))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("red")] Red(),
    #[k::syntax("green")] Green(),
    #[k::syntax("blue")] Blue(),
    #[k::syntax("show({c})")] Show { c: Stmt },
    #[k::syntax("duo({c}, {n})")] Duo { c: Stmt, n: Int },
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::constructor(sort = Stmt, syntax = "lit({v})")]
pub struct Lit {
    pub v: Term<Int>,
}

#[k::function(total, sort = Int, syntax = "code({c})")]
pub struct Code {
    pub c: Term<Stmt>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm] }
    }
}

k::rules! {
    for Stmt;
    use Cmd::*;
    seq: Seq(s1, s2) => k::k![s1, s2];
}

#[k::rule(label = "show")]
fn show(Cmd::Show { c }: Term<Stmt>) -> Term<Stmt> {
    Code { c }
}

#[k::equation(owise)]
fn code_other(Code { c: _ }: Term<Int>) -> Term<Int> {
    20
}
"#;

/// A function-rooted equation, natively and in `k::term!`, and simplifications rooted at a
/// declared function and at a builtin one.
const ACCEPTED: &str = r"
#[k::equation]
fn code_red(Code { c: Cmd::Red() }: Term<Int>) -> Term<Int> {
    10
}

#[k::equation]
fn code_green(k::term![Code { c: Cmd::Green() }]: Term<Int>) -> Term<Int> {
    11
}

#[k::simplification]
fn code_blue(Code { c: Cmd::Blue() }: Term<Int>) -> Term<Int> {
    20
}

#[k::simplification]
fn add_zero(k::term![int::add(x, 0)]: Term<Int>) -> Term<Int> {
    x
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A one-package workspace named `roots` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"roots\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-SUBJECT-ROOTS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .args(["--package", "roots", "--definition", "main"])
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

/// The emitted rules that mention `needle`, one per line.
fn rules(k: &str, needle: &str) -> String {
    k.lines()
        .map(str::trim)
        .filter(|line| line.starts_with("rule ") && line.contains(needle))
        .collect::<Vec<_>>()
        .join("\n")
}

/// A function's application at the root of an equation's or a simplification's subject is
/// accepted and emitted, with or without `k::term!`.
#[test]
fn a_function_at_the_root_is_accepted() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), ACCEPTED);
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
        rule code ( red ) => 10 [label(krsRule_0e1683227f61042e656a9e40)]
        rule code ( green ) => 11 [label(krsRule_bd44636864a415cfa80aa8d8)]
        rule code ( blue ) => 20 [simplification, label(krsRule_452d243e7d8f3d1119e4aca1)]
        rule X:Int +Int 0 => X:Int [simplification, label(krsRule_730cd6830110d52c0e7845d6)]"]]
    .assert_eq(
        &[
            rules(&k, "rule code ( red"),
            rules(&k, "rule code ( green"),
            rules(&k, "rule code ( blue"),
            rules(&k, "+Int 0"),
        ]
        .join("\n"),
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

/// Each case's `krs check` refusal.
fn refusals<const N: usize>(cases: [(&'static str, &str); N]) -> String {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    cases
        .map(|(name, source)| {
            let manifest = package(&temporary.path().join(name), source);
            format!("{name}:\n{}", check(target.path(), &manifest).join("\n"))
        })
        .join("\n")
}

/// An equation whose subject's root is a constructor, a literal or a builtin operation defines
/// no function, refused at the root's head in each spelling: a `#[k::equation]` fn with and
/// without `k::term!`, root alternatives that apply one constructor, and at the first of root
/// alternatives that applies no function, each alternative being a whole subject. An
/// alternative at another sort than the subject's is first of all at the wrong sort, told before
/// what its head is; its message reads as the descriptor validator's, as every term at a sort its
/// position does not admit does (finding NT-4-1). A
/// collection's element and list notation build a value as a constructor does. A `k::equations!`
/// table names its function in its header, so a constructor there is refused at the header. The
/// class tests cover a constructor in `k::term!` (`terms/equation/subject-root/Cmd::Go()`), whose
/// message the native constructor's case here shares.
#[test]
fn an_equation_rooted_at_no_function_is_refused_at_the_root() {
    expect_test::expect![[r"
        constructor:
        error[krs::analysis::subject-root-not-function]: an equation defines one function, so its subject is that function's application, but `Red` is a constructor: its application is a value, which evaluation leaves as written, so the equation defines no function; to define a function, write its application here, and to rewrite this term in a step of the computation, write a `#[k::rule]`
        --> src/lib.rs:62:11
        alternatives:
        error[krs::analysis::subject-root-not-function]: an equation defines one function, so its subject is that function's application, but `Duo` is a constructor: its application is a value, which evaluation leaves as written, so the equation defines no function; to define a function, write its application here, and to rewrite this term in a step of the computation, write a `#[k::rule]`
        --> src/lib.rs:62:12
        alternatives-term:
        error[krs::analysis::subject-root-not-function]: an equation defines one function, so its subject is that function's application, but `Duo` is a constructor: its application is a value, which evaluation leaves as written, so the equation defines no function; to define a function, write its application here, and to rewrite this term in a step of the computation, write a `#[k::rule]`
        --> src/lib.rs:62:20
        constructor-alternatives:
        error[krs::analysis::subject-root-not-function]: an equation defines one function, so its subject is that function's application, but `Red` is a constructor: its application is a value, which evaluation leaves as written, so the equation defines no function; to define a function, write its application here, and to rewrite this term in a step of the computation, write a `#[k::rule]`
        --> src/lib.rs:62:12
        literal:
        error[krs::analysis::subject-root-not-function]: an equation defines one function, so its subject is that function's application, and `1` applies none: it is a value, which no equation defines; to define a function, write its application here, and to rewrite this term in a step of the computation, write a `#[k::rule]`
        --> src/lib.rs:62:11
        builtin:
        error[krs::analysis::subject-root-not-function]: an equation defines one function the definition declares, so its subject is that function's application, but `k::builtin::int::add(..)` is a builtin operation, which its builtin domain defines; to state a fact about its applications, write a `#[k::simplification]`
        --> src/lib.rs:62:20
        mixed-alternatives:
        error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SUBJECT-ROOTS::not_fn (equation): application result sort ORG-KRS-SUBJECT-ROOTS::Stmt (sort) is not admissible at sort Int
        --> src/lib.rs:62:37
        set-element:
        error[krs::analysis::subject-root-not-function]: an equation defines one function, so its subject is that function's application, but `set::item(..)` builds a value of its builtin domain: its application is a value, which evaluation leaves as written, so the equation defines no function; to define a function, write its application here, and to rewrite this term in a step of the computation, write a `#[k::rule]`
        --> src/lib.rs:62:20
        list-notation:
        error[krs::analysis::subject-root-not-function]: an equation defines one function, so its subject is that function's application, but `[head, ..tail]` builds a value of its builtin domain: its application is a value, which evaluation leaves as written, so the equation defines no function; to define a function, write its application here, and to rewrite this term in a step of the computation, write a `#[k::rule]`
        --> src/lib.rs:62:21
        table:
        error[krs::syntax::invalid-equation-table]: `Lit` is not a non-parametric `#[k::function]`
        --> src/lib.rs:62:9"]].assert_eq(&refusals([
        (
            "constructor",
            "#[k::equation]\nfn not_fn(Cmd::Red(): Term<Stmt>) -> Term<Stmt> {\n    Cmd::Blue()\n}\n",
        ),
        (
            "alternatives",
            "#[k::equation]\nfn not_fn((Cmd::Duo { c: Cmd::Red(), n: 1 } | Cmd::Duo { c: Cmd::Red(), n: 2 }): Term<Stmt>) -> Term<Stmt> {\n    Cmd::Blue()\n}\n",
        ),
        (
            "alternatives-term",
            "#[k::equation]\nfn not_fn(k::term![Cmd::Duo { c: Cmd::Red(), n: 1 } | Cmd::Duo { c: Cmd::Red(), n: 2 }]: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Blue()\n}\n",
        ),
        (
            "constructor-alternatives",
            "#[k::equation]\nfn not_fn((Cmd::Red() | Cmd::Blue()): Term<Stmt>) -> Term<Stmt> {\n    Cmd::Green()\n}\n",
        ),
        (
            "literal",
            "#[k::equation]\nfn not_fn(1: Term<Int>) -> Term<Int> {\n    2\n}\n",
        ),
        (
            "builtin",
            "#[k::equation]\nfn not_fn(k::term![int::add(x, 1)]: Term<Int>) -> Term<Int> {\n    x\n}\n",
        ),
        (
            "mixed-alternatives",
            "#[k::equation]\nfn not_fn((Code { c: Cmd::Red() } | Cmd::Red()): Term<Int>) -> Term<Int> {\n    1\n}\n",
        ),
        (
            "set-element",
            "#[k::equation]\nfn not_fn(k::term![k::builtin::set::item(x)]: Term<k::builtin::Set>) -> Term<k::builtin::Set> {\n    k::builtin::set::empty()\n}\n",
        ),
        (
            "list-notation",
            "#[k::equation]\nfn not_fn(k::term![[x, ..rest]]: Term<k::builtin::List>) -> Term<k::builtin::List> {\n    rest\n}\n",
        ),
        (
            "table",
            "k::equations! {\n    for Lit;\n    lit_one: 1 => Cmd::Red();\n}\n",
        ),
    ]));
}

/// An alias or desugar clause's root is the production it expands, so a root that is no
/// production marked as the clause is (a constructor of an unmarked production, a function) is
/// refused at the root, not at the clause's name; the class tests cover every construct at the
/// root (`terms/{alias,desugar}/subject-root/..`).
#[test]
fn a_static_clause_rooted_at_no_marked_production_is_refused_at_the_root() {
    expect_test::expect![[r"
        alias-constructor:
        error[krs::analysis::invalid-static-clause]: alias clause `red_alias` expands `Cmd::Red`, which is not marked `#[k::alias]`; mark the production `#[k::alias]` or `#[k::alias(recursive)]`
        --> src/lib.rs:62:14
        desugar-function:
        error[krs::analysis::invalid-static-clause]: desugar clause `code_red` expands `Code`, which is not marked `#[k::desugar]`; mark the production `#[k::desugar]` or `#[k::desugar(recursive)]`
        --> src/lib.rs:62:22"]].assert_eq(&refusals([
        (
            "alias-constructor",
            "#[k::alias]\nfn red_alias(Cmd::Red(): Term<Stmt>) -> Term<Stmt> {\n    Cmd::Blue()\n}\n",
        ),
        (
            "desugar-function",
            "#[k::desugar]\nfn code_red(k::term![Code { c: Cmd::Red() }]: Term<Int>) -> Term<Int> {\n    1\n}\n",
        ),
    ]));
}

/// A simplification rewrites a function's unevaluated application, so a constructor, a set's
/// element or a literal at its root, a value, is refused at the root's head, with or without
/// `k::term!`; the class tests cover a constructor and `set::item` in `k::term!`
/// (`terms/simplification/subject-root/{Cmd::Go(),k::builtin::set::item(x)}`), whose messages the
/// cases here share.
#[test]
fn a_simplification_rooted_at_a_value_is_refused_at_the_root() {
    expect_test::expect![[r"
        constructor:
        error[krs::analysis::subject-root-not-function]: a simplification rewrites a function's unevaluated application to an equal, simpler term, but `Red` is a constructor, and its application is a value, which evaluation leaves as written, so the simplification simplifies nothing; to rewrite this term in a step of the computation, write a `#[k::rule]`
        --> src/lib.rs:62:9
        literal:
        error[krs::analysis::subject-root-not-function]: a simplification rewrites a function's unevaluated application to an equal, simpler term, but `1` applies no function and is a value, which evaluation leaves as written, so the simplification simplifies nothing; to rewrite this term in a step of the computation, write a `#[k::rule]`
        --> src/lib.rs:62:9
        list-notation:
        error[krs::analysis::subject-root-not-function]: a simplification rewrites a function's unevaluated application to an equal, simpler term, but `[head, ..tail]` builds a value of its builtin domain, and its application is a value, which evaluation leaves as written, so the simplification simplifies nothing; to rewrite this term in a step of the computation, write a `#[k::rule]`
        --> src/lib.rs:62:19
        set-element:
        error[krs::analysis::subject-root-not-function]: a simplification rewrites a function's unevaluated application to an equal, simpler term, but `set::item(..)` builds a value of its builtin domain, and its application is a value, which evaluation leaves as written, so the simplification simplifies nothing; to rewrite this term in a step of the computation, write a `#[k::rule]`
        --> src/lib.rs:62:18"]].assert_eq(&refusals([
        (
            "constructor",
            "#[k::simplification]\nfn simp(Cmd::Red(): Term<Stmt>) -> Term<Stmt> {\n    Cmd::Blue()\n}\n",
        ),
        (
            "literal",
            "#[k::simplification]\nfn simp(1: Term<Int>) -> Term<Int> {\n    2\n}\n",
        ),
        (
            "list-notation",
            "#[k::simplification]\nfn simp(k::term![[x, ..rest]]: Term<k::builtin::List>) -> Term<k::builtin::List> {\n    rest\n}\n",
        ),
        (
            "set-element",
            "#[k::simplification]\nfn simp(k::term![k::builtin::set::item(x)]: Term<k::builtin::Set>) -> Term<k::builtin::Set> {\n    k::builtin::set::item(x)\n}\n",
        ),
    ]));
}

/// `_`, an alias and a compiler-owned island stand below a subject's root, refused there with
/// and without `k::term!`, in a rule's and an equation's subject and in each alternative of a
/// root `A | B`. A rule fn's refusal shows the `for Sort` clause, whose root is any term of the
/// sort (decision D3), with the fn's rule attribute (an `owise` rule stays `owise`), its other
/// helpers, its subject and its result; an `anywhere` rule has no such clause, and says so. The class tests cover `_` and an island in a rule's and an equation's
/// `k::term!` (`terms/{rule,equation}/subject-root/{_,k::bytes!(b"ab")}`), whose messages the
/// native cases here share.
#[test]
fn a_wildcard_alias_or_island_at_a_subject_root_is_refused_with_or_without_the_wrapper() {
    expect_test::expect![[r#"
        rule-wildcard:
        error[krs::syntax::unsupported-rule-pattern]: unsupported rule pattern: a rule subject's root is the constructor or function the rule matches, so `_` stands only below it
        --> src/lib.rs:62:9
        = help: a rule for any term of a sort is a `for Sort` clause, whose root may be a bare name for the whole subject, `_`, an alias or an island: `k::rules! { for Stmt; #[k::rule(label = "warm", owise)] warm: _ => 1; }`
        equation-wildcard:
        error[krs::syntax::unsupported-rule-pattern]: unsupported rule pattern: a rule subject's root is the constructor or function the rule matches, so `_` stands only below it
        --> src/lib.rs:62:8
        alternative-wildcard-term:
        error[krs::syntax::unsupported-rule-pattern]: unsupported rule pattern: a rule subject's root is the constructor or function the rule matches, so `_` stands only below it
        --> src/lib.rs:62:18
        = help: a rule for any term of a sort is a `for Sort` clause, whose root may be a bare name for the whole subject, `_`, an alias or an island: `k::rules! { for Stmt; #[k::rule(label = "warm", owise)] warm: _ => 1; }`
        alias-term:
        error[krs::syntax::invalid-pattern-as]: `x @ pattern` cannot alias a whole rule subject: its root is the matched constructor or function; alias a subterm instead
        --> src/lib.rs:62:18
        = help: a rule for any term of a sort is a `for Sort` clause, whose root may be a bare name for the whole subject, `_`, an alias or an island: `k::rules! { for Stmt; #[k::rule(label = "warm", owise)] warm: k::term![x @ Cmd::Red()] => x; }`
        island:
        error[krs::syntax::unsupported-rule-pattern]: unsupported rule pattern: a rule subject's root is the constructor or function the rule matches, so a compiler-owned island stands below it, as in `F(k::fragment![Group { .. }])` or `F(k::bytes!(b".."))`
        --> src/lib.rs:62:9
        = help: a rule for any term of a sort is a `for Sort` clause, whose root may be a bare name for the whole subject, `_`, an alias or an island: `k::rules! { for Stmt; #[k::rule(label = "warm", owise)] warm: k::bytes!(b"ab") => 1; }`
        rewrite-term:
        error[krs::syntax::unsupported-rule-pattern]: unsupported rule pattern: a whole-subject `k::rewrite!(from => to)` is an ordinary rule: write `from` as the subject and `to` as the result, or mark the change below the subject's root
        --> src/lib.rs:62:18
        plain-wildcard:
        error[krs::syntax::unsupported-rule-pattern]: unsupported rule pattern: a rule subject's root is the constructor or function the rule matches, so `_` stands only below it
        --> src/lib.rs:63:9
        = help: a rule for any term of a sort is a `for Sort` clause, whose root may be a bare name for the whole subject, `_`, an alias or an island: `k::rules! { for Stmt; #[k::requires(true)] warm: _ => Cmd::Show { c: Cmd::Red() }; }`
        anywhere-wildcard:
        error[krs::syntax::unsupported-rule-pattern]: unsupported rule pattern: a rule subject's root is the constructor or function the rule matches, so `_` stands only below it
        --> src/lib.rs:62:9
        = help: an `anywhere` rule rewrites the application its subject's root names wherever that application occurs, so no form writes one for any term of a sort"#]].assert_eq(&refusals([
        (
            "rule-wildcard",
            "#[k::rule(label = \"warm\", owise)]\nfn warm(_: Term<Stmt>) -> Term<Stmt> {\n    1\n}\n",
        ),
        (
            "equation-wildcard",
            "#[k::equation(owise)]\nfn any(_: Term<Int>) -> Term<Int> {\n    3\n}\n",
        ),
        (
            "alternative-wildcard-term",
            "#[k::rule(label = \"warm\", owise)]\nfn warm(k::term![_ | Cmd::Red()]: Term<Stmt>) -> Term<Stmt> {\n    1\n}\n",
        ),
        (
            "alias-term",
            "#[k::rule(label = \"warm\", owise)]\nfn warm(k::term![x @ Cmd::Red()]: Term<Stmt>) -> Term<Stmt> {\n    x\n}\n",
        ),
        (
            "island",
            "#[k::rule(label = \"warm\", owise)]\nfn warm(k::bytes!(b\"ab\"): Term<Stmt>) -> Term<Stmt> {\n    1\n}\n",
        ),
        (
            "rewrite-term",
            "#[k::rule(label = \"warm\")]\nfn warm(k::term![k::rewrite!(Cmd::Red() => Cmd::Green())]: Term<Stmt>) {}\n",
        ),
        (
            "plain-wildcard",
            "#[k::rule]\n#[k::requires(true)]\nfn warm(_: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Show { c: Cmd::Red() }\n}\n",
        ),
        (
            "anywhere-wildcard",
            "#[k::rule(anywhere, label = \"warm\")]\nfn warm(_: Term<Int>) -> Term<Int> {\n    1\n}\n",
        ),
    ]));
}

/// A `for Sort` clause's root is any term of the clause's sort: a bare name binds it, `_` is it
/// unnamed, and an alias or an island stands there as below a constructor. `k::term![..]` is
/// optional around the root, so it reads its payload alike, and parentheses denote nothing: each
/// wrapped or parenthesized root emits the rule its bare spelling does. The class tests cover `x`, `_` and an alias at a `KItem` clause's root,
/// bare and wrapped (`terms/sort-rule/subject-root{,-term}/..`); here the clause's sort is a
/// declared one, which `_` matches as a variable of that sort.
#[test]
fn a_clause_root_reads_alike_bare_and_in_the_wrapper() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let emitted = [
        ("name", "s", "Cmd::Show { c: s }"),
        ("wildcard", "_", "Cmd::Blue()"),
        ("alias", "s @ Cmd::Red()", "Cmd::Show { c: s }"),
    ]
    .map(|(name, root, result)| {
        let spellings = [
            root.to_owned(),
            format!("k::term![{root}]"),
            format!("({root})"),
        ];
        let [bare, wrapped, parenthesized] = spellings.map(|root| {
            let source = format!(
                "k::rules! {{\n    for Stmt;\n    #[k::rule(owise)]\n    any: {root} => {result};\n}}\n"
            );
            let manifest = package(
                &temporary.path().join(format!("{name}-{}", root.len() + usize::from(root.starts_with('(')))),
                &source,
            );
            let output = manifest.with_file_name("emitted");
            let (success, _, stderr) = krs(
                target.path(),
                &manifest,
                "emit-k",
                &["--output", output.to_str().unwrap()],
            );
            assert!(success, "{name}: {root}: {stderr}");
            let k = fs::read_to_string(output.join("definition.k")).unwrap();
            let mut lines = k.lines().map(str::trim).skip_while(|line| *line != "rule [any]:");
            let head = lines
                .next()
                .unwrap_or_else(|| panic!("{name}: {root}: no rule `any` in\n{k}"));
            std::iter::once(head)
                .chain(lines.take_while(|line| !line.starts_with("rule ") && *line != "endmodule"))
                .collect::<Vec<_>>()
                .join(" ")
        });
        assert_eq!(bare, wrapped, "{name}: the wrapper reads its root as the bare root");
        assert_eq!(bare, parenthesized, "{name}: parentheses denote nothing");
        format!("{name}: {bare}")
    });
    expect_test::expect![[r"
        name: rule [any]: <k> S:Stmt => show ( S:Stmt ) ... </k> [owise]
        wildcard: rule [any]: <k> _:Stmt => blue ... </k> [owise]
        alias: rule [any]: <k> ( red #as S:Stmt ) => show ( S:Stmt ) ... </k> [owise]"]]
    .assert_eq(&emitted.join("\n"));
}
