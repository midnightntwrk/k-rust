//! Operators (`a + b`, `a < b`, `!a`, `-a`) end to end: a package written
//! with operators emits exactly the K of the same package written with the
//! calls they denote, in a function body, an equation table, a readable
//! rule, an initializer, and a claim; `krs expand` writes the calls; and
//! operands that choose no single domain are errors.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A package with one placeholder `{NAME}` per term; [`SPELLINGS`] fills each
/// with a call or with operators.
const SOURCE: &str = r#"
use k::builtin::{Bool, Float, Int, KSequence, int, string};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Step, Pause))]
pub enum ExpSyntax {
    #[k::syntax("step({n})")]
    Step { n: Int },
    #[k::syntax("pause")]
    Pause,
}

/// The half-carry flag of an 8-bit addition.
#[k::function(total, internal)]
pub fn HalfCarry(a: Term<Int>, b: Term<Int>) -> Term<Bool> {
    k::term![{HALF_CARRY}]
}

#[k::function(total, internal)]
pub fn Clamp(value: Term<Int>) -> Term<Int>;

k::equations! {
    for Clamp;
    #[k::requires({BELOW})]
    clamp_low: value => 0;
    #[k::requires({ABOVE})]
    clamp_high: value => 255;
    #[k::requires({WITHIN})]
    clamp_mid: value => {MID};
}

/// Half of an even number; its guard holds `==`.
#[k::function(partial, internal)]
#[k::requires({EVEN})]
pub fn Half(value: Term<Int>) -> Term<Int> {
    k::term![int::div(value, 2)]
}

#[k::function(partial, internal)]
pub fn One(value: Term<Int>) -> Term<Int>;

#[k::equation]
#[k::requires({ONE})]
fn one(k::term![One(value)]: Term<Int>) -> Term<Int> {
    value
}

#[k::function(total, internal)]
pub fn Shout(s: Term<string::String>, t: Term<string::String>) -> Term<Bool> {
    k::term![{SHOUT}]
}

#[k::function(total, internal)]
pub fn Close(x: Term<Float>, y: Term<Float>) -> Term<Bool> {
    k::term![{CLOSE}]
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Exp,
        #[k::config_var(name = "START")] start: Int,
    ) -> Self {
        Self {
            k: k::k![pgm],
            pc: {INIT},
            acc: start,
        }
    }
}

k::rules! {
    for Machine;
    use ExpSyntax::*;

    #[k::requires({STEP_REQUIRES})]
    step: { k: [Step(n), ..], pc: p, acc: a } => { k: [..], pc: {STEP_PC}, acc: {STEP_ACC} };
    // `a` is bound by the `acc` cell, which inference reaches after `pc`.
    pause: { k: [Pause(), ..], pc: _, acc: a } => { k: [..], pc: {PAUSE_PC} };
}

#[k::claim(all_paths, label = "step-claim")]
#[k::requires({CLAIM_REQUIRES})]
fn step_claim(
    n: Term<Int>,
    p: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Step(n), tail @ ..),
        pc: k::configuration::Cell(p),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        pc: k::configuration::Cell({CLAIM_PC}),
        ..state
    }
}
"#;

/// Each placeholder of [`SOURCE`], the builtin calls it is written with, and
/// the operators that denote them.
const SPELLINGS: &[(&str, &str, &str)] = &[
    (
        "HALF_CARRY",
        "int::gt(int::add(int::bit_and(a, 15), int::bit_and(b, 15)), 15)",
        "(a & 15) + (b & 15) > 15",
    ),
    ("EVEN", "int::eq(int::rem(value, 2), 0)", "value % 2 == 0"),
    (
        "ONE",
        "int::eq(value, 1) && int::ne(value, 2)",
        "value == 1 && value != 2",
    ),
    ("BELOW", "int::lt(value, 0)", "value < 0"),
    ("ABOVE", "int::gt(value, 255)", "value > 255"),
    (
        "WITHIN",
        "int::ge(value, 0) && int::le(value, 255)",
        "value >= 0 && value <= 255",
    ),
    (
        "MID",
        "int::bit_or(int::bit_xor(int::rem(int::div(value, 3), 7), int::bit_not(value)), int::shift_right(int::shift_left(value, 2), 1))",
        "value / 3 % 7 ^ !value | value << 2 >> 1",
    ),
    (
        "SHOUT",
        "bool::not(string::eq(string::concat(s, \"!\"), t)) && string::le(s, t)",
        "!(s + \"!\" == t) && s <= t",
    ),
    (
        "CLOSE",
        "float::ne(float::neg(x), float::mul(y, 2.0)) || float::eq(float::div(x, y), float::sub(x, -1.5))",
        "-x != y * 2.0 || x / y == x - -1.5",
    ),
    (
        "INIT",
        "int::sub(int::mul(start, start), 1)",
        "start * start - 1",
    ),
    (
        "STEP_REQUIRES",
        "int::gt(n, 0) && int::le(int::add(a, n), 1000)",
        "n > 0 && a + n <= 1000",
    ),
    ("STEP_PC", "int::add(p, 1)", "p + 1"),
    ("STEP_ACC", "int::sub(0, int::bit_xor(a, n))", "-(a ^ n)"),
    ("PAUSE_PC", "int::mul(a, a)", "a * a"),
    (
        "CLAIM_REQUIRES",
        "int::ge(n, 0) && bool::ne(int::lt(p, 10), false)",
        "n >= 0 && (p < 10) != false",
    ),
    ("CLAIM_PC", "int::add(p, 1)", "p + 1"),
];

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes the package `name` with `source` after a `use k::builtin::bool;`.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(
        directory.join("src/lib.rs"),
        format!("#![allow(unused_imports)]\nuse k::builtin::{{bool, float}};\n{source}"),
    )
    .unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-OPERATORS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// [`SOURCE`] with each placeholder written with operators or with calls.
fn spelled(operators: bool) -> String {
    SPELLINGS
        .iter()
        .fold(SOURCE.to_owned(), |source, (name, call, operator)| {
            let placeholder = format!("{{{name}}}");
            assert!(source.contains(&placeholder), "{placeholder} is unused");
            source.replace(&placeholder, if operators { operator } else { call })
        })
}

/// The emitted `.k` files of a package, by name.
fn emitted_k(target: &Path, root: &Path, source: &str) -> Vec<(String, String)> {
    let manifest = package(root, "operators", source);
    let output = root.join("emitted");
    let (success, _, stderr) = krs(
        target,
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let mut files = fs::read_dir(&output)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "k"))
        .map(|path| {
            (
                path.file_name().unwrap().to_string_lossy().into_owned(),
                fs::read_to_string(&path).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    files.sort();
    files
}

#[test]
fn operators_emit_the_k_of_the_calls_they_denote() {
    let target = shared_fixture_target();
    let calls = temp_dir();
    let operators = temp_dir();
    let call_k = emitted_k(target.path(), calls.path(), &spelled(false));
    let operator_k = emitted_k(target.path(), operators.path(), &spelled(true));
    assert_eq!(operator_k, call_k);
    let definition = &operator_k
        .iter()
        .find(|(name, _)| name == "definition.k")
        .expect("a definition is emitted")
        .1;
    for sentence in [
        "((A:Int &Int 15) +Int (B:Int &Int 15)) >Int 15",
        "0 -Int (A:Int xorInt N:Int)",
        "A:Int *Int A:Int",
        "(--Float X:Float) =/=Float (Y:Float *Float 2.0)",
        "(S:String +String \"!\") ==String T:String",
    ] {
        assert!(definition.contains(sentence), "{sentence}:\n{definition}");
    }
}

#[test]
fn expand_writes_the_calls_operators_denote() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "operators", &spelled(true));
    let (success, stdout, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let start = stdout
        .find("fn step(")
        .expect("the readable rule is written");
    let start = stdout[..start].rfind("#[k::requires(").unwrap();
    let end = start + stdout[start..].find("\n}\n").unwrap() + 3;
    expect_test::expect![[r"
        #[k::requires(
            k::builtin::bool::and_then(
                k::builtin::int::gt(n, 0),
                k::builtin::int::le(k::builtin::int::add(a, n), 1000)
            )
        )]
        pub fn step(
            n: k::Term<k::builtin::Int>,
            p: k::Term<k::builtin::Int>,
            a: k::Term<k::builtin::Int>,
            k::cells! {
                k : k::configuration::KCell(crate ::ExpSyntax::Step(n), tail @ ..), pc :
                k::configuration::Cell(p), acc : k::configuration::Cell(a), state @ ..
            }: crate::Machine,
        ) -> crate::Machine {
            k::cells! {
                k : k::configuration::KCell(..tail), pc :
                k::configuration::Cell(k::builtin::int::add(p, 1)), acc :
                k::configuration::Cell(k::builtin::int::sub(0, k::builtin::int::bit_xor(a, n))),
                ..state
            }
        }
    "]]
    .assert_eq(&stdout[start..end]);
}

/// The `#[k::requires]` of a fn's equation, `==` included, is written as the
/// calls it denotes, since a list attribute's arguments print as `key = value`
/// pairs, which would separate the two `=` of `==`.
#[test]
fn expand_writes_an_equation_guard_with_equality_as_calls() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "operators", &spelled(true));
    let (success, stdout, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let guard = |function: &str| {
        let at = stdout.find(function).expect("the equation is written");
        let start = stdout[..at].rfind("#[k::requires(").unwrap();
        stdout[start..at].to_owned()
    };
    expect_test::expect![[r"
        #[k::requires(k::builtin::int::eq(k::builtin::int::rem(value, 2), 0))]
    "]]
    .assert_eq(&guard("fn half("));
    expect_test::expect![[r"
        #[k::requires(
            k::builtin::bool::and_then(
                k::builtin::int::eq(value, 1),
                k::builtin::int::ne(value, 2)
            )
        )]
    "]]
    .assert_eq(&guard("fn one("));
}

/// Guards and ensures conditions holding `==`, written in a claim fn, a rule
/// fn, and a readable claim.
const GUARDS: &str = r#"
#[k::claim(all_paths, label = "settle")]
#[k::requires(n == 1 && p <= 9)]
#[k::exists(q: Int)]
#[k::ensures(q == p + n)]
fn settle(
    n: Term<Int>,
    p: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Step(n), tail @ ..),
        pc: k::configuration::Cell(p),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        pc: k::configuration::Cell(q),
        ..state
    }
}

#[k::rule(label = "jump", priority = 60)]
#[k::requires(n == 2 || n >= 7)]
fn jump(
    n: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Step(n), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), ..state }
}

k::claims! {
    for Machine;
    use ExpSyntax::*;

    #[k::claim(all_paths)]
    #[k::exists(q: Int)]
    #[k::ensures(q == p + n)]
    readable_settle: { k: [Step(n), ..], pc: p } => { k: [..], pc: q };
}
"#;

/// `krs expand` writes an attribute's comparisons and connectives as Rust,
/// `n == 1 && p <= 9`, where printing a list attribute's tokens would
/// separate the two `=` of `==`: a claim fn's `requires` and `ensures`, a
/// rule fn's `requires`, and a readable claim's `ensures`, which it keeps as
/// written. The expanded crate checks.
#[test]
fn expand_writes_comparisons_in_attributes_as_rust() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "operators",
        &format!("{}{GUARDS}", spelled(true)),
    );
    let (success, stdout, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let attributes = |function: &str| {
        let at = stdout.find(function).expect("the item is written");
        let start = stdout[..at].rfind("}\n").unwrap() + 2;
        stdout[start..at]
            .lines()
            .filter(|line| line.starts_with("#[k::requires") || line.starts_with("#[k::ensures"))
            .collect::<Vec<_>>()
            .join("\n")
    };
    expect_test::expect![[r##"
        [
            "#[k::requires(n == 1 && p <= 9)]\n#[k::ensures(q == p + n)]",
            "#[k::requires(n == 2 || n >= 7)]",
            "#[k::ensures(q == p + n)]",
        ]
    "##]]
    .assert_debug_eq(&[
        attributes("fn settle("),
        attributes("fn jump("),
        attributes("fn readable_settle("),
    ]);
    let expanded = package(temporary.path(), "expanded", "");
    fs::write(expanded.with_file_name("src").join("lib.rs"), &stdout).unwrap();
    let (success, _, stderr) = krs(target.path(), &expanded, "check", &[]);
    assert!(success, "the expanded crate does not check:\n{stderr}");
}

/// The first `error[..]` headline and its message of `krs check` on a
/// package whose last item is `item`.
fn check_error(target: &Path, item: &str) -> String {
    let temporary = temp_dir();
    let source = spelled(true) + item;
    let manifest = package(temporary.path(), "operators", &source);
    let (success, _, stderr) = krs(target, &manifest, "check", &[]);
    assert!(!success, "{item} was accepted");
    stderr
        .lines()
        .find(|line| line.starts_with("error["))
        .unwrap_or_else(|| panic!("no error headline:\n{stderr}"))
        .to_owned()
}

#[test]
fn operators_whose_operands_choose_no_one_domain_are_errors() {
    let target = shared_fixture_target();
    let errors = [
        // Two operands of a user sort.
        "#[k::function(total, internal)]
         pub fn Same(left: Term<dyn ExpSort>, right: Term<dyn ExpSort>) -> Term<Bool> {
             k::term![left == right]
         }",
        // `|` in a result is the operator, not a pattern alternative.
        "#[k::function(total, internal)]
         pub fn Either(e: Term<dyn ExpSort>) -> Term<Exp>;
         k::equations! { for Either; either: e => ExpSyntax::Pause() | e; }",
        // An Int and a Float.
        "#[k::function(total, internal)]
         pub fn Mixed(i: Term<Int>, x: Term<Float>) -> Term<Bool> { k::term![i < x] }",
        // Bytes has no operators.
        "#[k::function(total, internal)]
         pub fn SameBytes(b: Term<k::builtin::Bytes>, c: Term<k::builtin::Bytes>) -> Term<Bool> {
             k::term![b == c]
         }",
        // A domain that does not define the operator.
        "#[k::function(total, internal)]
         pub fn Both(p: Term<Bool>, q: Term<Bool>) -> Term<Bool> { k::term![p | q] }",
        "#[k::function(total, internal)]
         pub fn Remainder(x: Term<Float>) -> Term<Float> { k::term![x % 2.0] }",
        // The domain's sort check, as for the call.
        "#[k::function(total, internal)]
         pub fn Bump(e: Term<dyn ExpSort>) -> Term<Exp>;
         #[k::equation]
         fn bump(k::term![Bump(e)]: Term<Exp>) -> Term<Exp> { e + 1 }",
    ]
    .map(|item| check_error(target.path(), item));
    expect_test::expect![[r#"
        [
            "error[krs::analysis::ambiguous-operator]: `==` has operands of sorts `Exp` and `Exp`, which choose no builtin domain; write the operation you mean: `a.eq::<Int>(b)`, `a.eq::<Bool>(b)`, `a.eq::<String>(b)`, `a.eq::<Float>(b)`, or `a.eq::<K>(b)` to compare terms",
            "error[krs::analysis::ambiguous-operator]: `|` has operands of sorts `Exp` and `Exp`, which choose no builtin domain; write the operation you mean: `a.bit_or::<Int>(b)`; `|` joins pattern alternatives only on a left-hand side",
            "error[krs::analysis::ambiguous-operator]: `<` has operands of sorts `Int` and `Float`, which choose the domains `Int` and `Float`; write the operation you mean: `a.lt::<Int>(b)`, `a.lt::<String>(b)`, or `a.lt::<Float>(b)`",
            "error[krs::analysis::ambiguous-operator]: `==` has operands of sorts `Bytes` and `Bytes`, and `Bytes` has no operators, which read only in `Int`, `Bool`, `String`, and `Float`; compare the terms with `a.eq::<K>(b)`",
            "error[krs::syntax::invalid-expression-notation]: `|` is not a `Bool` connective: Rust's precedence would make `a == b | c == d` a parse error; write `a || b`, or `bool::or(a, b)` to evaluate both operands",
            "error[krs::syntax::invalid-expression-notation]: `%` is not an operation of `Float`, whose operators are `+`, `-`, `*`, `/`, `==`, `!=`, `<`, `<=`, `>`, `>=`, and unary `-`; write the operation you mean as a call",
            "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-OPERATORS::bump (equation): application result sort Int is not admissible at sort ORG-KRS-OPERATORS::Exp (sort)",
        ]
    "#]]
    .assert_debug_eq(&errors);
}
