//! A function declared `total` is checked (TOTAL-PARTIAL-BODY): each equation's result has a
//! value wherever the equation applies, or `krs check` refuses the function at the construct or
//! the application that is not shown to have one. The three definitions whose false claims
//! `krs prove` reported `proven` are refused; each way out the error names is accepted; and with
//! the function declared `partial` the false claim fails. `assumed = "reason"` is the unchecked
//! spelling, recorded in the IR.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A machine whose `keep` statement reads a function of the memory and drops the value: the
/// claim that `keep` reaches `pc: 1` on every memory is false where the function has no value.
/// `{functions}` are the functions under test, `{read}` the application `keep` drops.
const MACHINE: &str = r#"
use k::KResult;
use k::builtin::{Bool, Int, KSequence, List, Map, String, kequal, string};

k::sorts! {
    Stmt: k::KItem;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("keep")]
    KeepStmt(),
}

{functions}

/// Total, and ignores its second argument.
#[k::function(total, internal)]
pub fn Keep(kept: k::Term<Int>, _dropped: k::Term<Int>) -> k::Term<Int> {
    kept
}

#[k::configuration]
pub struct Machine {
    #[k::cell(name = "k")]
    pub k: KSequence,
    #[k::cell(name = "pc")]
    pub pc: Int,
    #[k::cell(name = "memory")]
    pub memory: Map<Int, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] program: Stmt) -> Self {
        Self {
            k: k::k![program],
            pc: 0,
            memory: k::map![],
        }
    }
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    keep_step: { k: [KeepStmt(), ..], pc: _, memory: m } => { k: [..], pc: Keep(1, {read}) };
}

k::claims! {
    for Machine;
    use StmtSyntax::*;

    /// False where `{read}` has no value: the state after `keep` is no state there.
    #[k::claim(all_paths)]
    keep_reaches_one: { k: [KeepStmt()], pc: _, memory: m } => { k: [], pc: 1, memory: m };
}
"#;

/// A lookup of a key the map may lack.
const AT9: &str = r"
#[k::function(TOTALITY, internal)]
pub fn At9(memory: k::Term<Map<Int, Int>>) -> k::Term<Int> {
    memory[9]
}
";

/// A division whose divisor may be zero.
const INV: &str = r"
#[k::function(TOTALITY, internal)]
pub fn Inv(memory: k::Term<Map<Int, Int>>) -> k::Term<Int> {
    100 / memory.len()
}
";

/// An application of a function declared `partial`.
const WRAP: &str = r"
#[k::function(partial, internal)]
pub fn PAt(memory: k::Term<Map<Int, Int>>) -> k::Term<Int> {
    memory[9]
}

#[k::function(TOTALITY, internal)]
pub fn Wrap(memory: k::Term<Map<Int, Int>>) -> k::Term<Int> {
    PAt(memory)
}
";

/// Every way out the error names, and the functions the check does not judge.
const WAYS_OUT: &str = r"
/// The domain is stated, and `owise` gives the rest: a typed map's read needs its key and the
/// sort KRS projects it to.
#[k::function(total, internal)]
pub fn Guarded(memory: k::Term<Map<Int, Int>>) -> k::Term<Int>;

k::equations! {
    for Guarded;
    #[k::requires(memory.contains_key(9) && k::is!(Int, memory[9]))]
    guarded_present: memory => memory[9];
    #[k::equation(owise)]
    guarded_absent: _ => 0;
}

/// A condition that evaluates the construct holds only where it has a value.
#[k::function(total, internal)]
pub fn Positive(memory: k::Term<Map<Int, Int>>) -> k::Term<Int>;

k::equations! {
    for Positive;
    #[k::requires(memory[9] > 0)]
    positive_present: memory => memory[9];
    #[k::equation(owise)]
    positive_other: _ => 0;
}

#[k::function(total, internal)]
pub fn Nonzero(x: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Nonzero;
    #[k::requires(x != 0)]
    nonzero: x => 100 / x;
    #[k::equation(owise)]
    zero: _ => 0;
}

/// A bound that implies the divisor's test.
#[k::function(total, internal)]
pub fn Above(x: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Above;
    #[k::requires(x > 0)]
    above: x => 100 / x;
    #[k::equation(owise)]
    not_above: _ => 0;
}

#[k::function(total, internal)]
pub fn Shifted(b: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Shifted;
    #[k::requires(b >= 0)]
    shifted: b => 1 << b;
    #[k::equation(owise)]
    not_shifted: _ => 0;
}

#[k::function(total, internal)]
pub fn AsInt(t: k::Term<k::KItem>) -> k::Term<Int>;

k::equations! {
    for AsInt;
    #[k::requires(k::is!(Int, t))]
    as_int: t => k::project!(Int, t);
    #[k::equation(owise)]
    not_int: _ => 0;
}

#[k::function(total, internal)]
pub fn Element(l: k::Term<List<Int>>, i: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Element;
    #[k::requires(0 <= i && i < l.len() && k::is!(Int, l[i]))]
    element_inside: (l, i) => l[i];
    #[k::equation(owise)]
    element_outside: (_, _) => 0;
}

/// An `if` block is two equations, whose conditions are its test and the test's negation.
#[k::function(total, internal)]
pub fn Branch(x: k::Term<Int>) -> k::Term<Int> {
    if x != 0 { 100 / x } else { 0 }
}

/// A read with a default at the sort the map holds has a value on every map.
#[k::function(total, internal)]
pub fn OrZero(memory: k::Term<Map<Int, k::KItem>>) -> k::Term<k::KItem> {
    memory.get_or(9, 0)
}

/// A test over a projection, lifted into a function of its own, under the projection's test.
#[k::function(total, internal)]
pub fn IsOne(t: k::Term<k::KItem>) -> k::Term<Bool>;

k::equations! {
    for IsOne;
    #[k::requires(k::is!(Int, t))]
    is_one: t => k::matches!(k::project!(Int, t), 1);
    #[k::equation(owise)]
    is_not_one: _ => false;
}

/// A function declared `partial` is not judged.
#[k::function(partial, internal)]
pub fn Inverse(x: k::Term<Int>) -> k::Term<Int> {
    100 / x
}

/// Nor is one with no equation.
#[k::function(total, internal)]
pub fn Opaque(x: k::Term<Int>) -> k::Term<Int>;

/// A recursive application is an application of a function declared `total`.
#[k::function(total, internal)]
pub fn Count(x: k::Term<Int>) -> k::Term<Int> {
    if x <= 0 { 0 } else { Count(x - 1) + 1 }
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes the package `name` whose definition is [`MACHINE`] with `functions` and `read`.
fn package(root: &Path, name: &str, functions: &str, read: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(
        directory.join("src/lib.rs"),
        MACHINE
            .replace("{functions}", functions)
            .replace("{read}", read),
    )
    .unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"TOTAL-VALUES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The diagnostics of `krs check`: each headline up to the end of its first sentence, and the
/// source line each points at.
fn checked(target: &Path, manifest: &Path) -> (bool, Vec<String>) {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    let mut lines = Vec::new();
    let mut pointed = false;
    for line in stderr.lines() {
        if line.starts_with("error[") || line.starts_with("warning[krs::analysis::") {
            let end = line.find(". `total` and").unwrap_or(line.len());
            lines.push(line[..end].to_owned());
            pointed = true;
        } else if pointed
            && let Some((number, source)) = line.split_once(" | ")
            && number.trim().parse::<usize>().is_ok()
        {
            lines.push(format!("at `{}`", source.trim()));
            pointed = false;
        }
    }
    (success, lines)
}

/// The three functions whose false claims were reported `proven` are refused by `krs check`,
/// each at the construct or the application, so no claim over them reaches a prover; the error
/// names the ways out.
#[test]
fn a_total_function_whose_result_may_have_no_value_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        ("lookup", AT9, "At9(m)"),
        ("division", INV, "Inv(m)"),
        ("call", WRAP, "Wrap(m)"),
    ];
    let mut reported = Vec::new();
    for (name, functions, read) in cases {
        let manifest = package(
            temporary.path(),
            name,
            &functions.replace("TOTALITY", "total"),
            read,
        );
        let (success, lines) = checked(target.path(), &manifest);
        assert!(!success, "{name}: {lines:#?}");
        reported.extend(lines);
        let (proved, stdout, stderr) = krs(target.path(), &manifest, "prove", &[]);
        assert!(!proved, "{name}: {stdout}");
        assert!(!stdout.contains("proven"), "{name}: {stdout}");
        assert!(
            stderr.contains("error[krs::analysis::total-without-value]")
                && stderr.contains("Ways out: state the domain in the equation's condition (`#[k::requires(..)]`) and give the remaining arguments an equation (`#[k::equation(owise)]`); or use a form that has a value everywhere (`get_or` at the sort the collection holds, an `if` block whose test is the construct's); or declare the function `partial`; or, where the function is total for a reason KRS does not read, say so with `#[k::function(total, assumed = \"reason\")]`"),
            "{name}: {stderr}"
        );
    }
    expect_test::expect![[r#"
        [
            "error[krs::analysis::total-without-value]: `At9` is declared `total`, but this equation's result is not shown to have a value wherever the equation applies: this lookup has a value only where (1) the key is a key of the map (`contains_key`), and (2) the element read has sort `Int`, which KRS projects the read to and no invariant of a typed collection establishes yet (`k::is!(Int, ..)` of the read), which the equation's condition does not state",
            "at `memory[9]`",
            "error[krs::analysis::total-without-value]: `Inv` is declared `total`, but this equation's result is not shown to have a value wherever the equation applies: this `int::div` has a value only where operand 2 != 0, which the equation's condition does not state",
            "at `100 / memory.len()`",
            "error[krs::analysis::total-without-value]: `Wrap` is declared `total`, but this equation's result is not shown to have a value wherever the equation applies: it applies `PAt`, which is not declared `total`, so the application has no value where `PAt` has none",
            "at `PAt(memory)`",
        ]
    "#]]
    .assert_debug_eq(&reported);
}

/// With the function declared `partial` the definition is accepted, and the false claim fails:
/// the prover keeps the branch where the function has no value.
#[test]
fn the_false_claim_fails_once_the_function_is_partial() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "partial",
        &AT9.replace("TOTALITY", "partial"),
        "At9(m)",
    );
    let (success, lines) = checked(target.path(), &manifest);
    assert!(success, "{lines:#?}");
    assert_eq!(lines, [""; 0]);
    let (proved, stdout, stderr) = krs(target.path(), &manifest, "prove", &[]);
    assert!(!proved, "{stdout}\n{stderr}");
    assert!(
        stdout.contains("TOTAL-VALUES-SPEC.keep-reaches-one: failed"),
        "{stdout}\n{stderr}"
    );
}

/// Each way out is accepted with no diagnostic: the domain stated in the condition with an
/// `owise` equation, a condition that evaluates the construct, a bound that implies the test,
/// an `if` block, `get_or` at the sort the map holds, and `partial`. A function with no
/// equation and a recursive one are not refused. The true claim over a guarded function proves.
#[test]
fn each_way_out_is_accepted() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "guarded", WAYS_OUT, "Guarded(m)");
    let (success, lines) = checked(target.path(), &manifest);
    assert!(success, "{lines:#?}");
    assert_eq!(lines, [""; 0]);
    let (proved, stdout, stderr) = krs(target.path(), &manifest, "prove", &[]);
    assert!(proved, "{stdout}\n{stderr}");
    assert!(
        stdout.contains("TOTAL-VALUES-SPEC.keep-reaches-one: proven"),
        "{stdout}\n{stderr}"
    );
}

/// What guards nothing: a conditional and a connective written as operations keep the
/// definedness of every operand; `get_or` on a typed map is projected to the element sort; a
/// `let` and a `k::matches!` over a projection are judged where they stand, and the test's
/// refusal is at the projection the author wrote, not at the function KRS lifts the test into;
/// an operation whose domain no condition states is refused as such.
#[test]
fn a_form_that_guards_nothing_is_refused_at_its_construct() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "ite",
            "pub fn F(m: k::Term<Map<Int, Int>>) -> k::Term<Int> { kequal::ite(m.len() != 0, 100 / m.len(), 0) }",
        ),
        (
            "and",
            "pub fn F(m: k::Term<Map<Int, Int>>) -> k::Term<Int> { Truth(m.len() != 0 && 100 / m.len() > 1) }",
        ),
        (
            "default",
            "pub fn F(m: k::Term<Map<Int, Int>>) -> k::Term<Int> { m.get_or(9, 0) }",
        ),
        (
            "block",
            "pub fn F(m: k::Term<Map<Int, Int>>) -> k::Term<Int> { let x: Int = AsItem(m); x + 1 }",
        ),
        (
            "test",
            "pub fn F(m: k::Term<Map<Int, Int>>) -> k::Term<Int> { Truth(k::matches!(k::project!(Int, AsItem(m)), 1)) }",
        ),
        (
            "untested",
            "pub fn F(m: k::Term<Map<Int, Int>>) -> k::Term<Int> { string::to_int(Text(m)) }",
        ),
    ];
    let helpers = r"
#[k::function(total, internal)]
pub fn Truth(value: k::Term<Bool>) -> k::Term<Int> {
    if value { 1 } else { 0 }
}

#[k::function(total, internal)]
pub fn AsItem(m: k::Term<Map<Int, Int>>) -> k::Term<k::KItem>;

#[k::function(total, internal)]
pub fn Text(m: k::Term<Map<Int, Int>>) -> k::Term<String>;
";
    let mut reported = Vec::new();
    for (name, function) in cases {
        let manifest = package(
            temporary.path(),
            name,
            &format!("{helpers}\n#[k::function(total, internal)]\n{function}\n"),
            "F(m)",
        );
        let (success, lines) = checked(target.path(), &manifest);
        assert!(!success, "{name}: {lines:#?}");
        reported.extend(lines);
    }
    expect_test::expect![[r#"
        [
            "error[krs::analysis::total-without-value]: `F` is declared `total`, but this equation's result is not shown to have a value wherever the equation applies: this `int::div` has a value only where operand 2 != 0, which the equation's condition does not state",
            "at `pub fn F(m: k::Term<Map<Int, Int>>) -> k::Term<Int> { kequal::ite(m.len() != 0, 100 / m.len(), 0) }`",
            "error[krs::analysis::total-without-value]: `F` is declared `total`, but this equation's result is not shown to have a value wherever the equation applies: this `int::div` has a value only where operand 2 != 0, which the equation's condition does not state",
            "at `pub fn F(m: k::Term<Map<Int, Int>>) -> k::Term<Int> { Truth(m.len() != 0 && 100 / m.len() > 1) }`",
            "error[krs::analysis::total-without-value]: `F` is declared `total`, but this equation's result is not shown to have a value wherever the equation applies: this `get_or` read has a value only where the element read has sort `Int`, which KRS projects the read to and no invariant of a typed collection establishes yet (`k::is!(Int, ..)` of the read), which the equation's condition does not state",
            "at `pub fn F(m: k::Term<Map<Int, Int>>) -> k::Term<Int> { m.get_or(9, 0) }`",
            "error[krs::analysis::total-without-value]: `F` is declared `total`, but this equation's result is not shown to have a value wherever the equation applies: this `let` statement has a value only where its pattern matches its value (`k::matches!(value, pattern)`), which the equation's condition does not state",
            "at `pub fn F(m: k::Term<Map<Int, Int>>) -> k::Term<Int> { let x: Int = AsItem(m); x + 1 }`",
            "error[krs::analysis::total-without-value]: `F` is declared `total`, but this equation's result is not shown to have a value wherever the equation applies: this construct of a `k::matches!` test is partial (a projection, a read KRS projects, or an operation outside its domain), and the equation's condition does not test it (for a projection `k::project!(S, t)`: `k::is!(S, t)`)",
            "at `pub fn F(m: k::Term<Map<Int, Int>>) -> k::Term<Int> { Truth(k::matches!(k::project!(Int, AsItem(m)), 1)) }`",
            "error[krs::analysis::total-without-value]: `F` is declared `total`, but this equation's result is not shown to have a value wherever the equation applies: this `string::to_int` is partial, and KRS has no test of its domain that a condition could state (defined on a decimal integer's text only, which no builtin tests)",
            "at `pub fn F(m: k::Term<Map<Int, Int>>) -> k::Term<Int> { string::to_int(Text(m)) }`",
        ]
    "#]].assert_debug_eq(&reported);
}

/// A function total on the author's word, and one that states `assumed` although the check
/// accepts it.
const ASSUMED: &str = r#"
#[k::function(total, internal, assumed = "the memory holds key 9 from its first state on")]
pub fn At9(memory: k::Term<Map<Int, Int>>) -> k::Term<Int> {
    memory[9]
}

#[k::function(total, internal, assumed = "nothing here needs it")]
pub fn Same(x: k::Term<Int>) -> k::Term<Int> {
    x
}
"#;

/// `#[k::function(total, assumed = "reason")]` is not judged: the definition is accepted, the
/// function is emitted `[function, total]` as a checked one is, and the Definition IR keeps the
/// reason on the production (the Semantic IR too), where a report can list it. `krs expand`
/// keeps the key. `assumed` on a function the check accepts is `stale-assumed`, at the reason.
#[test]
fn an_assumed_total_function_is_accepted_recorded_and_stale_when_checked() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "unchecked", ASSUMED, "At9(m)");
    let (success, lines) = checked(target.path(), &manifest);
    assert!(success, "{lines:#?}");
    expect_test::expect![[r#"
        [
            "warning[krs::analysis::stale-assumed]: `Same` states `assumed`, but KRS shows that each of its equations' results has a value wherever the equation applies, so the function is checked without it; remove `assumed`",
            "at `#[k::function(total, internal, assumed = \"nothing here needs it\")]`",
        ]
    "#]].assert_debug_eq(&lines);

    let output = temporary.path().join("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--ir", "--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    assert!(
        definition.contains(r#"syntax Int ::= "at9" "(" Map ")" [symbol(at9), function, total]"#),
        "{definition}"
    );
    assert!(!definition.contains("assumed"), "{definition}");
    for document in ["definition-ir.json", "semantic-ir.json"] {
        let ir: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(output.join(document)).unwrap()).unwrap();
        let mut reasons = Vec::new();
        assumed_reasons(&ir, &mut reasons);
        reasons.sort();
        assert_eq!(
            reasons,
            [
                "nothing here needs it",
                "the memory holds key 9 from its first state on"
            ],
            "{document}"
        );
    }

    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    assert!(
        expanded.contains(r#"assumed = "the memory holds key 9 from its first state on""#),
        "{expanded}"
    );
}

/// The reason of every `assumed` production attribute in an IR document.
fn assumed_reasons(value: &serde_json::Value, reasons: &mut Vec<String>) {
    match value {
        serde_json::Value::Object(fields) => {
            if fields
                .get("attribute_kind")
                .and_then(serde_json::Value::as_str)
                == Some("assumed")
            {
                reasons.push(fields["reason"].as_str().unwrap().to_owned());
            }
            for field in fields.values() {
                assumed_reasons(field, reasons);
            }
        }
        serde_json::Value::Array(items) => {
            for item in items {
                assumed_reasons(item, reasons);
            }
        }
        _ => {}
    }
}
