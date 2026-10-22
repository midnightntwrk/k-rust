//! The coverage lint of `total` functions on authored packages: the warning
//! headlines and witnesses every command reports, the `underspecified` key,
//! the functions the lint skips, and a constructor another package adds.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const LANGUAGE: &str = r##"
use k::builtin::{Bool, Bytes, Int, KSequence, List, int, list};
use k::{KItem, KItemSort, Term};

k::sorts! {
    Reg;
    Operand;
}

#[k::constructors(sort = Reg, result = k::KResult)]
#[k::precedence((A, B))]
pub enum Register {
    #[k::syntax("ra")]
    A,
    #[k::syntax("rb")]
    B,
}

#[k::constructors(sort = Operand, result = k::KResult)]
#[k::precedence((Reg, Immediate))]
pub enum Op {
    #[k::syntax("reg({register})")]
    Reg { register: Reg },
    #[k::syntax("imm")]
    Immediate,
}

/// An index table that names three of the Ints.
#[k::function(total, internal)]
pub fn Table(index: Term<Int>) -> Term<Operand>;

k::equations! {
    for Table;
    use Op::*;
    use Register::*;
    table_a: 0 => Reg(A());
    table_b: 1 => Reg(B());
    table_immediate: 2 => Immediate();
}

/// Guards that leave 0 to 255 without a value.
#[k::function(total, internal)]
pub fn Clamp(value: Term<Int>) -> Term<Int>;

k::equations! {
    for Clamp;
    #[k::requires(value.lt::<Int>(0))]
    clamp_low: value => 0;
    #[k::requires(value.gt::<Int>(255))]
    clamp_high: value => 255;
}

/// The high nibble of a byte.
#[k::function(total, internal)]
pub fn High(value: Term<Int>) -> Term<Int> {
    k::term![value.shift_right::<Int>(4)]
}

/// Guards whose shifts are defined only where an earlier conjunct holds:
/// the three cover every argument.
#[k::function(total, internal)]
pub fn SignedTruncate(value: Term<Int>, width: Term<Int>) -> Term<Int>;

k::equations! {
    for SignedTruncate;
    #[k::requires(int::le(width, 0))]
    signed_truncate_none: (value, width) => value;
    #[k::requires(int::gt(width, 0) && int::lt(value, int::shift_left(1, int::sub(width, 1))))]
    signed_truncate_low: (value, width) => value;
    #[k::requires(int::gt(width, 0) && int::ge(value, int::shift_left(1, int::sub(width, 1))))]
    signed_truncate_high: (value, width) => int::sub(value, int::shift_left(1, width));
}

/// Guards that read an element only where its index is in range: the
/// three cover every argument.
#[k::function(total, internal)]
pub fn Element(items: Term<List>, index: Term<Int>) -> Term<Int>;

k::equations! {
    for Element;
    #[k::requires(int::ge(index, 0) && int::lt(index, list::size(items)) && int::eq(list::get(items, index), 0))]
    element_clear: (items, index) => 0;
    #[k::requires(int::ge(index, 0) && int::lt(index, list::size(items)) && int::ne(list::get(items, index), 0))]
    element_set: (items, index) => 1;
    #[k::requires(int::lt(index, 0) || int::ge(index, list::size(items)))]
    element_outside: (items, index) => 2;
}

/// Guards that divide by `divisor`: neither holds where it is 0.
#[k::function(total, internal)]
pub fn Quotient(value: Term<Int>, divisor: Term<Int>) -> Term<Int>;

k::equations! {
    for Quotient;
    #[k::requires(int::ge(int::div(value, divisor), 0))]
    quotient_nonnegative: (value, divisor) => 0;
    #[k::requires(int::lt(int::div(value, divisor), 0))]
    quotient_negative: (value, divisor) => 1;
}

/// Guards on a total function of the argument: `High(opcode)` may be 2.
#[k::function(total, internal)]
pub fn Page(opcode: Term<Int>) -> Term<Reg>;

k::equations! {
    for Page;
    use Register::*;
    #[k::requires(High(opcode).eq::<Int>(0))]
    page_a: opcode => A();
    #[k::requires(High(opcode).eq::<Int>(1))]
    page_b: opcode => B();
}

/// Two bit templates cover `0..=15` and nothing beyond it.
#[k::function(total, internal)]
pub fn Nibble(value: Term<Int>) -> Term<Reg>;

k::equations! {
    for Nibble;
    use Register::*;
    nibble_low: k::bits!("0___") => A();
    nibble_high: k::bits!("1___") => B();
}

/// A template, the value its `requires` excludes, and the rest: covered.
#[k::function(total, internal)]
pub fn Opcode(value: Term<Int>) -> Term<Reg>;

k::equations! {
    for Opcode;
    use Register::*;
    #[k::requires(op.ne::<Int>(6))]
    opcode_load: op @ k::bits!("0___") => A();
    opcode_halt: 6 => B();
    #[k::equation(owise)]
    opcode_other: _ => B();
}

/// Complementary guards: covered.
#[k::function(total, internal)]
pub fn Signed(value: Term<Int>) -> Term<Int>;

k::equations! {
    for Signed;
    #[k::requires(value.lt::<Int>(128))]
    signed_positive: value => value;
    #[k::requires(value.ge::<Int>(128))]
    signed_negative: value => value.sub::<Int>(256);
}

#[k::sort(alias = Exp, parents = [KItem])]
pub trait ExpSort: KItemSort {}
pub type Exp = Term<dyn ExpSort>;

#[k::subsort(sort = Exp)]
impl ExpSort for Int {}

#[k::constructor(sort = Exp, syntax = "plus({left}, {right})")]
pub struct Plus {
    pub left: Term<dyn ExpSort>,
    pub right: Term<dyn ExpSort>,
}

/// Defined on `plus` only: the Ints `Exp` contains are uncovered.
#[k::function(total, internal)]
pub fn Size(expression: Term<dyn ExpSort>) -> Term<Int>;

k::equations! {
    for Size;
    size_plus: Plus(_, _) => 1;
}

/// A stated gap: no warning.
#[k::function(total, internal, underspecified = "the index is a one-bit field")]
pub fn Bit(index: Term<Int>) -> Term<Reg>;

k::equations! {
    for Bit;
    use Register::*;
    bit_a: 0 => A();
    bit_b: 1 => B();
}

/// A stated gap that does not exist: stale.
#[k::function(total, internal, underspecified = "only two values")]
pub fn FlagBit(flag: Term<Bool>) -> Term<Int>;

k::equations! {
    for FlagBit;
    flag_set: true => 1;
    flag_clear: false => 0;
}

/// Partial: a missing case is what `partial` means.
#[k::function(partial, internal)]
pub fn Half(value: Term<Int>) -> Term<Int>;

k::equations! {
    for Half;
    half_zero: 0 => 0;
}

/// Declared, never defined: uninterpreted.
#[k::function(total, internal)]
pub fn Opaque(value: Term<Int>) -> Term<Int>;

/// Defined for the SMT solver by its template.
#[k::function(total, internal, smt_hook = "(ite (< {value} 0) 0 {value})")]
pub fn Floor(value: Term<Int>) -> Term<Int>;

k::equations! {
    for Floor;
    #[k::requires(value.lt::<Int>(0))]
    floor_negative: value => 0;
}

/// Defined by the backend's hook.
#[k::function(total, sort = Bytes, syntax = "#sha({value})", hook = krypto::sha256_raw)]
pub struct Sha {
    pub value: Term<Bytes>,
}

#[k::requires(k::builtin::bytes::length(value).eq::<Int>(0))]
#[k::equation]
fn sha_empty(k::term![Sha(value)]: Term<Bytes>) -> Term<Bytes> {
    value
}

#[k::configuration(root = "machine")]
pub struct Machine {
    pub k: k::configuration::KCell<KSequence>,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![]),
        }
    }
}
"##;

const BASE: &str = r#"
use k::Term;

k::sorts! {
    Cond;
}

#[k::constructors(sort = Cond, result = k::KResult)]
#[k::precedence((Always, Never))]
pub enum Condition {
    #[k::syntax("always")]
    Always,
    #[k::syntax("never")]
    Never,
}

/// Covers both conditions of this package.
#[k::function(total, internal)]
pub fn Holds(condition: Term<Cond>) -> Term<k::builtin::Bool>;

k::equations! {
    for Holds;
    use Condition::*;
    holds_always: Always() => true;
    holds_never: Never() => false;
}
"#;

const ROOT: &str = r#"
use k::builtin::KSequence;

/// A third condition: `base::Holds` no longer covers `Cond`.
#[k::constructor(sort = base::Cond, syntax = "sometimes")]
pub struct Sometimes;

#[k::configuration(root = "machine")]
pub struct Machine {
    pub k: k::configuration::KCell<KSequence>,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![]),
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

/// Writes a package with one definition; `dependency` is another package
/// directory beside it.
fn package(root: &Path, name: &str, source: &str, dependency: Option<&str>, definition: &str) {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    let dependency = dependency.map_or_else(String::new, |dependency| {
        format!("{dependency} = {{ path = \"../{dependency}\" }}\n")
    });
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n{dependency}\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-COVERAGE-{}\"\n\n[package.metadata.krs.definitions.{definition}]\n",
            krs_path(),
            name.to_ascii_uppercase()
        ),
    )
    .unwrap();
}

fn workspace(root: &Path, members: &[&str]) -> PathBuf {
    let members = members
        .iter()
        .map(|member| format!("\"{member}\""))
        .collect::<Vec<_>>()
        .join(", ");
    fs::write(
        root.join("Cargo.toml"),
        format!("[workspace]\nresolver = \"3\"\nmembers = [{members}]\n"),
    )
    .unwrap();
    root.join("Cargo.toml")
}

/// The `warning[..]` and `error[..]` headlines and notes of `krs emit-k`.
fn emit(
    target: &Path,
    manifest: &Path,
    package: &str,
    output: &Path,
    extra: &[&str],
) -> (bool, Vec<String>) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let result = process
        .args(["emit-k", "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main", "--output"])
        .arg(output)
        .args(extra)
        .env("NO_COLOR", "1")
        .output()
        .unwrap();
    let stderr = String::from_utf8(result.stderr).unwrap();
    let lines = stderr
        .lines()
        .filter(|line| {
            line.starts_with("warning[krs::analysis::")
                || line.starts_with("error[")
                || line.trim_start().starts_with("= note: ")
                    && (line.contains("also uncovered") || line.contains("`requires`"))
        })
        .map(|line| line.trim().to_owned())
        .collect();
    (result.status.success(), lines)
}

#[test]
fn total_functions_warn_where_no_equation_applies() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    package(temporary.path(), "language", LANGUAGE, None, "main");
    let manifest = workspace(temporary.path(), &["language"]);
    let (success, lines) = emit(
        target.path(),
        &manifest,
        "language",
        &temporary.path().join("emitted"),
        &[],
    );
    assert!(success, "{lines:#?}");
    expect_test::expect![[r#"
        [
            "warning[krs::analysis::uncovered-total-function]: total function `Clamp` has no equation for `Clamp(0)`",
            "= note: 2 of its equations have `requires`; KRS decides a `requires` only as a Boolean combination of comparisons with integer constants and between two integers, reading the bits that comparisons of `bitRangeInt` and `&Int` fix, where each partial Int operation in it (division, remainder, shift, exponent, bit range) is defined",
            "warning[krs::analysis::stale-underspecified]: `FlagBit` states `underspecified`, but its equations define every argument; remove `underspecified`",
            "warning[krs::analysis::uncovered-total-function]: total function `Nibble` has no equation for `Nibble(16)`",
            "= note: KRS evaluated the `requires` of its equations on every argument they bound (0..=15) and on one argument beyond them, which stands for every other",
            "warning[krs::analysis::uncovered-total-function]: total function `Page` has no equation for `Page(opcode)` when `High(opcode)` is 2",
            "= note: 2 of its equations have `requires`; KRS decides a `requires` only as a Boolean combination of comparisons with integer constants and between two integers, reading the bits that comparisons of `bitRangeInt` and `&Int` fix, where each partial Int operation in it (division, remainder, shift, exponent, bit range) is defined",
            "warning[krs::analysis::uncovered-total-function]: total function `Quotient` has no equation for `Quotient(0, 0)`",
            "= note: 2 of its equations have `requires`; KRS decides a `requires` only as a Boolean combination of comparisons with integer constants and between two integers, reading the bits that comparisons of `bitRangeInt` and `&Int` fix, where each partial Int operation in it (division, remainder, shift, exponent, bit range) is defined",
            "warning[krs::analysis::uncovered-total-function]: total function `Size` has no equation for `Size(0)`",
            "warning[krs::analysis::uncovered-total-function]: total function `Table` has no equation for `Table(3)`",
        ]
    "#]]
    .assert_debug_eq(&lines);
}

/// Each builtin call of [`LANGUAGE`]'s guards and results, and the operator
/// notation that denotes it.
const OPERATOR_SPELLINGS: &[(&str, &str)] = &[
    ("value.lt::<Int>(0)", "value < 0"),
    ("value.gt::<Int>(255)", "value > 255"),
    ("value.shift_right::<Int>(4)", "value >> 4"),
    ("int::le(width, 0)", "width <= 0"),
    (
        "int::gt(width, 0) && int::lt(value, int::shift_left(1, int::sub(width, 1)))",
        "width > 0 && value < 1 << (width - 1)",
    ),
    (
        "int::gt(width, 0) && int::ge(value, int::shift_left(1, int::sub(width, 1)))",
        "width > 0 && value >= 1 << (width - 1)",
    ),
    (
        "int::sub(value, int::shift_left(1, width))",
        "value - (1 << width)",
    ),
    (
        "int::ge(index, 0) && int::lt(index, list::size(items)) && int::eq(list::get(items, index), 0)",
        "index >= 0 && index < list::size(items) && list::get(items, index) == 0",
    ),
    (
        "int::ge(index, 0) && int::lt(index, list::size(items)) && int::ne(list::get(items, index), 0)",
        "index >= 0 && index < list::size(items) && list::get(items, index) != 0",
    ),
    (
        "int::lt(index, 0) || int::ge(index, list::size(items))",
        "index < 0 || index >= list::size(items)",
    ),
    (
        "int::ge(int::div(value, divisor), 0)",
        "value / divisor >= 0",
    ),
    (
        "int::lt(int::div(value, divisor), 0)",
        "value / divisor < 0",
    ),
    ("High(opcode).eq::<Int>(0)", "High(opcode) == 0"),
    ("High(opcode).eq::<Int>(1)", "High(opcode) == 1"),
    ("op.ne::<Int>(6)", "op != 6"),
    ("value.lt::<Int>(128)", "value < 128"),
    ("value.ge::<Int>(128)", "value >= 128"),
    ("value.sub::<Int>(256)", "value - 256"),
    (
        "k::builtin::bytes::length(value).eq::<Int>(0)",
        "k::builtin::bytes::length(value) == 0",
    ),
];

/// The lint reads an operator guard as it reads the call the operator
/// denotes: [`LANGUAGE`] with every guard and result written with operators
/// warns exactly as it does with calls, and emits the same K.
#[test]
fn operator_guards_warn_as_the_calls_they_denote() {
    let mut operators = LANGUAGE.to_owned();
    for (call, operator) in OPERATOR_SPELLINGS {
        assert!(operators.contains(call), "`{call}` no longer occurs");
        operators = operators.replace(call, operator);
    }
    let target = shared_fixture_target();
    let emitted = |source: &str| {
        let temporary = temp_dir();
        package(temporary.path(), "language", source, None, "main");
        let manifest = workspace(temporary.path(), &["language"]);
        let output = temporary.path().join("emitted");
        let (success, lines) = emit(target.path(), &manifest, "language", &output, &[]);
        assert!(success, "{lines:#?}");
        (
            lines,
            fs::read_to_string(output.join("definition.k")).unwrap(),
        )
    };
    let (call_lines, call_k) = emitted(LANGUAGE);
    let (operator_lines, operator_k) = emitted(&operators);
    assert_eq!(operator_lines, call_lines);
    assert_eq!(operator_k, call_k);
}

#[test]
fn a_constructor_another_package_adds_uncovers_a_total_function() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    package(temporary.path(), "base", BASE, None, "base");
    package(temporary.path(), "root", ROOT, Some("base"), "main");
    let manifest = workspace(temporary.path(), &["base", "root"]);
    let (success, lines) = emit(
        target.path(),
        &manifest,
        "root",
        &temporary.path().join("emitted"),
        &["--dependency", "base:base"],
    );
    assert!(success, "{lines:#?}");
    expect_test::expect![[r#"
        [
            "warning[krs::analysis::uncovered-total-function]: total function `Holds` has no equation for `Holds(Sometimes)`",
        ]
    "#]]
    .assert_debug_eq(&lines);
}
