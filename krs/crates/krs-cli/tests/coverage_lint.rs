//! The coverage lint of `total` functions on authored packages: the warning
//! headlines and witnesses every command that lowers the definition reports
//! (`emit-k` and `expand` here), the `underspecified` key,
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

/// Guards that apply total functions and test patterns (`k::matches!`, which
/// branching bodies emit for a term scrutinee and a nested catch-all).
const GUARDS: &str = r#"
use k::builtin::{Bool, Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Kind;
    Shape;
    Item: KItem;
    impl Item for Int;
}

#[k::constructors(sort = Kind, result = k::KResult)]
#[k::precedence((A, B, C))]
pub enum Kinds {
    #[k::syntax("kA")]
    A,
    #[k::syntax("kB")]
    B,
    #[k::syntax("kC")]
    C,
}

#[k::constructors(sort = Shape, result = k::KResult)]
#[k::precedence((Circle, Pair))]
pub enum Shapes {
    #[k::syntax("circle({r})")]
    Circle { r: Int },
    #[k::syntax("pair({left}, {right})")]
    Pair { left: Kind, right: Kind },
}

#[k::constructors(sort = Item, result = k::KResult)]
#[k::precedence((Wrap, Other))]
pub enum Items {
    #[k::syntax("wrap({v})")]
    Wrap { v: Int },
    #[k::syntax("other")]
    Other,
}

#[k::function(total, internal)]
pub fn Classify(value: Term<Int>) -> Term<Kind> {
    if value < 0 { Kinds::A() } else if value == 0 { Kinds::B() } else { Kinds::C() }
}

/// 1, -1, or 0 outside `0..512`.
#[k::function(total, internal)]
pub fn Sign(value: Term<Int>) -> Term<Int> {
    if 0 <= value && value < 256 {
        1
    } else if 256 <= value && value < 512 {
        -1
    } else {
        0
    }
}

/// 1 or -1.
#[k::function(total, internal)]
pub fn TwoSign(value: Term<Int>) -> Term<Int> {
    if value >= 0 { 1 } else { -1 }
}

#[k::function(total, internal)]
pub fn BoolToWord(value: Term<Bool>) -> Term<Int>;

k::equations! {
    for BoolToWord;
    bool_to_word_true: true => 1;
    bool_to_word_false: false => 0;
}

/// Real gap: `Sign` may be 0.
#[k::function(total, internal)]
pub fn SignedLess(left: Term<Int>, right: Term<Int>) -> Term<Int> {
    match (Sign(left), Sign(right)) {
        (1, 1) => BoolToWord(left < right),
        (1, -1) => BoolToWord(false),
        (-1, 1) => BoolToWord(true),
        (-1, -1) => BoolToWord(right < left),
    }
}

/// Covered: `TwoSign` is 1 or -1.
#[k::function(total, internal)]
pub fn TwoSignedLess(left: Term<Int>, right: Term<Int>) -> Term<Int> {
    match (TwoSign(left), TwoSign(right)) {
        (1, 1) => BoolToWord(left < right),
        (1, -1) => BoolToWord(false),
        (-1, 1) => BoolToWord(true),
        (-1, -1) => BoolToWord(right < left),
    }
}

/// The same, stated as a gap: stale.
#[k::function(total, internal, underspecified = "TwoSign is 1 or -1")]
pub fn StatedLess(left: Term<Int>, right: Term<Int>) -> Term<Int> {
    match (TwoSign(left), TwoSign(right)) {
        (1, 1) => BoolToWord(left < right),
        (1, -1) => BoolToWord(false),
        (-1, 1) => BoolToWord(true),
        (-1, -1) => BoolToWord(right < left),
    }
}

/// A term scrutinee with constructor patterns: covered.
#[k::function(total, internal)]
pub fn Score(value: Term<Int>) -> Term<Int> {
    match Classify(value) {
        Kinds::A() => 1,
        Kinds::B() => 2,
        Kinds::C() => 3,
    }
}

/// Real gap: `Classify(value)` is `Kinds::C` for a positive `value`.
#[k::function(total, internal)]
pub fn PartialScore(value: Term<Int>) -> Term<Int> {
    match Classify(value) {
        Kinds::A() => 1,
        Kinds::B() => 2,
    }
}

/// A nested catch-all over a term: covered.
#[k::function(total, internal)]
pub fn Nested(value: Term<Int>, flag: Term<Int>) -> Term<Int> {
    if flag > 0 {
        match Classify(value) {
            Kinds::A() => 1,
            _ => 2,
        }
    } else {
        3
    }
}

/// A nested catch-all over a parameter: covered.
#[k::function(total, internal)]
pub fn Area(shape: Term<Shape>, flag: Term<Int>) -> Term<Int> {
    if flag > 0 {
        match shape {
            Shapes::Circle { r } => r,
            _ => 0,
        }
    } else {
        1
    }
}

/// Guarded arms before the catch-all: covered.
#[k::function(total, internal)]
pub fn Guarded(shape: Term<Shape>, flag: Term<Int>) -> Term<Int> {
    if flag > 0 {
        match shape {
            Shapes::Circle { .. } if flag > 5 => 1,
            Shapes::Pair { left: Kinds::A(), .. } => 2,
            _ => 3,
        }
    } else {
        4
    }
}

/// A nested catch-all over a sort with injected Ints: covered.
#[k::function(total, internal)]
pub fn Open(item: Term<Item>, flag: Term<Int>) -> Term<Int> {
    if flag > 0 {
        match item {
            Items::Wrap { .. } => 1,
            _ => 2,
        }
    } else {
        3
    }
}

/// Two of the three kinds: its range is `Kinds::A` and `Kinds::B`.
#[k::function(total, internal)]
pub fn Halve(value: Term<Int>) -> Term<Kind> {
    if value < 0 { Kinds::A() } else { Kinds::B() }
}

/// Covered: `Halve(value)` is never `Kinds::C`.
#[k::function(total, internal)]
pub fn UsesHalve(value: Term<Int>) -> Term<Int> {
    match Halve(value) {
        Kinds::A() => 1,
        Kinds::B() => 2,
    }
}

/// A range from a callee's range.
#[k::function(total, internal)]
pub fn Again(value: Term<Int>) -> Term<Int> {
    TwoSign(value)
}

#[k::function(total, internal)]
pub fn UsesAgain(value: Term<Int>) -> Term<Int> {
    match Again(value) {
        1 => 10,
        -1 => 20,
    }
}

/// A range from a mask.
#[k::function(total, internal)]
pub fn Low(value: Term<Int>) -> Term<Int> {
    value & 3
}

#[k::function(total, internal)]
pub fn UsesLow(value: Term<Int>) -> Term<Int> {
    match Low(value) {
        0 | 1 => 10,
        2 => 20,
        3 => 30,
    }
}

/// An uncovered callee has no range.
#[k::function(total, internal)]
pub fn LooseSign(value: Term<Int>) -> Term<Int>;

k::equations! {
    for LooseSign;
    #[k::requires(value > 0)]
    loose_sign_positive: value => 1;
    #[k::requires(value < 0)]
    loose_sign_negative: value => -1;
}

#[k::function(total, internal)]
pub fn UsesLooseSign(value: Term<Int>) -> Term<Int> {
    match LooseSign(value) {
        1 => 10,
        -1 => 20,
    }
}

/// An `underspecified` callee has no range (and states a stale gap).
#[k::function(total, internal, underspecified = "never 0")]
pub fn StatedSign(value: Term<Int>) -> Term<Int> {
    if value >= 0 { 1 } else { -1 }
}

#[k::function(total, internal)]
pub fn UsesStatedSign(value: Term<Int>) -> Term<Int> {
    match StatedSign(value) {
        1 => 10,
        -1 => 20,
    }
}

/// A cycle: `Ping` is checked first, so `Pong`, which reads `Ping`, has no
/// range of it, and `Ping`, still being checked when `Pong` asked, has none.
#[k::function(total, internal)]
pub fn Ping(value: Term<Int>) -> Term<Int> {
    if Pong(value) >= 0 { 1 } else { -1 }
}

#[k::function(total, internal)]
pub fn Pong(value: Term<Int>) -> Term<Int> {
    if Ping(value) >= 0 { 1 } else { -1 }
}

#[k::function(total, internal)]
pub fn UsesPing(value: Term<Int>) -> Term<Int> {
    match Ping(value) {
        1 => 10,
        -1 => 20,
    }
}

#[k::function(total, internal)]
pub fn UsesPong(value: Term<Int>) -> Term<Int> {
    match Pong(value) {
        1 => 10,
        -1 => 20,
    }
}

/// A Bool function with one result.
#[k::function(total, internal)]
pub fn Always(value: Term<Int>) -> Term<Bool> {
    true
}

#[k::function(total, internal)]
pub fn Gated(value: Term<Int>) -> Term<Int>;

k::equations! {
    for Gated;
    #[k::requires(Always(value))]
    gated: value => 1;
}

/// Bounded equations whose guards apply a function: the ground analysis
/// evaluates it, so the witnesses are exact.
#[k::function(total, internal)]
pub fn Field(op: Term<Int>) -> Term<Int> {
    (op >> 1) & 3
}

#[k::function(total, internal)]
pub fn Decoded(op: Term<Int>) -> Term<Int>;

k::equations! {
    for Decoded;
    #[k::requires(0 <= op && op < 8 && Field(op) == 0)]
    decoded_0: op => 0;
    #[k::requires(0 <= op && op < 8 && Field(op) == 1)]
    decoded_1: op => 1;
    #[k::requires(0 <= op && op < 8 && Field(op) == 2)]
    decoded_2: op => 2;
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
"#;

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
            "= note: 2 of its equations have `requires`; KRS decides a `requires` only as a Boolean combination of comparisons with integer constants and between two integers and of `k::matches!` tests, reading the bits that comparisons of `bitRangeInt` and `&Int` fix and each application of a total function as one unknown value (one of its equations' results, when they cover every argument), where each partial Int operation in it (division, remainder, shift, exponent, bit range) is defined",
            "warning[krs::analysis::stale-underspecified]: `FlagBit` states `underspecified`, but its equations define every argument; remove `underspecified`",
            "warning[krs::analysis::uncovered-total-function]: total function `Nibble` has no equation for `Nibble(16)`",
            "= note: KRS evaluated the `requires` of its equations on every argument they bound (0..=15) and on one argument beyond them, which stands for every other",
            "warning[krs::analysis::uncovered-total-function]: total function `Page` has no equation for `Page(opcode)` when `High(opcode)` is 2",
            "= note: 2 of its equations have `requires`; KRS decides a `requires` only as a Boolean combination of comparisons with integer constants and between two integers and of `k::matches!` tests, reading the bits that comparisons of `bitRangeInt` and `&Int` fix and each application of a total function as one unknown value (one of its equations' results, when they cover every argument), where each partial Int operation in it (division, remainder, shift, exponent, bit range) is defined",
            "warning[krs::analysis::uncovered-total-function]: total function `Quotient` has no equation for `Quotient(0, 0)`",
            "= note: 2 of its equations have `requires`; KRS decides a `requires` only as a Boolean combination of comparisons with integer constants and between two integers and of `k::matches!` tests, reading the bits that comparisons of `bitRangeInt` and `&Int` fix and each application of a total function as one unknown value (one of its equations' results, when they cover every argument), where each partial Int operation in it (division, remainder, shift, exponent, bit range) is defined",
            "warning[krs::analysis::uncovered-total-function]: total function `Size` has no equation for `Size(0)`",
            "warning[krs::analysis::uncovered-total-function]: total function `Table` has no equation for `Table(3)`",
        ]
    "#]]
    .assert_debug_eq(&lines);
}

/// `krs expand` lowers the definition as `emit-k` does, so it reports the same
/// warnings about it, on stderr in either message format, and its stdout
/// holds only the expansion.
#[test]
fn expand_reports_the_warnings_emit_k_reports() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    package(temporary.path(), "language", LANGUAGE, None, "main");
    let manifest = workspace(temporary.path(), &["language"]);
    let (success, emitted) = emit(
        target.path(),
        &manifest,
        "language",
        &temporary.path().join("emitted"),
        &[],
    );
    assert!(success, "{emitted:#?}");
    let emitted = emitted
        .into_iter()
        .filter(|line| line.starts_with("warning["))
        .collect::<Vec<_>>();
    assert!(!emitted.is_empty());
    let expand = |format: &str| {
        let mut process = krs_command!();
        fixture_build_env(&mut process, target.path());
        let result = process
            .args(["expand", format, "--manifest-path"])
            .arg(&manifest)
            .args(["--package", "language", "--definition", "main"])
            .env("NO_COLOR", "1")
            .output()
            .unwrap();
        let stderr = String::from_utf8(result.stderr).unwrap();
        assert!(result.status.success(), "{stderr}");
        (String::from_utf8(result.stdout).unwrap(), stderr)
    };
    let (human, stderr) = expand("--message-format=human");
    let headlines = stderr
        .lines()
        .filter(|line| line.starts_with("warning[") || line.starts_with("error["))
        .collect::<Vec<_>>();
    assert_eq!(headlines, emitted, "{stderr}");
    assert!(
        human.starts_with("// @generated by `krs expand`"),
        "{human}"
    );
    assert!(!human.contains("warning["), "{human}");
    let (json, stderr) = expand("--message-format=json");
    assert_eq!(json, human);
    let envelopes = stderr
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(envelopes.len(), emitted.len(), "{stderr}");
    for (envelope, headline) in envelopes.iter().zip(&emitted) {
        assert_eq!(envelope["schema_version"], 1, "{stderr}");
        assert_eq!(envelope["severity"], "warning", "{stderr}");
        let code = envelope["code"].as_str().unwrap();
        assert!(
            headline.starts_with(&format!("warning[{code}]: ")),
            "{headline}"
        );
    }
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
fn guards_that_apply_functions_and_match_patterns_are_read() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    package(temporary.path(), "guards", GUARDS, None, "main");
    let manifest = workspace(temporary.path(), &["guards"]);
    let (success, lines) = emit(
        target.path(),
        &manifest,
        "guards",
        &temporary.path().join("emitted"),
        &[],
    );
    assert!(success, "{lines:#?}");
    let headlines = lines
        .into_iter()
        .filter(|line| line.starts_with("warning[") || line.contains("also uncovered"))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "warning[krs::analysis::uncovered-total-function]: total function `Decoded` has no equation for `Decoded(6)`",
            "= note: also uncovered: `Decoded(7)`; `Decoded(8)`",
            "warning[krs::analysis::uncovered-total-function]: total function `LooseSign` has no equation for `LooseSign(0)`",
            "warning[krs::analysis::uncovered-total-function]: total function `PartialScore` has no equation for `PartialScore(value)` when `Classify(value)` is `Kinds::C`",
            "warning[krs::analysis::uncovered-total-function]: total function `SignedLess` has no equation for `SignedLess(0, right)` when `Sign(right)` is 0",
            "warning[krs::analysis::stale-underspecified]: `StatedLess` states `underspecified`, but its equations define every argument; remove `underspecified`",
            "warning[krs::analysis::stale-underspecified]: `StatedSign` states `underspecified`, but its equations define every argument; remove `underspecified`",
            "warning[krs::analysis::uncovered-total-function]: total function `UsesLooseSign` has no equation for `UsesLooseSign(value)` when `LooseSign(value)` is 0",
            "warning[krs::analysis::uncovered-total-function]: total function `UsesPing` has no equation for `UsesPing(value)` when `Ping(value)` is 0",
            "warning[krs::analysis::uncovered-total-function]: total function `UsesStatedSign` has no equation for `UsesStatedSign(value)` when `StatedSign(value)` is 0",
        ]
    "#]].assert_debug_eq(&headlines);
}

/// A `raw_k!` sentence may add an equation the checks do not see, so no
/// function has a range and none is evaluated.
#[test]
fn raw_k_sentences_turn_off_ranges_and_evaluation() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let source = r#"
use k::builtin::{Int, KSequence};
use k::Term;

#[k::function(total, internal)]
pub fn TwoSign(value: Term<Int>) -> Term<Int> {
    if value >= 0 { 1 } else { -1 }
}

#[k::function(total, internal)]
pub fn UsesTwoSign(value: Term<Int>) -> Term<Int> {
    match TwoSign(value) {
        1 => 10,
        -1 => 20,
    }
}

#[k::function(total, internal)]
pub fn Overlapping(value: Term<Int>) -> Term<Int> {
    match (TwoSign(value), value) {
        (1, v) if v < 10 => 1,
        (_, v) if v >= 5 => 2,
        _ => 3,
    }
}

k::raw_k!(r"rule twoSign(0) => 7 [priority(10)]");

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
    package(temporary.path(), "raw", source, None, "main");
    let manifest_path = temporary.path().join("raw/Cargo.toml");
    let manifest = fs::read_to_string(&manifest_path).unwrap().replace(
        "[package.metadata.krs]\n",
        "[package.metadata.krs]\nallow-raw-k = true\n",
    );
    fs::write(&manifest_path, manifest).unwrap();
    let manifest = workspace(temporary.path(), &["raw"]);
    let (success, lines) = emit(
        target.path(),
        &manifest,
        "raw",
        &temporary.path().join("emitted"),
        &[],
    );
    assert!(success, "{lines:#?}");
    let headlines = lines
        .into_iter()
        .filter(|line| line.starts_with("warning[") || line.starts_with("error["))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "warning[krs::analysis::uncovered-total-function]: total function `UsesTwoSign` has no equation for `UsesTwoSign(value)` when `TwoSign(value)` is 0",
        ]
    "#]].assert_debug_eq(&headlines);
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
