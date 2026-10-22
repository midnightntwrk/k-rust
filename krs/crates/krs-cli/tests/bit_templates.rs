//! `k::bits!` templates end to end: authored packages through `krs check`
//! and `krs run`, which run the macro and the collector's reparse on the same
//! source, so a template whose long form differs between them fails as a
//! stale anchor.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Bool, Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((FieldOf, AliasOf, PairOf, SpliceOf, CodeOf, FlagOf, PageOf, KindOf, ImmOf, BranchOf, UpperOf))]
pub enum ExpSyntax {
    #[k::syntax("fieldOf({n})")]
    FieldOf { n: Int },
    #[k::syntax("aliasOf({n})")]
    AliasOf { n: Int },
    #[k::syntax("pairOf({a}, {b})")]
    PairOf { a: Int, b: Int },
    #[k::syntax("spliceOf({n})")]
    SpliceOf { n: Int },
    #[k::syntax("codeOf({n})")]
    CodeOf { n: Int },
    #[k::syntax("flagOf({b})")]
    FlagOf { b: Bool },
    #[k::syntax("pageOf({n})")]
    PageOf { n: Int },
    #[k::syntax("kindOf({n})")]
    KindOf { n: Int },
    #[k::syntax("immOf({n})")]
    ImmOf { n: Int },
    #[k::syntax("branchOf({n})")]
    BranchOf { n: Int },
    #[k::syntax("upperOf({n})")]
    UpperOf { n: Int },
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

#[k::function(total, internal)]
pub fn Code(value: Term<Int>) -> Term<Int>;

#[k::function(total, internal)]
pub fn Flag(value: Term<Bool>) -> Term<Int>;
"#;

/// Fields in the results of readable clauses, with and without `op @`, in a
/// replacement and in a splice; templates beside an authored top-level `||`
/// in a table row and in an `#[k::equation]` fn; and `k::bits!(value, "..")`
/// tests as a `Bool` result, in conditions, and in a claim, which states
/// exactly the guard of the clause it is about. Two more claims state their
/// opcodes by arithmetic only: one needs the guard's `bitRangeInt` terms read
/// as division and remainder, the other needs the literal row an all-fixed
/// template becomes to be refuted, not to block `owise`, for a symbolic
/// argument.
const POSITIVE: &str = r#"
k::rules! {
    for Exp;
    use ExpSyntax::*;

    field_of : FieldOf(k::bits!("0aaa"))                     => a;
    alias_of : AliasOf(op @ k::bits!("1aaa"))                => a.add::<Int>(op);
    pair_of  : PairOf(k::bits!("0a"), k::bits!("b1"))        => a.add::<Int>(b);
    splice_of: SpliceOf(k::bits!("1 aa"))                     => k![a, a];
    code_of  : CodeOf(n)                                      => crate::Code(n);
    page_of  : PageOf(n)                                      => crate::Page(n);
    kind_of  : KindOf(n)                                      => crate::Kind(n);
    imm_of   : ImmOf(k::bits!("iiii 0011", i: signed))        => i;
    branch_of: BranchOf(k::bits!("bbb 0 b_", b: signed[4 | 2:1 | 3])) => b;
    upper_of : UpperOf(k::bits!("uuu 1", u: [6:4]))           => u;
}

k::equations! {
    for Code;
    #[k::requires(a.gt::<Int>(2) || a.eq::<Int>(0))]
    code_row: k::bits!("10 aa") => a;
    #[k::equation(owise)]
    code_other: n => 100;
}

#[k::requires(b.eq::<Int>(1) || b.eq::<Int>(2))]
#[k::equation]
fn code_fn(k::term![Code(k::bits!("01 bb"))]: Term<Int>) -> Term<Int> {
    b.add::<Int>(10)
}

#[k::function(total, internal)]
pub fn High(value: Term<Int>) -> Term<Bool>;

k::equations! {
    for High;
    high: n => k::bits!(n, "1_ __");
}

#[k::function(total, internal)]
pub fn Page(value: Term<Int>) -> Term<Int>;

k::equations! {
    for Page;
    #[k::requires(crate::High(n))]
    page_high: n => 1;
    #[k::requires(k::bits!(n, "00 aa") || k::bits!(n, "1"))]
    page_low: n => 2;
    #[k::equation(owise)]
    page_other: n => 0;
}

#[k::function(total, internal)]
pub fn Kind(value: Term<Int>) -> Term<Int>;

k::equations! {
    for Kind;
    kind_six  : k::bits!("0110")  => 1;
    kind_low  : k::bits!("00 aa") => a;
    #[k::equation(owise)]
    kind_other: n                 => 0;
}

#[k::claim(all_paths, label = "field-of-arith")]
#[k::requires(i.ge::<Int>(0) && i.lt::<Int>(8))]
pub fn field_of_arith(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::FieldOf(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(i, ..tail), ..state }
}

#[k::claim(all_paths, label = "kind-of-high")]
#[k::requires(i.ge::<Int>(16))]
pub fn kind_of_high(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::KindOf(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(0, ..tail), ..state }
}

#[k::claim(all_paths, label = "imm-of-negative")]
#[k::requires(k::bits!(i, "1___ 0011"))]
pub fn imm_of_negative(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::ImmOf(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(i.sub::<Int>(259).div::<Int>(16), ..tail), ..state }
}

#[k::claim(all_paths, label = "branch-of-negative")]
#[k::requires(k::bits!(i, "1__ 0 __"))]
pub fn branch_of_negative(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::BranchOf(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(
        i.bit_range::<Int>(4, 1).mul::<Int>(4)
            .add::<Int>(i.bit_range::<Int>(3, 1).mul::<Int>(2))
            .add::<Int>(i.bit_range::<Int>(1, 1).mul::<Int>(8))
            .sub::<Int>(16),
        ..tail
    ), ..state }
}

#[k::claim(all_paths, label = "upper-of-odd")]
#[k::requires(k::bits!(i, "___1"))]
pub fn upper_of_odd(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::UpperOf(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(i.sub::<Int>(1).mul::<Int>(8), ..tail), ..state }
}

#[k::claim(all_paths, label = "field-of-low")]
#[k::requires(k::bits!(i, "0aaa"))]
pub fn field_of_low(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::FieldOf(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(i.bit_range::<Int>(0, 3), ..tail), ..state }
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is the preamble and `source`.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-BITS-{}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
            name.to_ascii_uppercase()
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

/// The head of `<k>` after `krs run` of `program`.
fn run(target: &Path, manifest: &Path, program: &str) -> String {
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, program).unwrap();
    let (_, stdout, stderr) = krs(target, manifest, "run", &[file.to_str().unwrap()]);
    let mut lines = stdout.lines().skip_while(|line| line.trim() != "<k>");
    lines.nth(1).map_or_else(
        || panic!("`krs run {program}` printed no <k> cell:\n{stdout}\n{stderr}"),
        |line| line.trim().trim_end_matches(" ~> .K").to_owned(),
    )
}

#[test]
fn templates_and_tests_check_run_and_prove() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "positive", POSITIVE);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");
    let outcomes = [
        "fieldOf(5)",
        "aliasOf(13)",
        "pairOf(1, 3)",
        "spliceOf(6)",
        "codeOf(8)",
        "codeOf(11)",
        "codeOf(9)",
        "codeOf(5)",
        "codeOf(4)",
        "pageOf(9)",
        "pageOf(2)",
        "pageOf(5)",
        "pageOf(16)",
        "kindOf(6)",
        "kindOf(2)",
        "kindOf(7)",
        "immOf(243)",
        "immOf(115)",
        "immOf(131)",
        "branchOf(42)",
        "branchOf(16)",
        "upperOf(11)",
    ]
    .map(|program| format!("{program} => {}", run(target.path(), &manifest, program)));
    expect_test::expect![[r#"
        [
            "fieldOf(5) => 5",
            "aliasOf(13) => 18",
            "pairOf(1, 3) => 2",
            "spliceOf(6) => 2 ~> 2",
            "codeOf(8) => 0",
            "codeOf(11) => 3",
            "codeOf(9) => 100",
            "codeOf(5) => 11",
            "codeOf(4) => 100",
            "pageOf(9) => 1",
            "pageOf(2) => 2",
            "pageOf(5) => 0",
            "pageOf(16) => 0",
            "kindOf(6) => 1",
            "kindOf(2) => 2",
            "kindOf(7) => 0",
            "immOf(243) => -1",
            "immOf(115) => 7",
            "immOf(131) => -8",
            "branchOf(42) => -6",
            "branchOf(16) => 4",
            "upperOf(11) => 80",
        ]
    "#]]
    .assert_debug_eq(&outcomes);
    let (proven, stdout, stderr) = krs(target.path(), &manifest, "prove", &[]);
    assert!(proven, "{stdout}\n{stderr}");
    for label in [
        "field-of-low",
        "field-of-arith",
        "kind-of-high",
        "imm-of-negative",
        "branch-of-negative",
        "upper-of-odd",
    ] {
        assert!(stdout.contains(&format!("{label}: proven")), "{stdout}");
    }
}

/// The `error[..]` headlines of `krs check` and the locations they point at.
fn check_errors(target: &Path, manifest: &Path) -> Vec<String> {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    let directory = format!("{}/", manifest.parent().unwrap().display());
    stderr
        .lines()
        .filter(|line| line.starts_with("error[") || line.trim_start().starts_with("--> "))
        .map(|line| line.trim().replace(&directory, ""))
        .collect()
}

#[test]
fn a_template_at_a_position_of_another_sort_is_reported_at_the_template() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let errors = [
        (
            "row",
            "k::equations! {\n    for Flag;\n    flag_row: k::bits!(\"1_\") => 1;\n    #[k::equation(owise)]\n    flag_other: b => 0;\n}\n",
        ),
        (
            "function",
            "#[k::equation]\nfn flag_fn(k::term![Flag(k::bits!(\"1_\"))]: Term<Int>) -> Term<Int> {\n    1\n}\n",
        ),
        (
            "rule",
            "k::rules! {\n    for Exp;\n    use ExpSyntax::*;\n    flag_of: FlagOf(k::bits!(\"1_\")) => 0;\n}\n",
        ),
        (
            "all-fixed",
            "k::equations! {\n    for Flag;\n    flag_row: k::bits!(\"10\") => 1;\n    #[k::equation(owise)]\n    flag_other: b => 0;\n}\n",
        ),
    ]
    .map(|(name, source)| {
        let manifest = package(temporary.path(), name, source);
        check_errors(target.path(), &manifest)
    });
    expect_test::expect![[r#"
        [
            [
                "error[krs::analysis::bit-template-sort]: a `k::bits!` template matches an `Int`, but it stands where a term of sort Bool is expected, and no `Int` is one; a template belongs in an argument of sort `Int` or of a sort above it",
                "--> src/lib.rs:58:24",
            ],
            [
                "error[krs::analysis::bit-template-sort]: a `k::bits!` template matches an `Int`, but it stands where a term of sort Bool is expected, and no `Int` is one; a template belongs in an argument of sort `Int` or of a sort above it",
                "--> src/lib.rs:57:35",
            ],
            [
                "error[krs::analysis::bit-template-sort]: a `k::bits!` template matches an `Int`, but it stands where a term of sort Bool is expected, and no `Int` is one; a template belongs in an argument of sort `Int` or of a sort above it",
                "--> src/lib.rs:59:30",
            ],
            [
                "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-BITS-ALL-FIXED::flag_row (equation): literal `2` of sort Int is not admissible at sort Bool",
                "--> src/lib.rs:58:24",
            ],
        ]
    "#]]
    .assert_debug_eq(&errors);
}

#[test]
fn expand_writes_an_equation_fn_template_condition_as_a_table_row_does() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "expanded", POSITIVE);
    let (success, stdout, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    // From the table row's condition through the equation fn's body.
    let row = stdout
        .find("fn code_row(")
        .expect("the table row is written");
    let start = stdout[..row].rfind("#[k::requires(").unwrap();
    let function = stdout
        .find("fn code_fn(")
        .expect("the equation fn is written");
    let end = function + stdout[function..].find("\n}\n").unwrap() + 3;
    expect_test::expect![[r"
        #[k::requires(
            k::builtin::bool::and_then(
                k::builtin::bool::and_then(
                    k::builtin::bool::and_then(
                        k::builtin::int::ge(bits, 0),
                        k::builtin::int::lt(bits, 16)
                    ),
                    k::builtin::int::eq(k::builtin::int::bit_range(bits, 2, 2), 2)
                ),
                k::builtin::bool::or_else(
                    k::builtin::int::gt(k::builtin::int::bit_range(bits, 0, 2), 2),
                    k::builtin::int::eq(k::builtin::int::bit_range(bits, 0, 2), 0)
                )
            )
        )]
        fn code_row(
            k::term![crate ::Code(bits)]: k::Term<k::builtin::Int>,
        ) -> k::Term<k::builtin::Int> {
            k::builtin::int::bit_range(bits, 0, 2)
        }
        #[k::equation(owise)]
        fn code_other(
            k::term![crate ::Code(n)]: k::Term<k::builtin::Int>,
        ) -> k::Term<k::builtin::Int> {
            100
        }
        #[k::requires(
            k::builtin::bool::and_then(
                k::builtin::bool::and_then(
                    k::builtin::bool::and_then(
                        k::builtin::int::ge(bits, 0),
                        k::builtin::int::lt(bits, 16)
                    ),
                    k::builtin::int::eq(k::builtin::int::bit_range(bits, 2, 2), 1)
                ),
                k::builtin::bool::or_else(
                    k::builtin::int::eq(k::builtin::int::bit_range(bits, 0, 2), 1),
                    k::builtin::int::eq(k::builtin::int::bit_range(bits, 0, 2), 2)
                )
            )
        )]
        #[k::equation]
        fn code_fn(k::term![Code(bits)]: Term<Int>) -> Term<Int> {
            bits.bit_range::<Int>(0, 2).add::<Int>(10)
        }
    "]]
    .assert_eq(&stdout[start..end]);
}
