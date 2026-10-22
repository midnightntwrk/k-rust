//! Branching bodies of the function shorthand on authored packages: the
//! equations an `if` chain or a `match` defines are the equations written by
//! hand, overlapping arms are an error at the later arm, and the coverage
//! lint reads branches as it reads equations.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// The declarations both packages share.
const PRELUDE: &str = r#"
use k::builtin::{Bool, Int, KSequence, Map, int, map};
use k::Term;

k::sorts! {
    TypeInfo;
    Primitive;
}

#[k::constructors(sort = Primitive, result = k::KResult)]
#[k::precedence((Boolean, Signed))]
pub enum PrimitiveType {
    #[k::syntax("boolean")]
    Boolean,
    #[k::syntax("signed({width})")]
    Signed { width: Int },
}

#[k::constructors(sort = TypeInfo, result = k::KResult)]
#[k::precedence((PrimitiveInfo, TupleInfo))]
pub enum Info {
    #[k::syntax("primitive({primitive})")]
    PrimitiveInfo { primitive: Primitive },
    #[k::syntax("tuple({count}, {size})")]
    TupleInfo { count: Int, size: Int },
}

#[k::function(total, internal)]
pub fn Sign(value: Term<Int>) -> Term<Int>;

#[k::function(total, internal)]
pub fn Magnitude(value: Term<Int>) -> Term<Int> {
    int::abs(value)
}

#[k::function(total, internal)]
pub fn BoolToWord(value: Term<Bool>) -> Term<Int>;

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

/// The functions as branching bodies.
const BRANCHING: &str = r#"
#[k::function(total, internal)]
pub fn StorageValue(storage: Term<Map>, index: Term<Int>) -> Term<Int> {
    if map::in_keys(index, storage) { map::get(storage, index) } else { 0 }
}

#[k::function(total, internal, underspecified = "Sign is 1 or -1")]
pub fn SignedLess(left: Term<Int>, right: Term<Int>) -> Term<Int> {
    match (Sign(left), Sign(right)) {
        (1, 1) => BoolToWord(int::lt(left, right)),
        (1, -1) => BoolToWord(false),
        (-1, 1) => BoolToWord(true),
        (-1, -1) => BoolToWord(int::lt(Magnitude(right), Magnitude(left))),
    }
}

#[k::function(partial, internal)]
pub fn ElementSize(types: Term<Map>, info: Term<TypeInfo>) -> Term<Int> {
    match info {
        Info::PrimitiveInfo { primitive: PrimitiveType::Boolean() } => 1,
        Info::PrimitiveInfo { primitive: PrimitiveType::Signed { width } } => int::div(width, 8),
        Info::TupleInfo { count: 0, .. } => 0,
        Info::TupleInfo { size, .. } if int::gt(size, 0) => int::div(size, 8),
    }
}

#[k::function(total, internal)]
pub fn Flip(value: Term<Int>) -> Term<Int> {
    match value {
        2 | -1 => 1,
        1 => -1,
        _ => 0,
    }
}

#[k::requires(int::ge(width, 0))]
#[k::function(partial, internal)]
pub fn Fit(width: Term<Int>, value: Term<Int>) -> Term<Int> {
    match width {
        0 => 0,
        #[k::label(fit_wide)]
        _ => if int::lt(value, 0) { int::add(value, width) } else { value },
    }
}
"#;

/// The same equations written by hand, under the names the branches take.
const LONG_FORM: &str = r#"
#[k::function(total, internal)]
pub fn StorageValue(storage: Term<Map>, index: Term<Int>) -> Term<Int>;

#[k::requires(map::in_keys(index, storage))]
#[k::equation]
fn storage_value_1(k::term![StorageValue(storage, index)]: Term<Int>) -> Term<Int> {
    map::get(storage, index)
}

#[k::requires(map::in_keys(index, storage).not::<Bool>())]
#[k::equation]
fn storage_value_2(k::term![StorageValue(storage, index)]: Term<Int>) -> Term<Int> {
    0
}

#[k::function(total, internal, underspecified = "Sign is 1 or -1")]
pub fn SignedLess(left: Term<Int>, right: Term<Int>) -> Term<Int>;

#[k::requires(Sign(left).eq::<Int>(1) && Sign(right).eq::<Int>(1))]
#[k::equation]
fn signed_less_1(k::term![SignedLess(left, right)]: Term<Int>) -> Term<Int> {
    BoolToWord(int::lt(left, right))
}

#[k::requires(Sign(left).eq::<Int>(1) && Sign(right).eq::<Int>(-1))]
#[k::equation]
fn signed_less_2(k::term![SignedLess(left, right)]: Term<Int>) -> Term<Int> {
    BoolToWord(false)
}

#[k::requires(Sign(left).eq::<Int>(-1) && Sign(right).eq::<Int>(1))]
#[k::equation]
fn signed_less_3(k::term![SignedLess(left, right)]: Term<Int>) -> Term<Int> {
    BoolToWord(true)
}

#[k::requires(Sign(left).eq::<Int>(-1) && Sign(right).eq::<Int>(-1))]
#[k::equation]
fn signed_less_4(k::term![SignedLess(left, right)]: Term<Int>) -> Term<Int> {
    BoolToWord(int::lt(Magnitude(right), Magnitude(left)))
}

#[k::function(partial, internal)]
pub fn ElementSize(types: Term<Map>, info: Term<TypeInfo>) -> Term<Int>;

#[k::equation]
fn element_size_1(
    k::term![ElementSize(_, Info::PrimitiveInfo { primitive: PrimitiveType::Boolean() })]: Term<Int>,
) -> Term<Int> {
    1
}

#[k::equation]
fn element_size_2(
    k::term![ElementSize(_, Info::PrimitiveInfo { primitive: PrimitiveType::Signed { width } })]: Term<Int>,
) -> Term<Int> {
    int::div(width, 8)
}

#[k::equation]
fn element_size_3(k::term![ElementSize(_, Info::TupleInfo { count: 0, size: _ })]: Term<Int>) -> Term<Int> {
    0
}

#[k::requires(int::gt(size, 0))]
#[k::equation]
fn element_size_4(k::term![ElementSize(_, Info::TupleInfo { count: _, size })]: Term<Int>) -> Term<Int> {
    int::div(size, 8)
}

#[k::function(total, internal)]
pub fn Flip(value: Term<Int>) -> Term<Int>;

#[k::equation]
fn flip_1(k::term![Flip(2 | -1)]: Term<Int>) -> Term<Int> {
    1
}

#[k::equation]
fn flip_2(k::term![Flip(1)]: Term<Int>) -> Term<Int> {
    -1
}

#[k::equation(owise)]
fn flip_3(k::term![Flip(_)]: Term<Int>) -> Term<Int> {
    0
}

#[k::function(partial, internal)]
pub fn Fit(width: Term<Int>, value: Term<Int>) -> Term<Int>;

#[k::requires(int::ge(width, 0))]
#[k::equation]
fn fit_1(k::term![Fit(width @ 0, _)]: Term<Int>) -> Term<Int> {
    0
}

#[k::requires(int::ge(width, 0) && int::lt(value, 0))]
#[k::equation(owise)]
fn fit_wide_1(k::term![Fit(width, value)]: Term<Int>) -> Term<Int> {
    int::add(value, width)
}

#[k::requires(int::ge(width, 0) && int::lt(value, 0).not::<Bool>())]
#[k::equation(owise)]
fn fit_wide_2(k::term![Fit(width, value)]: Term<Int>) -> Term<Int> {
    value
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a package named `name` whose K namespace is `namespace`.
fn package(root: &Path, name: &str, namespace: &str, source: &str) {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n",
            krs_path(),
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

/// Runs `krs emit-k` and returns its success, its stderr, and the emitted
/// `definition.k`.
fn emit(target: &Path, manifest: &Path, package: &str, output: &Path) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let result = process
        .args(["emit-k", "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main", "--output"])
        .arg(output)
        .env("NO_COLOR", "1")
        .output()
        .unwrap();
    let definition = fs::read_to_string(output.join("definition.k")).unwrap_or_default();
    (
        result.status.success(),
        String::from_utf8(result.stderr).unwrap(),
        definition,
    )
}

/// The definition's rules, each with its continuation lines, without labels
/// (which hash each package's identities), in sorted order.
fn rules(definition: &str) -> Vec<String> {
    let mut rules: Vec<String> = Vec::new();
    for line in definition.lines() {
        let line = line.trim();
        if line.starts_with("rule ") {
            rules.push(line.to_owned());
        } else if line.starts_with("requires ")
            && let Some(rule) = rules.last_mut()
        {
            rule.push(' ');
            rule.push_str(line);
        }
    }
    for rule in &mut rules {
        if let Some(start) = rule.find("label(krsRule_") {
            let end = rule[start..]
                .find(')')
                .map_or(rule.len(), |end| start + end + 1);
            rule.replace_range(start..end, "label(..)");
        }
    }
    rules.sort();
    rules
}

#[test]
fn branches_emit_the_equations_written_by_hand() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    package(
        temporary.path(),
        "branching",
        "ORG-KRS-BRANCHES",
        &format!("{PRELUDE}{BRANCHING}"),
    );
    package(
        temporary.path(),
        "long_form",
        "ORG-KRS-BRANCHES",
        &format!("{PRELUDE}{LONG_FORM}"),
    );
    let manifest = workspace(temporary.path(), &["branching", "long_form"]);
    let (success, stderr, branching) = emit(
        target.path(),
        &manifest,
        "branching",
        &temporary.path().join("branching-out"),
    );
    assert!(success, "{stderr}");
    let (success, stderr, long_form) = emit(
        target.path(),
        &manifest,
        "long_form",
        &temporary.path().join("long-form-out"),
    );
    assert!(success, "{stderr}");
    let branching = rules(&branching);
    assert_eq!(branching, rules(&long_form));
    // `Magnitude`'s one equation, and the sixteen that branches define.
    assert_eq!(branching.len(), 17, "{branching:#?}");
}

/// Shapes whose equations the macro and the collector must anchor alike,
/// negative literals in every position among them.
const SHAPES: &str = r#"
#[k::function(total, internal, underspecified = "only the shapes matter")]
pub fn Shapes(value: Term<Int>, info: Term<TypeInfo>, flag: Term<Bool>) -> Term<Int> {
    match (value, Sign(value)) {
        (-1, 1 | -1) => 0,
        (0, ..) => match info {
            Info::TupleInfo { count: -1, .. } => 1,
            Info::PrimitiveInfo { primitive } if flag => if int::lt(value, 0) { 2 } else { 3 },
            #[k::label(shapes_tuple)]
            other => match Sign(Magnitude(value)) {
                -1 => 4,
                _ => 5,
            },
        },
        (n, -1) if flag && int::gt(n, 0) => match info {
            Info::TupleInfo { count: 0 | -1, size } => int::add(n, size),
            _ => int::add(value, 6),
        },
        _ => 7,
    }
}
"#;

#[test]
fn every_branch_shape_is_anchored_alike_by_the_macro_and_the_collector() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    package(
        temporary.path(),
        "shapes",
        "ORG-KRS-SHAPES",
        &format!("{PRELUDE}{SHAPES}"),
    );
    let manifest = workspace(temporary.path(), &["shapes"]);
    let (success, stderr, definition) = emit(
        target.path(),
        &manifest,
        "shapes",
        &temporary.path().join("emitted"),
    );
    assert!(success, "{stderr}");
    assert!(!stderr.contains("error"), "{stderr}");
    expect_test::expect![[r#"
        [
            "rule shapes ( ( -1 #as Value:Int ) , _ , _ ) => 0 requires (sign ( Value:Int ) ==Int 1) orElseBool (sign ( Value:Int ) ==Int -1) [label(..)]",
            "rule shapes ( ( 0 #as Value:Int ) , ( Other:TypeInfo #as Info:TypeInfo ) , Flag:Bool ) => 4 requires ((notBool ( tuple ( -1 , _ ) :=K Info:TypeInfo )) andThenBool (notBool (( primitive ( _ ) :=K Info:TypeInfo ) andThenBool Flag:Bool))) andThenBool (sign ( magnitude ( Value:Int ) ) ==Int -1) [label(..)]",
            "rule shapes ( ( 0 #as Value:Int ) , ( Other:TypeInfo #as Info:TypeInfo ) , Flag:Bool ) => 5 requires ((notBool ( tuple ( -1 , _ ) :=K Info:TypeInfo )) andThenBool (notBool (( primitive ( _ ) :=K Info:TypeInfo ) andThenBool Flag:Bool))) andThenBool (notBool (sign ( magnitude ( Value:Int ) ) ==Int -1)) [label(..)]",
            "rule shapes ( ( 0 #as Value:Int ) , primitive ( Primitive:Primitive ) , Flag:Bool ) => 2 requires Flag:Bool andThenBool (Value:Int <Int 0) [label(..)]",
            "rule shapes ( ( 0 #as Value:Int ) , primitive ( Primitive:Primitive ) , Flag:Bool ) => 3 requires Flag:Bool andThenBool (notBool (Value:Int <Int 0)) [label(..)]",
            "rule shapes ( ( N:Int #as Value:Int ) , Info:TypeInfo , Flag:Bool ) => Value:Int +Int 6 requires (((sign ( Value:Int ) ==Int -1) andThenBool Flag:Bool) andThenBool (N:Int >Int 0)) andThenBool (notBool ( tuple ( ( 0 #Or -1 ) , _ ) :=K Info:TypeInfo )) [label(..)]",
            "rule shapes ( ( N:Int #as Value:Int ) , tuple ( ( 0 #Or -1 ) , Size:Int ) , Flag:Bool ) => N:Int +Int Size:Int requires ((sign ( Value:Int ) ==Int -1) andThenBool Flag:Bool) andThenBool (N:Int >Int 0) [label(..)]",
            "rule shapes ( 0 , tuple ( -1 , _ ) , _ ) => 1 [label(..)]",
            "rule shapes ( _ , _ , _ ) => 7 [priority(200), label(..)]",
        ]
    "#]]
    .assert_debug_eq(
        &rules(&definition)
            .into_iter()
            .filter(|rule| rule.starts_with("rule shapes"))
            .collect::<Vec<_>>(),
    );
}

#[test]
fn overlapping_arms_are_an_error_at_the_later_arm() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    package(
        temporary.path(),
        "overlap",
        "ORG-KRS-OVERLAP",
        &format!(
            "{PRELUDE}
#[k::function(total, internal)]
pub fn Small(value: Term<Int>) -> Term<Int> {{
    match value {{
        0 => 1,
        n if int::lt(n, 5) => 2,
        _ => 3,
    }}
}}
"
        ),
    );
    let manifest = workspace(temporary.path(), &["overlap"]);
    let (success, stderr, _) = emit(
        target.path(),
        &manifest,
        "overlap",
        &temporary.path().join("emitted"),
    );
    assert!(!success, "{stderr}");
    let line = PRELUDE.lines().count() + 6;
    assert!(
        stderr.contains("error[krs::analysis::overlapping-match-arms]: branches `small_1` and `small_2` of `Small` both apply to `Small(0)` and give it different results, `1` and `2`"),
        "{stderr}"
    );
    assert!(
        stderr.contains(&format!("overlap/src/lib.rs:{line}:9")),
        "{stderr}"
    );
}

#[test]
fn the_coverage_lint_reads_branches_as_equations() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    package(
        temporary.path(),
        "uncovered",
        "ORG-KRS-UNCOVERED",
        &format!(
            "{PRELUDE}
#[k::function(total, internal)]
pub fn Digit(value: Term<Int>) -> Term<Int> {{
    match value {{
        0 => 10,
        n if int::lt(n, 0) => 11,
        1 | 2 => 12,
    }}
}}
"
        ),
    );
    let manifest = workspace(temporary.path(), &["uncovered"]);
    let (success, stderr, _) = emit(
        target.path(),
        &manifest,
        "uncovered",
        &temporary.path().join("emitted"),
    );
    assert!(success, "{stderr}");
    assert!(
        stderr.contains(
            "warning[krs::analysis::uncovered-total-function]: total function `Digit` has no equation for `Digit(3)`"
        ),
        "{stderr}"
    );
}
