//! Int literals in every radix and one-segment paths under a block's enum
//! import, end to end: authored packages through `krs check`, `emit-k`, and
//! `krs run`.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Load, Mask, Twice, Shadow, Wide))]
pub enum ExpSyntax {
    #[k::syntax("load({n})")]
    Load { n: Int },
    #[k::syntax("mask({n})")]
    Mask { n: Int },
    #[k::syntax("twice({n})")]
    Twice { n: Int },
    #[k::syntax("shadow({n})")]
    Shadow { n: Int },
    #[k::syntax("wide({n})")]
    Wide { n: Int },
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

mod helpers {
    use k::Term;
    use k::builtin::Int;

    #[k::function(total, internal)]
    pub fn Double(value: Term<Int>) -> Term<Int>;

    k::equations! {
        for Double;
        double: n => n.add::<Int>(n);
    }
}

use helpers::Double;

/// A crate function named like a variant of `ExpSyntax`.
#[k::function(total, internal)]
pub fn Shadow(value: Term<Int>) -> Term<Int>;

k::equations! {
    for Shadow;
    seven: n => 7;
}
"#;

/// The same definition, once with its Int literals in hex, octal, and binary
/// and once in decimal: a radix is spelling, so both emit the same K.
fn ports(literals: [&str; 6]) -> String {
    let [
        interrupt_flag,
        interrupt_enable,
        mask,
        low_nibble,
        wide,
        negative,
    ] = literals;
    format!(
        r"
#[k::function(total, internal)]
pub fn Port(value: Term<Int>) -> Term<Int>;

k::equations! {{
    for Port;
    use ExpSyntax::*;
    port_if: {interrupt_flag} => 1;
    port_ie: {interrupt_enable} => Double(2);
    #[k::equation(owise)]
    port_other: n => 0;
}}

k::rules! {{
    for Exp;
    use ExpSyntax::*;

    load:     Load(n)            => Port(n);
    mask:     Mask({mask})       => Double({low_nibble});
    twice:    Twice(n)           => Double(n);
    shadow:   Shadow(n)          => n;
    wide:     Wide({wide})       => {negative};
}}
"
    )
}

const RADIX: [&str; 6] = [
    "0xFF0F",
    "0xff_ff",
    "0b1010_0101",
    "0o17",
    "0x1_0000_0000_0000_0000_0000_0000_0000_0000",
    "-0x10",
];

const DECIMAL: [&str; 6] = [
    "65295",
    "65535",
    "165",
    "15",
    "340282366920938463463374607431768211456",
    "-16",
];

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace named `literals` under `root`, whose
/// library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    let directory = root.join("literals");
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"literals\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-LITERALS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package's `main` definition.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", "literals", "--definition", "main"])
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

/// The emitted `definition.k`.
fn emitted_k(target: &Path, manifest: &Path) -> String {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.k")).unwrap()
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

/// The `error[..]` headlines of `krs check` and the locations they point at.
fn check_errors(target: &Path, manifest: &Path) -> Vec<String> {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    let directory = format!("{}/", manifest.parent().unwrap().display());
    stderr
        .lines()
        .filter(|line| line.starts_with("error") || line.trim_start().starts_with("--> "))
        .map(|line| line.trim().replace(&directory, ""))
        .collect()
}

#[test]
fn radix_literals_emit_decimal_and_bare_paths_resolve_like_rust() {
    let target = shared_fixture_target();
    let radix = temp_dir();
    let decimal = temp_dir();
    let radix_manifest = package(radix.path(), &ports(RADIX));
    let decimal_manifest = package(decimal.path(), &ports(DECIMAL));
    let emitted = emitted_k(target.path(), &radix_manifest);
    assert_eq!(emitted, emitted_k(target.path(), &decimal_manifest));
    assert!(emitted.contains("65295"), "{emitted}");
    assert!(!emitted.contains("0xFF0F"), "{emitted}");

    let outcomes = [
        "load(65295)",
        "load(65535)",
        "load(3)",
        "mask(165)",
        "twice(21)",
        "shadow(5)",
        "wide(340282366920938463463374607431768211456)",
    ]
    .map(|program| {
        format!(
            "{program} => {}",
            run(target.path(), &radix_manifest, program)
        )
    });
    // `load` and `twice` call crate functions bare under `use ExpSyntax::*`,
    // `Double` through a module import; `shadow` names the variant, which
    // the block's glob import supplies over the crate function `Shadow`.
    expect_test::expect![[r#"
        [
            "load(65295) => 1",
            "load(65535) => 4",
            "load(3) => 0",
            "mask(165) => 30",
            "twice(21) => 42",
            "shadow(5) => 5",
            "wide(340282366920938463463374607431768211456) => -16",
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}

#[test]
fn a_suffixed_literal_is_rejected_whatever_its_radix() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "k::rules! {\n    for Exp;\n    use ExpSyntax::*;\n    wide: Wide(0xFFu8) => 0;\n}\n",
    );
    expect_test::expect![[r#"
        [
            "error[krs::syntax::unsupported-rule-pattern]: unsupported rule pattern: only unsuffixed Int (decimal, 0x hex, 0o octal, or 0b binary; optionally negative), Bool, String, and Float literals are term patterns",
            "--> src/lib.rs:65:16",
        ]
    "#]]
    .assert_debug_eq(&check_errors(target.path(), &manifest));
}

/// A second constructor enum whose `Load` shares a name with `ExpSyntax`'s.
const SECOND_ENUM: &str = r#"
#[k::constructors(sort = Exp, result = KResult)]
pub enum Boxed {
    #[k::syntax("boxed({n})")]
    Box { n: Int },
    #[k::syntax("fetch({n})")]
    Load { n: Int },
}
"#;

/// A rule block importing from two enums, written once with `use` items and
/// once with every head qualified.
fn imports(imported: bool) -> String {
    let block = if imported {
        "k::rules! {
    for Exp;
    use ExpSyntax::*;
    use Boxed::*;
    use Boxed::Load;
    use ExpSyntax::{Mask, Twice};

    boxed: Box(n)  => Twice(n);
    fetch: Load(n) => Mask(n);
}
"
    } else {
        "k::rules! {
    for Exp;

    boxed: Boxed::Box(n)  => ExpSyntax::Twice(n);
    fetch: Boxed::Load(n) => ExpSyntax::Mask(n);
}
"
    };
    format!("{SECOND_ENUM}{block}")
}

/// A block may hold any number of `use` items, which resolve its paths as
/// Rust resolves them: two globs supply every variant of both enums, the
/// explicit `use Boxed::Load` shadows the glob's `ExpSyntax::Load`, and a
/// grouped import names its variants, so the rules are the ones
/// written with qualified heads.
#[test]
fn a_block_resolves_its_paths_through_every_use_item() {
    let target = shared_fixture_target();
    let imported = temp_dir();
    let qualified = temp_dir();
    let imported_manifest = package(imported.path(), &imports(true));
    let qualified_manifest = package(qualified.path(), &imports(false));
    let emitted = emitted_k(target.path(), &imported_manifest);
    assert_eq!(emitted, emitted_k(target.path(), &qualified_manifest));
    assert!(emitted.contains("rule [fetch]:"), "{emitted}");
    assert!(emitted.contains("fetch ( N:Int )"), "{emitted}");
}

/// A name two glob imports supply is ambiguous only where a path uses it,
/// and rustc's error names both imports.
#[test]
fn a_name_two_globs_supply_is_an_error_naming_both_imports() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        &format!(
            "{SECOND_ENUM}k::rules! {{\n    for Exp;\n    use ExpSyntax::*;\n    use Boxed::*;\n    boxed: Box(n) => Twice(n);\n    fetch: Load(n) => n;\n}}\n"
        ),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    let directory = format!("{}/", manifest.parent().unwrap().display());
    let lines = stderr
        .lines()
        .filter(|line| {
            line.starts_with("error")
                || line.trim_start().starts_with("--> ")
                || line.trim_start().starts_with("= note")
        })
        .map(|line| line.trim().replace(&directory, ""))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "error[E0659]: `Load` is ambiguous",
            "--> src/lib.rs:75:12",
            "= note: ambiguous because of multiple glob imports of a name in the same module",
            "= note: `Load` could refer to the variant imported here (src/lib.rs:72:9)",
            "= note: `Load` could also refer to the variant imported here (src/lib.rs:73:9)",
        ]
    "#]]
    .assert_debug_eq(&lines);
}
