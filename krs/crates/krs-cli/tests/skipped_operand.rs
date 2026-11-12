//! `krs check` warns where a value or a condition depends on an operand that `&&`, `||`,
//! `bool::and`, `bool::or`, `bool::implies` or `kequal::ite` skips and that may have no value
//! (`krs::analysis::skipped-operand`): KRS keeps the skipped operand's definedness, a backend
//! that returns the selected operand alone does not, so the emitted K means different things on
//! different backends. The warning reads k-rust's analysis of the definition the `native-rust`
//! route loads (`k_rust_backend::short_circuit`), the analysis kink reads, so a definition with
//! no warning is one kink's analysis flags no rule of.

use std::fs;
use std::path::{Path, PathBuf};

use k_rust::backend::{Backend, BackendOptions};
use k_rust::k_rust_backend::short_circuit::ShortCircuitAnalysis;
use k_rust::kore::ast::{Definition, Sentence};
use k_rust::names::KoreAttribute;
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const NAMESPACE: &str = "ORG-KRS-SKIPPED";

const PREAMBLE: &str = r#"use k::builtin::{Bool, Float, Int, KSequence, Map, float, int, kequal};
use k::{KItem, KResult, Term};

k::sorts! {
    Stmt: KItem;
    Value: KResult;
    impl Value for Int;
    impl Value for Bool;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("res {n} {d}")] Res { n: Int, d: Int },
    #[k::syntax("cell {n} {d}")] CellIte { n: Int, d: Int },
    #[k::syntax("orhalf {a}")] OrHalf { a: Int },
    #[k::syntax("nothalf {a}")] NotHalf { a: Int },
    #[k::syntax("usecond {n} {d}")] UseCond { n: Int, d: Int },
    #[k::syntax("useres {n} {d}")] UseRes { n: Int, d: Int },
    #[k::syntax("dead {v}")] Dead { v: Value },
    #[k::syntax("hoisted {n} {a}")] Hoisted { n: Int, a: Int },
    #[k::syntax("lifted {n} {d}")] Lifted { n: Int, d: Int },
    #[k::syntax("liftedand {n} {d}")] LiftedAnd { n: Int, d: Int },
    #[k::syntax("orsmall {a}")] OrSmall { a: Int },
    #[k::syntax("done {b}")] Done { b: Bool },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Value,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm], acc: 0 }
    }
}

#[k::function(partial, internal)]
#[k::requires(a % 2 == 0)]
pub fn Half(a: Term<Int>) -> Term<Int> {
    a / 2
}

#[k::function(total, internal)]
pub fn Small(a: Term<Int>) -> Term<Bool> {
    a < 10
}

#[k::function(total, internal)]
pub fn Total(x: Term<Int>) -> Term<Int> {
    x + 1
}
"#;

/// Every shape that warns, and the shapes that do not, each an item of its own.
const WARNED: &str = r"
#[k::function(partial, internal)]
pub fn Ok(n: Term<Int>, d: Term<Int>) -> Term<Bool> {
    d != 0 && n / d > 1
}

#[k::function(partial, internal)]
pub fn Either(n: Term<Int>, d: Term<Int>) -> Term<Bool> {
    d == 0 || n / d > 1
}

#[k::function(partial, internal)]
pub fn Ratio(n: Term<Int>, d: Term<Int>) -> Term<Int> {
    kequal::ite(d != 0, n / d, 0)
}

#[k::function(partial, internal)]
pub fn Present(m: Term<Map>) -> Term<Bool> {
    m[1] > 0
        && m[2] > 0
        && m[3] > 0
}

#[k::function(total, internal)]
pub fn OwedLiteral(n: Term<Int>, d: Term<Int>) -> Term<Bool> {
    d != 0 && n / 16 > 1
}

#[k::function(total, internal)]
pub fn OwedBits(c: Term<Bool>, x: Term<Int>) -> Term<Bool> {
    c && int::bit_range(x, 4, 4) == 0
}

#[k::function(total, internal)]
pub fn OwedTotal(c: Term<Bool>, x: Term<Int>) -> Term<Bool> {
    c && Total(x) > 0
}

#[k::function(partial, internal)]
pub fn Deciding(a: Term<Int>, c: Term<Bool>) -> Term<Bool> {
    Half(a) > 0 || c
}

#[k::function(partial, internal)]
pub fn LetBody(n: Term<Int>, d: Term<Int>) -> Term<Bool> {
    let q = d;
    d == 0 || n / q > 1
}

#[k::function(partial, internal)]
pub fn Infinite(x: Term<Float>) -> Term<Bool> {
    float::is_infinite(x)
}

#[k::function(partial, internal)]
pub fn TwoSites(a: Term<Int>, c: Term<Bool>, e: Term<Bool>) -> Term<Int> {
    Total(kequal::ite(c, Half(a), 0)) + Total(kequal::ite(e, Half(a), 1))
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    res: { k: [Res(n, d), ..] } => { k: [Done(d != 0 && n / d > 1), ..] };
    cell_ite: { k: [CellIte(n, d), ..], acc: _ } => { k: [..], acc: kequal::ite(d != 0, n / d, 0) };
    #[k::requires(a == 0 || Half(a) > 0)]
    or_half: { k: [OrHalf(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(!(Small(a) && Half(a) > 0))]
    not_half: { k: [NotHalf(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(Ok(n, d))]
    use_cond: { k: [UseCond(n, d), ..], acc: _ } => { k: [..], acc: 1 };
    use_res: { k: [UseRes(n, d), ..], acc: _ } => { k: [..], acc: Ok(n, d) };
    #[k::requires(!k::is!(Int, v) || k::project!(Int, v) > 0)]
    dead: { k: [Dead(v), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(a == 0 || n / a > 1)]
    hoisted: { k: [Hoisted(n, a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires({ let q = d; d == 0 || n / q > 1 })]
    lifted: { k: [Lifted(n, d), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires({ let q = d; d != 0 && n / q > 1 })]
    lifted_and: { k: [LiftedAnd(n, d), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires((Small(a) && Half(a) > 0) || a > 100)]
    or_small: { k: [OrSmall(a), ..], acc: _ } => { k: [..], acc: 1 };
}
";

/// The warned shapes rewritten as branching bodies and one rule per case.
const BRANCHING: &str = r"
#[k::function(total, internal)]
pub fn Ok(n: Term<Int>, d: Term<Int>) -> Term<Bool> {
    if d != 0 { n / d > 1 } else { false }
}

#[k::function(total, internal)]
pub fn Either(n: Term<Int>, d: Term<Int>) -> Term<Bool> {
    if d == 0 { true } else { n / d > 1 }
}

#[k::function(total, internal)]
pub fn Ratio(n: Term<Int>, d: Term<Int>) -> Term<Int> {
    if d != 0 { n / d } else { 0 }
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    res: { k: [Res(n, d), ..] } => { k: [Done(Ok(n, d)), ..] };
    cell_ite: { k: [CellIte(n, d), ..], acc: _ } => { k: [..], acc: Ratio(n, d) };
    #[k::requires(a == 0)]
    or_half_zero: { k: [OrHalf(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(a != 0 && Half(a) > 0)]
    or_half_half: { k: [OrHalf(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(!Small(a))]
    not_half_large: { k: [NotHalf(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(Small(a) && Half(a) <= 0)]
    not_half_small: { k: [NotHalf(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(Ok(n, d))]
    use_cond: { k: [UseCond(n, d), ..], acc: _ } => { k: [..], acc: 1 };
    use_res: { k: [UseRes(n, d), ..], acc: _ } => { k: [..], acc: Either(n, d) };
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A one-package workspace named `skipped` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"skipped\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"{NAMESPACE}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    manifest
}

/// Runs `krs <command>` on the package's `main` definition.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", "skipped", "--definition", "main"])
        .args(extra)
        .env("NO_COLOR", "1")
        .env("KRS_NO_REUSE", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// The `skipped-operand` diagnostics of `stderr`, each with its source line and its notes and
/// help, one string per diagnostic.
fn skipped(stderr: &str) -> Vec<String> {
    let mut diagnostics = Vec::new();
    let mut current: Option<String> = None;
    for line in stderr.lines() {
        if line.starts_with("warning[") || line.starts_with("error[") {
            if let Some(done) = current.take() {
                diagnostics.push(done);
            }
            if line.contains("skipped-operand") {
                current = Some(line.to_owned());
            }
        } else if let Some(text) = &mut current {
            let trimmed = line.trim_start();
            if let Some(location) = trimmed.strip_prefix("--> ") {
                // The package lives in a temporary directory: keep its relative path.
                let relative = location
                    .rfind("/src/")
                    .map_or(location, |at| &location[at + 1..]);
                text.push_str("\n--> ");
                text.push_str(relative);
            } else if trimmed.starts_with("= ") {
                text.push('\n');
                text.push_str(trimmed);
            } else if trimmed.contains("may have no value") {
                text.push('\n');
                text.push_str(
                    trimmed
                        .trim_start_matches(|c: char| c.is_ascii_digit() || c == '|' || c == ' '),
                );
            }
        }
    }
    diagnostics.extend(current);
    diagnostics
}

/// The one diagnostic of `warnings` located at the line of `source` that reads `line`.
fn at_line<'w>(warnings: &'w [String], source: &str, line: &str) -> &'w str {
    let mut found = warnings
        .iter()
        .filter(|warning| line_of(warning, source) == line);
    let warning = found
        .next()
        .unwrap_or_else(|| panic!("no warning at `{line}`: {warnings:#?}"));
    assert!(found.next().is_none(), "two warnings at `{line}`");
    warning
}

/// The line of `source` the `-->` location of `diagnostic` names, trimmed.
fn line_of(diagnostic: &str, source: &str) -> String {
    let location = diagnostic
        .lines()
        .find_map(|line| line.strip_prefix("--> "))
        .unwrap_or_else(|| panic!("no location: {diagnostic}"));
    let line: usize = location.split(':').nth(1).unwrap().parse().unwrap();
    source.lines().nth(line - 1).unwrap().trim().to_owned()
}

/// The sentences of `kore` that depend on the short-circuit reading (the rules and equations
/// `rule_readings` and `equation_readings` name), by their `label` attribute; a sentence k-rust
/// generated without one (a lifted `let`) counts as `<unlabelled>`, since its `UNIQUE_ID` hashes
/// route-specific attributes.
fn flagged(kore: &str) -> Vec<String> {
    let definition = k_rust::kore::parser::parse_definition(kore).unwrap();
    let module = k_rust::kast::identifier::encode(NAMESPACE);
    let mut backend =
        Backend::from_definition(definition.clone(), &module, BackendOptions::default())
            .unwrap_or_else(|error| panic!("{error}"));
    let selected = backend.select_definition(None).unwrap();
    let mut analysis = ShortCircuitAnalysis::of(&selected);
    analysis.close_over(&definition);
    let label = |definition: &Definition,
                 at: k_rust::k_rust_backend::short_circuit::SentenceRef| {
        let (_, sentence) = at.resolve(definition).unwrap();
        let Sentence::Axiom { attributes, .. } = sentence else {
            panic!("not an axiom")
        };
        attributes
            .string(KoreAttribute::Label)
            .ok()
            .flatten()
            .unwrap_or("<unlabelled>")
            .to_owned()
    };
    let mut labels = analysis
        .rule_readings(&definition)
        .into_iter()
        .map(|reading| label(&definition, reading.rule))
        .chain(
            analysis
                .equation_readings(&definition)
                .into_iter()
                .map(|reading| label(&definition, reading.equation)),
        )
        .collect::<Vec<_>>();
    labels.sort();
    labels
}

/// The text route's KORE definition: the emitted `definition.k` compiled by k-rust's text
/// frontend, as `krust kcompile` compiles it.
fn text_route(definition: &str) -> String {
    use k_rust::builtin;
    use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
    use k_rust::outer::{LoadOptions, ResolvedSource, load_for_compilation};

    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    let syntax = format!("{NAMESPACE}-SYNTAX");
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("definition.k", definition.to_owned()),
        NAMESPACE,
        Some(syntax.as_str()),
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![builtin::embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust
                    .excluded_module_attribute()
                    .to_owned(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("the text route loads the definition: {error}\n{definition}"));
    compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("the text route compiles the definition: {error:?}"))
        .definition_kore
}

/// The native route's KORE definition: `krs build --backend haskell`'s `definition.kore`, the
/// definition `krs check` and the run commands load.
fn native_route(target: &Path, manifest: &Path, directory: &str) -> String {
    let output = manifest.with_file_name(directory);
    let (success, _, stderr) = krs(
        target,
        manifest,
        "build",
        &["--backend", "haskell", "--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.kore")).unwrap()
}

/// `krs emit-k`'s `definition.k`.
fn emitted(target: &Path, manifest: &Path, directory: &str) -> String {
    let output = manifest.with_file_name(directory);
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.k")).unwrap()
}

/// The full texts of the warnings of [`WARNED`] whose wording differs by where the operator is.
fn pin_texts(warnings: &[String], source: &str) {
    // A `&&` below `||` in a condition: a Rust reading gives the operator's value, not the
    // condition's.
    expect_test::expect![[r#"
        warning[krs::analysis::skipped-operand]: `&&` does not evaluate its right operand where its left operand is `false`, but keeps that operand's definedness, and the operand may have no value
        --> src/lib.rs:138:29
        ^^ ---- may have no value
        = note: so the sentence's condition does not hold where the operand has no value, while a Rust reading of `&&` gives `false` where its left operand is `false`, and the condition is then what that value makes it; and kink does not judge a run that reads it
        = help: write each case as a sentence of its own (a branch of the function's body, or a rule), each under its own condition
        = help: or state that the strict meaning is intended: `#[k::rule(.., skipped_operand = "..")]`"#]].assert_eq(at_line(
        warnings,
        source,
        "#[k::requires((Small(a) && Half(a) > 0) || a > 100)]",
    ));
    // K13: a condition's `let` block is a local function the rule applies in its condition, and
    // a function body's is one the body's value is.
    expect_test::expect![[r#"
        warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value
        --> src/lib.rs:134:39
        ^^   - may have no value
        = note: so the sentence's condition does not hold where the operand has no value, while a Rust reading of `||` gives `true` where its left operand is `true`, and the condition is then what that value makes it; and kink does not judge a run that reads it
        = note: the operator is in a local function k-rust generates from this sentence's `let` block or `k::matches!` test, which the sentence applies where the block stands
        = help: write each case as a sentence of its own (a branch of the function's body, or a rule), each under its own condition
        = help: or state that the strict meaning is intended: `#[k::rule(.., skipped_operand = "..")]`"#]].assert_eq(at_line(
        warnings,
        source,
        "#[k::requires({ let q = d; d == 0 || n / q > 1 })]",
    ));
    expect_test::expect![[r#"
        warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value
        --> src/lib.rs:104:12
        ^^   - may have no value
        = note: `||` is `bool::or_else`, one strict function: where the operand has no value, the application has none on every KRS route, while a backend that returns the selected operand alone gives `true`, so the K KRS emits means different things on different backends, and kink does not judge a run that reads it
        = note: the operator is in a local function k-rust generates from this sentence's `let` block or `k::matches!` test, which the sentence applies where the block stands
        = help: write a branching body, whose branches are separate equations, each with its own definedness: `if left { true } else { right }`, with `left` and `right` its operands; where this is not the whole body, move it into a helper function whose body branches
        = help: or state that the strict meaning is intended: `#[k::function(.., skipped_operand = "..")]`"#]].assert_eq(at_line(warnings, source, "d == 0 || n / q > 1"));
    // Two operators whose operands apply one term warn each at its own.
    let two_sites = warnings
        .iter()
        .filter(|warning| {
            line_of(warning, source)
                == "Total(kequal::ite(c, Half(a), 0)) + Total(kequal::ite(e, Half(a), 1))"
        })
        .filter_map(|warning| warning.lines().find_map(|line| line.strip_prefix("--> ")))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "src/lib.rs:114:11",
            "src/lib.rs:114:47",
        ]
    "#]]
    .assert_debug_eq(&two_sites);
    // A prelude function whose value depends on the reading warns where the author applies it,
    // with only the key to offer.
    expect_test::expect![[r#"
        warning[krs::analysis::skipped-operand]: `bool::or` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value: the operand `F:Float <Float --Float maxValueFloat (... precision: precisionFloat ( F:Float ) , exponentBits: exponentBitsFloat ( F:Float ) )` holds `F:Float <Float --Float maxValueFloat (... precision: precisionFloat ( F:Float ) , exponentBits: exponentBitsFloat ( F:Float ) )`
        --> src/lib.rs:109:5
        = note: `bool::or` is one strict function: where the operand has no value, the application has none on every KRS route, while a backend that returns the selected operand alone gives `true`, so the K KRS emits means different things on different backends, and kink does not judge a run that reads it
        = note: the operator is in the prelude's `isInfinite(_)_FLOAT_Bool_Float` (module `FLOAT`), which this sentence applies, and which a definition does not rewrite
        = help: state that the strict meaning is intended: `#[k::function(.., skipped_operand = "..")]`"#]].assert_eq(at_line(warnings, source, "float::is_infinite(x)"));
}

/// K2, K3, K7, K8, K9, K11, K12, K13: every value-position `&&`, `||` and `kequal::ite` whose
/// skipped operand may have no value warns once, at the operator, with the skipped operand
/// labelled, and two operators of one sentence whose operands apply one term warn each at its
/// own; so does a user partial function below `!` or `||` in a condition, and a condition whose
/// builtin construct KRS tests before it (the test does not reach the analysis); a `let` block
/// k-rust lifts into a local function warns at the sentence, worded by the part of the sentence
/// that applies it, with the note that names the local function, and not where it is a
/// top-level conjunct of a condition; a prelude function whose equation depends on the reading
/// warns at its application, offering only the key; a rule applying a warned function is not
/// warned again; an operand that owes nothing under the ceil theory, a total function's
/// application and a deciding operand do not warn; a construct `dead-guard` reports is reported
/// by it alone. K6: both routes flag the same sentences.
#[test]
fn value_positions_and_conditions_warn_at_the_operator() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), WARNED);
    let source = fs::read_to_string(temporary.path().join("src/lib.rs")).unwrap();
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");
    let warnings = skipped(&stderr);
    let lines = warnings
        .iter()
        .map(|warning| {
            format!(
                "{} | {}",
                line_of(warning, &source),
                warning.lines().next().unwrap()
            )
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r##"
        [
            "#[k::requires(a == 0 || n / a > 1)] | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "float::is_infinite(x) | warning[krs::analysis::skipped-operand]: `bool::or` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value: the operand `F:Float <Float --Float maxValueFloat (... precision: precisionFloat ( F:Float ) , exponentBits: exponentBitsFloat ( F:Float ) )` holds `F:Float <Float --Float maxValueFloat (... precision: precisionFloat ( F:Float ) , exponentBits: exponentBitsFloat ( F:Float ) )`",
            "cell_ite: { k: [CellIte(n, d), ..], acc: _ } => { k: [..], acc: kequal::ite(d != 0, n / d, 0) }; | warning[krs::analysis::skipped-operand]: `kequal::ite` does not evaluate its `then` operand where its condition is `false`, but keeps that operand's definedness, and the operand may have no value",
            "#[k::requires(!(Small(a) && Half(a) > 0))] | warning[krs::analysis::skipped-operand]: `&&` does not evaluate its right operand where its left operand is `false`, but keeps that operand's definedness, and the operand may have no value",
            "#[k::requires({ let q = d; d == 0 || n / q > 1 })] | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "#[k::requires(a == 0 || Half(a) > 0)] | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "res: { k: [Res(n, d), ..] } => { k: [Done(d != 0 && n / d > 1), ..] }; | warning[krs::analysis::skipped-operand]: `&&` does not evaluate its right operand where its left operand is `false`, but keeps that operand's definedness, and the operand may have no value",
            "#[k::requires((Small(a) && Half(a) > 0) || a > 100)] | warning[krs::analysis::skipped-operand]: `&&` does not evaluate its right operand where its left operand is `false`, but keeps that operand's definedness, and the operand may have no value",
            "kequal::ite(d != 0, n / d, 0) | warning[krs::analysis::skipped-operand]: `kequal::ite` does not evaluate its `then` operand where its condition is `false`, but keeps that operand's definedness, and the operand may have no value",
            "&& m[2] > 0 | warning[krs::analysis::skipped-operand]: `&&` does not evaluate its right operand where its left operand is `false`, but keeps that operand's definedness, and the operand may have no value",
            "&& m[3] > 0 | warning[krs::analysis::skipped-operand]: `&&` does not evaluate its right operand where its left operand is `false`, but keeps that operand's definedness, and the operand may have no value",
            "d != 0 && n / d > 1 | warning[krs::analysis::skipped-operand]: `&&` does not evaluate its right operand where its left operand is `false`, but keeps that operand's definedness, and the operand may have no value",
            "d == 0 || n / d > 1 | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "d == 0 || n / q > 1 | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "Total(kequal::ite(c, Half(a), 0)) + Total(kequal::ite(e, Half(a), 1)) | warning[krs::analysis::skipped-operand]: `kequal::ite` does not evaluate its `then` operand where its condition is `false`, but keeps that operand's definedness, and the operand may have no value",
            "Total(kequal::ite(c, Half(a), 0)) + Total(kequal::ite(e, Half(a), 1)) | warning[krs::analysis::skipped-operand]: `kequal::ite` does not evaluate its `then` operand where its condition is `false`, but keeps that operand's definedness, and the operand may have no value",
        ]
    "##]].assert_debug_eq(&lines);
    expect_test::expect![[r#"
        warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value
        --> src/lib.rs:132:26
        ^^   - may have no value
        = note: so the sentence's condition does not hold where the operand has no value, while a Rust reading of `||` gives `true` where its left operand is `true`, and the condition is then what that value makes it; and kink does not judge a run that reads it
        = help: write each case as a sentence of its own (a branch of the function's body, or a rule), each under its own condition
        = help: or state that the strict meaning is intended: `#[k::rule(.., skipped_operand = "..")]`"#]].assert_eq(&warnings[0]);
    pin_texts(&warnings, &source);
    assert!(
        stderr.contains("warning[krs::analysis::dead-guard]"),
        "{stderr}"
    );

    let native = flagged(&native_route(target.path(), &manifest, "native"));
    let text = flagged(&text_route(&emitted(target.path(), &manifest, "emitted")));
    assert_eq!(native, text);
    assert!(!native.is_empty());
}

/// K4, K5: the same specification rewritten as branching bodies and one rule per case has no
/// `skipped-operand` warning, and kink's short-circuit analysis flags no sentence of its emitted
/// K on the text route kink compiles.
#[test]
fn branching_bodies_are_silent_and_kink_flags_nothing() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), BRANCHING);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");
    assert_eq!(skipped(&stderr), Vec::<String>::new(), "{stderr}");
    let text = flagged(&text_route(&emitted(target.path(), &manifest, "emitted")));
    assert_eq!(text, Vec::<String>::new());
}

/// K14: `krs check --backend llvm` loads no backend definition, so it runs no analysis.
#[test]
fn the_llvm_route_runs_no_analysis() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), WARNED);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &["--backend", "llvm"]);
    assert!(success, "{stderr}");
    assert!(!stderr.contains("skipped-operand"), "{stderr}");
}

/// The warned functions with `skipped_operand` keys, and a function whose key silences nothing;
/// beside the keyed sentences, sentences of the same items that warn unkeyed: a table's other
/// row, another clause of the `k::rules!` block, and a caller of a keyed function with an origin
/// of its own.
const KEYED: &str = r#"
#[k::function(partial, internal, skipped_operand = "the strict value is the meaning")]
pub fn Ok(n: Term<Int>, d: Term<Int>) -> Term<Bool> {
    d != 0 && n / d > 1
}

#[k::function(partial, internal, skipped_operand = "a table row's value is strict too")]
pub fn Either(n: Term<Int>, d: Term<Int>) -> Term<Bool>;

k::equations! {
    for Either;
    either_zero: (n, 0) => true || n / 0 > 1;
    #[k::equation(owise)]
    either_other: (n, d) => d == 0 || n / d > 1;
}

#[k::function(partial, internal, skipped_operand = "a local function's value is the body's")]
pub fn LetBody(n: Term<Int>, d: Term<Int>) -> Term<Bool> {
    let q = d;
    d == 0 || n / q > 1
}

#[k::function(total, internal, skipped_operand = "nothing is skipped here")]
pub fn Plain(n: Term<Int>) -> Term<Bool> {
    n > 1
}

#[k::function(partial, internal)]
pub fn Third(n: Term<Int>, d: Term<Int>) -> Term<Bool>;

#[k::equation(skipped_operand = "an equation fn's value is strict too")]
fn third(k::term![Third(n, d)]: Term<Bool>) -> Term<Bool> {
    d != 0 && n / d > 1
}

#[k::function(partial, internal)]
pub fn Fourth(n: Term<Int>, d: Term<Int>) -> Term<Bool>;

k::equations! {
    for Fourth;
    #[k::equation(skipped_operand = "a row's value is strict too")]
    fourth_zero: (n, 0) => true || n / 0 > 1;
    #[k::equation(owise, skipped_operand = "so is the other row's")]
    fourth_other: (n, d) => d == 0 || n / d > 1;
}

#[k::function(partial, internal)]
pub fn Fifth(n: Term<Int>, d: Term<Int>) -> Term<Bool>;

k::equations! {
    for Fifth;
    #[k::equation(skipped_operand = "only this row's value is strict")]
    fifth_zero: (n, 0) => true || n / 0 > 1;
    #[k::equation(owise)]
    fifth_other: (n, d) => d == 0 || n / d > 1;
}

#[k::function(partial, internal)]
pub fn Caller(n: Term<Int>, d: Term<Int>) -> Term<Bool> {
    Ok(n, d) || n / d > 1
}

#[k::rule(skipped_operand = "a term rule's result is strict too")]
fn hoisted_fn(k::term![StmtSyntax::Hoisted { n, a }]: Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::Done(a != 0 && n / a > 1)
}

#[k::rule(skipped_operand = "a cells rule's cell is strict too")]
pub fn cell_ite(
    n: Int,
    d: Int,
    k::cells! { k: k::configuration::KCell(StmtSyntax::CellIte(n, d), tail @ ..), acc: k::configuration::Cell(_), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), acc: k::configuration::Cell(kequal::ite(d != 0, n / d, 0)), ..state }
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    use_res: { k: [UseRes(n, d), ..], acc: _ } => { k: [..], acc: Ok(n, d) };
    res: { k: [Res(n, d), ..] } => { k: [Done(LetBody(n, d)), ..] };
    #[k::requires(Either(n, d) && Plain(n) && Third(n, d) && Fourth(n, d))]
    use_cond: { k: [UseCond(n, d), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::rule(skipped_operand = "a clause's condition is strict too")]
    #[k::requires(d == 0 || n / d > 1)]
    lifted: { k: [Lifted(n, d), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::rule(skipped_operand = "nothing is skipped in this clause")]
    or_small: { k: [OrSmall(a), ..] } => { k: [Done(a > 1), ..] };
    #[k::rule(skipped_operand = "dead-guard reports this condition alone")]
    #[k::requires(!k::is!(Int, v) || k::project!(Int, v) > 0)]
    dead: { k: [Dead(v), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(a == 0 || Half(a) > 0)]
    or_half: { k: [OrHalf(a), ..], acc: _ } => { k: [..], acc: 1 };
}
"#;

/// `source` with every `skipped_operand` key removed, and a marker left with no other key
/// written bare where it marks a fn and dropped where it marks a row or a clause.
fn unkeyed(source: &str) -> String {
    let lines = source.lines().collect::<Vec<_>>();
    let mut out = Vec::new();
    for (at, line) in lines.iter().enumerate() {
        let Some(start) = line.find("skipped_operand = \"") else {
            out.push((*line).to_owned());
            continue;
        };
        let reason = start + "skipped_operand = \"".len();
        let end = reason + line[reason..].find('"').unwrap() + 1;
        let stripped = format!("{}{}", &line[..start], &line[end..]).replace(", )", ")");
        if let Some(marker) = stripped.trim().strip_suffix("()]") {
            let next = lines[at + 1].trim_start();
            if next.starts_with("fn ") || next.starts_with("pub fn ") {
                out.push(format!("{marker}]"));
            }
        } else {
            out.push(stripped);
        }
    }
    out.join("\n")
}

/// The `skipped-operand` and `stale-skipped-operand` warnings of `krs check` on a package of
/// `source`, each as its line and headline, with `source` as the package holds it.
fn checked(target: &Path, root: &Path, source: &str) -> (Vec<String>, Vec<String>, String) {
    let manifest = package(root, source);
    let source = fs::read_to_string(root.join("src/lib.rs")).unwrap();
    let (success, _, stderr) = krs(target, &manifest, "check", &[]);
    assert!(success, "{stderr}");
    let warnings = skipped(&stderr);
    let lines = warnings
        .iter()
        .map(|warning| {
            format!(
                "{} | {}",
                line_of(warning, &source),
                warning.lines().next().unwrap()
            )
        })
        .collect();
    (warnings, lines, source)
}

/// K10: `skipped_operand = "reason"` on `#[k::function(..)]` silences the warnings anchored at
/// the function's equations (its body, its table's rows, a local function k-rust generates from
/// its body), on `#[k::equation(..)]` (an equation fn, a table row) and on `#[k::rule(..)]` (a
/// term rule fn, a `cells!` rule fn, a clause of `k::rules!`) those anchored at the sentence it
/// marks, and no other: the same package without its keys warns at every keyed sentence, and
/// with them still at a table's unkeyed row, at an unkeyed clause of a block with keyed ones and
/// at a caller of a keyed function. A key that silences nothing is `stale-skipped-operand` at
/// the key, a key whose only finding `dead-guard` reports included. An unkeyed table row's help
/// offers its own key and its function's. (On `#[k::claim(..)]` the placement table refuses the
/// key: the macro fixture `claim_skipped_operand`.)
#[test]
fn a_key_silences_the_sentences_of_its_item_and_a_stale_key_warns() {
    let target = shared_fixture_target();
    let without = temp_dir();
    let (_, lines, _) = checked(target.path(), without.path(), &unkeyed(KEYED));
    expect_test::expect![[r##"
        [
            "either_zero: (n, 0) => true || n / 0 > 1; | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "fifth_zero: (n, 0) => true || n / 0 > 1; | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "fourth_zero: (n, 0) => true || n / 0 > 1; | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "#[k::requires(d == 0 || n / d > 1)] | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "#[k::requires(a == 0 || Half(a) > 0)] | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "d != 0 && n / d > 1 | warning[krs::analysis::skipped-operand]: `&&` does not evaluate its right operand where its left operand is `false`, but keeps that operand's definedness, and the operand may have no value",
            "StmtSyntax::Done(a != 0 && n / a > 1) | warning[krs::analysis::skipped-operand]: `&&` does not evaluate its right operand where its left operand is `false`, but keeps that operand's definedness, and the operand may have no value",
            "fourth_other: (n, d) => d == 0 || n / d > 1; | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "k::cells! { k: k::configuration::KCell(..tail), acc: k::configuration::Cell(kequal::ite(d != 0, n / d, 0)), ..state } | warning[krs::analysis::skipped-operand]: `kequal::ite` does not evaluate its `then` operand where its condition is `false`, but keeps that operand's definedness, and the operand may have no value",
            "d == 0 || n / q > 1 | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "d != 0 && n / d > 1 | warning[krs::analysis::skipped-operand]: `&&` does not evaluate its right operand where its left operand is `false`, but keeps that operand's definedness, and the operand may have no value",
            "fifth_other: (n, d) => d == 0 || n / d > 1; | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "either_other: (n, d) => d == 0 || n / d > 1; | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "Ok(n, d) || n / d > 1 | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
        ]
    "##]].assert_debug_eq(&lines);
    let temporary = temp_dir();
    let (warnings, lines, source) = checked(target.path(), temporary.path(), KEYED);
    expect_test::expect![[r##"
        [
            "#[k::requires(a == 0 || Half(a) > 0)] | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "fifth_other: (n, d) => d == 0 || n / d > 1; | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "Ok(n, d) || n / d > 1 | warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value",
            "#[k::function(total, internal, skipped_operand = \"nothing is skipped here\")] | warning[krs::analysis::stale-skipped-operand]: `skipped_operand` states that a value may depend on an operand `&&`, `||` or `kequal::ite` skips, but no sentence of this item has a `krs::analysis::skipped-operand` warning to silence",
            "#[k::rule(skipped_operand = \"dead-guard reports this condition alone\")] | warning[krs::analysis::stale-skipped-operand]: `skipped_operand` states that a value may depend on an operand `&&`, `||` or `kequal::ite` skips, but no sentence of this item has a `krs::analysis::skipped-operand` warning to silence",
            "#[k::rule(skipped_operand = \"nothing is skipped in this clause\")] | warning[krs::analysis::stale-skipped-operand]: `skipped_operand` states that a value may depend on an operand `&&`, `||` or `kequal::ite` skips, but no sentence of this item has a `krs::analysis::skipped-operand` warning to silence",
        ]
    "##]].assert_debug_eq(&lines);
    expect_test::expect![[r#"
        warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value
        --> src/lib.rs:112:35
        ^^   - may have no value
        = note: `||` is `bool::or_else`, one strict function: where the operand has no value, the application has none on every KRS route, while a backend that returns the selected operand alone gives `true`, so the K KRS emits means different things on different backends, and kink does not judge a run that reads it
        = help: write a branching body, whose branches are separate equations, each with its own definedness: `if left { true } else { right }`, with `left` and `right` its operands; where this is not the whole body, move it into a helper function whose body branches
        = help: or state that the strict meaning is intended: `#[k::equation(.., skipped_operand = "..")]` on this equation, or `#[k::function(.., skipped_operand = "..")]` on its function, for every equation of the function"#]].assert_eq(at_line(&warnings, &source, "fifth_other: (n, d) => d == 0 || n / d > 1;"));

    // A keyed clause prints as the `cells!` rule its key marks, so the print states what its
    // source states and is silenced and warned exactly where its source is. (A warning names the
    // operator as the print spells it, `bool::or_else` for `||`, so the warnings are compared by
    // their kind.)
    let (expanded, printed, stderr) = krs(
        target.path(),
        &temporary.path().join("Cargo.toml"),
        "expand",
        &[],
    );
    assert!(expanded, "{stderr}");
    let attribute = printed.split_whitespace().collect::<Vec<_>>().join(" ");
    for keyed in [
        r#"#[k::rule(skipped_operand = "a clause's condition is strict too", label = "lifted")]"#,
        r#"#[k::rule(skipped_operand = "nothing is skipped in this clause", label = "or-small")]"#,
    ] {
        assert!(attribute.contains(keyed), "{keyed}\n{printed}");
    }
    let reprinted = temp_dir();
    let manifest = package(reprinted.path(), "");
    fs::write(reprinted.path().join("src/lib.rs"), &printed).unwrap();
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");
    let headlines = |warnings: &[String]| {
        let mut headlines = warnings
            .iter()
            .map(|warning| warning.split("]:").next().unwrap().to_owned())
            .collect::<Vec<_>>();
        headlines.sort();
        headlines
    };
    assert_eq!(headlines(&skipped(&stderr)), headlines(&warnings));
}

/// Every origin a sentence depends on, at its own place, however the author writes the
/// expression: two `let` blocks under `&&` warn at each block's `||` and at the `&&`, as the same
/// expression written in place does; and a prelude function the sentence applies twice warns at
/// each application.
const ORIGINS: &str = r"
#[k::function(partial, internal)]
pub fn TwoLets(n: Term<Int>, d: Term<Int>, e: Term<Int>) -> Term<Bool> {
    ({ let q = d; d == 0 || n / q > 1 }) && ({ let r = e; e == 0 || Half(r) > 1 })
}

#[k::function(partial, internal)]
pub fn TwoInPlace(n: Term<Int>, d: Term<Int>, e: Term<Int>) -> Term<Bool> {
    (d == 0 || n / d > 1) && (e == 0 || Half(e) > 1)
}

#[k::function(partial, internal)]
pub fn Mixed(n: Term<Int>, d: Term<Int>, e: Term<Int>) -> Term<Bool> {
    (e == 0 || n / e > 1) && { let q = d; d == 0 || n / q > 1 }
}

#[k::function(partial, internal)]
pub fn MixedInPlace(n: Term<Int>, d: Term<Int>, e: Term<Int>) -> Term<Bool> {
    (e == 0 || n / e > 1) && (d == 0 || n / d > 1)
}

#[k::function(partial, internal)]
pub fn LetOperand(n: Term<Int>, d: Term<Int>) -> Term<Bool> {
    Small(n) || { let q = d; n / q > 1 }
}

#[k::function(partial, internal)]
pub fn Infinities(x: Term<Float>, y: Term<Float>) -> Term<Bool> {
    float::is_infinite(x) == float::is_infinite(y)
}

#[k::function(partial, internal)]
pub fn SupLoc(n: Term<Int>, d: Term<Int>, c: Term<Bool>) -> Term<Int> {
    Total(kequal::ite(c, Half(n) / d, 0)) + Total(kequal::ite(c, n / d, 1))
}

#[k::function(partial, internal)]
pub fn SupLocA(n: Term<Int>, d: Term<Int>, c: Term<Bool>) -> Term<Int> {
    Total(kequal::ite(c, Half(n) / d, 0))
}

#[k::function(partial, internal)]
pub fn SupLocB(n: Term<Int>, d: Term<Int>, c: Term<Bool>) -> Term<Int> {
    Total(kequal::ite(c, n / d, 1))
}

#[k::function(partial, internal)]
pub fn SupLet(n: Term<Int>, d: Term<Int>, e: Term<Int>) -> Term<Bool> {
    ({ let q = d; d == 0 || Half(n) / q > 1 }) && ({ let r = e; e == 0 || n / r > 1 })
}

#[k::function(partial, internal)]
pub fn SupInPlace(n: Term<Int>, d: Term<Int>, e: Term<Int>) -> Term<Bool> {
    (d == 0 || Half(n) / d > 1) && (e == 0 || n / e > 1)
}
";

/// A reader fixes origins one at a time, so each is warned at its own place, and writing a `let`
/// changes none of them, nor does an operand whose term is a more specific application of the
/// same symbol than another operator's (`Half(n) / d` beside `n / d`); the label of a `let` block
/// that may have no value is on the application in the block's value that may have none, not on
/// its binding.
#[test]
fn every_origin_warns_at_its_own_place_with_or_without_a_let() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), ORIGINS);
    let source = fs::read_to_string(temporary.path().join("src/lib.rs")).unwrap();
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");
    let warnings = skipped(&stderr);
    let mut places = warnings
        .iter()
        .map(|warning| {
            let location = warning
                .lines()
                .find_map(|line| line.strip_prefix("--> "))
                .unwrap_or_default();
            format!(
                "{} @ {}",
                line_of(warning, &source),
                location.rsplit(':').next().unwrap_or_default()
            )
        })
        .collect::<Vec<_>>();
    places.sort();
    expect_test::expect![[r#"
        [
            "(d == 0 || Half(n) / d > 1) && (e == 0 || n / e > 1) @ 13",
            "(d == 0 || Half(n) / d > 1) && (e == 0 || n / e > 1) @ 33",
            "(d == 0 || Half(n) / d > 1) && (e == 0 || n / e > 1) @ 44",
            "(d == 0 || n / d > 1) && (e == 0 || Half(e) > 1) @ 13",
            "(d == 0 || n / d > 1) && (e == 0 || Half(e) > 1) @ 27",
            "(d == 0 || n / d > 1) && (e == 0 || Half(e) > 1) @ 38",
            "(e == 0 || n / e > 1) && (d == 0 || n / d > 1) @ 13",
            "(e == 0 || n / e > 1) && (d == 0 || n / d > 1) @ 27",
            "(e == 0 || n / e > 1) && (d == 0 || n / d > 1) @ 38",
            "(e == 0 || n / e > 1) && { let q = d; d == 0 || n / q > 1 } @ 13",
            "(e == 0 || n / e > 1) && { let q = d; d == 0 || n / q > 1 } @ 27",
            "(e == 0 || n / e > 1) && { let q = d; d == 0 || n / q > 1 } @ 50",
            "({ let q = d; d == 0 || Half(n) / q > 1 }) && ({ let r = e; e == 0 || n / r > 1 }) @ 26",
            "({ let q = d; d == 0 || Half(n) / q > 1 }) && ({ let r = e; e == 0 || n / r > 1 }) @ 48",
            "({ let q = d; d == 0 || Half(n) / q > 1 }) && ({ let r = e; e == 0 || n / r > 1 }) @ 72",
            "({ let q = d; d == 0 || n / q > 1 }) && ({ let r = e; e == 0 || Half(r) > 1 }) @ 26",
            "({ let q = d; d == 0 || n / q > 1 }) && ({ let r = e; e == 0 || Half(r) > 1 }) @ 42",
            "({ let q = d; d == 0 || n / q > 1 }) && ({ let r = e; e == 0 || Half(r) > 1 }) @ 66",
            "Small(n) || { let q = d; n / q > 1 } @ 14",
            "Total(kequal::ite(c, Half(n) / d, 0)) + Total(kequal::ite(c, n / d, 1)) @ 11",
            "Total(kequal::ite(c, Half(n) / d, 0)) + Total(kequal::ite(c, n / d, 1)) @ 51",
            "Total(kequal::ite(c, Half(n) / d, 0)) @ 11",
            "Total(kequal::ite(c, n / d, 1)) @ 11",
            "float::is_infinite(x) == float::is_infinite(y) @ 30",
            "float::is_infinite(x) == float::is_infinite(y) @ 5",
        ]
    "#]]
    .assert_debug_eq(&places);
    let count = |line: &str| {
        warnings
            .iter()
            .filter(|warning| line_of(warning, &source) == line)
            .count()
    };
    assert_eq!(
        count("({ let q = d; d == 0 || n / q > 1 }) && ({ let r = e; e == 0 || Half(r) > 1 })"),
        count("(d == 0 || n / d > 1) && (e == 0 || Half(e) > 1)"),
    );
    assert_eq!(
        count("(e == 0 || n / e > 1) && { let q = d; d == 0 || n / q > 1 }"),
        count("(e == 0 || n / e > 1) && (d == 0 || n / d > 1)"),
    );
    assert_eq!(
        count("Total(kequal::ite(c, Half(n) / d, 0)) + Total(kequal::ite(c, n / d, 1))"),
        count("Total(kequal::ite(c, Half(n) / d, 0))") + count("Total(kequal::ite(c, n / d, 1))"),
    );
    assert_eq!(
        count("({ let q = d; d == 0 || Half(n) / q > 1 }) && ({ let r = e; e == 0 || n / r > 1 })"),
        count("(d == 0 || Half(n) / d > 1) && (e == 0 || n / e > 1)"),
    );
    assert_eq!(
        count("(d == 0 || Half(n) / d > 1) && (e == 0 || n / e > 1)"),
        3
    );
    expect_test::expect![[r#"
        warning[krs::analysis::skipped-operand]: `||` does not evaluate its right operand where its left operand is `true`, but keeps that operand's definedness, and the operand may have no value
        --> src/lib.rs:81:14
        ^^                - may have no value
        = note: `||` is `bool::or_else`, one strict function: where the operand has no value, the application has none on every KRS route, while a backend that returns the selected operand alone gives `true`, so the K KRS emits means different things on different backends, and kink does not judge a run that reads it
        = help: write a branching body, whose branches are separate equations, each with its own definedness: `if left { true } else { right }`, with `left` and `right` its operands; where this is not the whole body, move it into a helper function whose body branches
        = help: or state that the strict meaning is intended: `#[k::function(.., skipped_operand = "..")]`"#]]
    .assert_eq(at_line(&warnings, &source, "Small(n) || { let q = d; n / q > 1 }"));
}
