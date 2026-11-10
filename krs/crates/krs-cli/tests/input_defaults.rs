//! An input's declared default (`#[k::config_var(name = "N", default = D)]`): the input's value
//! when a run binds none. It belongs to the input, not to a cell: every cell that reads the input
//! starts from its value, and the emitted K reads `$N` as before, since a K configuration
//! declares no defaults. `D` is an initializer term that reads no input, checked at the
//! parameter's declared type, element types included; the Definition IR carries it on the
//! input's descriptor, and the native compile result carries its KORE, lowered as the
//! initializer's terms are, for the routes that build the initial configuration.

use std::fs;
use std::path::{Path, PathBuf};

use krs_ir_levels::DefinitionIr;
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const LIBRARY: &str = r#"
use k::builtin::{Bool, Int, KSequence, List, Map, list};

k::sorts! {
    Stmt;
    Request;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
}

#[k::constructors(sort = Request, result = KResult)]
pub enum RequestSyntax {
    #[k::syntax("irq {n}")]
    Irq { n: Int },
}

#[k::constant]
pub const IRQ0: Request = RequestSyntax::Irq(0);

#[k::function(total, internal)]
pub fn Boot(n: k::Term<Int>) -> k::Term<List<Request>> {
    [RequestSyntax::Irq(n)]
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub requests: List<Request>,
    #[k::cell]
    pub booted: List<Request>,
    #[k::cell]
    pub one: Request,
    #[k::cell]
    pub table: Map<Int, Request>,
    #[k::cell]
    pub flag: Bool,
    #[k::cell(multiplicity = "?")]
    pub pending: Option<Request>,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "REQUESTS")] requests: List<Request>,
        #[k::config_var(name = "BOOTED")] booted: List<Request>,
        #[k::config_var(name = "ONE")] one: Request,
        #[k::config_var(name = "TABLE")] table: Map<Int, Request>,
        #[k::config_var(name = "FLAG")] flag: Bool,
        #[k::config_var(name = "LATER")] later: Request,
    ) -> Self {
        Self {
            k: k::k![pgm],
            requests,
            booted,
            one,
            table,
            flag,
            pending: Some(later),
        }
    }
}

/// Keeps `list` used whatever the defaults name.
#[k::function(total, internal)]
pub fn Empty() -> k::Term<List<Request>> {
    list::empty()
}
"#;

/// The parameter attributes `LIBRARY` writes, each to be given a default.
const ATTRIBUTES: [&str; 7] = [
    r#"#[k::config_var(name = "PGM", main)]"#,
    r#"#[k::config_var(name = "REQUESTS")]"#,
    r#"#[k::config_var(name = "BOOTED")]"#,
    r#"#[k::config_var(name = "ONE")]"#,
    r#"#[k::config_var(name = "TABLE")]"#,
    r#"#[k::config_var(name = "FLAG")]"#,
    r#"#[k::config_var(name = "LATER")]"#,
];

/// `LIBRARY` with each `(attribute, replacement)` written in place of the attribute.
fn library(replacements: &[(&str, &str)]) -> String {
    let mut source = LIBRARY.to_owned();
    for (attribute, replacement) in replacements {
        assert!(source.contains(attribute), "{attribute}");
        source = source.replacen(attribute, replacement, 1);
    }
    source
}

/// The accepted defaults: brackets read as the input's list, a function call, a constructor and
/// a constant, a map literal, a literal, and one on the main input.
const DEFAULTS: [(&str, &str); 7] = [
    (
        ATTRIBUTES[0],
        r#"#[k::config_var(name = "PGM", main, default = StmtSyntax::Skip())]"#,
    ),
    (
        ATTRIBUTES[1],
        r#"#[k::config_var(name = "REQUESTS", default = [])]"#,
    ),
    (
        ATTRIBUTES[2],
        r#"#[k::config_var(name = "BOOTED", default = Boot(3))]"#,
    ),
    (
        ATTRIBUTES[3],
        r#"#[k::config_var(name = "ONE", default = RequestSyntax::Irq { n: 7 })]"#,
    ),
    (
        ATTRIBUTES[4],
        r#"#[k::config_var(name = "TABLE", default = k::map![1 -> IRQ0, 2 -> RequestSyntax::Irq(2)])]"#,
    ),
    (
        ATTRIBUTES[5],
        r#"#[k::config_var(name = "FLAG", default = true)]"#,
    ),
    (
        ATTRIBUTES[6],
        r#"#[k::config_var(name = "LATER", default = IRQ0)]"#,
    ),
];

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is `library`, denying warnings, so that a name a
/// default alone reads counts as used.
fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-INPUT-DEFAULTS\"\n\n[package.metadata.krs.definitions.main]\n\n[lints.rust]\nwarnings = \"deny\"\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package's `main` definition, with `environment` set.
fn krs(
    target: &Path,
    manifest: &Path,
    command: &str,
    extra: &[&str],
    environment: &[(&str, &str)],
) -> (bool, String, String) {
    let package = manifest
        .parent()
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())
        .unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main"])
        .args(extra)
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"));
    for (key, value) in environment {
        process.env(key, value);
    }
    let output = process.output().unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// The emitted `definition.k` without its header line, which names the package, and the
/// package-relative source comments, which name it too.
fn emitted_k(target: &Path, manifest: &Path, output: &Path) -> String {
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--ir", "--output", output.to_str().unwrap()],
        &[],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.k"))
        .unwrap()
        .lines()
        .skip(1)
        .filter(|line| !line.trim_start().starts_with("// KRS "))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The first error's headline and the source text its caret marks.
fn first_error(stderr: &str) -> (String, String) {
    let lines = stderr.lines().collect::<Vec<_>>();
    let index = lines
        .iter()
        .position(|line| line.starts_with("error"))
        .unwrap_or_else(|| panic!("no error:\n{stderr}"));
    // `--> path`, ` |`, `N | source`, ` |   ^^^`.
    let marked = lines
        .get(index + 3)
        .zip(lines.get(index + 4))
        .and_then(|(source, carets)| {
            let source = source.split_once(" | ")?.1;
            let carets = carets.split_once(" | ")?.1;
            let start = carets.find('^')?;
            let width = carets[start..].chars().take_while(|c| *c == '^').count();
            source.get(start..start + width).map(str::to_owned)
        })
        .unwrap_or_default();
    (lines[index].to_owned(), marked)
}

/// Every accepted default checks, `krs expand` prints it back as written and the print checks
/// to the same K, and the emitted K is the K of the same definition without defaults: each cell
/// still reads its `$N`. The Definition IR carries each default on its input, and the native
/// compile result carries each one's KORE, keyed by the input's K name, at the input's sort.
#[test]
fn a_default_is_checked_carried_and_lowered_and_the_k_reads_its_input() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let plain = package(temporary.path(), "plain", &library(&[]));
    let defaulted = package(temporary.path(), "defaulted", &library(&DEFAULTS));
    let (success, _, stderr) = krs(
        target.path(),
        &defaulted,
        "check",
        &[],
        &[("KRS_CHECK_EXPANDS", "1")],
    );
    assert!(success, "{stderr}");

    let plain_k = emitted_k(target.path(), &plain, &temporary.path().join("plain-out"));
    let emitted = temporary.path().join("defaulted-out");
    let defaulted_k = emitted_k(target.path(), &defaulted, &emitted);
    assert_eq!(defaulted_k, plain_k);
    for cell in [
        "<k> $PGM:Stmt </k>",
        "<requests> $REQUESTS:List </requests>",
        "<flag> $FLAG:Bool </flag>",
    ] {
        assert!(defaulted_k.contains(cell), "{cell}\n{defaulted_k}");
    }

    let definition: DefinitionIr =
        serde_json::from_slice(&fs::read(emitted.join("definition-ir.json")).unwrap()).unwrap();
    let defaulted_inputs = definition
        .modules()
        .iter()
        .flat_map(krs_ir_levels::DefinitionModule::sentences)
        .filter_map(|sentence| match sentence {
            krs_ir_levels::DefinitionSentence::Configuration(configuration) => Some(configuration),
            _ => None,
        })
        .flat_map(krs_ir::FixedConfiguration::variables)
        .filter(|variable| variable.default().is_some())
        .map(|variable| variable.external_name().to_owned())
        .collect::<Vec<_>>();
    assert_eq!(
        defaulted_inputs,
        ["PGM", "REQUESTS", "BOOTED", "ONE", "TABLE", "FLAG", "LATER"]
    );

    let compiled =
        krs_k_rust::compile_definition(&definition, krs_k_rust::CompileOptions::default()).unwrap();
    let defaults = compiled
        .input_defaults()
        .iter()
        .map(|(name, pattern)| (name.as_str(), pattern.to_string()))
        .collect::<Vec<_>>();
    for (name, pattern) in &defaults {
        // Each pattern is KORE over the compiled definition's own symbols.
        for symbol in pattern
            .split(|c: char| !(c.is_alphanumeric() || c == '\''))
            .filter(|word| word.starts_with("Lbl"))
        {
            assert!(
                compiled
                    .definition_kore
                    .contains(&format!("symbol {symbol}{{")),
                "{name}: {symbol} in {pattern}"
            );
        }
    }
    let defaults = defaults
        .iter()
        .map(|(name, pattern)| (*name, pattern.as_str()))
        .collect::<Vec<_>>();
    // A call stays the function's application, which the backend's initialization evaluates; a
    // constant is its constructor term, a map literal the updates of the empty map it is, each
    // entry written over the one before.
    assert_eq!(
        defaults,
        [
            ("BOOTED", r#"Lblboot{}(\dv{SortInt{}}("3"))"#),
            ("FLAG", r#"\dv{SortBool{}}("true")"#),
            ("LATER", r#"LblrequestSyntaxIrq{}(\dv{SortInt{}}("0"))"#),
            ("ONE", r#"LblrequestSyntaxIrq{}(\dv{SortInt{}}("7"))"#),
            ("PGM", "LblstmtSyntaxSkip{}()"),
            ("REQUESTS", "Lbl'Stop'List{}()"),
            (
                "TABLE",
                concat!(
                    r#"LblMap'Coln'update{}(LblMap'Coln'update{}(Lbl'Stop'Map{}(), "#,
                    r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")), "#,
                    r#"inj{SortRequest{}, SortKItem{}}(LblrequestSyntaxIrq{}(\dv{SortInt{}}("0")))), "#,
                    r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("2")), "#,
                    r#"inj{SortRequest{}, SortKItem{}}(LblrequestSyntaxIrq{}(\dv{SortInt{}}("2"))))"#,
                ),
            ),
        ]
    );

    // The print keeps each default as written and checks to the same K.
    let (success, expanded, stderr) = krs(target.path(), &defaulted, "expand", &[], &[]);
    assert!(success, "{stderr}");
    assert!(expanded.contains("default = Boot(3)"), "{expanded}");
    let reprinted = package(temporary.path(), "reprinted", &expanded);
    let reprinted_k = emitted_k(
        target.path(),
        &reprinted,
        &temporary.path().join("reprinted-out"),
    );
    assert_eq!(reprinted_k, plain_k);
}

/// Each refused default, with the mistake it makes and where: a name, an input read, a sort and
/// an element type of its own, the attribute's own keys, the computation's notation, which no
/// term writes, and, after its sort is judged, a construct an input's default does not support
/// yet.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of refused defaults, each with its expected refusal."
)]
fn a_refused_default_is_refused_for_its_own_mistake() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let requests = ATTRIBUTES[1];
    let one = ATTRIBUTES[3];
    let flag = ATTRIBUTES[5];
    let unsupported = |input: &str, variable: &str, what: &str| {
        format!(
            "error[krs::analysis::unsupported-input-default]: the default of `{input}` (`${variable}`) holds {what}, which an input's default does not support yet: K's compiler evaluates it by a function it generates for the sentence that holds it, and a default is in no sentence, since krs binds it as a value built from the definition's constructors, functions and collection operations"
        )
    };
    let cases = [
        (
            "free",
            requests,
            r#"#[k::config_var(name = "REQUESTS", default = foo)]"#,
            "error[krs::expand::unbound-name]: `foo` is not bound in this default: an input's default reads no input, so a bare snake-case name in it is one an enclosing `let` inside it binds".to_owned(),
            "foo",
        ),
        (
            "reads-input",
            requests,
            r#"#[k::config_var(name = "REQUESTS", default = list::item(one))]"#,
            "error[krs::expand::default-reads-input]: `one` is an input of this initializer, which an input's default does not read: a default is its input's value when a run binds none, so it is built from constants alone".to_owned(),
            "one",
        ),
        (
            "reads-itself",
            requests,
            r#"#[k::config_var(name = "REQUESTS", default = requests)]"#,
            "error[krs::expand::default-reads-input]: `requests` is an input of this initializer, which an input's default does not read: a default is its input's value when a run binds none, so it is built from constants alone".to_owned(),
            "requests",
        ),
        (
            "wrong-sort",
            requests,
            r#"#[k::config_var(name = "REQUESTS", default = 5)]"#,
            "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-INPUT-DEFAULTS::Machine (configuration): literal `5` of sort Int is not admissible at sort List".to_owned(),
            "5",
        ),
        (
            "ill-typed-element",
            requests,
            r#"#[k::config_var(name = "REQUESTS", default = [5])]"#,
            "error[krs::analysis::collection-element-sort]: `5` of sort Int is stored as an element of `requests`, the configuration variable `$REQUESTS`, declared `List<Request>`, and Int is not a Request".to_owned(),
            "5",
        ),
        (
            "twice",
            requests,
            r#"#[k::config_var(name = "REQUESTS", default = [], default = [])]"#,
            "error[krs::syntax::duplicate-argument]: duplicate argument `default`".to_owned(),
            "default",
        ),
        (
            "no-name",
            requests,
            r"#[k::config_var(default = [])]",
            "error[krs::syntax::missing-argument]: missing required argument `name = ...`"
                .to_owned(),
            "default",
        ),
        (
            "computation",
            requests,
            r#"#[k::config_var(name = "REQUESTS", default = k::k![])]"#,
            "error[krs::syntax::unsupported-term-expression]: unsupported term expression: the root must be a named path/call/record or an Int/Bool literal".to_owned(),
            "k",
        ),
        (
            "let",
            one,
            r#"#[k::config_var(name = "ONE", default = { let n = 3; RequestSyntax::Irq(n) })]"#,
            unsupported("one", "ONE", "a `let` block or a record update"),
            "let n = 3;",
        ),
        (
            "record-update",
            one,
            r#"#[k::config_var(name = "ONE", default = RequestSyntax::Irq { n: 1, ..IRQ0 })]"#,
            unsupported("one", "ONE", "a `let` block or a record update"),
            // The update reads its base's other fields by a `let`, at the base.
            "IRQ0",
        ),
        (
            "matches",
            flag,
            r#"#[k::config_var(name = "FLAG", default = k::matches!(IRQ0, RequestSyntax::Irq(_)))]"#,
            unsupported("flag", "FLAG", "a `k::matches!` test"),
            "k::matches!(IRQ0, RequestSyntax::Irq(_))",
        ),
        (
            "projection",
            one,
            r#"#[k::config_var(name = "ONE", default = RequestSyntax::Irq(k::project!(Int, 3)))]"#,
            unsupported("one", "ONE", "a `k::project!` projection"),
            "k::project!(Int, 3)",
        ),
        (
            // A sort error in an unsupported construct is the default's own mistake, heard first.
            "let-of-another-sort",
            one,
            r#"#[k::config_var(name = "ONE", default = { let n = 3; n })]"#,
            "error[krs::analysis::invalid-term]".to_owned(),
            "",
        ),
    ];
    for (name, attribute, replacement, headline, marked) in cases {
        let manifest = package(
            temporary.path(),
            &format!("refused-{name}"),
            &library(&[(attribute, replacement)]),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[], &[]);
        assert!(!success, "{name}: krs check unexpectedly passed:\n{stderr}");
        let (actual, actual_marked) = first_error(&stderr);
        if marked.is_empty() {
            assert!(actual.starts_with(&headline), "{name}:\n{stderr}");
        } else {
            assert_eq!(
                (actual.as_str(), actual_marked.as_str()),
                (headline.as_str(), marked),
                "{name}:\n{stderr}"
            );
        }
    }
}

/// A `?` cell whose template reads an input with a default still starts present, so it is still
/// written `Some(..)`: the input always has a value now, which has to land in it.
#[test]
fn a_cell_reading_a_defaulted_input_starts_present_as_before() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let source = library(&[(
        ATTRIBUTES[6],
        r#"#[k::config_var(name = "LATER", default = IRQ0)]"#,
    )])
    .replace("pending: Some(later),", "pending: k::absent!(later),");
    let manifest = package(temporary.path(), "absent", &source);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[], &[]);
    assert!(!success, "{stderr}");
    assert!(
        first_error(&stderr)
            .0
            .starts_with("error[krs::analysis::collection-config-var-without-initial]"),
        "{stderr}"
    );
}

/// Each input's value bound by hand, as `--input` documents: the value each of `DEFAULTS` gives.
const BY_HAND: [(&str, &str); 7] = [
    ("pgm", r#""Skip""#),
    ("requests", "[]"),
    ("booted", r#"{"$call": {"Boot": [3]}}"#),
    ("one", r#"{"Irq": {"n": 7}}"#),
    ("table", r#"{"1": {"Irq": [0]}, "2": {"Irq": [2]}}"#),
    ("flag", "true"),
    ("later", r#"{"Irq": [0]}"#),
];

/// `--input NAME=JSON` for each of `inputs`.
fn input_arguments(inputs: &[(&str, &str)]) -> Vec<String> {
    inputs
        .iter()
        .flat_map(|(name, document)| ["--input".to_owned(), format!("{name}={document}")])
        .collect()
}

/// `krs <command> --depth 0 --output kore` (`--output kore` for `search`) with `extra`, which
/// must succeed: its stdout.
fn kore_end(target: &Path, manifest: &Path, command: &str, extra: &[String]) -> String {
    let mut arguments = vec!["--output", "kore"];
    if command == "run" {
        arguments.extend(["--depth", "0"]);
    }
    arguments.extend(extra.iter().map(String::as_str));
    let (success, stdout, stderr) = krs(target, manifest, command, &arguments, &[]);
    assert!(success, "krs {command} {arguments:?}:\n{stderr}");
    stdout
}

/// A run or a search that binds no input starts where binding each default by hand starts: every
/// input, the main one included, takes its default, and a call default is evaluated when the
/// configuration is built. A binding replaces its input's default whole.
#[test]
fn run_and_search_without_a_binding_take_each_default() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let defaulted = package(temporary.path(), "defaulted", &library(&DEFAULTS));
    let by_hand = input_arguments(&BY_HAND);
    for command in ["run", "search"] {
        let unbound = kore_end(target.path(), &defaulted, command, &[]);
        assert_eq!(
            unbound,
            kore_end(target.path(), &defaulted, command, &by_hand),
            "krs {command}"
        );
        // `Boot(3)` is evaluated at init: its result is in `<booted>`, its application nowhere.
        assert!(!unbound.contains("Lblboot{}"), "{unbound}");
        assert!(
            unbound.contains(r#"LblrequestSyntaxIrq{}(\dv{SortInt{}}("3"))"#),
            "{unbound}"
        );
    }
    // A binding replaces the default whole: nothing of `[]` is merged into `[Irq(5)]`, and every
    // other input keeps its default.
    let overridden = kore_end(
        target.path(),
        &defaulted,
        "run",
        &input_arguments(&[("requests", r#"[{"Irq": [5]}, {"Irq": [6]}]"#)]),
    );
    let mut by_hand_overridden = BY_HAND;
    by_hand_overridden[1].1 = r#"[{"Irq": [5]}, {"Irq": [6]}]"#;
    assert_eq!(
        overridden,
        kore_end(
            target.path(),
            &defaulted,
            "run",
            &input_arguments(&by_hand_overridden)
        )
    );
    assert_ne!(overridden, kore_end(target.path(), &defaulted, "run", &[]));
    // A main input bound by FILE or by name replaces its default too.
    let (success, _, stderr) = krs(
        target.path(),
        &defaulted,
        "run",
        &["--depth", "0", "-c", "PGM=skip"],
        &[],
    );
    assert!(success, "{stderr}");
}

/// An input without a default still needs a value, and the refusal names it: the main input
/// without a default is the unbound main parameter, another input a missing variable, whatever
/// the other inputs' defaults.
#[test]
fn an_input_without_a_default_is_still_refused_unbound() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    // Every input but the main one and `one` has a default.
    let partly = package(
        temporary.path(),
        "partly",
        &library(
            &DEFAULTS
                .iter()
                .enumerate()
                .filter(|(index, _)| ![0, 3].contains(index))
                .map(|(_, default)| *default)
                .collect::<Vec<_>>(),
        ),
    );
    let (success, _, stderr) = krs(target.path(), &partly, "run", &["--depth", "0"], &[]);
    assert!(!success);
    assert!(
        stderr.contains("the main parameter `pgm` ($PGM: Stmt) is unbound"),
        "{stderr}"
    );
    let (success, _, stderr) = krs(
        target.path(),
        &partly,
        "run",
        &["--depth", "0", "-c", "PGM=skip"],
        &[],
    );
    assert!(!success);
    let first = stderr.lines().next().unwrap_or_default();
    assert!(
        first.contains("missing configuration variables; pass -c one=VALUE"),
        "{stderr}"
    );
    let (success, _, stderr) = krs(
        target.path(),
        &partly,
        "run",
        &[
            "--depth",
            "0",
            "-c",
            "PGM=skip",
            "--input",
            r#"one={"Irq": [1]}"#,
        ],
        &[],
    );
    assert!(success, "{stderr}");
}

/// A run from a warm stage cache binds what a cold one binds: the stage carries each input's
/// default.
#[test]
fn a_warm_stage_binds_the_defaults_a_cold_compile_binds() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let defaulted = package(temporary.path(), "warm", &library(&DEFAULTS));
    let stages = temporary.path().join("stages");
    let stages_text = stages.to_str().unwrap();
    let run = || {
        let (success, stdout, stderr) = krs(
            target.path(),
            &defaulted,
            "run",
            &["--depth", "0", "--output", "kore"],
            &[("KRS_STAGE_CACHE_DIR", stages_text)],
        );
        assert!(success, "{stderr}");
        stdout
    };
    let cold = run();
    let entries = fs::read_dir(stages.join("entries"))
        .map(Iterator::count)
        .unwrap_or_default();
    assert!(entries > 0, "the cold run stored its stage");
    assert_eq!(run(), cold);
}
