//! `k::patterns!` (FB-49 K1): chain patterns written in KRS, in a package of their own that
//! depends on the specification's. Each step and each `unless` is the readable claim whose
//! subject is the part's set of states, so `emit_patterns` writes each part as the K that
//! claim's left side is; no part is a sentence of `definition.k` or `spec.k`, and the
//! specification emits the same bytes whether or not a patterns package exists.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// The specification: a machine with a computation cell, a memory map, a program counter, a
/// flag, a bus log, a group and a cell of any item.
const SPEC: &str = r#"
use k::KResult;
use k::builtin::{Bool, Int, KSequence, List, Map};

k::sorts! {
    Step: k::KItem;
    Ev: KResult;
    WordStack;
}

#[k::constructors(sort = WordStack, result = KResult)]
#[k::cons_list]
#[k::precedence((StackEmpty, StackCons))]
pub enum Stack {
    #[k::syntax(".WordStack")]
    StackEmpty(),
    #[k::syntax("{head} : {tail}")]
    StackCons { head: Int, tail: WordStack },
}

#[k::constructors(sort = Step, result = KResult)]
pub enum StepOp {
    #[k::syntax("dispatch")]
    Dispatch(),
    #[k::syntax("boundary")]
    Boundary(),
    #[k::syntax("fetch")]
    Fetch(),
    #[k::syntax("selectVector({v})")]
    SelectVector { v: Int },
}

#[k::constructors(sort = Ev, result = KResult)]
pub enum Event {
    #[k::syntax("write({a}, {v})")]
    Write { a: Int, v: Int },
    #[k::syntax("read({a}, {v})")]
    Read { a: Int, v: Int },
}

/// Interrupt flag register.
#[k::constant]
pub const IF: Int = 0xFF0F;

#[k::function(total, internal)]
pub fn Low(value: k::Term<Int>) -> k::Term<Int> {
    value & 0x1F
}

#[k::cell]
pub struct Frame {
    #[k::cell(name = "fpc")]
    pub fpc: Int,
    #[k::cell(name = "fgas")]
    pub fgas: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell(name = "k")]
    pub k: KSequence,
    #[k::cell(name = "memory")]
    pub memory: Map<Int, Int>,
    #[k::cell(name = "pc")]
    pub pc: Int,
    #[k::cell(name = "haltBug")]
    pub halt_bug: Bool,
    #[k::cell(name = "bus")]
    pub bus: List<Ev>,
    #[k::cell(nested, name = "frame")]
    pub frame: Frame,
    #[k::cell(name = "stash")]
    pub stash: k::KItem,
    #[k::cell(name = "stack")]
    pub stack: WordStack,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] program: KSequence) -> Self {
        Self {
            k: k::k![program],
            memory: k::map![],
            pc: 0,
            halt_bug: false,
            bus: [],
            frame: Frame { fpc: 0, fgas: 0 },
            stash: 0,
            stack: Stack::StackEmpty(),
        }
    }
}

k::rules! {
    for Machine;
    use StepOp::*;
    fetch: { k: [Fetch(), ..], pc } => { k: [..], pc: pc + 1 };
}
"#;

/// The acceptance examples E1 (dispatch-request) and E2 (halt-bug-rst), a condition over two
/// steps, and an expectation.
const PATTERNS: &str = r#"#![deny(non_snake_case)]
use spec::{IF, Low};

k::patterns! {
    for spec::Machine;
    use spec::StepOp::*;

    /// dispatch-request: VBlank arrives inside a timer dispatch.
    #[k::cases("scheduled/dispatch-request")]
    #[k::requires(before & 0x1F == 0x04)]
    #[k::requires(after & 0x05 == 0x05)]
    dispatch_request: {
        k: [Dispatch(), ..],
        memory: { IF -> before, .. },
    } => unless({ k: [Boundary(), ..] }) {
        k: [SelectVector(_), ..],
        memory: { IF -> after, .. },
    };

    #[k::cases("cases/halt-bug-rst")]
    halt_bug_rst: { k: [Fetch(), ..], halt_bug: true, pc: p } => { k: [Fetch(), ..], halt_bug: false, pc: p };

    #[k::expect(no)]
    #[k::requires(d2 == d + 1 && Low(d) == 4)]
    climbs: { pc: d, .. } => unless({ k: [Boundary(), ..] }, requires(d > 9)) { pc: d2 };
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

fn write_package(root: &Path, name: &str, source: &str, dependencies: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-PATTERNS-{}\"\n\n[package.metadata.krs.definitions.main]\n",
            krs_path(),
            name.to_ascii_uppercase()
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// A workspace of `spec` and, when given, `pats` depending on it; the manifests.
fn workspace(root: &Path, spec: &str, patterns: Option<&str>) -> (PathBuf, Option<PathBuf>) {
    let spec = write_package(root, "spec", spec, "");
    let patterns = patterns
        .map(|source| write_package(root, "pats", source, "spec = { path = \"../spec\" }\n"));
    let members = if patterns.is_some() {
        "\"spec\", \"pats\""
    } else {
        "\"spec\""
    };
    fs::write(
        root.join("Cargo.toml"),
        format!("[workspace]\nmembers = [{members}]\nresolver = \"3\"\n"),
    )
    .unwrap();
    (spec, patterns)
}

/// Runs `krs <command>` on `package`'s `main` definition, composed with `spec`'s unless it is
/// `spec`.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
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
        .args(["--package", package, "--definition", "main"]);
    if package != "spec" {
        process.args(["--dependency", "spec:main"]);
    }
    let output = process
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

/// Two conjuncts and more on one part (FB56 P1): a part's conditions are one conjunction, so
/// each spelling, attributes or `&&` or both, gives the part one `requires` whose conjuncts are
/// joined by `andThenBool` in source order. The generated part names are no lint of the
/// author's (P4a): the package denies `non_snake_case`.
const CONJUNCTS: &str = r"#![deny(non_snake_case)]
use spec::Low;

k::patterns! {
    for spec::Machine;
    use spec::StepOp::*;

    #[k::requires(z >= 0x80)]
    #[k::requires(z < 0x100)]
    two_attributes: { k: [Fetch(), ..], pc: z };

    #[k::requires(z >= 0x80 && z < 0x100)]
    one_attribute: { k: [Fetch(), ..], pc: z };

    #[k::requires(z >= 0x80)]
    #[k::requires(z < 0x100)]
    #[k::requires(Low(z) == 4)]
    three: { pc: z };

    #[k::requires(z >= 0x80 && z < 0x100)]
    #[k::requires(Low(z) == 4)]
    mixed: { pc: z };

    on_unless: { pc: d } => unless({ pc: e }, requires(e > d && e < 0x100)) { k: [Fetch(), ..] };

    #[k::requires(d > 0)]
    #[k::requires(d2 == d + 1)]
    #[k::requires(Low(d2) == 4)]
    beside: { pc: d } => { pc: d2 };
}
";

/// The files `krs emit-k --ir` writes for the package, in `directory`.
fn emit(target: &Path, manifest: &Path, directory: &Path) {
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--ir", "--output", directory.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
}

/// `emit_patterns` over the package's Definition IR.
fn emitted_patterns(
    target: &Path,
    manifest: &Path,
) -> Result<Vec<krs_compiler::EmittedPattern>, krs_compiler::EmitError> {
    let directory = manifest.with_file_name("emitted");
    emit(target, manifest, &directory);
    let definition: krs_ir_levels::DefinitionIr =
        serde_json::from_str(&fs::read_to_string(directory.join("definition-ir.json")).unwrap())
            .unwrap();
    krs_compiler::emit_patterns(&definition)
}

/// The first `error[..]` line of a failing `krs check`.
fn check_error(target: &Path, manifest: &Path) -> String {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    stderr
        .lines()
        .find(|line| line.starts_with("error"))
        .unwrap_or_else(|| panic!("an error line:\n{stderr}"))
        .to_owned()
}

#[test]
fn e1_and_e2_emit_each_step_as_the_k_its_claim_subject_is() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let (_, patterns) = workspace(temporary.path(), SPEC, Some(PATTERNS));
    let patterns = patterns.unwrap();
    let emitted = emitted_patterns(target.path(), &patterns).unwrap();
    // No part is a sentence of the emitted K: the package declares no claim.
    assert!(!patterns.with_file_name("emitted").join("spec.k").exists());
    let ids = emitted
        .iter()
        .map(|pattern| pattern.id.as_str())
        .collect::<Vec<_>>();
    assert_eq!(ids, ["climbs", "dispatch-request", "halt-bug-rst"]);
    let [climbs, dispatch, halt] = emitted.as_slice() else {
        unreachable!()
    };

    // E1: two steps, an `unless`, each step's binders its own, each condition at its step.
    // The literal is the constant's whole value, which the step's text writes bare.
    assert_eq!(
        dispatch.note.as_deref(),
        Some("dispatch-request: VBlank arrives inside a timer dispatch.")
    );
    assert_eq!(
        dispatch.programs.as_deref(),
        Some(&["scheduled/dispatch-request".to_owned()][..])
    );
    assert_eq!(dispatch.expect, None);
    assert_eq!(dispatch.item, "pats::dispatch_request");
    assert_eq!(dispatch.source.file, "src/lib.rs");
    let source = fs::read_to_string(patterns.with_file_name("src").join("lib.rs")).unwrap();
    assert_eq!(dispatch.source.line(&source), 12);
    let steps = dispatch
        .steps
        .iter()
        .map(|step| (step.pattern.as_str(), step.unless.as_deref()))
        .collect::<Vec<_>>();
    assert_eq!(
        steps,
        [
            (
                "<k> dispatch ... </k> <memory> 65295 |-> Before:Int ... </memory> requires (Before:Int &Int 31) ==Int 4",
                None
            ),
            (
                "<k> selectVector ( _ ) ... </k> <memory> 65295 |-> After:Int ... </memory> requires (After:Int &Int 5) ==Int 5",
                Some("<k> boundary ... </k>")
            ),
        ]
    );
    assert_eq!(
        dispatch.variables,
        [
            variable("After", "after", "Int"),
            variable("Before", "before", "Int")
        ]
    );

    // E2: `p` is one variable of both steps.
    assert_eq!(
        halt.steps
            .iter()
            .map(|step| step.pattern.as_str())
            .collect::<Vec<_>>(),
        [
            "<k> fetch ... </k> <haltBug> true </haltBug> <pc> P:Int </pc>",
            "<k> fetch ... </k> <haltBug> false </haltBug> <pc> P:Int </pc>",
        ]
    );
    assert!(halt.steps.iter().all(|step| step.unless.is_none()));
    assert_eq!(halt.variables, [variable("P", "p", "Int")]);

    // A conjunct over both steps' binders is placed at step 2, which reads step 1's `d`; one
    // over `d` alone stays at step 1, and the `unless`'s own condition reads step 1's `d`.
    assert_eq!(climbs.expect.as_deref(), Some("no"));
    assert_eq!(climbs.programs, None);
    assert_eq!(climbs.steps.len(), 2);
    assert!(
        climbs.steps[0]
            .pattern
            .starts_with("<pc> D:Int </pc> requires "),
        "{}",
        climbs.steps[0].pattern
    );
    assert!(climbs.steps[0].pattern.contains("low ( D:Int )"));
    assert_eq!(
        climbs.steps[1].pattern,
        "<pc> D2:Int </pc> requires D2:Int ==Int (D:Int +Int 1)"
    );
    assert_eq!(
        climbs.steps[1].unless.as_deref(),
        Some("<k> boundary ... </k> requires D:Int >Int 9")
    );
    assert_eq!(
        climbs.variables,
        [variable("D", "d", "Int"), variable("D2", "d2", "Int")]
    );
}

fn variable(k: &str, krs: &str, sort: &str) -> krs_compiler::PatternVariable {
    krs_compiler::PatternVariable {
        k: k.to_owned(),
        krs: krs.to_owned(),
        sort: sort.to_owned(),
    }
}

/// A variable no author named is its part's own: two steps' list rests are two variables.
#[test]
fn a_part_s_conjuncts_are_one_requires_in_every_spelling() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let (_, patterns) = workspace(temporary.path(), SPEC, Some(CONJUNCTS));
    let emitted = emitted_patterns(target.path(), &patterns.unwrap()).unwrap();
    let steps = |id: &str| {
        emitted
            .iter()
            .find(|pattern| pattern.id == id)
            .unwrap_or_else(|| panic!("`{id}` emits"))
            .steps
            .iter()
            .map(|step| (step.pattern.clone(), step.unless.clone()))
            .collect::<Vec<_>>()
    };
    let two = "<k> fetch ... </k> <pc> Z:Int </pc> requires (Z:Int >=Int 128) andThenBool (Z:Int <Int 256)";
    assert_eq!(steps("two-attributes"), [(two.to_owned(), None)]);
    assert_eq!(steps("one-attribute"), [(two.to_owned(), None)]);
    let three = "<pc> Z:Int </pc> requires ((Z:Int >=Int 128) andThenBool (Z:Int <Int 256)) andThenBool (low ( Z:Int ) ==Int 4)";
    assert_eq!(steps("three"), [(three.to_owned(), None)]);
    assert_eq!(steps("mixed"), [(three.to_owned(), None)]);
    // An `unless`'s own condition is one conjunction too.
    assert_eq!(
        steps("on-unless"),
        [
            ("<pc> D:Int </pc>".to_owned(), None),
            (
                "<k> fetch ... </k>".to_owned(),
                Some(
                    "<pc> E:Int </pc> requires (E:Int >Int D:Int) andThenBool (E:Int <Int 256)"
                        .to_owned()
                )
            ),
        ]
    );
    // `d > 0` stays at step 1; the two that read step 2's `d2` are step 2's one conjunction.
    assert_eq!(
        steps("beside"),
        [
            ("<pc> D:Int </pc> requires D:Int >Int 0".to_owned(), None),
            (
                "<pc> D2:Int </pc> requires (D2:Int ==Int (D:Int +Int 1)) andThenBool (low ( D2:Int ) ==Int 4)"
                    .to_owned(),
                None
            ),
        ]
    );

    // The claim with the same conditions emits the same `requires`.
    let temporary = temp_dir();
    let claims = "k::claims! {
        for Machine;
        use StepOp::*;
        #[k::claim(one_path)]
        #[k::requires(z >= 0x80)]
        #[k::requires(z < 0x100)]
        two_attributes: { k: [Fetch(), ..], pc: z } => {};
    }";
    let (spec, _) = workspace(temporary.path(), &format!("{SPEC}\n{claims}\n"), None);
    let directory = spec.with_file_name("emitted");
    emit(target.path(), &spec, &directory);
    let claims = fs::read_to_string(directory.join("spec.k")).unwrap();
    assert!(
        claims.contains("requires (Z:Int >=Int 128) andThenBool (Z:Int <Int 256)"),
        "{claims}"
    );
}

#[test]
fn a_generated_variable_is_renamed_apart_per_step() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let (_, patterns) = workspace(
        temporary.path(),
        SPEC,
        Some(
            "k::patterns! {
                for spec::Machine;
                use spec::Event::*;
                logged: { bus: [Write(1, v), ..] } => { bus: [.., Read(1, v)] };
            }",
        ),
    );
    let emitted = emitted_patterns(target.path(), &patterns.unwrap()).unwrap();
    let steps = emitted[0]
        .steps
        .iter()
        .map(|step| step.pattern.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        steps,
        [
            "<bus> ListItem(write ( 1 , V:Int )) Krs_RestBus_Step1:List </bus>",
            "<bus> Krs_RestBus_Step2:List ListItem(read ( 1 , V:Int )) </bus>",
        ]
    );
}

/// The specification's `definition.k` and Definition IR are the same bytes whether or not a
/// patterns package depends on it.
#[test]
fn the_specification_emits_the_same_bytes_beside_a_patterns_package() {
    let target = shared_fixture_target();
    let without = temp_dir();
    let with = temp_dir();
    let (alone, _) = workspace(without.path(), SPEC, None);
    let (beside, _) = workspace(with.path(), SPEC, Some(PATTERNS));
    let first = alone.with_file_name("emitted");
    let second = beside.with_file_name("emitted");
    emit(target.path(), &alone, &first);
    emit(target.path(), &beside, &second);
    for file in ["definition.k", "definition-ir.json", "semantic-ir.json"] {
        assert_eq!(
            fs::read(first.join(file)).unwrap(),
            fs::read(second.join(file)).unwrap(),
            "{file}"
        );
    }
    assert!(!first.join("spec.k").exists() && !second.join("spec.k").exists());
}

/// A binder two parts name is one variable: of one sort, and a variable in each.
#[test]
fn a_binder_is_one_variable_of_the_pattern() {
    let target = shared_fixture_target();
    for (block, expected) in [
        (
            "two_sorts: { pc: x } => { halt_bug: x };",
            "`x` is `Int` in step 1 of `two_sorts` and `Bool` in step 2",
        ),
        (
            "group: { frame: f @ spec::Frame { fpc: x, .. } } => { stash: f };",
            "`f` is no variable in step 1 of `group`",
        ),
    ] {
        let temporary = temp_dir();
        let (_, patterns) = workspace(
            temporary.path(),
            SPEC,
            Some(&format!("k::patterns! {{ for spec::Machine; {block} }}")),
        );
        let error = emitted_patterns(target.path(), &patterns.unwrap()).unwrap_err();
        assert!(
            matches!(error, krs_compiler::EmitError::PatternBinder { .. }),
            "{error}"
        );
        assert!(error.to_string().contains(expected), "{block}: {error}");
    }
}

/// A patterns package declares nothing but `use` items and the block, and stands outside the
/// definition's closure.
#[test]
fn a_patterns_package_declares_nothing_else_and_nothing_imports_it() {
    let target = shared_fixture_target();
    let block = "k::patterns! { for spec::Machine; use spec::StepOp::*; p: { k: [Fetch(), ..] }; }";
    for (patterns, expected) in [
        (
            format!(
                "{block}\n#[k::function(total, internal)]\npub fn Twice(value: k::Term<k::builtin::Int>) -> k::Term<k::builtin::Int> {{ value + value }}\n"
            ),
            "error[krs::analysis::pattern-helper]: `Twice` is a function of the package that holds `k::patterns!`",
        ),
        (
            format!("{block}\n#[k::constant]\npub const TOP: k::builtin::Int = 3;\n"),
            "error[krs::analysis::patterns-package]: `TOP` is declared in the package that holds `k::patterns!`",
        ),
        (
            format!("mod a {{ {block} }}\nmod b {{ {block} }}\n"),
            "error[krs::syntax::invalid-pattern]: the pattern `p` is declared in `a` and in `b` of one package",
        ),
        (
            "k::patterns! { for spec::Frame; p: { fpc: x }; }".to_owned(),
            "error[krs::syntax::invalid-pattern]: a pattern typed by the cell group `Frame` is not supported yet",
        ),
    ] {
        let temporary = temp_dir();
        let (_, manifest) = workspace(temporary.path(), SPEC, Some(&patterns));
        let error = check_error(target.path(), &manifest.unwrap());
        assert!(error.starts_with(expected), "{error}");
    }
    // A block in the specification's own package: that package declares the definition, its
    // function first.
    let temporary = temp_dir();
    let (spec, _) = workspace(
        temporary.path(),
        &format!(
            "{SPEC}\nk::patterns! {{ for Machine; use StepOp::*; p: {{ k: [Fetch(), ..] }}; }}\n"
        ),
        None,
    );
    let error = check_error(target.path(), &spec);
    assert!(
        error.starts_with(
            "error[krs::analysis::pattern-helper]: `Low` is a function of the package that holds `k::patterns!`"
        ) && error.contains("move the block there, or `Low` to the specification's package"),
        "{error}"
    );
}

/// A pure patterns package that the semantics depends on is inside the definition's closure.
#[test]
fn a_patterns_package_the_semantics_imports_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let root = temporary.path();
    // `lib` is the specification; `inner` holds patterns over it, and `top` extends the
    // specification and depends on `inner`, which puts `inner` in its definition's closure.
    write_package(root, "lib", SPEC, "");
    write_package(
        root,
        "inner",
        "k::patterns! { for lib::Machine; use lib::StepOp::*; p: { k: [Fetch(), ..] }; }\n",
        "lib = { path = \"../lib\" }\n",
    );
    let top = write_package(
        root,
        "top",
        "k::rules! { for lib::Machine; use lib::StepOp::*; boundary: { k: [Boundary(), ..] } => { k: [..] }; }\n",
        "lib = { path = \"../lib\" }\ninner = { path = \"../inner\" }\n",
    );
    fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"lib\", \"inner\", \"top\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, target.path());
    let output = process
        .args(["check", "--manifest-path"])
        .arg(&top)
        .args([
            "--package",
            "top",
            "--definition",
            "main",
            "--dependency",
            "lib:main",
            "--dependency",
            "inner:main",
        ])
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.path().join("stages"))
        .output()
        .unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(!output.status.success(), "{stderr}");
    assert!(
        stderr.contains("error[krs::analysis::patterns-package]: this `k::patterns!` block is in a package the definition's semantics depends on"),
        "{stderr}"
    );
}

/// `krs expand` prints a patterns block as written, and the print checks again.
#[test]
fn the_expand_print_of_a_patterns_block_checks_again() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let (_, patterns) = workspace(temporary.path(), SPEC, Some(PATTERNS));
    let patterns = patterns.unwrap();
    let (success, printed, stderr) = krs(target.path(), &patterns, "expand", &[]);
    assert!(success, "{stderr}");
    assert!(printed.contains("k::patterns!"), "{printed}");
    fs::write(patterns.with_file_name("src").join("lib.rs"), &printed).unwrap();
    let (success, _, stderr) = krs(target.path(), &patterns, "check", &[]);
    assert!(success, "{stderr}");
}

/// No reader of the definition's claims sees a part: the Definition IR keeps the parts apart
/// from every module's sentences (`DefinitionModule::pattern_parts`), so `krs prove` finds no
/// claim, `spec.k` is not written, `definition.k` holds none, and `krs check` reports nothing
/// of them.
#[test]
fn no_reader_of_claims_sees_a_part() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let (_, patterns) = workspace(temporary.path(), SPEC, Some(PATTERNS));
    let patterns = patterns.unwrap();
    let directory = patterns.with_file_name("emitted");
    emit(target.path(), &patterns, &directory);
    assert!(!directory.join("spec.k").exists());
    let definition = fs::read_to_string(directory.join("definition.k")).unwrap();
    assert!(!definition.contains("claim"), "{definition}");
    let ir: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(directory.join("definition-ir.json")).unwrap())
            .unwrap();
    let modules = ir["modules"].as_array().unwrap();
    let parts = modules
        .iter()
        .filter_map(|module| module["patterns"].as_array())
        .map(Vec::len)
        .sum::<usize>();
    assert_eq!(parts, 8, "every part is kept apart");
    // An IR whose parts stand among a module's sentences or rules is refused when it is read:
    // the readers' own constructors partition, and validation checks a deserialized one.
    for (file, among) in [
        ("definition-ir.json", "sentences"),
        ("semantic-ir.json", "rules"),
    ] {
        let mut value: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(directory.join(file)).unwrap()).unwrap();
        for module in value["modules"].as_array_mut().unwrap() {
            if let Some(parts) = module.as_object_mut().unwrap().remove("patterns") {
                module[among]
                    .as_array_mut()
                    .unwrap()
                    .extend(parts.as_array().unwrap().iter().cloned());
            }
        }
        let text = serde_json::to_string(&value).unwrap();
        let error = if file == "definition-ir.json" {
            serde_json::from_str::<krs_ir_levels::DefinitionIr>(&text)
                .err()
                .map(|error| error.to_string())
        } else {
            serde_json::from_str::<krs_ir_levels::SemanticTheory>(&text)
                .err()
                .map(|error| error.to_string())
        };
        assert!(
            error
                .as_deref()
                .is_some_and(|error| error.contains("holds a pattern part")),
            "{file}: {error:?}"
        );
    }
    let (success, _, stderr) = krs(target.path(), &patterns, "prove", &[]);
    assert!(!success);
    assert!(
        stderr.contains("error[krs::exec::claim]: this definition has no claims"),
        "{stderr}"
    );
    let (success, _, stderr) = krs(target.path(), &patterns, "check", &[]);
    assert!(success, "{stderr}");
    for name in [
        "dispatch_request",
        "halt_bug_rst",
        "climbs",
        "dispatch-request",
    ] {
        assert!(!stderr.contains(name), "{stderr}");
    }
}

/// Several rests in a step's list (R-2): the items occur in this order, with any list between
/// and around them. A step holds when some split of the list matches, so the one-rest rule's
/// reason, a result that uses one binding, does not apply.
#[test]
fn several_rests_in_a_step_s_list_are_items_in_order() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let (_, patterns) = workspace(
        temporary.path(),
        SPEC,
        Some(
            "k::patterns! {
                for spec::Machine;
                use spec::Event::*;
                use spec::StepOp::*;

                written_then_read: { bus: [.., Write(0xC110, v), .., Read(0xC110, v), ..] };

                shared: { bus: [.., Write(1, v), ..] } => unless({ bus: [.., Read(1, v), ..] }) { bus: [.., Read(2, v), ..] };

                #[k::requires(k::builtin::list::contains(Read(3, v), l))]
                member: { bus: [.., Write(3, v), l @ .., Write(4, v), ..] };
            }",
        ),
    );
    let emitted = emitted_patterns(target.path(), &patterns.unwrap()).unwrap();
    let steps = |id: &str| {
        emitted
            .iter()
            .find(|pattern| pattern.id == id)
            .unwrap()
            .steps
            .iter()
            .map(|step| (step.pattern.clone(), step.unless.clone()))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        steps("written-then-read"),
        [(
            "<bus> _ ListItem(write ( 49424 , V:Int )) _ ListItem(read ( 49424 , V:Int )) _ </bus>"
                .to_owned(),
            None
        )]
    );
    assert_eq!(
        steps("shared"),
        [
            (
                "<bus> _ ListItem(write ( 1 , V:Int )) _ </bus>".to_owned(),
                None
            ),
            (
                "<bus> _ ListItem(read ( 2 , V:Int )) _ </bus>".to_owned(),
                Some("<bus> _ ListItem(read ( 1 , V:Int )) _ </bus>".to_owned())
            ),
        ]
    );
    let member = steps("member");
    assert_eq!(member.len(), 1);
    assert_eq!(
        member[0].0,
        "<bus> _ ListItem(write ( 3 , V:Int )) L:List ListItem(write ( 4 , V:Int )) _ </bus> requires read ( 3 , V:Int ) in L:List",
    );
}

/// Several rests where a list is no builtin `List`, and every other sentence keeps one rest.
#[test]
fn several_rests_are_refused_where_they_mean_nothing() {
    let target = shared_fixture_target();
    for (block, expected) in [
        (
            "k::patterns! { for spec::Machine; p: { stack: [.., 1, .., 2, ..] }; }",
            "error[krs::analysis::invalid-list-notation]:",
        ),
        (
            "k::patterns! { for spec::Machine; p: { memory: [.., 1, ..] }; }",
            "error[krs::analysis::invalid-list-notation]: the cell `memory` holds a `Map` leaf, which brackets do not denote",
        ),
        (
            "k::patterns! { for spec::Machine; use spec::StepOp::*; p: { k: [.., Fetch(), ..] }; }",
            "error[krs::collect::invalid-configuration]: the entry of the computation cell `k` has an item after its rest: a computation is read from its front",
        ),
    ] {
        let temporary = temp_dir();
        let (_, manifest) = workspace(temporary.path(), SPEC, Some(block));
        let error = check_error(target.path(), &manifest.unwrap());
        assert!(error.starts_with(expected), "{block}: {error}");
    }
}

/// A rule, an equation and a claim keep the one-rest rule: their results use one binding. The
/// brackets are the `bus` cell's whether or not the record names the computation cell beside
/// them, so a record whose only cell is `bus` gets the same refusal, at the same rest (EDOTS
/// item 3: such a clause once left the record no cell and failed the configuration's check).
#[test]
fn every_other_sentence_keeps_one_rest() {
    let target = shared_fixture_target();
    let errors = [
        "k::rules! { for Machine; use StepOp::*; r: { k: [Fetch(), ..], bus: [.., x, ..] } => { k: [..] }; }",
        "k::rules! { for Machine; use StepOp::*; r: { bus: [.., x, ..] } => {}; }",
        "k::claims! { for Machine; use StepOp::*; #[k::claim(one_path)] c: { k: [Fetch(), ..], bus: [.., x, ..] } => { k: [..] }; }",
        "k::claims! { for Machine; use StepOp::*; #[k::claim(one_path)] c: { bus: [.., x, ..] } => {}; }",
        "#[k::function(total, internal)]\npub fn Second(list: k::Term<List>) -> k::Term<k::KItem>;\nk::equations! { for Second; second: [.., x, ..] => x; }",
    ]
    .map(|sentences| {
        let temporary = temp_dir();
        let (spec, _) = workspace(temporary.path(), &format!("{SPEC}\n{sentences}\n"), None);
        let error = check_error(target.path(), &spec);
        assert!(
            error.starts_with(
                "error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`"
            ),
            "{sentences}: {error}"
        );
        let location = check_location(target.path(), &spec);
        (error, location)
    });
    assert_eq!(errors[0], errors[1], "a rule with and without `k`");
    assert_eq!(errors[2], errors[3], "a claim with and without `k`");
}

/// The source the first error of `krs check` stands at in `manifest`'s library, up to the end of
/// the brackets it is in: `..]` at a list's second rest.
fn check_location(target: &Path, manifest: &Path) -> String {
    let (_, _, stderr) = krs(target, manifest, "check", &[]);
    let (line, column) = stderr
        .lines()
        .find_map(|line| line.trim_start().strip_prefix("--> "))
        .and_then(|location| location.split_once("src/lib.rs:"))
        .and_then(|(_, location)| {
            let (line, column) = location.split_once(':')?;
            Some((line.parse::<usize>().ok()?, column.parse::<usize>().ok()?))
        })
        .unwrap_or_else(|| panic!("an error located in the library:\n{stderr}"));
    let source = fs::read_to_string(manifest.with_file_name("src").join("lib.rs")).unwrap();
    let text = &source.lines().nth(line - 1).unwrap()[column - 1..];
    text[..=text.find(']').unwrap_or(text.len() - 1)].to_owned()
}
