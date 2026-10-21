//! The `krust-fuzz` executable (ARCHITECTURE 9.4, impl.toml FZ-07): campaigns from a campaign
//! file, `--replay` and its identity check, the differential target over two compiled
//! directories, the per-case safety limit's default (D24), and `krust fuzz` forwarding.
//!
//! Compiled directories are written from the fixtures (`tests/support`) as `krust kcompile`
//! writes them: the KORE files, then the runnable artifact, whose manifest is published last.
//! Every campaign fixes its seed (impl.toml `[common].determinism`).

mod support;

use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    sync::Arc,
};

use k_rust::{
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    native::{FUZZ_PARENT_BUILD_ENV, write_runnable_artifact},
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};
use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl,
    HoleLocation, OutcomeClass, ProgramInput, ProgramSource, ProposerConfig, SpanAddress, Target,
    TargetKind,
    report::{CampaignOutcome, FuzzReport, KillKind},
    spec::{DEFAULT_REJECTION_CAP, ProgramText},
    target::{PatternAt, PatternTarget},
    values::{Constraints, GenerationBounds},
};
use support::{COIN, COIN_KILL, COIN_LAYOUT, Fixture, IMP};

/// `r` of `le.imp` is not 1 at a clean natural end (the anchors' `x <= y` branch is not taken),
/// as `tests/campaign_m1.rs` states it.
const LE_VIOLATION: &str =
    r#"<k> .K </k> <state> (#token("r", "Id") |-> R:Int) _:Map </state> requires R =/=Int 1"#;

/// The campaign file of the `le.imp` property: the holes of ARCHITECTURE 2.2 and the target.
fn le_campaign() -> String {
    format!(
        r#"
definition = "imp-kompiled"
program = "le.imp"
seed = "0x5eed"
cases = 200

[target]
pattern = '{LE_VIOLATION}'
negated-property = true

[[hole]]
name = "X"
sort = "Int"
line = 2
find = "x = 3;"
literal = "3"

[[hole]]
name = "Y"
sort = "Int"
find = "y = 5;"
literal = "5"
"#
    )
}

/// Write the compiled directory of `fixture` to `directory`, as `krust kcompile` writes it.
fn write_compiled(fixture: &'static Fixture, directory: &Path) {
    fs::create_dir_all(directory).expect("the compiled directory is created");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let options = LoadOptions {
        implicit_sources: vec![embedded("prelude.md").expect("the prelude is embedded")],
        ..CompilationBackend::Rust.load_options()
    };
    let (loaded, syntax_module) = load_for_compilation(
        ResolvedSource::new(fixture.file, fixture.source),
        fixture.main_module,
        None,
        &mut resolver,
        &options,
    )
    .unwrap_or_else(|error| panic!("{} does not load: {error:?}", fixture.file));
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("{} does not compile: {error}", fixture.file));
    for (name, text) in [
        ("definition.kore", &artifacts.definition_kore),
        ("syntaxDefinition.kore", &artifacts.syntax_definition_kore),
        ("macros.kore", &artifacts.macros_kore),
    ] {
        fs::write(directory.join(name), text).expect("a KORE file is written");
    }
    write_runnable_artifact(
        directory,
        fixture.main_module,
        &syntax_module,
        loaded.definition(),
        loaded.source_table(),
        &artifacts.execution_definition,
        &artifacts.configuration_variables,
        &artifacts.execution_rewrite_order,
        &artifacts.definition_kore,
    )
    .expect("the runnable artifact is written");
}

/// A fresh working directory for one test, under Cargo's temporary directory for integration
/// tests, holding the compiled directories and the files it names. Each test has its own, so
/// that tests running in parallel threads or processes (nextest) never share one.
fn workspace(
    test: &str,
    definitions: &[(&str, &'static Fixture)],
    files: &[(&str, &str)],
) -> PathBuf {
    let directory = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("cli")
        .join(test);
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).expect("the test directory is created");
    for (name, fixture) in definitions {
        write_compiled(fixture, &directory.join(name));
    }
    for (name, text) in files {
        fs::write(directory.join(name), text).expect("a test file is written");
    }
    directory
}

/// Run `krust-fuzz` in `directory` with `args`, with no standard input and no parent krust.
fn krust_fuzz(directory: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_krust-fuzz"))
        .current_dir(directory)
        .args(args)
        .env_remove(FUZZ_PARENT_BUILD_ENV)
        .stdin(Stdio::null())
        .output()
        .expect("krust-fuzz runs")
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// The exit status and the report a `--json` run printed.
fn json_run(directory: &Path, args: &[&str]) -> (Option<i32>, FuzzReport) {
    let output = krust_fuzz(directory, args);
    let report = FuzzReport::from_json(text(&output.stdout).trim()).unwrap_or_else(|error| {
        panic!(
            "no report ({error}); stdout: {}; stderr: {}",
            text(&output.stdout),
            text(&output.stderr)
        )
    });
    (output.status.code(), report)
}

fn le_workspace(test: &str) -> PathBuf {
    let le = IMP.program("imp/le.imp").text;
    workspace(
        test,
        &[("imp-kompiled", &IMP)],
        &[("le.imp", le), ("le.toml", &le_campaign())],
    )
}

#[test]
fn a_replayed_witness_reproduces_its_class_and_final_configuration() {
    let directory = le_workspace("replay");
    let (status, report) = json_run(
        &directory,
        &[
            "--campaign",
            "le.toml",
            "--witness",
            "witness.json",
            "--json",
        ],
    );
    assert_eq!(status, Some(0), "a witness exits 0");
    let witness = report.witness().expect("a confirmed counterexample");
    assert_eq!(witness.first.class, OutcomeClass::Hit);
    let recorded: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(directory.join("witness.json")).unwrap())
            .expect("the witness file is JSON");
    assert_eq!(recorded["schema"], "krust-fuzz-witness");
    assert_eq!(
        FuzzReport::from_json(&recorded["report"].to_string()).unwrap(),
        report,
        "the witness file records the campaign's report"
    );

    let replay = krust_fuzz(&directory, &["--replay", "witness.json"]);
    let stdout = text(&replay.stdout);
    assert_eq!(
        replay.status.code(),
        Some(0),
        "{stdout}{}",
        text(&replay.stderr)
    );
    assert!(stdout.contains("first witness: reproduced"), "{stdout}");
    if witness.shrunk.is_some() {
        assert!(stdout.contains("shrunk witness: reproduced"), "{stdout}");
    }

    // The comparison reads the final configuration: a witness file whose recorded end is not
    // the one the run reaches does not reproduce.
    let mut tampered = recorded.clone();
    let end = &mut tampered["report"]["outcome"]["witness"]["first"]["sides"][0]["final-configurations"]
        [0];
    *end = serde_json::Value::String(end.as_str().unwrap().replace("\"0\"", "\"7\""));
    fs::write(directory.join("tampered.json"), tampered.to_string()).unwrap();
    let replay = krust_fuzz(&directory, &["--replay", "tampered.json"]);
    let stdout = text(&replay.stdout);
    assert_eq!(
        replay.status.code(),
        Some(1),
        "{stdout}{}",
        text(&replay.stderr)
    );
    assert!(stdout.contains("first witness: not reproduced"), "{stdout}");
    assert!(
        stdout.contains("the final configurations of side 0 differ"),
        "{stdout}"
    );
}

#[test]
fn an_identity_mismatch_is_refused_unless_forced() {
    let directory = le_workspace("identity");
    let campaign = [
        "--campaign",
        "le.toml",
        "--witness",
        "witness.json",
        "--no-shrink",
    ];
    let output = krust_fuzz(
        &directory,
        &[&campaign[..], &["--k-rust-revision", "another-revision"]].concat(),
    );
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));

    let refused = krust_fuzz(&directory, &["--replay", "witness.json"]);
    let stderr = text(&refused.stderr);
    assert_eq!(refused.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("identity mismatch: k-rust revision: the witness has `another-revision`"),
        "{stderr}"
    );
    assert!(text(&refused.stdout).is_empty(), "nothing ran");

    let forced = krust_fuzz(&directory, &["--replay", "witness.json", "--force"]);
    let stdout = text(&forced.stdout);
    assert_eq!(
        forced.status.code(),
        Some(0),
        "{stdout}{}",
        text(&forced.stderr)
    );
    assert!(
        stdout.contains("identity mismatch (forced): k-rust revision"),
        "{stdout}"
    );
    assert!(stdout.contains("first witness: reproduced"), "{stdout}");

    // `--k-rust-revision` names the replaying build's revision.
    let named = krust_fuzz(
        &directory,
        &[
            "--replay",
            "witness.json",
            "--k-rust-revision",
            "another-revision",
        ],
    );
    let stdout = text(&named.stdout);
    assert_eq!(
        named.status.code(),
        Some(0),
        "{stdout}{}",
        text(&named.stderr)
    );
    assert!(!stdout.contains("identity mismatch"), "{stdout}");

    // A program that changed since the witness was found is another program.
    let output = krust_fuzz(&directory, &campaign);
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    let le = IMP.program("imp/le.imp").text;
    fs::write(directory.join("le.imp"), format!("{le}\n")).unwrap();
    let refused = krust_fuzz(&directory, &["--replay", "witness.json"]);
    let stderr = text(&refused.stderr);
    assert_eq!(refused.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("identity mismatch: program digest"),
        "{stderr}"
    );
    assert!(!stderr.contains("k-rust revision"), "{stderr}");
}

#[test]
fn the_command_line_runs_the_library_campaign() {
    let directory = le_workspace("library");
    let (status, report) = json_run(&directory, &["--campaign", "le.toml", "--json"]);
    assert_eq!(status, Some(0));

    let hole = |name: &str, find: &str, literal: &str, line: Option<u32>| HoleDecl {
        name: name.into(),
        sort: "Int".into(),
        location: HoleLocation::Span(SpanAddress {
            program: "le.imp".into(),
            line,
            find: find.into(),
            literal: literal.into(),
        }),
        constraints: Constraints::default(),
        allow_refused_sort: false,
    };
    let spec = CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(IMP.compiled().definition()),
            mutant: None,
        },
        program: ProgramInput::Source(ProgramSource {
            program: Some(ProgramText {
                name: "le.imp".into(),
                text: IMP.program("imp/le.imp").text.into(),
                start_sort: "Pgm".into(),
            }),
            config_vars: Vec::new(),
        }),
        holes: vec![
            hole("X", "x = 3;", "3", Some(2)),
            hole("Y", "y = 5;", "5", None),
        ],
        target: Target {
            kind: TargetKind::Pattern(PatternTarget {
                pattern: LE_VIOLATION.into(),
                at: PatternAt::Final,
            }),
            run_to_completion: false,
            negated_property: true,
        },
        options: CaseOptions {
            safety_limit_ms: Some(60_000),
            ..CaseOptions::default()
        },
        proposers: ProposerConfig::default(),
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 0x5eed,
        identity: CallerIdentity {
            k_rust_revision: report.identity.k_rust_revision.clone(),
            thread_stack_size: report.identity.thread_stack_size,
        },
    };
    let library = Campaign::new(spec)
        .expect("the library campaign is valid")
        .run(Budget::Cases(200), None);
    assert_eq!(report.outcome, library.outcome);
    assert_eq!(report.totals, library.totals);
    assert_eq!(
        report.identity.program_digest,
        library.identity.program_digest
    );
    assert_eq!(
        report.identity.overlay_digest,
        library.identity.overlay_digest
    );
    assert_eq!(
        report.identity.target_digest,
        library.identity.target_digest
    );
    assert_eq!(report.identity.options, library.identity.options);
    assert_eq!(
        report.identity.definitions[0].execution_digest,
        library.identity.definitions[0].execution_digest
    );
}

#[test]
fn the_differential_target_takes_two_compiled_definitions() {
    let flip = COIN.program("coin/flip.pgm").text;
    let campaign = r#"
seed = 7
cases = 64

[[hole]]
name = "N"
sort = "Int"
literal = "3"
"#;
    let directory = workspace(
        "differential",
        &[
            ("coin", &COIN),
            ("coin-kill", &COIN_KILL),
            ("coin-layout", &COIN_LAYOUT),
        ],
        &[("flip.pgm", flip), ("flip.toml", campaign)],
    );
    let args = |mutant: &'static str| {
        [
            "--campaign",
            "flip.toml",
            "--definition",
            "coin",
            "--program",
            "flip.pgm",
            "--mutant",
            mutant,
            "--json",
            "--witness",
            "kill.json",
        ]
    };
    let (status, report) = json_run(&directory, &args("coin-kill"));
    assert_eq!(status, Some(0));
    let witness = report.witness().expect("the mutant is killed");
    assert_eq!(witness.first.kill, Some(KillKind::AddedEnd));
    assert_eq!(report.identity.definitions.len(), 2);
    let replay = krust_fuzz(&directory, &["--replay", "kill.json"]);
    assert_eq!(
        replay.status.code(),
        Some(0),
        "{}{}",
        text(&replay.stdout),
        text(&replay.stderr)
    );

    let (status, report) = json_run(&directory, &args("coin-layout"));
    assert_eq!(status, Some(1), "no witness exits 1");
    assert_eq!(report.outcome, CampaignOutcome::Equivalent);
}

#[test]
fn the_per_case_safety_limit_defaults_to_60_seconds_and_is_recorded() {
    let directory = le_workspace("safety");
    let limit = |extra: &[&str]| {
        let args = [
            &["--campaign", "le.toml", "--cases", "1", "--json"][..],
            extra,
        ]
        .concat();
        let (status, report) = json_run(&directory, &args);
        assert_eq!(status, Some(1), "the anchors do not violate the property");
        report.identity.options.safety_limit_ms
    };
    assert_eq!(limit(&[]), Some(60_000));
    assert_eq!(limit(&["--safety-limit", "5"]), Some(5_000));
    assert_eq!(limit(&["--no-safety-limit"]), None);
}

#[test]
fn krust_fuzz_refuses_to_run_for_a_krust_of_another_build() {
    let output = Command::new(env!("CARGO_BIN_EXE_krust-fuzz"))
        .arg("--help")
        .env(FUZZ_PARENT_BUILD_ENV, "0.0.0+another-build")
        .stdin(Stdio::null())
        .output()
        .expect("krust-fuzz runs");
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    assert!(stderr.contains("version skew"), "{stderr}");
    assert!(stderr.contains("0.0.0+another-build"), "{stderr}");

    let output = Command::new(env!("CARGO_BIN_EXE_krust-fuzz"))
        .arg("--version")
        .env(FUZZ_PARENT_BUILD_ENV, k_rust::native::build_identity())
        .stdin(Stdio::null())
        .output()
        .expect("krust-fuzz runs");
    assert!(output.status.success(), "{}", text(&output.stderr));
}

/// `krust fuzz` runs the `krust-fuzz` beside it. Cargo builds `krust` into the same directory
/// as `krust-fuzz` whenever it builds both, as a workspace build of the tests does; a
/// `-p k-rust-fuzz` build does not build `krust`, and this test then says how to.
#[test]
fn krust_fuzz_help_reaches_krust_fuzz() {
    let krust_fuzz = Path::new(env!("CARGO_BIN_EXE_krust-fuzz"));
    let krust = krust_fuzz.with_file_name(format!("krust{}", std::env::consts::EXE_SUFFIX));
    assert!(
        krust.is_file(),
        "`{}` is missing: build it with `cargo build -p k-rust --bin krust` into the same target \
         directory (a workspace test run builds it)",
        krust.display()
    );
    let output = Command::new(&krust)
        .args(["fuzz", "--help"])
        .env_remove(FUZZ_PARENT_BUILD_ENV)
        .stdin(Stdio::null())
        .output()
        .expect("krust runs");
    let stdout = text(&output.stdout);
    assert!(output.status.success(), "{stdout}{}", text(&output.stderr));
    assert!(stdout.contains("Usage: krust-fuzz"), "{stdout}");
    assert!(stdout.contains("--replay <FILE>"), "{stdout}");
}
