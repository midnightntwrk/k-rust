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
    report::{CampaignOutcome, FuzzReport, KillKind, REPORT_VERSION},
    spec::{DEFAULT_REJECTION_CAP, ProgramText},
    target::{PatternAt, PatternTarget},
    values::{Constraints, GenerationBounds},
};
use support::{
    COIN, COIN_KILL, COIN_LAYOUT, Fixture, IMP, IMP_DIFF, IMP_DIV_GUARD_DROPPED, R3_PLAINQ,
    R3_PLAINQ_M,
};

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
    write_compiled_source(fixture.file, fixture.source, fixture.main_module, directory);
}

/// Write the compiled directory of `source`, under the source name `file`, whose main module is
/// `main_module`, to `directory`, as `krust kcompile` writes it.
fn write_compiled_source(file: &str, source: &str, main_module: &str, directory: &Path) {
    write_compiled_with(file, source, main_module, &[], directory);
}

/// [`write_compiled_source`], with `requires` (name, text) resolving the definition's
/// `requires` beside k-rust's embedded builtins.
fn write_compiled_with(
    file: &str,
    source: &str,
    main_module: &str,
    requires: &[(&str, &str)],
    directory: &Path,
) {
    fs::create_dir_all(directory).expect("the compiled directory is created");
    let mut resolver = |_: &str, required: &str| {
        requires
            .iter()
            .find(|(name, _)| *name == required)
            .map(|(name, text)| ResolvedSource::new(*name, *text))
            .or_else(|| embedded(required))
            .ok_or_else(|| format!("unexpected require {required}"))
    };
    let options = LoadOptions {
        implicit_sources: vec![embedded("prelude.md").expect("the prelude is embedded")],
        ..CompilationBackend::Rust.load_options()
    };
    let (loaded, syntax_module) = load_for_compilation(
        ResolvedSource::new(file, source),
        main_module,
        None,
        &mut resolver,
        &options,
    )
    .unwrap_or_else(|error| panic!("{file} does not load: {error:?}"));
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("{file} does not compile: {error}"));
    for (name, text) in [
        ("definition.kore", &artifacts.definition_kore),
        ("syntaxDefinition.kore", &artifacts.syntax_definition_kore),
        ("macros.kore", &artifacts.macros_kore),
    ] {
        fs::write(directory.join(name), text).expect("a KORE file is written");
    }
    write_runnable_artifact(
        directory,
        main_module,
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

    // How each leaf ended is part of the reproduction too (FZ-DIFFEND: a differential kill rests
    // on it): a witness file whose recorded halt is another does not reproduce.
    let mut tampered = recorded.clone();
    let halts = &mut tampered["report"]["outcome"]["witness"]["first"]["sides"][0]["halts"];
    assert_eq!(halts[0], "stuck", "{halts}");
    halts[0] = serde_json::Value::String("trivial".to_owned());
    fs::write(directory.join("halts.json"), tampered.to_string()).unwrap();
    let replay = krust_fuzz(&directory, &["--replay", "halts.json"]);
    let stdout = text(&replay.stdout);
    assert_eq!(
        replay.status.code(),
        Some(1),
        "{stdout}{}",
        text(&replay.stderr)
    );
    assert!(stdout.contains("the halts of side 0 differ"), "{stdout}");
}

/// The guide's `krust fuzz` kill: IMP's `primes` with four holes against the mutant that drops
/// the division's guard, whose witness is shrunk, has a krun line per side and names the
/// mutant's undefined step's rule.
const PRIMES_CAMPAIGN: &str = r#"
definition = "imp-kompiled"
mutant = "mutant-kompiled"
program = "primes.imp"
seed = 0
cases = 100

[options]
max-work = 20000

[[hole]]
name = "M"
sort = "Int"
find = "m = 4;"
literal = "4"
range = { min = 0, max = 8 }

[[hole]]
name = "N"
sort = "Int"
find = "n = 2;"
literal = "2"
range = { min = 0, max = 8 }

[[hole]]
name = "I"
sort = "Int"
find = "i = 2;"
literal = "2"
range = { min = 0, max = 8 }

[[hole]]
name = "T"
sort = "Int"
find = "t = 1;"
literal = "1"
range = { min = 0, max = 3 }
"#;

/// FZ-REPLAY-WHOLE (final review B1): a replay compares the whole witness, so a witness file
/// whose program, configuration variables, krun lines, label, clean-leaf facts, work or
/// undefined-step rules were edited does not reproduce; only the documented exclusions
/// (`repaired-from`) may differ.
#[test]
fn a_replay_compares_the_whole_witness() {
    let primes = IMP_DIFF.program("imp-diff/primes.imp").text;
    let directory = workspace(
        "replay-whole",
        &[
            ("imp-kompiled", &IMP_DIFF),
            ("mutant-kompiled", &IMP_DIV_GUARD_DROPPED),
        ],
        &[("primes.imp", primes), ("primes.toml", PRIMES_CAMPAIGN)],
    );
    let found = krust_fuzz(
        &directory,
        &["--campaign", "primes.toml", "--witness", "witness.json"],
    );
    assert_eq!(found.status.code(), Some(0), "{}", text(&found.stdout));
    let recorded: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(directory.join("witness.json")).unwrap()).unwrap();
    let witness = &recorded["report"]["outcome"]["witness"];
    assert!(witness["shrunk"].is_object(), "{witness}");
    assert!(witness["mutant-krun-command"].is_string(), "{witness}");
    assert!(
        witness["shrunk"]["sides"][1]["undefined-rules"].is_array(),
        "{witness}"
    );
    let replay = krust_fuzz(&directory, &["--replay", "witness.json"]);
    assert_eq!(
        replay.status.code(),
        Some(0),
        "{}{}",
        text(&replay.stdout),
        text(&replay.stderr)
    );

    type Tamper = fn(&mut serde_json::Value);
    let tampers: [(&str, Tamper, &str); 10] = [
        (
            "program",
            |w| {
                let program = w["shrunk"]["program"]
                    .as_str()
                    .unwrap()
                    .replace("m = 0;", "m = 7;");
                w["shrunk"]["program"] = program.into();
            },
            "shrunk witness: not reproduced\n  the instantiated program differs",
        ),
        (
            "first-program",
            |w| w["first"]["program"] = "int x;".into(),
            "first witness: not reproduced\n  the instantiated program differs",
        ),
        (
            "config-vars",
            |w| w["shrunk"]["config-vars"] = serde_json::json!({"$PGM": "int x;"}),
            "the instantiated configuration variables differ",
        ),
        (
            "krun-command",
            |w| {
                let line = format!("rm -rf / # {}", w["krun-command"].as_str().unwrap());
                w["krun-command"] = line.into();
            },
            "the krun line (`krun-command`) differs",
        ),
        (
            "mutant-krun-command",
            |w| w["mutant-krun-command"] = "echo hi".into(),
            "the mutant's krun line (`mutant-krun-command`) differs",
        ),
        (
            "work",
            |w| w["shrunk"]["sides"][0]["work"] = 1.into(),
            "the work of side 0 differs: the witness has 1, the replay ",
        ),
        (
            "clean-leaf-facts",
            |w| w["clean-leaf-facts"] = serde_json::json!(["nothing-checked"]),
            "the clean-leaf facts differ",
        ),
        (
            "label",
            |w| w["label"] = "property-failure".into(),
            "the label differs: the witness has `property-failure`, the replay `hit`",
        ),
        (
            "undefined-rules",
            |w| {
                w["shrunk"]["sides"][1]
                    .as_object_mut()
                    .unwrap()
                    .remove("undefined-rules");
            },
            "shrunk witness: not reproduced\n  the undefined-step rules of side 1 differ",
        ),
        (
            "steps",
            |w| w["first"]["steps"] = 1.into(),
            "the step count differs: the witness has 1, the replay ",
        ),
    ];
    for (name, tamper, said) in tampers {
        let mut tampered = recorded.clone();
        tamper(&mut tampered["report"]["outcome"]["witness"]);
        let file = format!("{name}.json");
        fs::write(directory.join(&file), tampered.to_string()).unwrap();
        let replay = krust_fuzz(&directory, &["--replay", &file]);
        let stdout = text(&replay.stdout);
        assert_eq!(
            replay.status.code(),
            Some(1),
            "{name}: {stdout}{}",
            text(&replay.stderr)
        );
        assert!(stdout.contains(said), "{name}: {said}: {stdout}");
    }

    // The documented exclusion: the refused hit a client's filter repaired `first` from records
    // the campaign's search, which a replay does not repeat.
    let mut tampered = recorded.clone();
    tampered["report"]["outcome"]["witness"]["repaired-from"] =
        serde_json::json!({"case": 3, "holes": [], "cause": "end-not-ascii"});
    fs::write(directory.join("repaired.json"), tampered.to_string()).unwrap();
    let replay = krust_fuzz(&directory, &["--replay", "repaired.json"]);
    assert_eq!(
        replay.status.code(),
        Some(0),
        "{}{}",
        text(&replay.stdout),
        text(&replay.stderr)
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
    let output = krust_fuzz(&directory, &campaign);
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    // A witness of another k-rust build: no flag can name a revision, so edit the record.
    let path = directory.join("witness.json");
    let mut recorded: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
    recorded["report"]["identity"]["k-rust-revision"] = "another-revision".into();
    fs::write(&path, recorded.to_string()).unwrap();

    let refused = krust_fuzz(&directory, &["--replay", "witness.json"]);
    let stderr = text(&refused.stderr);
    assert_eq!(refused.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("identity mismatch: k-rust-revision: the witness has \"another-revision\""),
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
        stdout.contains("identity mismatch (forced): k-rust-revision"),
        "{stdout}"
    );
    assert!(stdout.contains("first witness: reproduced"), "{stdout}");
    assert!(
        stdout.contains("forced: replayed despite 1 identity mismatch"),
        "a forced replay says so: {stdout}"
    );

    // No flag lets a replay name its own revision and pass the check silently.
    let named = krust_fuzz(
        &directory,
        &[
            "--replay",
            "witness.json",
            "--k-rust-revision",
            "another-revision",
        ],
    );
    assert_eq!(named.status.code(), Some(2), "{}", text(&named.stderr));
    assert!(text(&named.stdout).is_empty());

    // A program that changed since the witness was found is another program.
    let output = krust_fuzz(&directory, &campaign);
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    let le = IMP.program("imp/le.imp").text;
    fs::write(directory.join("le.imp"), format!("{le}\n")).unwrap();
    let refused = krust_fuzz(&directory, &["--replay", "witness.json"]);
    let stderr = text(&refused.stderr);
    assert_eq!(refused.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("identity mismatch: program-digest"),
        "{stderr}"
    );
    assert!(!stderr.contains("k-rust-revision"), "{stderr}");
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
            column: None,
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
            data_end: true,
            comparable: false,
            query_confirmable: false,
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
    // One definition gives one identity whichever route loaded it: the compiled directory and
    // the in-process compilation of the same source (FZ-SETUP).
    assert_eq!(report.identity.definitions, library.identity.definitions);
}

/// FZ-SETUP fix round (S1): a witness found on a definition compiled in one directory replays on
/// the same definition compiled in another: the identity names each source relative to the
/// main file's directory, not by the absolute path the compiled directory records.
#[test]
fn a_witness_replays_on_the_definition_compiled_elsewhere() {
    let directory = le_workspace("relocated");
    for (root, compiled) in [("A", "imp-a"), ("B/deeper", "imp-b")] {
        let name = directory.join(root).join("src/imp.k");
        write_compiled_source(
            name.to_str().expect("a UTF-8 path"),
            IMP.source,
            IMP.main_module,
            &directory.join(compiled),
        );
    }
    let a = fs::read_to_string(directory.join("imp-a/frontend.json")).unwrap();
    assert!(
        a.contains("/A/src/imp.k"),
        "the compiled directory records its path"
    );
    let found = krust_fuzz(
        &directory,
        &[
            "--campaign",
            "le.toml",
            "--definition",
            "imp-a",
            "--witness",
            "witness.json",
            "--no-shrink",
        ],
    );
    assert_eq!(found.status.code(), Some(0), "{}", text(&found.stderr));
    let replay = krust_fuzz(
        &directory,
        &["--replay", "witness.json", "--definition", "imp-b"],
    );
    let stdout = text(&replay.stdout);
    assert_eq!(
        replay.status.code(),
        Some(0),
        "{stdout}{}",
        text(&replay.stderr)
    );
    assert!(stdout.contains("first witness: reproduced"), "{stdout}");
}

/// INT7 (FZ-RULEREF review I2 with FZ-SETUP): a rule target's witness replays on its definition
/// compiled elsewhere too, although the report names the target rule by the catalog's source
/// path, which records where it was compiled; replay compares the target rule by its id.
#[test]
fn a_rule_witness_replays_on_the_definition_compiled_elsewhere() {
    let directory = le_workspace("relocated-rule");
    for (root, compiled) in [("A", "imp-a"), ("B/deeper", "imp-b")] {
        let name = directory.join(root).join("src/imp.k");
        write_compiled_source(
            name.to_str().expect("a UTF-8 path"),
            IMP.source,
            IMP.main_module,
            &directory.join(compiled),
        );
    }
    // `if-false` (line 78): a witness needs x > y.
    let found = krust_fuzz(
        &directory,
        &[
            "--campaign",
            "le.toml",
            "--definition",
            "imp-a",
            "--reach-rule",
            "imp.k:78",
            "--witness",
            "witness.json",
            "--no-shrink",
        ],
    );
    assert_eq!(found.status.code(), Some(0), "{}", text(&found.stderr));
    let recorded: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(directory.join("witness.json")).unwrap())
            .expect("the witness file is JSON");
    let source = &recorded["report"]["identity"]["target-rule"]["name"]["locations"][0]["source"];
    assert!(
        source
            .as_str()
            .is_some_and(|source| source.ends_with("/A/src/imp.k")),
        "the target rule is named where it was compiled: {source}"
    );
    let replay = krust_fuzz(
        &directory,
        &["--replay", "witness.json", "--definition", "imp-b"],
    );
    let stdout = text(&replay.stdout);
    assert_eq!(
        replay.status.code(),
        Some(0),
        "{stdout}{}",
        text(&replay.stderr)
    );
    assert!(stdout.contains("first witness: reproduced"), "{stdout}");
}

/// FZ-SETUP: a grammar change the frontend digest caught when it hashed the definition's
/// `Debug` rendering is still caught. Making `-` right-associative changes how `a - b - c`
/// parses, so a program can assemble into another initial configuration.
#[test]
fn a_replay_on_a_changed_grammar_is_refused() {
    let directory = le_workspace("grammar");
    let output = krust_fuzz(
        &directory,
        &[
            "--campaign",
            "le.toml",
            "--witness",
            "witness.json",
            "--no-shrink",
        ],
    );
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    let production = r#"| AExp "-" AExp              [symbol(_-_), left,"#;
    assert_eq!(IMP.source.matches(production).count(), 1);
    let source = IMP.source.replace(
        production,
        r#"| AExp "-" AExp              [symbol(_-_), right,"#,
    );
    write_compiled_source(
        IMP.file,
        &source,
        IMP.main_module,
        &directory.join("imp-right"),
    );
    let refused = krust_fuzz(
        &directory,
        &["--replay", "witness.json", "--definition", "imp-right"],
    );
    let stderr = text(&refused.stderr);
    assert_eq!(refused.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("identity mismatch: definitions[0].frontend-digest"),
        "{stderr}"
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

    // The summary of a differential witness (FZ-POLISH S10, S-T7): the kind of kill, the
    // instantiated program, both sides' ends as K text with the killing one marked, and a krun
    // line per side.
    let summary = krust_fuzz(
        &directory,
        &[
            "--campaign",
            "flip.toml",
            "--definition",
            "coin",
            "--program",
            "flip.pgm",
            "--mutant",
            "coin-kill",
        ],
    );
    let stdout = text(&summary.stdout);
    assert_eq!(summary.status.code(), Some(0), "{stdout}");
    for needle in [
        "kill: added end",
        "program:\n  flip(",
        "baseline ends: 2\n",
        "mutant ends: 1\n",
        "  end 0 (the killing end):\n",
        "<out>",
        "krun (baseline): krust krun --definition <definition-dir> ",
        " --strategy all ",
        "krun (mutant): krust krun --definition <mutant-dir> ",
        " -e 'flip(",
    ] {
        assert!(stdout.contains(needle), "{needle}: {stdout}");
    }
    assert!(
        !stdout.contains("\\dv{"),
        "the ends print as K text: {stdout}"
    );

    let (status, report) = json_run(&directory, &args("coin-layout"));
    assert_eq!(status, Some(1), "no witness exits 1");
    assert_eq!(report.outcome, CampaignOutcome::Equivalent);
}

/// FZ-POLISH: a differential campaign on definitions whose critical-pair checks report a pair
/// is not comparable at setup: no case runs, the summary leads with why and lists the finding
/// as genuine with its instance and its name, and `--assume-joined` with those names makes the
/// cases run under the stated premise.
#[test]
fn a_not_comparable_campaign_says_why_and_assume_joined_runs_it() {
    let program = R3_PLAINQ.program("r3-plainq/go.pgm").text;
    let campaign = r#"
seed = 7
cases = 4

[[hole]]
name = "N"
sort = "Int"
literal = "3"
"#;
    let directory = workspace(
        "not-comparable",
        &[("b-kompiled", &R3_PLAINQ), ("m-kompiled", &R3_PLAINQ_M)],
        &[("go.pgm", program), ("d.toml", campaign)],
    );
    let base = [
        "--campaign",
        "d.toml",
        "--definition",
        "b-kompiled",
        "--mutant",
        "m-kompiled",
        "--program",
        "go.pgm",
    ];
    let output = krust_fuzz(&directory, &base);
    let summary = text(&output.stdout);
    assert_eq!(
        output.status.code(),
        Some(1),
        "{summary}{}",
        text(&output.stderr)
    );
    assert!(summary.starts_with("not comparable"), "{summary}");
    assert!(summary.contains("cases: 0"), "{summary}");
    assert!(summary.contains("no kill can be established"), "{summary}");
    assert!(
        summary.contains("baseline critical-pair findings: 1 genuine, 0 undecided"),
        "{summary}"
    );
    assert!(summary.contains("[genuine]"), "{summary}");
    assert!(summary.contains("name: b.k:"), "{summary}");
    assert!(!summary.contains("Lbl"), "{summary}");
    let (_, report) = json_run(&directory, &[&base[..], &["--json"]].concat());
    let names = report
        .definition_findings
        .iter()
        .filter_map(|finding| finding.name.clone())
        .collect::<Vec<_>>();
    assert_eq!(names.len(), 2, "{:?}", report.definition_findings);
    let mut args = base.to_vec();
    for name in &names {
        args.extend(["--assume-joined", name.as_str()]);
    }
    args.push("--json");
    let (status, report) = json_run(&directory, &args);
    assert_eq!(status, Some(0), "{:?}", report.outcome);
    assert_eq!(report.identity.options.assume_joined, names);
    let refused = krust_fuzz(
        &directory,
        &[&base[..], &["--assume-joined", "b.k:1:1,b.k:2:1@root"]].concat(),
    );
    assert_eq!(refused.status.code(), Some(2), "{}", text(&refused.stderr));
    assert!(
        text(&refused.stderr).contains("matches no unjoined pair"),
        "{}",
        text(&refused.stderr)
    );
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
        .env(FUZZ_PARENT_BUILD_ENV, k_rust::build_identity())
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

/// Round 2, S2: every identity field the report holds is compared. A comment appended to the
/// compiled `macros.kore` keeps the execution digest but is another assembly input (D22).
#[test]
fn a_replay_on_changed_macros_is_refused() {
    let directory = le_workspace("macros");
    let output = krust_fuzz(
        &directory,
        &[
            "--campaign",
            "le.toml",
            "--witness",
            "witness.json",
            "--no-shrink",
        ],
    );
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    write_compiled(&IMP, &directory.join("imp-macros"));
    let macros = directory.join("imp-macros/macros.kore");
    let text_before = fs::read_to_string(&macros).unwrap();
    fs::write(&macros, format!("{text_before}\n// a comment\n")).unwrap();
    let refused = krust_fuzz(
        &directory,
        &["--replay", "witness.json", "--definition", "imp-macros"],
    );
    let stderr = text(&refused.stderr);
    assert_eq!(refused.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("identity mismatch: definitions[0].syntax-definition-digest"),
        "{stderr}"
    );
}

/// Round 2, S3: the recorded k-rust revision distinguishes source trees without any variable
/// set at build time.
#[test]
fn the_k_rust_revision_names_the_source_tree() {
    let identity = k_rust::build_identity();
    assert!(identity.contains("+src."), "{identity}");
    let directory = le_workspace("revision");
    let (_, report) = json_run(
        &directory,
        &["--campaign", "le.toml", "--cases", "1", "--json"],
    );
    assert_eq!(report.identity.k_rust_revision, identity);
    let version = krust_fuzz(&directory, &["--version"]);
    assert!(
        text(&version.stdout).contains(&identity),
        "--version names the k-rust build: {}",
        text(&version.stdout)
    );
}

/// Round 2, S4: an unwritable output path is refused before the campaign runs.
#[test]
fn an_unwritable_output_path_is_refused_before_the_campaign() {
    let directory = le_workspace("unwritable");
    // With `--cases 1` the campaign finds no witness, so before round 2 the witness path was
    // never written and the bad path went unnoticed (exit 1).
    for flag in ["--report", "--witness"] {
        let output = krust_fuzz(
            &directory,
            &[
                "--campaign",
                "le.toml",
                "--cases",
                "1",
                flag,
                "missing-directory/out.json",
            ],
        );
        let stderr = text(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{flag}: {stderr}");
        assert!(
            stderr.contains("missing-directory/out.json"),
            "{flag}: {stderr}"
        );
        assert!(text(&output.stdout).is_empty(), "{flag}: nothing ran");
    }
}

/// Round 2, N7: a run that finds no witness does not leave an older witness at its path.
#[test]
fn a_run_without_a_witness_removes_a_stale_witness_file() {
    let directory = le_workspace("stale");
    let found = krust_fuzz(
        &directory,
        &["--campaign", "le.toml", "--witness", "w.json"],
    );
    assert_eq!(found.status.code(), Some(0), "{}", text(&found.stderr));
    assert!(directory.join("w.json").is_file());
    let none = krust_fuzz(
        &directory,
        &[
            "--campaign",
            "le.toml",
            "--cases",
            "1",
            "--witness",
            "w.json",
        ],
    );
    assert_eq!(none.status.code(), Some(1), "{}", text(&none.stderr));
    assert!(
        !directory.join("w.json").exists(),
        "the stale witness is removed"
    );
}

/// Round 2, notes N4 and N5: refused option combinations, and flags that switch off what the
/// campaign file switched on.
#[test]
fn contradictory_options_are_refused_and_flags_switch_off_the_file() {
    let directory = le_workspace("options");
    let refused = |args: &[&str], needle: &str| {
        let output = krust_fuzz(&directory, &[&["--campaign", "le.toml"][..], args].concat());
        let stderr = text(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{args:?}: {stderr}");
        assert!(stderr.contains(needle), "{args:?}: {stderr}");
    };
    refused(&["--safety-limit", "0"], "safety limit");
    refused(&["--rule-mode", "covered"], "--rule-mode");
    refused(&["--reach-rule", "assign", "--at", "any-state"], "--at");
    fs::write(
        directory.join("all.toml"),
        format!("{}\n[options]\npaths = \"all-paths\"\n", le_campaign()),
    )
    .unwrap();
    let (_, report) = json_run(
        &directory,
        &[
            "--campaign",
            "all.toml",
            "--cases",
            "1",
            "--one-path",
            "--json",
        ],
    );
    assert_eq!(
        report.identity.options.paths,
        k_rust_fuzz::PathMode::OnePath
    );
    let plain = krust_fuzz(
        &directory,
        &["--campaign", "le.toml", "--no-negated-property"],
    );
    let stdout = text(&plain.stdout);
    assert!(stdout.starts_with("witness found\n"), "{stdout}");
    // The file's pattern matched at any state: only an end has an empty `<k>`, so its ends
    // reach it as before.
    let any_state = krust_fuzz(
        &directory,
        &[
            "--campaign",
            "le.toml",
            "--no-negated-property",
            "--at",
            "any-state",
        ],
    );
    let stdout = text(&any_state.stdout);
    assert!(stdout.starts_with("witness found\n"), "{stdout}");
}

/// FZ-POLISH S6: a pattern that does not compile is refused naming where it came from (the
/// campaign file's key or the flag), with its position in the pattern's own text, never
/// krun's `<command line>`.
#[test]
fn a_pattern_refusal_names_where_the_pattern_came_from() {
    let directory = le_workspace("pattern-origin");
    let broken = le_campaign().replace(LE_VIOLATION, "<k> .K </k> <state> r |-> R </state>");
    fs::write(directory.join("broken.toml"), broken).unwrap();
    let refused = |args: &[&str], needles: &[&str]| {
        let output = krust_fuzz(&directory, args);
        let stderr = text(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{args:?}: {stderr}");
        for needle in needles {
            assert!(stderr.contains(needle), "{args:?}: {stderr}");
        }
        assert!(!stderr.contains("<command line>"), "{args:?}: {stderr}");
    };
    refused(
        &["--campaign", "broken.toml"],
        &["`pattern` of `[target]` in broken.toml", "line 1, column"],
    );
    refused(
        &[
            "--campaign",
            "le.toml",
            "--pattern",
            "<k> .K </k> <state> r |-> R </state>",
        ],
        &["--pattern", "line 1, column"],
    );
    refused(
        &[
            "--campaign",
            "le.toml",
            "--normal-end",
            "<k> .K </k> <nope> </nope>",
        ],
        &["--normal-end"],
    );
}

/// Round 2, S1 and N2: a missing or non-executable `krust-fuzz` is an error (exit 2), never
/// the "no witness" status 1; a non-executable candidate on PATH is skipped; a leading `--`
/// reaches `krust-fuzz`.
#[test]
fn krust_fuzz_lookup_failures_are_errors_and_arguments_pass_unchanged() {
    let krust_fuzz = Path::new(env!("CARGO_BIN_EXE_krust-fuzz"));
    let krust = krust_fuzz.with_file_name(format!("krust{}", std::env::consts::EXE_SUFFIX));
    assert!(
        krust.is_file(),
        "`{}` is missing; see krust_fuzz_help_reaches_krust_fuzz",
        krust.display()
    );
    let directory = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("cli")
        .join("lookup");
    let _ = fs::remove_dir_all(&directory);
    for sub in ["bin", "plain", "script"] {
        fs::create_dir_all(directory.join(sub)).unwrap();
    }
    // A krust with no krust-fuzz beside it.
    let lonely = directory.join("bin/krust");
    fs::hard_link(&krust, &lonely)
        .or_else(|_| fs::copy(&krust, &lonely).map(|_| ()))
        .unwrap();
    fs::write(directory.join("plain/krust-fuzz"), "not a program\n").unwrap();
    let script = directory.join("script/krust-fuzz");
    fs::write(&script, "#!/bin/sh\nprintf '%s\\n' \"$@\"\nexit 7\n").unwrap();
    {
        use std::os::unix::fs::PermissionsExt as _;
        fs::set_permissions(&script, fs::Permissions::from_mode(0o755)).unwrap();
        fs::set_permissions(
            directory.join("plain/krust-fuzz"),
            fs::Permissions::from_mode(0o644),
        )
        .unwrap();
    }
    let run = |path: &str, args: &[&str]| {
        Command::new(&lonely)
            .args(args)
            .env("PATH", path)
            .stdin(Stdio::null())
            .output()
            .expect("krust runs")
    };
    let plain = directory.join("plain").display().to_string();
    let scripted = directory.join("script").display().to_string();
    let missing = run(&plain, &["fuzz", "--help"]);
    assert_eq!(missing.status.code(), Some(2), "{}", text(&missing.stderr));
    let found = run(
        &format!("{plain}:{scripted}"),
        &["fuzz", "--", "--x", "a b"],
    );
    assert_eq!(found.status.code(), Some(7), "{}", text(&found.stderr));
    assert_eq!(text(&found.stdout), "--\n--x\na b\n");
}

/// Round 3, R3: a run records this build's identity; neither a flag nor the campaign file can
/// name another revision.
#[test]
fn the_k_rust_revision_cannot_be_named_by_hand() {
    let directory = le_workspace("named-revision");
    let flag = krust_fuzz(
        &directory,
        &["--campaign", "le.toml", "--k-rust-revision", "0.8.0+src.0"],
    );
    assert_eq!(flag.status.code(), Some(2), "{}", text(&flag.stderr));
    fs::write(
        directory.join("named.toml"),
        format!("k-rust-revision = \"0.8.0+src.0\"\n{}", le_campaign()),
    )
    .unwrap();
    let key = krust_fuzz(&directory, &["--campaign", "named.toml"]);
    let stderr = text(&key.stderr);
    assert_eq!(key.status.code(), Some(2), "{stderr}");
    assert!(stderr.contains("k-rust-revision"), "{stderr}");
}

/// Round 3: one path for the report and the witness would let a run without a witness remove
/// the report it just wrote.
#[test]
fn the_report_and_the_witness_need_different_paths() {
    let directory = le_workspace("same-path");
    let output = krust_fuzz(
        &directory,
        &[
            "--campaign",
            "le.toml",
            "--report",
            "out.json",
            "--witness",
            "./out.json",
        ],
    );
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    assert!(stderr.contains("same file"), "{stderr}");
    assert!(text(&output.stdout).is_empty(), "nothing ran");
}

/// A witness file holds the report's hole values, which may nest up to
/// `values::MAX_VALUE_DEPTH` levels, deeper than `serde_json`'s default recursion limit of 128;
/// the file is read as the report is (`FuzzReport::from_json`), with that limit lifted.
#[test]
fn a_witness_holding_a_deeply_nested_value_reads_back() {
    let directory = le_workspace("deep-witness");
    let output = krust_fuzz(
        &directory,
        &["--campaign", "le.toml", "--witness", "witness.json"],
    );
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    let mut recorded: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(directory.join("witness.json")).unwrap())
            .expect("the witness file is JSON");
    // 200 list levels, two JSON levels each.
    let mut deep = serde_json::json!({ "int": "0" });
    for _ in 0..200 {
        deep = serde_json::json!({ "list": [deep] });
    }
    recorded["report"]["outcome"]["witness"]["first"]["holes"][0]["value"] = deep;
    fs::write(directory.join("deep.json"), recorded.to_string()).unwrap();
    let replay = krust_fuzz(&directory, &["--replay", "deep.json"]);
    let stderr = text(&replay.stderr);
    assert!(
        !stderr.contains("is not a krust-fuzz witness file"),
        "the witness file reads: {stderr}"
    );
}

/// A witness found with the dictionary replays on the build that found it: the dictionary's
/// parameters (`identity.dictionary`) only choose cases, as the proposers do, and a replay runs
/// the recorded case alone.
#[test]
fn a_witness_found_with_the_dictionary_replays() {
    let campaign = format!(
        "{}\n[proposers]\nweights = {{ blind = 1, dictionary = 1 }}\n",
        le_campaign()
    );
    let le = IMP.program("imp/le.imp").text;
    let directory = workspace(
        "dictionary-replay",
        &[("imp-kompiled", &IMP)],
        &[("le.imp", le), ("le.toml", &campaign)],
    );
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
    assert!(
        report.identity.dictionary.is_some(),
        "the report records the dictionary"
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
    assert!(!stdout.contains("forced"), "{stdout}");
}

/// A witness found with the climb replays on the build that found it: the climb's parameters
/// (`identity.climb`) only choose cases, and the condition records a climbing campaign asks for
/// change no other field of a result, so the replay, which asks for none, runs the same case.
#[test]
fn a_witness_found_with_the_climb_replays() {
    let campaign = le_campaign().replace(
        &format!("pattern = '{LE_VIOLATION}'\nnegated-property = true"),
        "rule = \"if-false\"",
    );
    assert!(campaign.contains("if-false"), "{campaign}");
    let campaign = format!("{campaign}\n[proposers]\nweights = {{ blind = 1, climb = 1 }}\n");
    let le = IMP.program("imp/le.imp").text;
    let directory = workspace(
        "climb-replay",
        &[("imp-kompiled", &IMP)],
        &[("le.imp", le), ("le.toml", &campaign)],
    );
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
    assert!(
        report.identity.climb.is_some(),
        "the report records the climb"
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
    assert!(!stdout.contains("forced"), "{stdout}");
}

/// A witness file is read only when its embedded report is a report this build reads: its
/// schema and version, not only the witness file's own.
#[test]
fn a_witness_whose_report_has_another_schema_or_version_is_refused() {
    let directory = le_workspace("report-version");
    let output = krust_fuzz(
        &directory,
        &["--campaign", "le.toml", "--witness", "witness.json"],
    );
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    let recorded: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(directory.join("witness.json")).unwrap())
            .expect("the witness file is JSON");
    for (field, value, expected) in [
        ("version", serde_json::json!(3), "version 3"),
        (
            "schema",
            serde_json::json!("something-else"),
            "something-else",
        ),
    ] {
        let mut tampered = recorded.clone();
        tampered["report"][field] = value;
        fs::write(directory.join("tampered.json"), tampered.to_string()).unwrap();
        let replay = krust_fuzz(&directory, &["--replay", "tampered.json", "--force"]);
        let stderr = text(&replay.stderr);
        assert_eq!(replay.status.code(), Some(2), "{field}: {stderr}");
        assert!(stderr.contains(expected), "{field}: {stderr}");
        assert!(stderr.contains("krust-fuzz-report"), "{field}: {stderr}");
    }
}

/// A witness of an older report version is refused by its version, before the report's fields
/// are read: an older report lacks fields this version requires and may hold fields it no
/// longer has, which would otherwise give a "missing field" or "unknown field" error instead of
/// the version (FZ-RULEREF review S4).
#[test]
fn a_witness_of_an_older_report_version_is_refused_by_its_version() {
    let directory = le_workspace("report-version-old");
    let output = krust_fuzz(
        &directory,
        &["--campaign", "le.toml", "--witness", "witness.json"],
    );
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    let mut old: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(directory.join("witness.json")).unwrap())
            .expect("the witness file is JSON");
    let previous = REPORT_VERSION - 1;
    old["report"]["version"] = serde_json::json!(previous);
    // Fields an older report does not have, and one it had that this version does not.
    let totals = old["report"]["totals"]
        .as_object_mut()
        .expect("the report has totals");
    totals.remove("unsupported-reasons");
    totals.remove("baseline-incomplete-reasons");
    totals["coverage"]
        .as_object_mut()
        .expect("the totals have coverage")
        .remove("names");
    old["report"]["retired-field"] = serde_json::json!(true);
    fs::write(directory.join("old.json"), old.to_string()).unwrap();
    let replay = krust_fuzz(&directory, &["--replay", "old.json"]);
    let stderr = text(&replay.stderr);
    assert_eq!(replay.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains(&format!(
            "holds a krust-fuzz-report version {previous} report; this krust-fuzz reads \
             krust-fuzz-report version {REPORT_VERSION}"
        )),
        "{stderr}"
    );
    assert!(!stderr.contains("field"), "{stderr}");
    // A witness file of another version of its own is refused by that version too.
    let mut other = old;
    other["version"] = serde_json::json!(0);
    fs::write(directory.join("other.json"), other.to_string()).unwrap();
    let replay = krust_fuzz(&directory, &["--replay", "other.json"]);
    let stderr = text(&replay.stderr);
    assert_eq!(replay.status.code(), Some(2), "{stderr}");
    assert!(stderr.contains("krust-fuzz-witness version 0"), "{stderr}");
}

/// FZ-STATESET (S8): version 9 judges all-paths rule, `final` pattern and comparability runs on
/// state sets, which report each distinct end once, where version 8 ran them as path sets; a
/// version-8 witness's final configurations, steps and reaching leaf need not be this build's,
/// so it is refused by its version, and the refusal says why. The refusal names those runs
/// only: a differential witness's sides were state sets before version 9 too, so it claims
/// no path set for every case.
#[test]
fn a_version_8_witness_is_refused_by_its_version_with_the_modality_change() {
    let directory = le_workspace("report-version-8");
    let output = krust_fuzz(
        &directory,
        &["--campaign", "le.toml", "--witness", "witness.json"],
    );
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    let mut old: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(directory.join("witness.json")).unwrap())
            .expect("the witness file is JSON");
    old["report"]["version"] = serde_json::json!(8);
    fs::write(directory.join("v8.json"), old.to_string()).unwrap();
    let replay = krust_fuzz(&directory, &["--replay", "v8.json", "--force"]);
    let stderr = text(&replay.stderr);
    assert_eq!(replay.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("holds a krust-fuzz-report version 8 report"),
        "{stderr}"
    );
    assert!(stderr.contains("state set"), "{stderr}");
    assert!(!stderr.contains("every case"), "{stderr}");
}

/// FZ-RULEREF: a workspace holding kink's IMP (`kink/examples/imp/imp.k`, the pl-tutorial
/// lesson whose expression rules carry no label), compiled as `krust kcompile imp.k` compiles
/// it, and `files`.
fn kink_imp_workspace(test: &str, files: &[(&str, &str)]) -> PathBuf {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../kink/examples/imp/imp.k");
    let source = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("cannot read `{}`: {error}", path.display()));
    let directory = workspace(test, &[], files);
    write_compiled_source("imp.k", &source, "IMP", &directory.join("imp-kompiled"));
    directory
}

/// The TRIAL2 campaign on kink's IMP (items 8 and 9): `program` with two `Int` holes, the rule
/// target `rule` in mode `covered` with run-to-completion.
fn kink_imp_campaign(program: &str, rule: &str, holes: [(&str, &str, &str); 2]) -> String {
    use std::fmt::Write as _;
    let mut text = format!(
        "definition = \"imp-kompiled\"\nprogram = \"{program}\"\nseed = 1\ncases = 100\n\
         [target]\nrule = \"{rule}\"\nmode = \"covered\"\nrun-to-completion = true\n\
         [options]\nmax-work = 20000\n"
    );
    for (name, find, literal) in holes {
        let _ = write!(
            text,
            "[[hole]]\nname = \"{name}\"\nsort = \"Int\"\nfind = \"{find}\"\n\
             literal = \"{literal}\"\nrange = {{ min = 0, max = 1000 }}\n"
        );
    }
    text
}

/// TRIAL2's `clamp` (item 8): rule 47 `- I1` fires only when `lo <= x` fails.
const CLAMP: &str = "// Clamp: r is x when x is at least lo, else -1.\nint x, lo, r;\nx = 7;\nlo = 3;\n\
                     if (lo <= x) { r = x; } else { r = -1; }\n";

/// TRIAL2's `guard` (item 9): rule 52 `false && _` fires only when `x <= 10` fails.
const GUARD: &str = "// Divide only when both operands are small.\nint x, y, r;\nx = 5;\ny = 8;\n\
                     if (x <= 10 && y <= 10) { r = x / y; } else { r = 0; }\n";

/// The report a `--json` run printed, as JSON.
fn json_value(output: &Output) -> serde_json::Value {
    serde_json::from_str(text(&output.stdout).trim()).unwrap_or_else(|error| {
        panic!(
            "no report ({error}); stdout: {}; stderr: {}",
            text(&output.stdout),
            text(&output.stderr)
        )
    })
}

/// The ids the report's coverage names with a location in a file ending with `file` that
/// starts on `line`.
fn named_ids(report: &serde_json::Value, file: &str, line: u64) -> Vec<String> {
    let names = report["totals"]["coverage"]["names"]
        .as_object()
        .unwrap_or_else(|| panic!("the coverage names no rule: {report}"));
    names
        .iter()
        .filter(|(_, name)| {
            name["locations"].as_array().is_some_and(|locations| {
                locations.iter().any(|location| {
                    location["source"]
                        .as_str()
                        .is_some_and(|source| source.ends_with(file))
                        && location["line"].as_u64() == Some(line)
                })
            })
        })
        .map(|(id, _)| id.clone())
        .collect()
}

/// FZ-RULEREF (DOGFOOD B2, TRIAL2): the uncovered unlabelled rules of TRIAL2's IMP corpus are
/// targeted from the command line, with no labelled copy of the definition, by the file and
/// start line kink lists, and by the unique id the report names them with.
#[test]
fn an_unlabelled_rule_is_targeted_by_source_line_or_unique_id() {
    let neg = kink_imp_campaign(
        "clamp.imp",
        "imp.k:47",
        [("X", "x = 7;", "7"), ("LO", "lo = 3;", "3")],
    );
    let and = kink_imp_campaign(
        "guard.imp",
        "imp.k:52",
        [("X", "x = 5;", "5"), ("Y", "y = 8;", "8")],
    );
    let directory = kink_imp_workspace(
        "rule-by-location",
        &[
            ("clamp.imp", CLAMP),
            ("guard.imp", GUARD),
            ("neg.toml", &neg),
            ("and.toml", &and),
        ],
    );
    for (campaign, line) in [("neg.toml", 47), ("and.toml", 52)] {
        let output = krust_fuzz(&directory, &["--campaign", campaign, "--json"]);
        assert_eq!(
            output.status.code(),
            Some(0),
            "{campaign}: {}",
            text(&output.stderr)
        );
        let report = json_value(&output);
        assert_eq!(report["outcome"]["status"], "witness-found", "{report}");
        let ids = named_ids(&report, "imp.k", line);
        assert_eq!(ids.len(), 1, "{campaign}: {report}");
        // The id the report names the rule with targets it too, from the flag.
        let by_id = krust_fuzz(
            &directory,
            &["--campaign", campaign, "--reach-rule", &ids[0], "--json"],
        );
        assert_eq!(
            by_id.status.code(),
            Some(0),
            "{campaign}: {}",
            text(&by_id.stderr)
        );
        assert_eq!(json_value(&by_id)["outcome"]["status"], "witness-found");
    }
    // The flag takes the location too, and replaces the file's rule.
    let output = krust_fuzz(
        &directory,
        &[
            "--campaign",
            "and.toml",
            "--reach-rule",
            "imp.k:47",
            "--json",
        ],
    );
    assert_eq!(output.status.code(), Some(1), "{}", text(&output.stderr));
    // A run without a witness still names the rule the reference resolved to (review S2).
    let report = json_value(&output);
    assert_eq!(report["outcome"]["status"], "no-witness-found", "{report}");
    let target = &report["identity"]["target-rule"];
    assert_eq!(target["name"]["locations"][0]["line"], 47, "{report}");
    assert_eq!(
        target["name"]["locations"][0]["reference"], "imp.k",
        "{report}"
    );
    let id = target["id"].as_str().expect("the target rule's id");
    let output = krust_fuzz(
        &directory,
        &["--campaign", "and.toml", "--reach-rule", "imp.k:47"],
    );
    let stdout = text(&output.stdout);
    assert!(
        stdout.starts_with(&format!(
            "no witness found\ntarget rule: imp.k:47 unique id {id}\n"
        )),
        "{stdout}"
    );
}

/// FZ-COMPARABLE-A: TRIAL2's hits on kink's IMP (rules 47 and 52) stay hits under
/// `--comparable`, and their witnesses carry a comparable judgement that holds: the programs are
/// deterministic and their runs end cleanly with no diagnostic.
#[test]
fn imp_rule_hits_stay_hits_under_comparable_end() {
    let neg = kink_imp_campaign(
        "clamp.imp",
        "imp.k:47",
        [("X", "x = 7;", "7"), ("LO", "lo = 3;", "3")],
    );
    let and = kink_imp_campaign(
        "guard.imp",
        "imp.k:52",
        [("X", "x = 5;", "5"), ("Y", "y = 8;", "8")],
    );
    let directory = kink_imp_workspace(
        "rule-comparable",
        &[
            ("clamp.imp", CLAMP),
            ("guard.imp", GUARD),
            ("neg.toml", &neg),
            ("and.toml", &and),
        ],
    );
    for campaign in ["neg.toml", "and.toml"] {
        let output = krust_fuzz(
            &directory,
            &["--campaign", campaign, "--comparable", "--json"],
        );
        assert_eq!(
            output.status.code(),
            Some(0),
            "{campaign}: {}",
            text(&output.stderr)
        );
        let report = json_value(&output);
        assert_eq!(report["outcome"]["status"], "witness-found", "{report}");
        let witness = &report["outcome"]["witness"];
        for case in [&witness["first"], &witness["shrunk"]] {
            if !case.is_null() {
                assert_eq!(
                    case["comparable"],
                    serde_json::json!({"holds": true, "reasons": []}),
                    "{campaign}: {report}"
                );
            }
        }
    }
}

/// A replay compares the target rule by its id only (FZ-RULEREF review I2): its name is read
/// from the definition's catalog, whose source paths say where the definition was compiled.
#[test]
fn a_rule_witness_replay_compares_the_target_rule_by_id() {
    let neg = kink_imp_campaign(
        "clamp.imp",
        "imp.k:47",
        [("X", "x = 7;", "7"), ("LO", "lo = 3;", "3")],
    );
    let directory = kink_imp_workspace(
        "rule-replay-id",
        &[("clamp.imp", CLAMP), ("neg.toml", &neg)],
    );
    let output = krust_fuzz(
        &directory,
        &["--campaign", "neg.toml", "--witness", "w.json"],
    );
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    let recorded: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(directory.join("w.json")).unwrap())
            .expect("the witness file is JSON");
    // Another path for the rule's source, as a definition compiled elsewhere records: the
    // witness still reproduces.
    let mut moved = recorded.clone();
    let location = &mut moved["report"]["identity"]["target-rule"]["name"]["locations"][0];
    location["source"] = serde_json::Value::String("/elsewhere/imp.k".to_owned());
    location["reference"] = serde_json::Value::String("elsewhere/imp.k".to_owned());
    fs::write(directory.join("moved.json"), moved.to_string()).unwrap();
    let replay = krust_fuzz(&directory, &["--replay", "moved.json"]);
    let stdout = text(&replay.stdout);
    assert_eq!(
        replay.status.code(),
        Some(0),
        "{stdout}{}",
        text(&replay.stderr)
    );
    assert!(stdout.contains("first witness: reproduced"), "{stdout}");
    // Another id is another rule: refused.
    let mut other = recorded;
    other["report"]["identity"]["target-rule"]["id"] = serde_json::Value::String("0".repeat(64));
    fs::write(directory.join("other.json"), other.to_string()).unwrap();
    let replay = krust_fuzz(&directory, &["--replay", "other.json"]);
    assert_eq!(replay.status.code(), Some(2), "{}", text(&replay.stdout));
    assert!(
        text(&replay.stdout).contains("target-rule.id")
            || text(&replay.stderr).contains("target-rule.id"),
        "{}{}",
        text(&replay.stdout),
        text(&replay.stderr)
    );
}

/// FZ-RULEREF: a source reference names the rule whose span holds the line, not only the rule
/// that starts on it (MAZE's `enter` spans lines 37 to 40).
#[test]
fn a_line_inside_a_multi_line_rule_names_that_rule() {
    let campaign = "program = \"walk.pgm\"\ndefinition = \"maze-kompiled\"\ncases = 5\n\
                    [[hole]]\nname = \"A\"\nsort = \"Int\"\nfind = \"walk(0,\"\nliteral = \"0\"\n";
    let directory = workspace(
        "rule-span",
        &[("maze-kompiled", &support::MAZE)],
        &[
            ("walk.pgm", support::MAZE.program("maze/walk.pgm").text),
            ("walk.toml", campaign),
        ],
    );
    // `37-40` is the range the summary prints for `enter` (FZ-RULEREF review I1): fed back, it
    // names the same rule.
    for line in ["37", "39", "40", "37-40"] {
        let rule = format!("maze.k:{line}");
        let output = krust_fuzz(
            &directory,
            &["--campaign", "walk.toml", "--reach-rule", &rule],
        );
        assert_eq!(
            output.status.code(),
            Some(0),
            "{rule}: {}",
            text(&output.stderr)
        );
        assert!(
            text(&output.stdout).contains("target rule: maze.k:37-40"),
            "{rule}: {}",
            text(&output.stdout)
        );
    }
    // A range that reaches past the rule its first line names may name another rule too: refused
    // before any case (INT7 review S3).
    let output = krust_fuzz(
        &directory,
        &["--campaign", "walk.toml", "--reach-rule", "maze.k:37-41"],
    );
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("lines 37-41 are not inside one rule") && stderr.contains("maze.k:37-40"),
        "{stderr}"
    );
}

/// FZ-RULEREF: an unknown rule reference is refused in words, with the candidates an author
/// can name instead.
#[test]
fn an_unknown_rule_reference_lists_candidates() {
    let div = IMP.program("imp/div.imp").text;
    let campaign = "definition = \"imp-kompiled\"\nprogram = \"div.imp\"\ncases = 5\n\
                    [[hole]]\nname = \"Y\"\nsort = \"Int\"\nfind = \"y = 2;\"\nliteral = \"2\"\n";
    let directory = workspace(
        "rule-unknown",
        &[("imp-kompiled", &IMP)],
        &[("div.imp", div), ("div.toml", campaign)],
    );
    let refused = |rule: &str, needles: &[&str]| {
        let output = krust_fuzz(
            &directory,
            &["--campaign", "div.toml", "--reach-rule", rule],
        );
        let stderr = text(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{rule}: {stderr}");
        assert!(!stderr.contains("UnknownRule"), "{rule}: {stderr}");
        for needle in needles {
            assert!(stderr.contains(needle), "{rule}: no `{needle}` in {stderr}");
        }
    };
    // The nearest labels, and the unlabelled rules' other names.
    refused(
        "asign",
        &["`asign`", "[IMP.assign]", "rewrite rules have no label"],
    );
    // The rules starting nearest a line between rules (55 is blank; 56 is `*`).
    refused(
        "imp.k:55",
        &["line 55 of `imp.k`", "\n  imp.k:56", "\n  imp.k:54"],
    );
    // A file that holds no rule: the files that do.
    refused(
        "nosuch.k:3",
        &["nosuch.k", "rules are written in:\n  imp.k"],
    );
    // An id of no catalog entry.
    refused(&"0".repeat(64), &["unique id", &"0".repeat(64)]);
}

/// FZ-RULEREF: the summary names the rules the campaign reached by source location and label.
#[test]
fn the_summary_names_the_rules_the_campaign_reached() {
    let div = IMP.program("imp/div.imp").text;
    let campaign = "definition = \"imp-kompiled\"\nprogram = \"div.imp\"\ncases = 5\n\
                    [target]\nrule = \"imp.k:57\"\n\
                    [[hole]]\nname = \"Y\"\nsort = \"Int\"\nfind = \"y = 2;\"\nliteral = \"2\"\n";
    let directory = workspace(
        "rule-summary",
        &[("imp-kompiled", &IMP)],
        &[("div.imp", div), ("div.toml", campaign)],
    );
    let output = krust_fuzz(&directory, &["--campaign", "div.toml"]);
    let stdout = text(&output.stdout);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{stdout}{}",
        text(&output.stderr)
    );
    for needle in [
        "target rule: imp.k:57 unique id",
        "\n  imp.k:73 [IMP.assign]",
    ] {
        assert!(stdout.contains(needle), "no `{needle}` in {stdout}");
    }
}

/// FZ-RULEREF review B1: a source position whose file names two files of the definition is
/// refused whatever the line. `a/rules.k` has a rule on line 5, where `b/rules.k` has a comment;
/// `rules.k:5` once resolved to `a`'s rule.
#[test]
fn a_file_that_names_two_files_is_refused_at_every_line() {
    let campaign = "definition = \"main-kompiled\"\nprogram = \"p.pgm\"\ncases = 5\n\
                    [[hole]]\nname = \"I\"\nsort = \"Int\"\nfind = \"3\"\nliteral = \"3\"\n";
    let directory = workspace(
        "rule-two-files",
        &[],
        &[
            ("p.pgm", include_str!("data/dup/p.pgm")),
            ("c.toml", campaign),
        ],
    );
    write_compiled_with(
        "dup/main.k",
        include_str!("data/dup/main.k"),
        "MAIN",
        &[
            ("a/rules.k", include_str!("data/dup/a/rules.k")),
            ("b/rules.k", include_str!("data/dup/b/rules.k")),
        ],
        &directory.join("main-kompiled"),
    );
    for rule in ["rules.k:5", "rules.k:7"] {
        let output = krust_fuzz(&directory, &["--campaign", "c.toml", "--reach-rule", rule]);
        let stderr = text(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{rule}: {stderr}");
        assert!(
            stderr.contains(
                "`rules.k` names 2 files of the definition; name one by a longer \
                             path:\n  a/rules.k\n  b/rules.k"
            ),
            "{rule}: {stderr}"
        );
    }
    let output = krust_fuzz(
        &directory,
        &["--campaign", "c.toml", "--reach-rule", "b/rules.k:5"],
    );
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    assert!(stderr.contains("\n  b/rules.k:7 unique id"), "{stderr}");
    let output = krust_fuzz(
        &directory,
        &["--campaign", "c.toml", "--reach-rule", "a/rules.k:5"],
    );
    let stdout = text(&output.stdout);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{stdout}{}",
        text(&output.stderr)
    );
    assert!(
        stdout.contains("\ntarget rule: a/rules.k:5 unique id "),
        "{stdout}"
    );
}

/// FZ-INCIDENTAL: a SIMPLE division by zero is stuck under the every-`<k>` default (SIMPLE's
/// `<k>` lies under the multiplicity cell `<thread>`), and the first such case is reported as
/// information: one summary line, and `incidental.stuck` in the report with the hole values, the
/// `<k>` item and a krun line.
#[test]
fn a_simple_division_by_zero_is_reported_as_an_incidental_stuck_case() {
    let campaign = "definition = \"simple-kompiled\"\nprogram = \"div.simple\"\nsort = \"Stmt\"\n\
                    seed = 1\ncases = 3\n[target]\nrule = \"simple.md:910\"\nmode = \"covered\"\n\
                    [options]\nmax-work = 50000\n\
                    [proposers]\nexplicit = [{ D = 0 }]\n\
                    [[hole]]\nname = \"D\"\nsort = \"Int\"\nfind = \"var d = 4;\"\nliteral = \"4\"\n\
                    range = { min = 0, max = 8 }\n";
    let directory = workspace(
        "incidental-simple",
        &[],
        &[
            ("div.simple", include_str!("data/simple/div.simple")),
            ("div.toml", campaign),
        ],
    );
    write_compiled_source(
        "simple/simple.md",
        include_str!("data/simple/simple.md"),
        "SIMPLE-UNTYPED",
        &directory.join("simple-kompiled"),
    );
    let output = krust_fuzz(&directory, &["--campaign", "div.toml"]);
    let stdout = text(&output.stdout);
    assert_eq!(
        output.status.code(),
        Some(1),
        "{stdout}{}",
        text(&output.stderr)
    );
    let lines: Vec<&str> = stdout
        .lines()
        .filter(|line| line.starts_with("incidental"))
        .collect();
    assert_eq!(lines.len(), 1, "{stdout}");
    assert!(
        lines[0].starts_with(
            "incidental (information, not a failure): case 1 (D = 0) got stuck before a natural \
             end"
        ) && lines[0].contains("at `10 / 0`"),
        "{stdout}"
    );
    let output = krust_fuzz(&directory, &["--campaign", "div.toml", "--json"]);
    let report = json_value(&output);
    assert_eq!(report["normal-end"]["baseline"], "every-k", "{report}");
    assert_eq!(report["totals"]["classes"]["stuck"], 1, "{report}");
    let stuck = &report["incidental"]["stuck"];
    assert_eq!(stuck["case"], 1, "{report}");
    assert_eq!(stuck["holes"][0]["value"]["int"], "0");
    assert_eq!(stuck["k-heads"], serde_json::json!(["10 / 0"]));
    let krun = stuck["krun-command"].as_str().expect("a krun line");
    assert!(krun.contains("var d = 0;"), "{krun}");
    assert_eq!(report["incidental"].get("undefined"), None);
}

/// A workspace for `test` with SIMPLE compiled to `simple-kompiled` and `files`.
fn simple_workspace(test: &str, files: &[(&str, &str)]) -> PathBuf {
    let directory = workspace(test, &[], files);
    write_compiled_source(
        "simple/simple.md",
        include_str!("data/simple/simple.md"),
        "SIMPLE-UNTYPED",
        &directory.join("simple-kompiled"),
    );
    directory
}

/// A SIMPLE campaign on `program` that targets a rule it never reaches, with `holes` (TOML).
fn simple_campaign(program: &str, holes: &str) -> String {
    format!(
        "definition = \"simple-kompiled\"\nprogram = \"{program}\"\nsort = \"Stmt\"\nseed = 1\n\
         cases = 3\n[target]\nrule = \"simple.md:910\"\nmode = \"covered\"\n[options]\n\
         max-work = 50000\n{holes}"
    )
}

/// FZ-INCIDENTAL review S4: under every-`<k>` a stuck configuration is stuck in every thread, so
/// the finding names the head of each non-empty `<k>`, in order: main waiting at `join` and the
/// spawned thread stopped at `10 / 0`.
#[test]
fn a_stuck_threaded_finding_names_every_threads_head() {
    let holes = "[proposers]\nexplicit = [{ D = 0 }]\n[[hole]]\nname = \"D\"\nsort = \"Int\"\n\
                 find = \"var d = 4;\"\nliteral = \"4\"\nrange = { min = 0, max = 8 }\n";
    let campaign = simple_campaign("join.simple", holes);
    let directory = simple_workspace(
        "incidental-join",
        &[
            ("join.simple", include_str!("data/simple/join.simple")),
            ("join.toml", &campaign),
        ],
    );
    let output = krust_fuzz(&directory, &["--campaign", "join.toml", "--json"]);
    let report = json_value(&output);
    let stuck = &report["incidental"]["stuck"];
    assert_eq!(stuck["case"], 1, "{report}");
    assert_eq!(
        stuck["k-heads"],
        serde_json::json!(["join 0 ;", "10 / 0"]),
        "{stuck}"
    );
}

/// FZ-INCIDENTAL review nit N2: a campaign without holes names no empty hole list.
#[test]
fn an_incidental_line_without_holes_lists_none() {
    let program = "function main() {\n  var d = 0;\n  print(7 / d, \"\\n\");\n}\n";
    let campaign = simple_campaign("zero.simple", "");
    let directory = simple_workspace(
        "incidental-no-holes",
        &[("zero.simple", program), ("zero.toml", &campaign)],
    );
    let output = krust_fuzz(&directory, &["--campaign", "zero.toml"]);
    let stdout = text(&output.stdout);
    let line = stdout
        .lines()
        .find(|line| line.starts_with("incidental"))
        .unwrap_or_else(|| panic!("no incidental line in {stdout}"));
    assert!(
        line.starts_with("incidental (information, not a failure): case 0 got stuck"),
        "{line}"
    );
}

/// FZ-INCIDENTAL review S2: `go(0)` branches to an undefined step (`a(0)`, `10 /Int 0`) and an
/// end (`b(0)`). krun reports an undefined step only when every path takes one, so the
/// all-paths finding says it is one path of several, and its krun line says krun will not show
/// it; on one path krun shows it, and the line carries no such note.
#[test]
fn an_undefined_finding_on_one_path_of_several_says_so() {
    let campaign = "definition = \"nd-kompiled\"\nprogram = \"nd.pgm\"\nseed = 1\ncases = 3\n\
                    [target]\npattern = '<k> .K </k> <out> X </out> requires X >Int 1000'\n\
                    [options]\nmax-work = 10000\n[proposers]\nexplicit = [{ N = 0 }]\n\
                    [[hole]]\nname = \"N\"\nsort = \"Int\"\nfind = \"go(3)\"\nliteral = \"3\"\n\
                    range = { min = 0, max = 50 }\n";
    let directory = workspace(
        "incidental-nd",
        &[],
        &[
            ("nd.pgm", include_str!("data/nd/nd.pgm")),
            ("nd.toml", campaign),
        ],
    );
    write_compiled_source(
        "nd/nd.k",
        include_str!("data/nd/nd.k"),
        "ND",
        &directory.join("nd-kompiled"),
    );
    let note = "krun reports an undefined step only when every path takes one";
    let output = krust_fuzz(
        &directory,
        &["--campaign", "nd.toml", "--json", "--all-paths"],
    );
    let report = json_value(&output);
    let undefined = &report["incidental"]["undefined"];
    assert_eq!(undefined["case"], 1, "{report}");
    assert_eq!(undefined["leaves"], 2, "{undefined}");
    let krun = undefined["krun-command"].as_str().expect("a krun line");
    assert!(
        krun.contains("--strategy all") && krun.contains(note),
        "{krun}"
    );
    // One trailing comment: the max-work note and the undefined-step note share it.
    assert_eq!(krun.matches('#').count(), 1, "{krun}");
    assert!(krun.contains("which krun cannot; krun reports"), "{krun}");
    let output = krust_fuzz(
        &directory,
        &["--campaign", "nd.toml", "--json", "--one-path"],
    );
    let report = json_value(&output);
    let undefined = &report["incidental"]["undefined"];
    assert_eq!(undefined["leaves"], 1, "{report}");
    let krun = undefined["krun-command"].as_str().expect("a krun line");
    assert!(!krun.contains(note), "{krun}");
}

/// FZ-RULEREF review S3: SIMPLE untyped (the pl-tutorial definition, without its `stream`
/// attributes), whose rules carry no label: TRIAL2 item 15's `popx`, which spans lines 915-916,
/// and the `try` rule, which spans 908-913, are reached by any of their lines.
#[test]
fn a_simple_rule_is_targeted_by_any_line() {
    let campaign = "definition = \"simple-kompiled\"\nprogram = \"exc.simple\"\nsort = \"Stmt\"\n\
                    seed = 1\ncases = 50\n[target]\nmode = \"covered\"\nrun-to-completion = true\n\
                    [options]\nmax-work = 50000\nnormal-end-pattern = \"<threads> .Bag </threads>\"\n\
                    [[hole]]\nname = \"TH\"\nsort = \"Int\"\nfind = \"x > 5\"\nliteral = \"5\"\n\
                    range = { min = 0, max = 20 }\n";
    let directory = workspace(
        "rule-simple",
        &[],
        &[
            ("exc.simple", include_str!("data/simple/exc.simple")),
            ("exc.toml", campaign),
        ],
    );
    write_compiled_source(
        "simple/simple.md",
        include_str!("data/simple/simple.md"),
        "SIMPLE-UNTYPED",
        &directory.join("simple-kompiled"),
    );
    for (rule, location) in [
        ("simple.md:915", "simple.md:915-916"),
        ("simple.md:916", "simple.md:915-916"),
        ("simple.md:910", "simple.md:908-913"),
    ] {
        let output = krust_fuzz(
            &directory,
            &["--campaign", "exc.toml", "--reach-rule", rule],
        );
        let stdout = text(&output.stdout);
        assert_eq!(
            output.status.code(),
            Some(0),
            "{rule}: {stdout}{}",
            text(&output.stderr)
        );
        assert!(
            stdout.contains(&format!("\ntarget rule: {location} unique id ")),
            "{stdout}"
        );
    }
}

/// The fenced blocks of the guide: (language, opening line, lines).
fn guide_blocks(guide: &str) -> Vec<(String, usize, Vec<&str>)> {
    let mut blocks = Vec::new();
    let mut open = None;
    for (index, line) in guide.lines().enumerate() {
        match (line.strip_prefix("```"), open.take()) {
            (Some(_), Some(block)) => blocks.push(block),
            (Some(info), None) => open = Some((info.to_owned(), index + 1, Vec::new())),
            (None, Some((info, at, mut lines))) => {
                lines.push(line);
                open = Some((info, at, lines));
            }
            (None, None) => {}
        }
    }
    blocks
}

/// The words of a guide command, single quotes grouping one.
fn guide_words(command: &str) -> Vec<String> {
    let mut words = Vec::new();
    let mut rest = command.trim();
    while !rest.is_empty() {
        if let Some(quoted) = rest.strip_prefix('\'') {
            let end = quoted.find('\'').expect("a closed quote");
            words.push(quoted[..end].to_owned());
            rest = quoted[end + 1..].trim_start();
        } else {
            let end = rest.find(char::is_whitespace).unwrap_or(rest.len());
            words.push(rest[..end].to_owned());
            rest = rest[end..].trim_start();
        }
    }
    words
}

/// fz26 FZ-GUIDE: the `krust` commands of the user guide, `docs/fuzzing.md`, run as written, in
/// order, and give the exit status and output lines the guide states. The guide's forms are those
/// kink-flow's `tests/guide.rs` documents and checks (it runs the guide's `kink-flow` blocks):
/// an `sh` block is `cp -r SOURCE DIRECTORY` (SOURCE a repository path), `cd DIRECTORY`,
/// `cat > FILE <<'EOF'` up to `EOF`, and commands with an optional trailing `# exit N`, a path
/// under `/tmp/` naming one under this test's scratch directory; a `text` block after it lists
/// lines of the last command's output, in order. `krust kcompile FILE -m MODULE -o DIRECTORY`
/// compiles in process as `krust kcompile` does (this package has no `krust` executable), and
/// `krust fuzz ARGS` runs `krust-fuzz ARGS`.
#[test]
fn the_guide_krust_commands_give_the_stated_outcomes() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let guide = fs::read_to_string(repository.join("docs/fuzzing.md")).expect("the guide reads");
    let scratch = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("cli")
        .join("guide");
    let _ = fs::remove_dir_all(&scratch);
    fs::create_dir_all(&scratch).expect("the scratch directory is created");
    let resolve = |cwd: &Path, word: &str| -> PathBuf {
        let path = match word.strip_prefix("/tmp/") {
            Some(rest) => scratch.join(rest),
            None => cwd.join(word),
        };
        assert!(path.starts_with(&scratch), "`{word}` is outside /tmp");
        path
    };
    let blocks = guide_blocks(&guide);
    let mut cwd = repository.clone();
    let mut stdout = String::new();
    let mut checked = 0;
    for (index, (language, at, lines)) in blocks.iter().enumerate() {
        let krust = lines
            .iter()
            .any(|line| line.split_whitespace().next() == Some("krust"));
        if language != "sh" || !krust {
            continue;
        }
        let mut lines = lines.iter();
        while let Some(line) = lines.next() {
            let (command, status) = match line.split_once(" # exit ") {
                Some((command, status)) => (command, status.trim().parse().unwrap()),
                None => (*line, 0),
            };
            let words = guide_words(command);
            let words = words.iter().map(String::as_str).collect::<Vec<_>>();
            match words.as_slice() {
                [] => {}
                ["cp", "-r", source, target] => {
                    let target = resolve(&cwd, target);
                    fs::create_dir_all(&target).unwrap();
                    for entry in fs::read_dir(repository.join(source)).unwrap() {
                        let entry = entry.unwrap();
                        assert!(entry.file_type().unwrap().is_file(), "{source} is flat");
                        fs::copy(entry.path(), target.join(entry.file_name())).unwrap();
                    }
                }
                ["cd", directory] => cwd = resolve(&cwd, directory),
                ["cat", ">", file, "<<'EOF'"] => {
                    let mut text = String::new();
                    for line in lines.by_ref().take_while(|line| **line != "EOF") {
                        text.push_str(line);
                        text.push('\n');
                    }
                    fs::write(resolve(&cwd, file), text).unwrap();
                }
                ["krust", "kcompile", file, "-m", module, "-o", directory] => {
                    let source = fs::read_to_string(cwd.join(file)).unwrap();
                    write_compiled_source(file, &source, module, &resolve(&cwd, directory));
                }
                ["krust", "fuzz", args @ ..] => {
                    assert!(
                        cwd.starts_with(&scratch),
                        "guide line {at}: `cd` into /tmp first"
                    );
                    let output = krust_fuzz(&cwd, args);
                    stdout = text(&output.stdout);
                    assert_eq!(
                        output.status.code(),
                        Some(status),
                        "guide line {at}: `{line}`: {stdout}{}",
                        text(&output.stderr)
                    );
                }
                _ => panic!("guide line {at}: `{line}` is none of the guide's forms"),
            }
        }
        let Some((language, at, excerpt)) = blocks.get(index + 1) else {
            continue;
        };
        assert_ne!(
            language, "json",
            "guide line {at}: `krust fuzz` prints text"
        );
        if language == "text" {
            let mut output = stdout.lines();
            for line in excerpt {
                assert!(
                    output.any(|out| out == *line),
                    "guide line {at}: `{line}` is not in the output (in order):\n{stdout}"
                );
            }
            checked += 1;
        }
    }
    assert!(checked >= 5, "{checked} excerpts checked");
}
