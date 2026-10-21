//! The golden determinism test (ARCHITECTURE 5.4, 9.3; finding T-15).
//!
//! The crate has no executable, so the test re-executes its own test binary
//! (`std::env::current_exe()`, `--exact golden_child`) twice, with different environments, and
//! requires the reports the two children print to be byte-identical to each other and to the
//! report of the parent process. The environments differ in every variable proptest reads, in
//! locale, time zone, home directory and backtrace settings: none of them may reach the report.
//!
//! The test also pins a fingerprint of the case sequence (each report's case-sequence digest,
//! witness values, case count, classes and rejections) for the current [`ENGINE_VERSION`], so that a change to the proposers,
//! the schedule or the generators that changes the sequence fails here until the version is
//! bumped and the fingerprint re-pinned. `KRUST_FUZZ_GOLDEN_PRINT=1` prints the fingerprint.

mod support;

use std::{collections::BTreeMap, process::Command, sync::Arc};

use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, ENGINE_VERSION,
    HoleDecl, HoleLocation, ProgramInput, ProposerConfig, SpanAddress, Target, TargetKind,
    report::{FuzzReport, digest_hex},
    spec::PathMode,
    spec::{DEFAULT_REJECTION_CAP, ProposerKind},
    target::{DifferentialTarget, PatternAt, PatternTarget, RuleMode, RuleRef, RuleTarget},
    values::{Constraints, GenerationBounds, IntRange},
};
use num_bigint::BigInt;
use support::{COIN, COIN_KILL, DICT, IMP, UNSIGNED};

/// The variable that makes [`golden_child`] run the campaigns and print their reports.
const CHILD: &str = "KRUST_FUZZ_GOLDEN_CHILD";
const BEGIN: &str = "=====BEGIN-KRUST-FUZZ-REPORTS=====";
const END: &str = "=====END-KRUST-FUZZ-REPORTS=====";

/// The pinned fingerprint of the golden campaigns' case sequence at [`ENGINE_VERSION`] 2.
/// Pinned at integration round 1, when the modules behind the engine landed; re-pin it, with
/// a version bump, only when the case sequence is meant to change. Version 2 (map holes shrink
/// by whole entries) leaves these Int-hole campaigns' sequences and shrunk witnesses as they
/// were, so the fingerprint is version 1's.
const PINNED: Option<(u32, &str)> = Some((
    2,
    "f903fed03207d94ac94a4beff8a2c72061a003ed4663e947d2926cde1e5d16e2",
));

/// The pinned fingerprint of the dictionary campaigns' case sequence (FZ-11) at
/// [`ENGINE_VERSION`] 2, the first version with the dictionary. A change of the dictionary's parameters (`report::DictionaryParameters`)
/// or of its harvest moves it: bump `ENGINE_VERSION` and re-pin both fingerprints.
const PINNED_DICTIONARY: Option<(u32, &str)> = Some((
    2,
    "174abe2bf3fcf2720866374ed6cbffa3c3141ab8cc3c2adb3d9f3e58ad71bd18",
));

/// How many of [`golden_reports`] are blind campaigns, fingerprinted by [`PINNED`]; the rest
/// enable the dictionary and are fingerprinted by [`PINNED_DICTIONARY`].
const BLIND_CAMPAIGNS: usize = 4;

fn int_hole(name: &str, program: &str, find: &str, literal: &str) -> HoleDecl {
    HoleDecl {
        name: name.into(),
        sort: "Int".into(),
        location: HoleLocation::Span(SpanAddress {
            program: program.into(),
            line: None,
            find: find.into(),
            literal: literal.into(),
        }),
        constraints: Constraints::default(),
        allow_refused_sort: false,
    }
}

/// A campaign on IMP's `program` whose target is a natural end matching `violation`; the
/// explicit proposer tries the anchors, then `explicit` (values of `Y`), before blind sampling.
fn spec(
    program: &str,
    holes: Vec<HoleDecl>,
    pattern: &str,
    explicit: &[i64],
    seed: u64,
) -> CampaignSpec {
    let compiled = IMP.compiled();
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(compiled.definition()),
            mutant: None,
        },
        program: ProgramInput::Source(compiled.program_source(program)),
        holes,
        target: violation(pattern),
        options: CaseOptions::default(),
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: explicit
                .iter()
                .map(|y| BTreeMap::from([("Y".to_owned(), k_rust_fuzz::Value::Int((*y).into()))]))
                .collect(),
            weights: ProposerConfig::default().weights,
        },
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed,
        identity: CallerIdentity {
            k_rust_revision: "fz26-golden".into(),
            thread_stack_size: None,
        },
    }
}

/// A pattern target over a clean final leaf, as a negated property.
fn violation(pattern: &str) -> Target {
    Target {
        kind: TargetKind::Pattern(PatternTarget {
            pattern: pattern.into(),
            at: PatternAt::Final,
        }),
        run_to_completion: false,
        negated_property: true,
    }
}

/// The golden campaigns, which between them exercise every part of the report:
/// - `le.imp`: a blind witness, confirmed and shrunk along its value trees;
/// - `commute.imp`: explicit assignments, then blind cases, and no witness;
/// - COIN against COIN-KILL in all-paths mode under a work budget: a differential witness with
///   both sides' leaves, and all-paths leaf order;
/// - UNSIGNED with a range that excludes the anchor and admits negative values, which do not
///   round-trip: rejections for two reasons;
/// - DICT's `goal` with blind and the dictionary: a witness of harvested values, shrunk by
///   moves;
/// - DICT's `probe` under a pattern target, with the dictionary alone: the pattern's own
///   constant;
/// - COIN against COIN-KILL with the dictionary: the rules that differ come first.
fn golden_reports() -> Vec<FuzzReport> {
    let le = spec(
        "imp/le.imp",
        vec![
            int_hole("X", "imp/le.imp", "x = 3;", "3"),
            int_hole("Y", "imp/le.imp", "y = 5;", "5"),
        ],
        r#"<k> .K </k> <state> (#token("r", "Id") |-> R:Int) _:Map </state> requires R =/=Int 1"#,
        &[],
        0x00c0_ffee,
    );
    let commute = spec(
        "imp/commute.imp",
        vec![
            int_hole("X", "imp/commute.imp", "x = 3;", "3"),
            int_hole("Y", "imp/commute.imp", "y = 5;", "5"),
        ],
        concat!(
            r#"<k> .K </k> <state> (#token("a", "Id") |-> A:Int) "#,
            r#"(#token("b", "Id") |-> B:Int) _:Map </state> requires A =/=Int B"#
        ),
        &[-1, 7],
        0x0bad_5eed,
    );
    let coin = {
        let baseline = COIN.compiled();
        let mut spec = spec("imp/le.imp", Vec::new(), "<k> .K </k>", &[], 0x0c01_0c01);
        spec.definitions = Definitions {
            baseline: Arc::new(baseline.definition()),
            mutant: Some(Arc::new(COIN_KILL.compiled().definition())),
        };
        spec.program = ProgramInput::Source(baseline.program_source("coin/flip.pgm"));
        spec.holes = vec![int_hole("N", "coin/flip.pgm", "3", "3")];
        spec.target = Target {
            kind: TargetKind::Differential(DifferentialTarget::default()),
            run_to_completion: false,
            negated_property: false,
        };
        spec.options.paths = PathMode::AllPaths;
        spec
    };
    let unsigned = {
        let compiled = UNSIGNED.compiled();
        let mut spec = spec("imp/le.imp", Vec::new(), "<k> .K </k>", &[], 0x0005_1673);
        spec.definitions = Definitions {
            baseline: Arc::new(compiled.definition()),
            mutant: None,
        };
        spec.program = ProgramInput::Source(compiled.program_source("unsigned/sum.pgm"));
        let mut hole = int_hole("B", "unsigned/sum.pgm", "5 ;", "5");
        hole.constraints.range = Some(IntRange {
            min: Some(BigInt::from(-40)),
            max: Some(BigInt::from(4)),
        });
        spec.holes = vec![hole];
        spec.target = violation("<k> .K </k> <out> ListItem(N:Int) </out> requires N ==Int 9");
        spec
    };
    let coin_spec = coin.clone();
    [
        (le, Budget::Cases(40)),
        (commute, Budget::Cases(24)),
        (coin, Budget::Work(4000)),
        (unsigned, Budget::Cases(30)),
    ]
    .into_iter()
    .chain(dictionary_campaigns(&coin_spec))
    .map(|(spec, budget)| {
        Campaign::new(spec)
            .expect("the golden campaign is valid")
            .run(budget, None)
    })
    .collect()
}

/// The golden campaigns that enable the dictionary (see [`golden_reports`]); `coin` is the
/// blind differential campaign, run again with the dictionary.
fn dictionary_campaigns(coin: &CampaignSpec) -> Vec<(CampaignSpec, Budget)> {
    let with_dictionary = |mut spec: CampaignSpec, weights: &[(ProposerKind, u32)]| {
        spec.proposers.weights = weights.iter().copied().collect();
        spec
    };
    let dict_goal = {
        let compiled = DICT.compiled();
        let mut spec = spec("imp/le.imp", Vec::new(), "<k> .K </k>", &[], 0x0d1c_7001);
        spec.definitions = Definitions {
            baseline: Arc::new(compiled.definition()),
            mutant: None,
        };
        spec.program = ProgramInput::Source(compiled.program_source("dict/run.pgm"));
        let mut text = int_hole("S", "dict/run.pgm", "\"shut\"", "\"shut\"");
        text.sort = "String".into();
        spec.holes = vec![int_hole("N", "dict/run.pgm", "run(3,", "3"), text];
        spec.target = Target {
            kind: TargetKind::Rule(RuleTarget {
                rule: RuleRef::Label("DICT.goal".into()),
                mode: RuleMode::Fired,
            }),
            run_to_completion: false,
            negated_property: false,
        };
        with_dictionary(
            spec,
            &[(ProposerKind::Blind, 1), (ProposerKind::Dictionary, 1)],
        )
    };
    let dict_pattern = {
        let compiled = DICT.compiled();
        let mut spec = spec(
            "imp/le.imp",
            Vec::new(),
            "<k> .K </k> <out> X:Int </out> requires X ==Int 9091",
            &[],
            0x0d1c_7002,
        );
        spec.definitions = Definitions {
            baseline: Arc::new(compiled.definition()),
            mutant: None,
        };
        spec.program = ProgramInput::Source(compiled.program_source("dict/probe.pgm"));
        spec.holes = vec![int_hole("N", "dict/probe.pgm", "run(5,", "5")];
        spec.target.negated_property = false;
        with_dictionary(spec, &[(ProposerKind::Dictionary, 1)])
    };
    let coin_dictionary = with_dictionary(
        {
            let mut spec = coin.clone();
            spec.seed = 0x0d1c_7003;
            spec
        },
        &[(ProposerKind::Blind, 1), (ProposerKind::Dictionary, 1)],
    );
    vec![
        (dict_goal, Budget::Cases(80)),
        (dict_pattern, Budget::Cases(80)),
        (coin_dictionary, Budget::Work(4000)),
    ]
}

fn render(reports: &[FuzzReport]) -> String {
    reports
        .iter()
        .map(FuzzReport::to_canonical_json)
        .collect::<Vec<_>>()
        .join("\n")
}

/// The case sequence's fingerprint: what the proposers and the schedule decide, without the
/// configurations and work counts that k-rust's own revision decides.
fn fingerprint(reports: &[FuzzReport]) -> String {
    let parts: Vec<String> = reports
        .iter()
        .map(|report| {
            let witness = report.witness().map(|witness| {
                let values = |case: &k_rust_fuzz::report::WitnessCase| {
                    case.holes
                        .iter()
                        .map(|hole| serde_json::to_string(&hole.value).expect("serializes"))
                        .collect::<Vec<_>>()
                        .join(",")
                };
                (values(&witness.first), witness.shrunk.as_ref().map(values))
            });
            format!(
                "{}|{}|{:?}|{}|{}",
                report.totals.cases,
                report.totals.case_sequence_digest,
                witness,
                serde_json::to_string(&report.totals.classes).expect("serializes"),
                serde_json::to_string(&report.totals.rejections).expect("serializes")
            )
        })
        .collect();
    digest_hex(parts.join("\n").as_bytes())
}

/// Runs the golden campaigns and prints their reports, only when [`CHILD`] is set; otherwise it
/// does nothing, so that an ordinary test run passes it.
#[test]
fn golden_child() {
    if std::env::var_os(CHILD).is_none() {
        return;
    }
    println!("{BEGIN}\n{}\n{END}", render(&golden_reports()));
}

fn child_reports(environment: &[(&str, Option<&str>)]) -> String {
    let executable = std::env::current_exe().expect("the test binary's path");
    let mut command = Command::new(executable);
    command
        .args(["--exact", "golden_child", "--nocapture", "--test-threads=1"])
        .env(CHILD, "1");
    for (name, value) in environment {
        match value {
            Some(value) => command.env(name, value),
            None => command.env_remove(name),
        };
    }
    let output = command.output().expect("the child runs");
    let stdout = String::from_utf8(output.stdout).expect("UTF-8");
    assert!(
        output.status.success(),
        "child failed: {stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let start = stdout.find(BEGIN).expect("the child printed its reports") + BEGIN.len();
    let end = stdout.find(END).expect("the child finished its reports");
    stdout[start..end].trim().to_owned()
}

#[test]
fn the_same_campaign_in_two_processes_gives_byte_identical_reports() {
    let quiet = [
        ("PROPTEST_CASES", None),
        ("PROPTEST_RNG_SEED", None),
        ("PROPTEST_RNG_ALGORITHM", None),
        ("PROPTEST_MAX_SHRINK_ITERS", None),
        ("PROPTEST_MAX_LOCAL_REJECTS", None),
        ("PROPTEST_MAX_GLOBAL_REJECTS", None),
        ("PROPTEST_FAILURE_PERSISTENCE", None),
        ("RUST_BACKTRACE", Some("0")),
        ("LC_ALL", Some("C")),
        ("TZ", Some("UTC")),
    ];
    let noisy = [
        ("PROPTEST_CASES", Some("3")),
        ("PROPTEST_RNG_SEED", Some("424242")),
        ("PROPTEST_RNG_ALGORITHM", Some("xs")),
        ("PROPTEST_MAX_SHRINK_ITERS", Some("1")),
        ("PROPTEST_MAX_LOCAL_REJECTS", Some("1")),
        ("PROPTEST_MAX_GLOBAL_REJECTS", Some("1")),
        ("PROPTEST_FAILURE_PERSISTENCE", Some("direct")),
        ("RUST_BACKTRACE", Some("full")),
        ("LC_ALL", Some("tr_TR.UTF-8")),
        ("TZ", Some("Pacific/Chatham")),
        ("HOME", Some("/nonexistent-krust-fuzz-home")),
    ];
    let first = child_reports(&quiet);
    let second = child_reports(&noisy);
    assert_eq!(first, second, "the environment reached the report");
    let reports = golden_reports();
    assert_eq!(render(&reports), first, "the parent's report differs");

    let computed = fingerprint(&reports[..BLIND_CAMPAIGNS]);
    let dictionary = fingerprint(&reports[BLIND_CAMPAIGNS..]);
    if std::env::var_os("KRUST_FUZZ_GOLDEN_PRINT").is_some() {
        eprintln!("golden fingerprint at engine version {ENGINE_VERSION}: {computed}");
        eprintln!("dictionary fingerprint at engine version {ENGINE_VERSION}: {dictionary}");
    }
    match PINNED_DICTIONARY {
        Some((version, pinned)) => {
            assert_eq!(
                version, ENGINE_VERSION,
                "ENGINE_VERSION changed: re-pin the dictionary fingerprint for the new version"
            );
            assert_eq!(
                dictionary, pinned,
                "the dictionary's case sequence changed (its parameters or its harvest) \
                 without an ENGINE_VERSION bump"
            );
        }
        None => panic!(
            "no dictionary fingerprint is pinned for engine version {ENGINE_VERSION}; pin \
             Some(({ENGINE_VERSION}, \"{dictionary}\")) in tests/golden.rs"
        ),
    }
    match PINNED {
        Some((version, pinned)) => {
            assert_eq!(
                version, ENGINE_VERSION,
                "ENGINE_VERSION changed: re-pin the fingerprint for the new version"
            );
            assert_eq!(
                computed, pinned,
                "the case sequence changed without an ENGINE_VERSION bump"
            );
        }
        None => panic!(
            "no fingerprint is pinned for engine version {ENGINE_VERSION}; pin \
             Some(({ENGINE_VERSION}, \"{computed}\")) in tests/golden.rs"
        ),
    }
}
