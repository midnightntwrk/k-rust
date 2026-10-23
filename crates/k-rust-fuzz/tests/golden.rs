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
    HoleDecl, HoleLocation, ProgramInput, ProgramSource, ProposerConfig, SpanAddress, Target,
    TargetKind,
    report::{FuzzReport, digest_hex},
    spec::PathMode,
    spec::{DEFAULT_REJECTION_CAP, ProgramText, ProposerKind},
    target::{DifferentialTarget, PatternAt, PatternTarget, RuleMode, RuleRef, RuleTarget},
    values::{Constraints, ElementSorts, GenerationBounds, IntRange},
};
use num_bigint::BigInt;
use support::{COIN, COIN_KILL, DICT, IMP, LOCK, MAZE, UNSIGNED, VALUES};

/// The variable that makes [`golden_child`] run the campaigns and print their reports.
const CHILD: &str = "KRUST_FUZZ_GOLDEN_CHILD";
const BEGIN: &str = "=====BEGIN-KRUST-FUZZ-REPORTS=====";
const END: &str = "=====END-KRUST-FUZZ-REPORTS=====";

/// The pinned fingerprint of the golden campaigns' case sequence at [`ENGINE_VERSION`] 4.
/// Pinned at integration round 1, when the modules behind the engine landed; re-pin it, with
/// a version bump, only when the case sequence is meant to change. Version 2 left the four
/// Int-hole campaigns' fingerprint as it was at version 1 (`f903fed0…`), and added the map
/// campaign, whose shrunk witness guards version 2's shrinking of map holes by whole entries:
/// a change to the map shrinker moves it. Version 3 (the run-time literals and the corpus's
/// count buckets) left it as it was at version 2: blind campaigns record no conditions and ask
/// for no counts. FZ-INTGEN moved it (from `3467dc44…`) through the UNSIGNED campaign alone:
/// its hole's range `-40 ..= 4` is generated as `0 ..= 4`, since UNSIGNED's literals read no
/// negative value back, and the campaign tries one explicit negative value so that it keeps a
/// round-trip rejection. Version 4 (phase 5, whose other changes move no golden campaign) re-pins
/// it by recomputation with the same digest.
const PINNED: Option<(u32, &str)> = Some((
    4,
    "78acdd4634fdfb3f7122ba61f905123719610d56f4356d1909d849530e1d2a13",
));

/// The pinned fingerprint of the dictionary campaigns' case sequence (FZ-11) at
/// [`ENGINE_VERSION`] 4. Version 2 was the first version with the dictionary; versions 3 and 4
/// left the fingerprint as it was, since the dictionary draws no run-time literals and asks for
/// no counts, and no phase-5 change moves its campaigns. A change of the dictionary's parameters
/// (`report::DictionaryParameters`) or of its harvest moves it: bump `ENGINE_VERSION` and re-pin
/// both fingerprints.
const PINNED_DICTIONARY: Option<(u32, &str)> = Some((
    4,
    "174abe2bf3fcf2720866374ed6cbffa3c3141ab8cc3c2adb3d9f3e58ad71bd18",
));

/// The pinned fingerprint of the climb campaign's case sequence (FZ-12), at [`ENGINE_VERSION`]
/// 4. The climb came in within version 2; version 3 moved this fingerprint (from `3c303ba3…`)
/// because the climb now changes its incumbent from the run-time literals of the guards it
/// refuted (FZ-16); version 4 left it as it was. A change of the climb's parameters
/// (`report::ClimbParameters`), of its moves or of the scores it climbs moves it: bump
/// `ENGINE_VERSION` and re-pin every fingerprint.
const PINNED_CLIMB: Option<(u32, &str)> = Some((
    4,
    "81695de9cdab5c23e5be7b35a9c68817ed07904f54c038ab6c0bc57a862149cf",
));

/// The pinned fingerprint of the corpus campaign's case sequence (FZ-14), at [`ENGINE_VERSION`]
/// 4 (unmoved from version 3). The corpus came in within version 2; version 3 moved this
/// fingerprint (from `1e959791…`) because the corpus now changes kept cases, and follows up its own
/// missed case, from the run-time literals of the guards they refuted (FZ-16). The corpus's count
/// buckets (FZ-17) do not move it: on the lock every rule applies at most once per run, so no count
/// reaches a bucket beyond 1 and no case is kept for its counts alone. A change of the corpus's
/// parameters (`report::CorpusParameters`), of its mutations or of the harvest it draws literals
/// from moves it: bump `ENGINE_VERSION` and re-pin every fingerprint.
const PINNED_CORPUS: Option<(u32, &str)> = Some((
    4,
    "ace0f86bbab3b028bd4c5ce24f9dbdd7007c66ca8c37326a54deea3be937ddb2",
));

/// The pinned fingerprint of the solve campaign's case sequence (FZ-15), in builds with the `z3`
/// feature, at [`ENGINE_VERSION`] 4. The solve proposer came in within version 2; versions 3
/// and 4 left the fingerprint as it was (the solving campaign weighs neither the climb nor the
/// corpus, so it draws no run-time literals and asks for no counts; and a Z3 context per query,
/// which changes no answer a fresh process gives, moved nothing). A change of its parameters
/// (`report::SolveParameters`), of its trigger or of the condition records it reads moves it: bump
/// `ENGINE_VERSION` and re-pin every fingerprint.
#[cfg(feature = "z3")]
const PINNED_SOLVE: Option<(u32, &str)> = Some((
    4,
    "1db20f24905eefd79e9ec7b3cc4b7ce634c12838eb34d27810e6a1071d76e29e",
));

/// How many of [`golden_reports`], at the end, enable the solve proposer: one in builds with the
/// `z3` feature, none otherwise.
const SOLVE_CAMPAIGNS: usize = if cfg!(feature = "z3") { 1 } else { 0 };

/// How many of [`golden_reports`] are blind campaigns, fingerprinted by [`PINNED`]; the
/// dictionary campaigns follow, fingerprinted by [`PINNED_DICTIONARY`], then the climb campaigns
/// ([`CLIMB_CAMPAIGNS`]), fingerprinted by [`PINNED_CLIMB`], then the corpus campaigns
/// ([`CORPUS_CAMPAIGNS`]), fingerprinted by [`PINNED_CORPUS`], and the solve campaigns last
/// ([`SOLVE_CAMPAIGNS`], in builds with the `z3` feature), checked by `check_solve`.
const BLIND_CAMPAIGNS: usize = 5;

/// How many of [`golden_reports`], before the corpus campaigns, enable the climb.
const CLIMB_CAMPAIGNS: usize = 1;

/// How many of [`golden_reports`], before the solve campaigns, enable the corpus.
const CORPUS_CAMPAIGNS: usize = 1;

/// The index of the map campaign in [`golden_reports`].
const MAP_CAMPAIGN: usize = 4;

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
        data_end: true,
    }
}

/// The golden campaigns, which between them exercise every part of the report:
/// - `le.imp`: a blind witness, confirmed and shrunk along its value trees;
/// - `commute.imp`: explicit assignments, then blind cases, and no witness;
/// - COIN against COIN-KILL in all-paths mode under a work budget: a differential witness with
///   both sides' leaves, and all-paths leaf order;
/// - UNSIGNED with a range that excludes the anchor and admits negative values, which do not
///   round-trip there, so generation starts at 0 (FZ-INTGEN), and an explicit negative value,
///   which the declared range admits: rejections for two reasons (the anchor's constraint and
///   the explicit value's round-trip);
/// - VALUES with a `Map` configuration-variable hole and a target that needs three entries: a
///   map witness that shrinks by whole entries (`ENGINE_VERSION` 2);
/// - DICT's `goal` with blind and the dictionary: a witness of harvested values, shrunk by
///   moves;
/// - DICT's `probe` under a pattern target, with the dictionary alone: the pattern's own
///   constant;
/// - COIN against COIN-KILL with the dictionary: the rules that differ come first;
/// - the maze's window cell `c4` with blind sampling and the climb: a witness the climb walks
///   into the window `1000 < D < 1100`, shrunk by moves;
/// - the lock's third cell with blind sampling and the corpus: a list of keys the corpus builds
///   one key at a time, shrunk by collection-length moves.
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
            data_end: true,
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
        spec.proposers.explicit = vec![BTreeMap::from([(
            "B".to_owned(),
            k_rust_fuzz::Value::Int((-3).into()),
        )])];
        spec.target = violation("<k> .K </k> <out> ListItem(N:Int) </out> requires N ==Int 9");
        spec
    };
    let map = map_campaign();
    let coin_spec = coin.clone();
    [
        (le, Budget::Cases(40)),
        (commute, Budget::Cases(24)),
        (coin, Budget::Work(4000)),
        (unsigned, Budget::Cases(30)),
        (map, Budget::Cases(40)),
    ]
    .into_iter()
    .chain(dictionary_campaigns(&coin_spec))
    .chain([(climb_campaign(), Budget::Cases(200))])
    .chain([(corpus_campaign(), Budget::Cases(1500))])
    .chain(solve_campaigns())
    .map(|(spec, budget)| {
        Campaign::new(spec)
            .expect("the golden campaign is valid")
            .run(budget, None)
    })
    .collect()
}

/// VALUES with a `Map` configuration-variable hole of `Int` keys and values, and a target that
/// needs three entries (see [`golden_reports`]).
fn map_campaign() -> CampaignSpec {
    let compiled = VALUES.compiled();
    let mut spec = spec("imp/le.imp", Vec::new(), "<k> .K </k>", &[], 0x0000_3a95);
    spec.definitions = Definitions {
        baseline: Arc::new(compiled.definition()),
        mutant: None,
    };
    let bindings = [
        ("SHAPE", "circle(5)"),
        ("REC", "rec(1, unit, leaf(0))"),
        ("PAIR", "1 & 2"),
        ("WRAPPER", "wrap(3)"),
        ("ACCOUNT", "account(1, .Map)"),
        ("LIST", ".List"),
        ("SET", ".Set"),
        ("MAP", ".Map"),
    ];
    spec.program = ProgramInput::Source(ProgramSource {
        program: Some(ProgramText {
            name: "values/run.pgm".into(),
            text: "run".into(),
            start_sort: "Pgm".into(),
        }),
        config_vars: bindings
            .iter()
            .map(|(name, value)| ((*name).to_owned(), (*value).to_owned()))
            .collect(),
    });
    spec.holes = vec![HoleDecl {
        name: "M".into(),
        sort: "Map".into(),
        location: HoleLocation::ConfigVar { name: "MAP".into() },
        constraints: Constraints {
            elements: Some(ElementSorts::Entries {
                key: "Int".into(),
                value: "Int".into(),
            }),
            ..Constraints::default()
        },
        allow_refused_sort: false,
    }];
    spec.target = violation("<k> .K </k> <map> M:Map </map> requires size(M) >=Int 3");
    spec
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
            data_end: true,
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

/// The maze with every hole but `D` and `G` fixed in the program text, at values that pass the
/// guards before room `r3`, and the target `c4` (`1000 < D < 1100`), with blind sampling and the
/// climb at equal weights.
fn climb_campaign() -> CampaignSpec {
    let compiled = MAZE.compiled();
    let program = "maze/climb.pgm";
    let mut spec = spec("imp/le.imp", Vec::new(), "<k> .K </k>", &[], 0x0c11_3b01);
    spec.definitions = Definitions {
        baseline: Arc::new(compiled.definition()),
        mutant: None,
    };
    spec.program = ProgramInput::Source(ProgramSource {
        program: Some(ProgramText {
            name: program.into(),
            text: "walk(1, 2, 7, -3, 4, 5, 6, 8, 9)\n".into(),
            start_sort: "Pgm".into(),
        }),
        config_vars: Vec::new(),
    });
    spec.holes = vec![
        int_hole("D", program, " -3,", "-3"),
        int_hole("G", program, " 6,", "6"),
    ];
    spec.target = Target {
        kind: TargetKind::Rule(RuleTarget {
            rule: RuleRef::Label("MAZE.c4".into()),
            mode: RuleMode::Fired,
        }),
        run_to_completion: false,
        negated_property: false,
        data_end: true,
    };
    spec.proposers.weights = [(ProposerKind::Blind, 1), (ProposerKind::Climb, 1)]
        .into_iter()
        .collect();
    spec
}

/// The lock's `List` hole `KEYS` and the target `l3` (its first three keys `17`, a key in
/// `1000 < X < 1100`, `31337`), with blind sampling and the corpus at equal weights.
fn corpus_campaign() -> CampaignSpec {
    let compiled = LOCK.compiled();
    let mut spec = spec("imp/le.imp", Vec::new(), "<k> .K </k>", &[], 0x0c0d_0e01);
    spec.definitions = Definitions {
        baseline: Arc::new(compiled.definition()),
        mutant: None,
    };
    spec.program = ProgramInput::Source(compiled.program_source("lock/open.pgm"));
    spec.holes = vec![HoleDecl {
        name: "KEYS".into(),
        sort: "List".into(),
        location: HoleLocation::ConfigVar {
            name: "KEYS".into(),
        },
        constraints: Constraints {
            elements: Some(ElementSorts::Elements {
                element: "Int".into(),
            }),
            ..Constraints::default()
        },
        allow_refused_sort: false,
    }];
    spec.target = Target {
        kind: TargetKind::Rule(RuleTarget {
            rule: RuleRef::Label("LOCK.l3".into()),
            mode: RuleMode::Fired,
        }),
        run_to_completion: false,
        negated_property: false,
        data_end: true,
    };
    spec.proposers.weights = [(ProposerKind::Blind, 1), (ProposerKind::Corpus, 1)]
        .into_iter()
        .collect();
    spec
}

/// The maze with every hole but `F` and `G` fixed in the program text, at values that pass the
/// guards before room `r5`, and the target `c6` (`3 F == G + 1000001`, `G > 5000`), a linear
/// guard whose symbolic run the solver decides without an unknown answer, with blind sampling and
/// the solve proposer at equal weights; in builds with the `z3` feature only.
fn solve_campaigns() -> Vec<(CampaignSpec, Budget)> {
    if !cfg!(feature = "z3") {
        return Vec::new();
    }
    let mut spec = climb_campaign();
    let program = "maze/solve.pgm";
    spec.seed = 0x5017_e001;
    spec.program = ProgramInput::Source(ProgramSource {
        program: Some(ProgramText {
            name: program.into(),
            text: "walk(1, 2, 7, 1050, 31337, 5, 6, 8, 9)\n".into(),
            start_sort: "Pgm".into(),
        }),
        config_vars: Vec::new(),
    });
    spec.holes = vec![
        int_hole("F", program, " 5,", "5"),
        int_hole("G", program, " 6,", "6"),
    ];
    spec.target = Target {
        kind: TargetKind::Rule(RuleTarget {
            rule: RuleRef::Label("MAZE.c6".into()),
            mode: RuleMode::Fired,
        }),
        run_to_completion: false,
        negated_property: false,
        data_end: true,
    };
    spec.proposers.weights = [(ProposerKind::Blind, 1), (ProposerKind::Solve, 1)]
        .into_iter()
        .collect();
    vec![(spec, Budget::Cases(200))]
}

/// The solve campaign finds its witness through a model, inside the determinism contract, and
/// its fingerprint is [`PINNED_SOLVE`].
#[cfg(feature = "z3")]
fn check_solve(reports: &[FuzzReport]) {
    let solve = fingerprint(reports);
    if std::env::var_os("KRUST_FUZZ_GOLDEN_PRINT").is_some() {
        eprintln!("solve fingerprint at engine version {ENGINE_VERSION}: {solve}");
    }
    for report in reports {
        assert!(report.witness().is_some(), "{:?}", report.outcome);
        let totals = report.totals.solve.as_ref().expect("solve totals");
        assert!(totals.candidates >= 1, "{totals:?}");
        assert_eq!(totals.outside_determinism, 0, "{totals:?}");
    }
    check_pin(
        "solve",
        PINNED_SOLVE,
        &solve,
        "its parameters, its trigger or its records",
    );
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

/// Check the fingerprint `computed` of the `name` campaigns against `pinned`; `moves` says what
/// moves it.
fn check_pin(name: &str, pinned: Option<(u32, &str)>, computed: &str, moves: &str) {
    match pinned {
        Some((version, pinned)) => {
            assert_eq!(
                version, ENGINE_VERSION,
                "ENGINE_VERSION changed: re-pin the {name} fingerprint for the new version"
            );
            assert_eq!(
                computed, pinned,
                "the {name} case sequence changed ({moves}) without an ENGINE_VERSION bump"
            );
        }
        None => panic!(
            "no {name} fingerprint is pinned for engine version {ENGINE_VERSION}; pin \
             Some(({ENGINE_VERSION}, \"{computed}\")) in tests/golden.rs"
        ),
    }
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
    // The map campaign pins map shrinking: its witness loses whole entries down to the three
    // the target needs.
    let entries = |case: &k_rust_fuzz::report::WitnessCase| match &case.holes[0].value {
        k_rust_fuzz::Value::Map(entries) => entries.len(),
        other => panic!("a map value: {other:?}"),
    };
    let map = reports[MAP_CAMPAIGN]
        .witness()
        .expect("the map campaign finds a witness");
    let shrunk = map.shrunk.as_ref().expect("the map witness shrinks");
    assert!(entries(&map.first) > 3, "{:?}", map.first.holes[0].value);
    assert_eq!(entries(shrunk), 3, "{:?}", shrunk.holes[0].value);

    let solving = reports.len() - SOLVE_CAMPAIGNS;
    let corpus_start = solving - CORPUS_CAMPAIGNS;
    let climbing = corpus_start - CLIMB_CAMPAIGNS;
    let computed = fingerprint(&reports[..BLIND_CAMPAIGNS]);
    let dictionary = fingerprint(&reports[BLIND_CAMPAIGNS..climbing]);
    let climb = fingerprint(&reports[climbing..corpus_start]);
    let corpus = fingerprint(&reports[corpus_start..solving]);
    #[cfg(feature = "z3")]
    check_solve(&reports[solving..]);
    if std::env::var_os("KRUST_FUZZ_GOLDEN_PRINT").is_some() {
        eprintln!("golden fingerprint at engine version {ENGINE_VERSION}: {computed}");
        eprintln!("dictionary fingerprint at engine version {ENGINE_VERSION}: {dictionary}");
        eprintln!("climb fingerprint at engine version {ENGINE_VERSION}: {climb}");
        eprintln!("corpus fingerprint at engine version {ENGINE_VERSION}: {corpus}");
    }
    // The corpus campaign finds its witness within its budget, and its report records the
    // corpus's parameters.
    assert!(
        reports[corpus_start].witness().is_some(),
        "{:?}",
        reports[corpus_start].outcome
    );
    assert_eq!(
        reports[corpus_start].identity.corpus,
        Some(k_rust_fuzz::report::CorpusParameters::for_target(
            &corpus_campaign().target.kind
        ))
    );
    check_pin(
        "corpus",
        PINNED_CORPUS,
        &corpus,
        "its parameters, its mutations or its harvest",
    );
    // The climb campaign finds its witness within its budget.
    assert!(
        reports[climbing].witness().is_some(),
        "{:?}",
        reports[climbing].outcome
    );
    check_pin(
        "climb",
        PINNED_CLIMB,
        &climb,
        "its parameters, its moves or its score",
    );
    check_pin(
        "dictionary",
        PINNED_DICTIONARY,
        &dictionary,
        "its parameters or its harvest",
    );
    check_pin(
        "golden",
        PINNED,
        &computed,
        "the blind proposers, the schedule or the generators",
    );
}
