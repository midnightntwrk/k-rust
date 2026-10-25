//! Crash findings on live campaigns (FZ-CRASH design section 8, tests C to K), through the
//! `exec::run::seam` test seam: a panic at a fixed location, `stacker`'s mapping text, or a typed
//! or text error, when a case's initial state holds given Int literals. Each test runs the
//! campaign through the library on the calling thread, where the seam's rule lives.
//!
//! These tests use the seam, which exists only in this crate's test build, so they cannot
//! compile at the base; each is checked by reverting its fix instead (the inner catch site, the
//! rebuild's `RunSetup`, the typed kinds, the hook's clearing).

use std::{collections::BTreeMap, sync::Arc};

use k_rust::backend::{BackendError, BackendErrorKind};
use serde_json::Value as Json;

use super::Campaign;
use crate::{
    exec::run::seam::{self, Action},
    holes::{HoleDecl, HoleLocation, SpanAddress},
    report::{CrashStage, FuzzReport},
    spec::{
        BackendRoute, Budget, CallerIdentity, CampaignSpec, CaseOptions, DEFAULT_REJECTION_CAP,
        Definitions, ProgramInput, ProposerConfig, ProposerKind,
    },
    support::{IMP, MAZE},
    target::{PatternAt, PatternTarget, RuleMode, RuleRef, RuleTarget, Target, TargetKind},
    values::{Constraints, GenerationBounds, IntRange, Value},
};

fn int_hole(name: &str, program: &str, find: &str, literal: &str) -> HoleDecl {
    HoleDecl {
        name: name.into(),
        sort: "Int".into(),
        location: HoleLocation::Span(SpanAddress {
            program: program.into(),
            line: None,
            column: None,
            find: find.into(),
            literal: literal.into(),
        }),
        constraints: Constraints::default(),
        allow_refused_sort: false,
    }
}

/// IMP's `le.imp` with `x` as the hole `X` in `[0, 40]` (`y` stays 5, `r` takes 0 or 1), the
/// explicit assignments `explicit` after the anchor 3, blind sampling at weight `blind`, and a
/// pattern target no end reaches (`r` ending as 42), on `route`.
fn le_campaign(explicit: &[i64], blind: u32, route: Option<BackendRoute>) -> CampaignSpec {
    let compiled = IMP.compiled();
    let definition = match route {
        Some(route) => compiled.definition_on(route),
        None => compiled.definition(),
    };
    let mut hole = int_hole("X", "imp/le.imp", "x = 3;", "3");
    hole.constraints.range = Some(IntRange {
        min: Some(0.into()),
        max: Some(40.into()),
    });
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(definition),
            mutant: None,
        },
        program: ProgramInput::Source(compiled.program_source("imp/le.imp")),
        holes: vec![hole],
        target: Target {
            kind: TargetKind::Pattern(PatternTarget {
                pattern: concat!(
                    r#"<k> .K </k> <state> (#token("r", "Id") |-> R:Int) _:Map </state> "#,
                    "requires R ==Int 42"
                )
                .into(),
                at: PatternAt::Final,
            }),
            run_to_completion: false,
            negated_property: false,
            data_end: false,
            comparable: false,
            query_confirmable: false,
        },
        options: CaseOptions::default(),
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: explicit
                .iter()
                .map(|x| BTreeMap::from([("X".to_owned(), Value::Int((*x).into()))]))
                .collect(),
            weights: if blind > 0 {
                BTreeMap::from([(ProposerKind::Blind, blind)])
            } else {
                BTreeMap::new()
            },
        },
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 7,
        identity: CallerIdentity::default(),
    }
}

fn run(spec: CampaignSpec, budget: Budget) -> FuzzReport {
    Campaign::new(spec)
        .expect("the campaign is valid")
        .run(budget, None)
}

fn json(report: &FuzzReport) -> Json {
    serde_json::from_str(&report.to_canonical_json()).expect("a report is JSON")
}

/// The value of `X` in a state of `le.imp`: its literals are `X`, 5, 1 and 0, so a rule over
/// `X >= 7` or `X` in `1..=4` reads it unambiguously.
fn x_is(ints: &[i64], test: impl Fn(i64) -> bool) -> bool {
    ints.iter().any(|value| test(*value))
}

/// (C) A panic in `Backend::execute` at `X = 7` is a crash finding of the baseline's run at
/// stage `execute`, located in the seam, reproduced on a fresh backend; the case is
/// `unsupported` with the reason `panic`, and every other case is classed as without the
/// panic, in the same case sequence. Fails without the inner catch site (the panic is then the
/// engine's).
#[test]
fn a_live_panic_is_a_crash_of_the_baselines_run_and_the_campaign_goes_on() {
    let spec = || le_campaign(&[1, 7, 2, 9], 0, None);
    let plain = json(&run(spec(), Budget::Cases(10)));
    let _seam = seam::install(Box::new(|stage, ints| {
        (stage == CrashStage::Execute && x_is(ints, |x| x == 7))
            .then_some(Action::PanicHere("the seam panics at x = 7"))
    }));
    let crashed = json(&run(spec(), Budget::Cases(10)));
    let found = crashed["crashes"].as_array().expect("a crashes list");
    assert_eq!(found.len(), 1, "{found:?}");
    let crash = &found[0];
    assert_eq!(crash["signature"]["kind"], "panic", "{crash}");
    assert_eq!(crash["signature"]["side"], "baseline", "{crash}");
    assert_eq!(crash["signature"]["stage"], "execute", "{crash}");
    assert_eq!(crash["signature"]["site-kind"], "location", "{crash}");
    assert!(
        crash["signature"]["site"]
            .as_str()
            .is_some_and(|site| site.starts_with("k-rust-fuzz/src/exec/run.rs:")),
        "{crash}"
    );
    assert_eq!(crash["phase"], "case", "{crash}");
    assert_eq!(crash["case"], 2, "{crash}");
    assert_eq!(crash["holes"][0]["value"]["int"], "7", "{crash}");
    assert_eq!(crash["reproduced"], true, "{crash}");
    assert_eq!(crash["determinism"], "unknown", "{crash}");
    assert_eq!(crash["count"], 1, "{crash}");
    assert!(
        crash["program"]
            .as_str()
            .is_some_and(|program| program.contains("x = 7;"))
    );
    // No smaller value crashes, so the crash keeps its values.
    assert_eq!(crash.get("shrunk-holes"), None, "{crash}");
    assert!(
        crashed["totals"]["crash-work"]
            .as_u64()
            .is_some_and(|work| work > 0)
    );
    // The same cases, the same work, and every class but the crashed case's as without it.
    assert_eq!(
        crashed["totals"]["case-sequence-digest"],
        plain["totals"]["case-sequence-digest"]
    );
    assert_eq!(crashed["totals"]["cases"], plain["totals"]["cases"]);
    let misses = plain["totals"]["classes"]["miss"].as_u64().expect("misses");
    assert_eq!(crashed["totals"]["classes"]["miss"], misses - 1);
    assert_eq!(crashed["totals"]["classes"]["unsupported"], 1);
    assert_eq!(crashed["totals"]["unsupported-reasons"]["panic"], 1);
}

/// The maze's climb campaign of the golden test (holes `D` and `G`) with the target `MAZE.c5`,
/// which the program's fixed `E` keeps out of reach, so that every case runs; blind sampling, the
/// climb and the corpus at equal weights: the climb reads condition entries and the corpus
/// applied counts, which `Campaign::run` asks the case execution for.
fn climb_corpus_campaign() -> CampaignSpec {
    let compiled = MAZE.compiled();
    let program = "maze/climb.pgm";
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(compiled.definition()),
            mutant: None,
        },
        program: ProgramInput::Source(crate::spec::ProgramSource {
            program: Some(crate::spec::ProgramText {
                name: program.into(),
                text: "walk(1, 2, 7, -3, 4, 5, 6, 8, 9)\n".into(),
                start_sort: "Pgm".into(),
            }),
            config_vars: Vec::new(),
        }),
        holes: vec![
            int_hole("D", program, " -3,", "-3"),
            int_hole("G", program, " 6,", "6"),
        ],
        target: Target {
            kind: TargetKind::Rule(RuleTarget {
                rule: RuleRef::Label("MAZE.c5".into()),
                mode: RuleMode::Fired,
            }),
            run_to_completion: false,
            negated_property: false,
            data_end: true,
            comparable: false,
            query_confirmable: false,
        },
        options: CaseOptions::default(),
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: Vec::new(),
            weights: BTreeMap::from([
                (ProposerKind::Blind, 1),
                (ProposerKind::Climb, 1),
                (ProposerKind::Corpus, 1),
            ]),
        },
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 0x0c11_3b01,
        identity: CallerIdentity::default(),
    }
}

/// A seam rule that acts on the `at`-th execution only (counted from 1), with `action`.
fn on_execution(at: usize, action: fn() -> Action) -> seam::Rule {
    let mut executions = 0;
    Box::new(move |stage, _| {
        if stage != CrashStage::Execute {
            return None;
        }
        executions += 1;
        (executions == at).then(action)
    })
}

/// (D, S1) A rebuild after a crash asks the case execution for what the run asked of it (the
/// climb's condition entries, the corpus's counts): a campaign whose third execution panics,
/// which rebuilds, makes the same observations and runs the same case sequence as one whose
/// third execution answers an internal error, which does not rebuild. Fails without the
/// rebuild's `RunSetup`.
#[test]
fn a_rebuilt_runner_records_what_the_campaigns_own_recorded() {
    let report = |action: fn() -> Action| {
        let campaign = Campaign::new(climb_corpus_campaign()).expect("the campaign is valid");
        let mut campaign = campaign;
        let _seam = seam::install(on_execution(3, action));
        json(&campaign.run(Budget::Cases(80), None))
    };
    let panicked = report(|| Action::PanicHere("the seam panics once"));
    let failed = report(|| Action::Error(BackendError::new("the seam's internal error")));
    assert_eq!(panicked["crashes"][0]["signature"]["kind"], "panic");
    assert_eq!(failed["crashes"][0]["signature"]["kind"], "internal-error");
    for key in [
        "case-sequence-digest",
        "cases",
        "work",
        "classes",
        "coverage",
        "best-score",
        "target-blocked",
    ] {
        assert_eq!(
            panicked["totals"][key], failed["totals"][key],
            "totals.{key}"
        );
    }
    assert_eq!(panicked["outcome"]["status"], failed["outcome"]["status"]);
    assert_eq!(panicked["totals"]["cases"], 80);
}

/// (E) A panic only on the first execution of its values is not repeated by the confirmation:
/// `reproduced` false, determinism `outside`, and the case counts as outside the determinism
/// contract.
#[test]
fn a_panic_the_confirmation_does_not_repeat_is_outside_the_determinism_contract() {
    let mut fired = false;
    let _seam = seam::install(Box::new(move |stage, ints| {
        if stage == CrashStage::Execute && !fired && x_is(ints, |x| x == 7) {
            fired = true;
            return Some(Action::PanicHere("the seam panics once at x = 7"));
        }
        None
    }));
    let report = json(&run(le_campaign(&[7, 2], 0, None), Budget::Cases(5)));
    let crash = &report["crashes"][0];
    assert_eq!(crash["reproduced"], false, "{crash}");
    assert_eq!(crash["determinism"], "outside", "{crash}");
    assert_eq!(report["totals"]["outside-determinism"], 1);
    assert_eq!(crash.get("shrunk-holes"), None, "{crash}");
}

/// (F) A crash shrinks under its own signature: a panic at one location for `X >= 7` shrinks
/// from 20 to 7, while the candidates 2, 4 and 6, which panic at another location, are dropped
/// (the first of them kept as a crash of phase `shrink`), within the cap of 32 runs.
#[test]
fn a_crash_shrinks_under_its_own_signature() {
    let runs = std::rc::Rc::new(std::cell::Cell::new(0_u32));
    let counted = std::rc::Rc::clone(&runs);
    let _seam = seam::install(Box::new(move |stage, ints| {
        if stage != CrashStage::Execute {
            return None;
        }
        counted.set(counted.get() + 1);
        if x_is(ints, |x| x >= 7) {
            Some(Action::PanicHere("the seam panics at x >= 7"))
        } else if x_is(ints, |x| [2, 4, 6].contains(&x)) {
            Some(Action::PanicThere("the seam panics at a small x"))
        } else {
            None
        }
    }));
    let report = json(&run(le_campaign(&[20], 0, None), Budget::Cases(2)));
    let crashes = report["crashes"].as_array().expect("a crashes list");
    let first = &crashes[0];
    assert_eq!(first["holes"][0]["value"]["int"], "20", "{first}");
    assert_eq!(first["shrunk-holes"][0]["value"]["int"], "7", "{first}");
    assert_eq!(first["shrunk-reproduced"], true, "{first}");
    let other = crashes
        .iter()
        .find(|crash| crash["phase"] == "shrink")
        .expect("the other location's crash, of phase shrink");
    assert_ne!(other["signature"]["site"], first["signature"]["site"]);
    assert_eq!(other["case"], 1, "{other}");
    // Two cases (the anchor 3 and 20), the confirmations, and at most 32 shrink candidates.
    assert!(runs.get() <= 2 + 4 + 32, "{} executions", runs.get());
}

/// (G) Typed kinds, never message texts, class an error: `InsufficientStack` gives `too-deep`,
/// `StackSegmentRefused` and `stacker`'s panic `stack-mapping-refused` (outside the determinism
/// contract, no finding), an untyped error `internal-error` (a finding), and `SolverInit`
/// aborts the campaign with kind `solver-init`.
#[test]
fn typed_kinds_class_errors_and_environment_refusals() {
    let _seam = seam::install(Box::new(|stage, ints| {
        if stage != CrashStage::Execute {
            return None;
        }
        let kinded = |kind| {
            Action::Error(BackendError::of_kind(
                kind,
                "the request is too deep for the backend: worded otherwise",
            ))
        };
        if x_is(ints, |x| x == 11) {
            Some(kinded(BackendErrorKind::InsufficientStack))
        } else if x_is(ints, |x| x == 12) {
            Some(kinded(BackendErrorKind::StackSegmentRefused))
        } else if x_is(ints, |x| x == 13) {
            Some(Action::StackerPanic)
        } else if x_is(ints, |x| x == 14) {
            Some(Action::Error(BackendError::new(
                "the request is too deep for the backend: but untyped",
            )))
        } else if x_is(ints, |x| x == 15) {
            Some(Action::Error(BackendError::of_kind(
                BackendErrorKind::SolverInit,
                "could not initialize Z3: the seam's",
            )))
        } else {
            None
        }
    }));
    let report = json(&run(
        le_campaign(&[11, 12, 13, 14, 15, 16], 0, None),
        Budget::Cases(10),
    ));
    let reasons = &report["totals"]["unsupported-reasons"];
    assert_eq!(reasons["too-deep"], 1, "{reasons}");
    assert_eq!(reasons["stack-mapping-refused"], 2, "{reasons}");
    assert_eq!(reasons["internal-error"], 1, "{reasons}");
    assert_eq!(report["totals"]["outside-determinism"], 2);
    let crashes = report["crashes"].as_array().expect("a crashes list");
    assert_eq!(crashes.len(), 1, "{crashes:?}");
    assert_eq!(crashes[0]["signature"]["kind"], "internal-error");
    assert_eq!(crashes[0]["signature"]["site-kind"], "message");
    assert_eq!(
        crashes[0]["signature"]["site"],
        "the request is too deep for the backend"
    );
    assert_eq!(report["outcome"]["status"], "aborted");
    assert_eq!(report["outcome"]["kind"], "solver-init");
    // The anchor and 11 to 15 ran; 16 never did.
    assert_eq!(report["totals"]["cases"], 5);
}

/// (H) A panic the stage catches and handles itself leaves no record behind: the run goes on,
/// no crash is reported, and the hook's last record is empty after every case.
#[test]
fn a_panic_handled_inside_a_stage_leaves_no_record() {
    let spec = || le_campaign(&[1, 2], 0, None);
    let plain = run(spec(), Budget::Cases(3));
    let _seam = seam::install(Box::new(|_, _| Some(Action::HandledPanic)));
    let handled = run(spec(), Budget::Cases(3));
    assert!(crate::crash::no_record(), "a handled panic left its record");
    assert_eq!(handled.crashes, plain.crashes);
    assert_eq!(handled.totals, plain.totals);
}

/// (I) A rebuild that fails ends the campaign `aborted` with kind `rebuild-failed`, keeping the
/// crash, and no case runs on the poisoned backends.
#[test]
fn a_failed_rebuild_aborts_and_keeps_the_crash() {
    let _seam = seam::install(Box::new(|stage, ints| {
        (stage == CrashStage::Execute && x_is(ints, |x| x == 7))
            .then_some(Action::PanicHere("the seam panics at x = 7"))
    }));
    let _refused = seam::fail_recover();
    let report = json(&run(le_campaign(&[7, 2, 9], 0, None), Budget::Cases(10)));
    assert_eq!(
        report["outcome"]["status"], "aborted",
        "{}",
        report["outcome"]
    );
    assert_eq!(report["outcome"]["kind"], "rebuild-failed");
    assert!(
        report["outcome"]["reason"]
            .as_str()
            .is_some_and(|reason| reason.contains("did not rebuild after a crash at case 1")),
        "{}",
        report["outcome"]
    );
    assert_eq!(report["crashes"][0]["holes"][0]["value"]["int"], "7");
    assert_eq!(report["totals"]["cases"], 2);
}

/// (J) A campaign with crashes reports the same bytes on every run, under a case budget and
/// under a work budget.
#[test]
fn a_campaign_with_crashes_is_deterministic_under_both_budgets() {
    let rule = || -> seam::Rule {
        Box::new(|stage, ints| {
            (stage == CrashStage::Execute && x_is(ints, |x| x >= 7 && x % 5 == 0))
                .then_some(Action::PanicHere("the seam panics at multiples of 5"))
        })
    };
    for budget in [Budget::Cases(30), Budget::Work(600)] {
        let reports: Vec<String> = (0..2)
            .map(|_| {
                let _seam = seam::install(rule());
                run(le_campaign(&[], 1, None), budget).to_canonical_json()
            })
            .collect();
        assert_eq!(reports[0], reports[1], "{budget:?}");
        assert!(
            reports[0].contains(r#""crashes":["#),
            "{budget:?}: no crash"
        );
    }
}

/// (K) On the `from-definition` route, whose cache holds no internalization, a rebuild builds
/// its backend from a copy of the internalized definition the campaign's own session held
/// (`Backend::from_internalized`), and the rebuilt runner classes cases as the campaign's did.
#[test]
fn a_from_definition_rebuild_copies_the_sessions_definition() {
    use super::{
        live::{LiveCases, LiveRunner, RunSetup},
        runner::CaseRunner as _,
    };
    let spec = Arc::new(le_campaign(&[], 0, Some(BackendRoute::FromDefinition)));
    let mut cases = LiveCases::build(Arc::clone(&spec)).expect("the campaign builds");
    let session = cases
        .baseline
        .executor_mut()
        .backend_mut()
        .select_definition(None)
        .expect("the session's definition");
    let parts = cases.assembly_parts();
    let mut runner = LiveRunner {
        cases,
        parts: &parts,
        assemblers: parts.assemblers(),
        cache: Arc::default(),
        graph: None,
        setup: RunSetup::default(),
        sessions: None,
    };
    let x = |n: i64| vec![Value::Int(n.into())];
    let before = runner.run_case(&x(4), None).expect("runs");
    {
        let _seam = seam::install(Box::new(|stage, _| {
            (stage == CrashStage::Execute).then_some(Action::PanicHere("the seam panics"))
        }));
        let crashed = runner.run_case(&x(4), None).expect("runs");
        assert!(crashed.poisoned && crashed.crash.is_some());
    }
    runner.recover().expect("the rebuild succeeds");
    let rebuilt = runner
        .cases
        .baseline
        .internalized()
        .expect("the rebuilt side holds the session's definition");
    assert!(
        Arc::ptr_eq(rebuilt, &session),
        "copied from the session, not internalized again"
    );
    let after = runner.run_case(&x(4), None).expect("runs");
    assert!(!after.poisoned);
    assert_eq!(after.class, before.class);
    assert_eq!(after.applied, before.applied);
}

/// The cost of a rebuild after a crash (FZ-CRASH design section 8), on both routes: IMP's
/// `le.imp` from the fixtures, and, when `FZ_CRASH_KEVM` names a compiled KEVM directory
/// (`krust kcompile` of `driver.md`), KEVM's `store4.json` from `FZ_CRASH_KEVM_PROGRAM` with
/// `CHAINID` as the hole. For each it prints the time of a case, of the first rebuild (which
/// also builds the confirmations' definition cache) and of a second rebuild. A measurement,
/// not a check: run it with `--ignored --nocapture` in a release-like build.
#[cfg(feature = "cli")]
#[test]
#[ignore = "measurement"]
#[expect(
    clippy::too_many_lines,
    reason = "one measurement: IMP on both routes, then KEVM's definition, program and hole"
)]
fn measure_the_rebuild_cost() {
    use std::time::Instant;

    use super::{
        live::{LiveCases, LiveRunner, RunSetup},
        runner::CaseRunner as _,
    };
    use crate::spec::{CompiledDefinition, ProgramSource, ProgramText};

    fn measure(name: &str, spec: CampaignSpec, values: &[Value]) {
        let spec = Arc::new(spec);
        let started = Instant::now();
        let cases = LiveCases::build(Arc::clone(&spec)).expect("the campaign builds");
        let built = started.elapsed();
        let parts = cases.assembly_parts();
        let mut runner = LiveRunner {
            cases,
            parts: &parts,
            assemblers: parts.assemblers(),
            cache: Arc::default(),
            graph: None,
            setup: RunSetup::default(),
            sessions: None,
        };
        let started = Instant::now();
        let run = runner.run_case(values, None).expect("runs");
        let case = started.elapsed();
        let started = Instant::now();
        runner.recover().expect("the first rebuild");
        let first = started.elapsed();
        let started = Instant::now();
        runner.recover().expect("the second rebuild");
        let second = started.elapsed();
        let again = runner.run_case(values, None).expect("runs");
        assert_eq!(again.class, run.class);
        println!(
            "REBUILD {name}: build {built:?}, case {case:?} ({:?}), first rebuild {first:?}, \
             second rebuild {second:?}",
            run.class
        );
    }

    for route in [None, Some(BackendRoute::FromDefinition)] {
        let name = format!(
            "imp {}",
            if route.is_some() {
                "from-definition"
            } else {
                "source"
            }
        );
        measure(&name, le_campaign(&[], 0, route), &[Value::Int(4.into())]);
    }
    let (Ok(directory), Ok(program)) = (
        std::env::var("FZ_CRASH_KEVM"),
        std::env::var("FZ_CRASH_KEVM_PROGRAM"),
    ) else {
        println!("REBUILD kevm: FZ_CRASH_KEVM or FZ_CRASH_KEVM_PROGRAM unset, skipped");
        return;
    };
    let directory = std::path::Path::new(&directory);
    let artifact = k_rust::native::load_runnable_artifact(directory).expect("loads");
    let companions = k_rust::native::load_kore_companions(directory).expect("loads");
    let execution_definition = artifact.execution.decode().expect("decodes");
    let kore = k_rust::kore::parser::parse_definition(&artifact.definition_kore).expect("parses");
    let source = CompiledDefinition {
        main_module: artifact.main_module,
        syntax_module: artifact.syntax_module,
        frontend_definition: artifact.frontend_definition,
        execution_definition,
        source_table: artifact.source_table,
        configuration_variables: artifact.configuration_variables,
        kore,
        syntax_definition_kore: companions.syntax_definition_kore,
        macros_kore: companions.macros_kore,
        route: BackendRoute::SourceExecution {
            execution_rewrite_order: artifact.execution_rewrite_order,
        },
    };
    let text = std::fs::read_to_string(&program).expect("the program");
    let kevm = |definition: CompiledDefinition| {
        let mut spec = le_campaign(&[], 0, None);
        spec.definitions.baseline = Arc::new(definition);
        spec.program = ProgramInput::Source(ProgramSource {
            program: Some(ProgramText {
                name: "store4.json".into(),
                text: text.clone(),
                start_sort: "EthereumSimulation".into(),
            }),
            config_vars: [
                ("MODE", "VMTESTS"),
                ("SCHEDULE", "LONDON"),
                ("CHAINID", "1"),
                ("USEGAS", "true"),
            ]
            .iter()
            .map(|(name, value)| ((*name).to_owned(), (*value).to_owned()))
            .collect(),
        });
        let mut hole = int_hole("C", "store4.json", "", "");
        hole.location = HoleLocation::ConfigVar {
            name: "CHAINID".into(),
        };
        hole.constraints.range = Some(IntRange {
            min: Some(0.into()),
            max: Some(10.into()),
        });
        spec.holes = vec![hole];
        spec.target.kind = TargetKind::Pattern(PatternTarget {
            pattern: "<mode> SUCCESS </mode>".into(),
            at: PatternAt::Final,
        });
        spec.options.max_work = Some(200_000);
        spec
    };
    let from_definition = CompiledDefinition {
        route: BackendRoute::FromDefinition,
        ..source.clone()
    };
    measure("kevm source", kevm(source), &[Value::Int(1.into())]);
    measure(
        "kevm from-definition",
        kevm(from_definition),
        &[Value::Int(1.into())],
    );
}

/// Panics when a configuration's `<state>` cell holds the integer 10: in `le.imp` exactly when
/// the hole `X` is 10.
struct PanicsAtTen;

impl crate::target::Observer for PanicsAtTen {
    type State = ();

    fn start(&self) {}

    fn branch(&self, (): &()) {}

    fn step(
        &self,
        (): &mut (),
        _pre: &crate::target::ConfigurationView,
        post: &crate::target::ConfigurationView,
    ) -> crate::target::ObserverVerdict {
        let mut work: Vec<&k_rust::kore::ast::Pattern> = post.cell("state").into_iter().collect();
        while let Some(next) = work.pop() {
            if let k_rust::kore::ast::Pattern::DomainValue { value, .. } = next
                && value.as_utf8().ok() == Some("10")
            {
                panic!("the observer met x = 10");
            }
            work.extend(k_rust::kore::walk::children(next));
        }
        crate::target::ObserverVerdict::Nothing
    }
}

/// (Fix round, D2) An observer that panics while a crash is shrunk aborts the campaign with
/// the candidate that made it panic, instead of the panic being swallowed by the shrinker.
#[test]
fn an_observer_panic_while_a_crash_shrinks_aborts_with_its_values() {
    let mut spec = le_campaign(&[20], 0, None);
    spec.target.kind = TargetKind::Observer(crate::target::ObserverTarget::new(
        "panics-at-10",
        PanicsAtTen,
    ));
    let _seam = seam::install(Box::new(|stage, ints| {
        (stage == CrashStage::Execute && x_is(ints, |x| x >= 20))
            .then_some(Action::PanicHere("the seam panics at x >= 20"))
    }));
    let report = json(&run(spec, Budget::Cases(5)));
    let outcome = &report["outcome"];
    assert_eq!(outcome["status"], "aborted", "{outcome}");
    assert_eq!(outcome["kind"], "client-panic", "{outcome}");
    assert_eq!(outcome["holes"][0]["value"]["int"], "10", "{outcome}");
    assert_eq!(outcome["case"], 1, "{outcome}");
    assert_eq!(report["crashes"][0]["holes"][0]["value"]["int"], "20");
}

/// `le.imp` with the target `r` ending as 1, which the anchor 3 reaches on its one path.
fn le_reaching(comparable: bool) -> CampaignSpec {
    let mut spec = le_campaign(&[], 0, None);
    spec.target.kind = TargetKind::Pattern(PatternTarget {
        pattern: concat!(
            r#"<k> .K </k> <state> (#token("r", "Id") |-> R:Int) _:Map </state> "#,
            "requires R ==Int 1"
        )
        .into(),
        at: PatternAt::Final,
    });
    spec.target.comparable = comparable;
    spec
}

/// A seam rule that panics on every run of every path.
fn panics_on_every_path() -> seam::Rule {
    Box::new(|stage, _| {
        (stage == CrashStage::Execute && seam::all_paths())
            .then_some(Action::PanicHere("the seam panics on every path"))
    })
}

/// (Fix round, D1) A deterministic crash of the run of every path that judges a witness's
/// comparability outside its case is confirmed by re-running that judgement on fresh cases:
/// `reproduced` is true, as `--replay` finds it.
#[test]
fn a_crash_of_the_comparability_run_is_confirmed_by_that_run() {
    let _seam = seam::install(panics_on_every_path());
    let report = json(&run(le_reaching(false), Budget::Cases(3)));
    assert_eq!(
        report["outcome"]["status"], "witness-found",
        "{}",
        report["outcome"]
    );
    assert_eq!(
        report["outcome"]["witness"]["first"]["comparable"],
        serde_json::json!({"holds": false, "reasons": ["crash"]})
    );
    let crash = &report["crashes"][0];
    assert_eq!(crash["phase"], "comparability", "{crash}");
    assert_eq!(crash["reproduced"], true, "{crash}");
    assert_eq!(crash["determinism"], "unknown", "{crash}");
}

/// (Fix round, S1) Under `comparable-end`, a case whose run of every path panics is unsupported
/// with the reason `panic`, not `end-not-comparable:crash`.
#[test]
fn a_crash_of_the_comparable_end_run_has_the_reason_panic() {
    let _seam = seam::install(panics_on_every_path());
    let report = json(&run(le_reaching(true), Budget::Cases(1)));
    let reasons = &report["totals"]["unsupported-reasons"];
    assert_eq!(reasons["panic"], 1, "{reasons}");
    assert_eq!(report["crashes"][0]["phase"], "case");
}

/// (Fix round, D4) In a differential case, a panic of the mutant's run is kept although the
/// baseline refuses the state, which makes the case `rejected`.
#[test]
fn a_panic_on_one_side_is_kept_when_the_other_refuses_the_state() {
    use crate::support::{IMP_ADD_COMMUTED, IMP_DIFF};
    const DIV: &str = "imp-diff/div.imp";
    let definition =
        |fixture: &'static crate::support::Fixture| Arc::new(fixture.compiled().definition());
    let spec = CampaignSpec {
        definitions: Definitions {
            baseline: definition(&IMP_DIFF),
            mutant: Some(definition(&IMP_ADD_COMMUTED)),
        },
        program: ProgramInput::Source(IMP_DIFF.compiled().program_source(DIV)),
        holes: vec![int_hole("B", DIV, "b = 7;", "7")],
        target: Target {
            kind: TargetKind::Differential(crate::target::DifferentialTarget::default()),
            run_to_completion: false,
            negated_property: false,
            data_end: true,
            comparable: false,
            query_confirmable: false,
        },
        options: CaseOptions {
            max_work: Some(10_000),
            ..CaseOptions::default()
        },
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: vec![BTreeMap::from([("B".to_owned(), Value::Int(77.into()))])],
            weights: BTreeMap::new(),
        },
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 3,
        identity: CallerIdentity::default(),
    };
    // Of each pair of runs on B = 77, the first (the baseline's) is refused and the second (the
    // mutant's) panics.
    let mut calls = 0;
    let _seam = seam::install(Box::new(move |stage, ints| {
        if stage != CrashStage::Execute || !x_is(ints, |b| b == 77) {
            return None;
        }
        calls += 1;
        Some(if calls % 2 == 1 {
            Action::Error(BackendError::of_kind(
                BackendErrorKind::InvalidState,
                "invalid executable state: the seam's",
            ))
        } else {
            Action::PanicHere("the seam panics on the mutant")
        })
    }));
    let report = json(&run(spec, Budget::Cases(2)));
    assert_eq!(
        report["totals"]["classes"]["rejected"], 1,
        "{} {}",
        report["outcome"], report["totals"]
    );
    let crash = &report["crashes"][0];
    assert_eq!(crash["signature"]["side"], "mutant", "{crash}");
    assert_eq!(crash["holes"][0]["value"]["int"], "77", "{crash}");
}
