//! `krs-exec` stop rules and resumable states on an authored definition (CF-22).
//!
//! The fixture is a machine that runs in boundary steps, as Foldiboy's SM83 does: `boundary`
//! queues one unit of work and the next `#boundary` while the counter is below 3, and `work`
//! counts it, so the whole run is six steps, `boundary` and `work` three times each, and ends
//! stuck at `#boundary` with the counter at 3.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::sync::OnceLock;

use krs_exec::{
    CompiledStage, ConfigInputs, CoverageOptions, ExecError, Halt, RunOptions, RunReport,
    Semantics, State, StopAt, StopRules, View,
};
use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const FIXTURE: &str = r##"
use k::builtin::{Int, KSequence};
use k::KItem;

k::sorts! {
    Op: KItem;
}

#[k::constructors(sort = Op, result = k::KResult)]
pub enum Step {
    /// Queue one unit of work, then the next boundary.
    #[k::syntax("#boundary")]
    Boundary,
    /// One unit of work.
    #[k::syntax("#work")]
    Work,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub count: Int,
}

impl Machine {
    #[k::init]
    pub fn init(start: Int) -> Self {
        Self {
            k: k::k![Step::Boundary],
            count: start,
        }
    }
}

k::rules! {
    for Machine;

    #[k::requires(count < 3)]
    boundary: {
        k: [Step::Boundary, ..],
        count,
    } => {
        k: [Step::Work, Step::Boundary, ..],
    };

    work: {
        k: [Step::Work, ..],
        count,
    } => {
        k: [..],
        count: count + 1,
    };
}
"##;
const PACKAGE: &str = "krs-exec-stop-rules-fixture";

/// The fixture's Definition IR and compiled stage, built once per test process.
fn compiled() -> &'static (DefinitionIr, CompiledStage) {
    static COMPILED: OnceLock<(DefinitionIr, CompiledStage)> = OnceLock::new();
    COMPILED.get_or_init(|| {
        let target = shared_fixture_target();
        let temporary = temp_dir();
        let project = temporary.path().join("language");
        fs::create_dir_all(project.join("src")).unwrap();
        fs::write(project.join("src/lib.rs"), FIXTURE).unwrap();
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        fs::write(
            project.join("Cargo.toml"),
            format!(
                "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-EXEC-STOPS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
            ),
        )
        .unwrap();
        let emitted = temporary.path().join("emitted");
        let mut process = krs_command!();
        fixture_build_env(&mut process, target.path());
        let output = process
            .current_dir(&project)
            .args(["emit-k", "--ir", "--manifest-path"])
            .arg(project.join("Cargo.toml"))
            .args(["--package", PACKAGE, "--definition", "main", "--output"])
            .arg(&emitted)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let definition: DefinitionIr =
            serde_json::from_slice(&fs::read(emitted.join("definition-ir.json")).unwrap())
                .unwrap();
        let stage = CompiledStage::compile(&definition, &mut Timings::disabled()).unwrap();
        (definition, stage)
    })
}

/// Run `test` on the fixture's semantics, on a thread with the stack every `krs-exec` operation
/// needs.
fn with_semantics(test: impl FnOnce(&mut Semantics) + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn_scoped(scope, || {
                let (definition, stage) = compiled();
                let mut semantics = Semantics::from_stage(
                    definition,
                    stage.clone(),
                    None,
                    &mut Timings::disabled(),
                )
                .unwrap();
                test(&mut semantics);
            })
            .unwrap()
            .join()
            .unwrap();
    });
}

fn initial(semantics: &mut Semantics) -> State {
    semantics
        .configure(&ConfigInputs {
            variables: vec![("start".to_owned(), "0".into())],
            ..ConfigInputs::default()
        })
        .unwrap()
}

/// The counter and the head of `<k>` of a report's state, the head as its constructor's syntax.
fn observe(semantics: &mut Semantics, report: &RunReport) -> (i64, String) {
    let View::State(view) = semantics.view(&report.state).unwrap() else {
        panic!("the state is defined");
    };
    let count = view.value("count").unwrap().as_i64().unwrap();
    let k = view.value("k").unwrap();
    let head = k
        .as_seq()
        .and_then(<[_]>::first)
        .and_then(krs_exec::Value::as_ctor)
        .map_or_else(
            || panic!("<k> is {k:?}"),
            |ctor| ctor.decl().path().to_owned(),
        );
    let head = match head.rsplit_once("::") {
        Some((_, "Boundary")) => "#boundary",
        Some((_, "Work")) => "#work",
        _ => panic!("<k> starts with {head}"),
    };
    (count, head.to_owned())
}

fn run(semantics: &mut Semantics, state: &State, stop: &StopRules) -> RunReport {
    semantics
        .run(
            state,
            RunOptions {
                stop: stop.clone(),
                ..RunOptions::default()
            },
        )
        .unwrap()
}

/// Run from the initial state to the end, resuming after every stop; each piece's steps and
/// whether it stopped, and the last piece's report.
fn pieces(semantics: &mut Semantics, stop: &StopRules) -> (Vec<(u64, bool)>, RunReport) {
    let mut state = initial(semantics);
    let mut pieces = Vec::new();
    loop {
        let report = run(semantics, &state, stop);
        let stopped = report.halt == Halt::Stopped;
        assert_eq!(stopped, report.stop.is_some(), "{report:?}");
        pieces.push((report.steps, stopped));
        if !stopped {
            return (pieces, report);
        }
        assert!(pieces.len() < 10, "the run does not end: {pieces:?}");
        state = report.resume();
    }
}

#[test]
fn a_run_stops_after_a_named_rule_and_resumes_from_its_state() {
    with_semantics(|semantics| {
        let start = initial(semantics);
        let whole = run(semantics, &start, &StopRules::default());
        assert_eq!((whole.halt, whole.steps), (Halt::Stuck, 6));
        assert!(whole.stop.is_none());
        assert_eq!(observe(semantics, &whole), (3, "#boundary".to_owned()));

        let after = StopRules {
            after: vec!["boundary".to_owned()],
            ..StopRules::default()
        };
        let start = initial(semantics);
        let first = run(semantics, &start, &after);
        assert_eq!((first.halt, first.steps), (Halt::Stopped, 1));
        let stop = first.stop.as_ref().unwrap();
        assert_eq!(stop.at, StopAt::After);
        let rule = stop.rule.as_ref().unwrap();
        assert!(
            rule.label.as_deref().unwrap().ends_with(".boundary"),
            "{rule:?}"
        );
        assert_eq!(rule.item.as_deref(), Some("boundary"), "{rule:?}");
        // The run ends at the rule's successor: the work is queued, nothing is counted yet.
        assert_eq!(observe(semantics, &first), (0, "#work".to_owned()));

        // A second run resumes from the returned state: it does the work, crosses the next
        // boundary and stops after it.
        let second = run(semantics, &first.resume(), &after);
        assert_eq!((second.halt, second.steps), (Halt::Stopped, 2));
        assert_eq!(observe(semantics, &second), (1, "#work".to_owned()));

        // Cut at every boundary, the pieces take the whole run's six steps and end where it ends.
        let (cut, last) = pieces(semantics, &after);
        assert_eq!(cut, [(1, true), (2, true), (2, true), (1, false)]);
        assert_eq!(last.halt, Halt::Stuck);
        assert_eq!(observe(semantics, &last), (3, "#boundary".to_owned()));
    });
}

#[test]
fn a_run_stops_before_a_named_rule_and_resumes_past_it() {
    with_semantics(|semantics| {
        let before = StopRules {
            before: vec!["boundary".to_owned()],
            ..StopRules::default()
        };
        // The first step is a boundary step, so the run ends where it starts.
        let start = initial(semantics);
        let first = run(semantics, &start, &before);
        assert_eq!((first.halt, first.steps), (Halt::Stopped, 0));
        let stop = first.stop.as_ref().unwrap();
        assert_eq!(stop.at, StopAt::Before);
        assert_eq!(
            stop.rule.as_ref().unwrap().item.as_deref(),
            Some("boundary")
        );
        assert_eq!(observe(semantics, &first), (0, "#boundary".to_owned()));
        // The next run takes the boundary step first, then does the work, and stops at the next
        // boundary: two steps, the boundary's counted.
        let second = run(semantics, &first.resume(), &before);
        assert_eq!((second.halt, second.steps), (Halt::Stopped, 2));
        assert_eq!(observe(semantics, &second), (1, "#boundary".to_owned()));

        // A depth bound of 0 leaves the boundary step untaken: the run ends where the stopped
        // one did, and resumes as it would.
        let held = semantics
            .run(
                &first.resume(),
                RunOptions {
                    depth: Some(0),
                    stop: before.clone(),
                    ..RunOptions::default()
                },
            )
            .unwrap();
        assert_eq!((held.halt, held.steps), (Halt::DepthBound, 0));
        assert_eq!(observe(semantics, &held), (0, "#boundary".to_owned()));
        let again = run(semantics, &held.resume(), &before);
        assert_eq!((again.halt, again.steps), (Halt::Stopped, 2));
        // A bound of 1 takes the boundary step alone.
        let one = semantics
            .run(
                &first.resume(),
                RunOptions {
                    depth: Some(1),
                    stop: before.clone(),
                    ..RunOptions::default()
                },
            )
            .unwrap();
        assert_eq!((one.halt, one.steps), (Halt::DepthBound, 1));
        assert_eq!(observe(semantics, &one), (0, "#work".to_owned()));

        // Each step is taken by one piece: the pieces' steps add up to the whole run's six.
        let (cut, last) = pieces(semantics, &before);
        assert_eq!(cut, [(0, true), (2, true), (2, true), (2, false)]);
        assert_eq!(cut.iter().map(|(steps, _)| steps).sum::<u64>(), 6);
        assert_eq!(last.halt, Halt::Stuck);
        assert_eq!(observe(semantics, &last), (3, "#boundary".to_owned()));
    });
}

#[test]
fn stop_rules_name_rewrite_rules_by_label() {
    with_semantics(|semantics| {
        let state = initial(semantics);
        let refused = |semantics: &mut Semantics, stop: StopRules| {
            semantics
                .run(
                    &state,
                    RunOptions {
                        stop,
                        ..RunOptions::default()
                    },
                )
                .unwrap_err()
        };
        let unknown = refused(
            semantics,
            StopRules {
                after: vec!["missing".to_owned()],
                ..StopRules::default()
            },
        );
        assert!(
            matches!(unknown, ExecError::UnknownRule { .. }),
            "{unknown:?}"
        );
        // The full label selects the rule as its suffix does.
        let label = run(
            semantics,
            &state,
            &StopRules {
                after: vec!["boundary".to_owned()],
                ..StopRules::default()
            },
        )
        .stop
        .unwrap()
        .rule
        .unwrap()
        .label
        .unwrap();
        let exact = run(
            semantics,
            &state,
            &StopRules {
                after: vec![label],
                ..StopRules::default()
            },
        );
        assert_eq!((exact.halt, exact.steps), (Halt::Stopped, 1));
    });
}

/// A run's coverage commits each rewrite rule a path took, with how many times (CF-15).
#[test]
fn coverage_counts_the_rewrite_rules_a_run_committed() {
    with_semantics(|semantics| {
        let start = initial(semantics);
        let report = semantics
            .run(
                &start,
                RunOptions {
                    coverage: Some(CoverageOptions::default()),
                    ..RunOptions::default()
                },
            )
            .unwrap();
        let coverage = report.coverage.unwrap();
        for item in ["boundary", "work"] {
            let rule = coverage
                .rules
                .iter()
                .find(|rule| rule.item.as_deref() == Some(item))
                .unwrap_or_else(|| panic!("{item}: {coverage:#?}"));
            assert!(rule.matched && rule.applied && rule.committed, "{rule:?}");
            assert_eq!(rule.applications, 3, "{rule:?}");
            assert_eq!(rule.kind, Some(krs_exec::RuleKind::Rule), "{rule:?}");
        }
    });
}

/// A rule's coverage and trace over a run cut at stop rules and resumed (CF-15, CF-22): each
/// step is in exactly one piece's `steps`, trace and coverage, so the pieces' traces in order are
/// the uncut run's, and their coverage, each predicate's identities united and the
/// applications summed, is the uncut run's.
#[test]
fn pieces_of_a_cut_run_trace_and_cover_what_the_uncut_run_does() {
    type Covered = BTreeMap<String, (bool, bool, bool, u64)>;
    let traced = |stop: &StopRules| RunOptions {
        trace: true,
        coverage: Some(CoverageOptions::default()),
        stop: stop.clone(),
        ..RunOptions::default()
    };
    let add = |covered: &mut Covered, report: &RunReport| {
        for rule in &report.coverage.as_ref().unwrap().rules {
            let entry = covered.entry(rule.rule_id.clone()).or_default();
            entry.0 |= rule.matched;
            entry.1 |= rule.applied;
            entry.2 |= rule.committed;
            entry.3 += rule.applications;
        }
    };
    with_semantics(|semantics| {
        let start = initial(semantics);
        let whole = semantics
            .run(&start, traced(&StopRules::default()))
            .unwrap();
        let whole_trace = whole
            .trace
            .iter()
            .map(|step| step.rule_id.clone())
            .collect::<Vec<_>>();
        assert_eq!(whole_trace.len(), 6);
        let mut whole_coverage = Covered::new();
        add(&mut whole_coverage, &whole);

        for stop in [
            StopRules {
                before: vec!["boundary".to_owned()],
                ..StopRules::default()
            },
            StopRules {
                after: vec!["boundary".to_owned()],
                ..StopRules::default()
            },
            StopRules {
                before: vec!["work".to_owned()],
                after: vec!["boundary".to_owned()],
            },
        ] {
            let mut state = initial(semantics);
            let mut trace = Vec::new();
            let mut steps = 0;
            let mut covered = Covered::new();
            for _ in 0..10 {
                let report = semantics.run(&state, traced(&stop)).unwrap();
                assert_eq!(
                    report
                        .trace
                        .iter()
                        .map(|step| step.index)
                        .collect::<Vec<_>>(),
                    (1..=report.steps).collect::<Vec<_>>(),
                    "{stop:?}: {report:?}"
                );
                trace.extend(report.trace.iter().map(|step| step.rule_id.clone()));
                steps += report.steps;
                add(&mut covered, &report);
                if report.halt != Halt::Stopped {
                    assert_eq!(report.halt, Halt::Stuck);
                    break;
                }
                state = report.resume();
            }
            assert_eq!(steps, 6, "{stop:?}");
            assert_eq!(trace, whole_trace, "{stop:?}");
            assert_eq!(covered, whole_coverage, "{stop:?}");
        }
    });
}
