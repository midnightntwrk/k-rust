//! `krs-exec` stop rules, counted stops and resumable states on authored definitions (CF-22,
//! CF-21).
//!
//! The first fixture is a machine that runs in boundary steps, as Foldiboy's SM83 does:
//! `boundary` queues one unit of work and the next `#boundary` while the counter is below 3, and
//! `work` counts it, so the whole run is six steps, `boundary` and `work` three times each, and
//! ends stuck at `#boundary` with the counter at 3.
//!
//! The second ([`FREE_RUNNING`]) is the same machine without the guard, which never ends on its
//! own: the end of a run of it is the observer's, a counted stop. Its unit of work is an amount
//! evaluated first, through the context `work_amount`, so one frame is five steps: `boundary`,
//! the context's heat rule, `add`, its cool rule, and `work`.
//!
//! The third ([`STRICT`]) evaluates `(1 + 2) + 3` through a `#[k::seqstrict]` variant, so its
//! run is four steps: the heat rule of the left operand, `add`, the cool rule, and `add`.

use std::collections::BTreeMap;
use std::fs;
use std::num::NonZeroU64;
use std::path::Path;
use std::sync::OnceLock;

use krs_exec::{
    CompiledStage, ConfigInputs, CoverageOptions, ExecError, Halt, RunOptions, RunReport,
    Semantics, State, StopAt, StopCriterion, StopRules, View,
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

/// The machine of [`FIXTURE`] without its guard, its work an amount evaluated first.
const FREE_RUNNING: &str = r##"
use k::builtin::{Int, KSequence, int};
use k::{KItem, KResult, Term};

k::sorts! {
    Op: KItem;
    #[k::bracket("(", ")")]
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Op, result = KResult)]
pub enum Step {
    /// Queue one unit of work, then the next boundary.
    #[k::syntax("#boundary")]
    Boundary,
    /// Count the work's amount, once it is a value.
    #[k::syntax("#work({amount})")]
    Work { amount: Exp },
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence(left (Add))]
pub enum Arith {
    #[k::syntax("{lhs} + {rhs}")]
    Add { lhs: Exp, rhs: Exp },
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
    for Exp;
    use Arith::*;

    add: Add { lhs, rhs } => int::add(lhs, rhs) where lhs: Int, rhs: Int;
}

k::rules! {
    for Machine;

    boundary: {
        k: [Step::Boundary, ..],
    } => {
        k: [Step::Work { amount: Arith::Add { lhs: 1, rhs: 0 } }, Step::Boundary, ..],
    };

    work: {
        k: [Step::Work { amount }, ..],
        count,
    } => {
        k: [..],
        count: count + amount,
    } where amount: Int;
}

/// The amount is evaluated before the work counts it: K's `context #work(HOLE)`.
#[k::context(hole = h)]
fn work_amount(k::term![Step::Work(h)]: Term<Op>) {}
"##;
const FREE_RUNNING_PACKAGE: &str = "krs-exec-free-running-fixture";

/// A sum evaluated through the rules K generates for a strict variant.
const STRICT: &str = r#"
use k::builtin::{Int, KSequence, int};
use k::KResult;

k::sorts! {
    #[k::bracket("(", ")")]
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence(left (Add))]
pub enum Arith {
    #[k::syntax("{lhs} + {rhs}")]
    #[k::seqstrict]
    Add { lhs: Exp, rhs: Exp },
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
            k: k::k![Arith::Add { lhs: Arith::Add { lhs: 1, rhs: 2 }, rhs: 3 }],
            count: start,
        }
    }
}

k::rules! {
    for Exp;
    use Arith::*;

    add: Add { lhs, rhs } => int::add(lhs, rhs) where lhs: Int, rhs: Int;
}
"#;
const STRICT_PACKAGE: &str = "krs-exec-strict-fixture";

/// A Cargo project of the KRS definition `source`, as package `package`.
fn project(source: &str, package: &str, namespace: &str) -> krs_test_support::TempDir {
    let temporary = temp_dir();
    let project = temporary.path().join("language");
    fs::create_dir_all(project.join("src")).unwrap();
    fs::write(project.join("src/lib.rs"), source).unwrap();
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
    fs::write(
        project.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{package}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
        ),
    )
    .unwrap();
    temporary
}

/// A fixture's Definition IR and compiled stage.
fn compile(source: &str, package: &str, namespace: &str) -> (DefinitionIr, CompiledStage) {
    let target = shared_fixture_target();
    let temporary = project(source, package, namespace);
    let project = temporary.path().join("language");
    let emitted = temporary.path().join("emitted");
    let mut process = krs_command!();
    fixture_build_env(&mut process, target.path());
    let output = process
        .current_dir(&project)
        .args(["emit-k", "--ir", "--manifest-path"])
        .arg(project.join("Cargo.toml"))
        .args(["--package", package, "--definition", "main", "--output"])
        .arg(&emitted)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let definition: DefinitionIr =
        serde_json::from_slice(&fs::read(emitted.join("definition-ir.json")).unwrap()).unwrap();
    let stage = CompiledStage::compile(&definition, &mut Timings::disabled()).unwrap();
    (definition, stage)
}

/// [`FIXTURE`]'s Definition IR and compiled stage, built once per test process.
fn compiled() -> &'static (DefinitionIr, CompiledStage) {
    static COMPILED: OnceLock<(DefinitionIr, CompiledStage)> = OnceLock::new();
    COMPILED.get_or_init(|| compile(FIXTURE, PACKAGE, "ORG-KRS-EXEC-STOPS"))
}

/// [`FREE_RUNNING`]'s Definition IR and compiled stage, built once per test process.
fn free_running() -> &'static (DefinitionIr, CompiledStage) {
    static COMPILED: OnceLock<(DefinitionIr, CompiledStage)> = OnceLock::new();
    COMPILED.get_or_init(|| compile(FREE_RUNNING, FREE_RUNNING_PACKAGE, "ORG-KRS-EXEC-FREE"))
}

/// [`STRICT`]'s Definition IR and compiled stage, built once per test process.
fn strict() -> &'static (DefinitionIr, CompiledStage) {
    static COMPILED: OnceLock<(DefinitionIr, CompiledStage)> = OnceLock::new();
    COMPILED.get_or_init(|| compile(STRICT, STRICT_PACKAGE, "ORG-KRS-EXEC-STRICT"))
}

/// Run `test` on the fixture's semantics, on a thread with the stack every `krs-exec` operation
/// needs.
fn with_semantics(test: impl FnOnce(&mut Semantics) + Send) {
    on(compiled(), test);
}

/// Run `test` on the semantics of `fixture`, on a thread with the stack every `krs-exec`
/// operation needs.
fn on(fixture: &'static (DefinitionIr, CompiledStage), test: impl FnOnce(&mut Semantics) + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn_scoped(scope, || {
                let (definition, stage) = fixture;
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
        Some((_, "Add")) => "+",
        _ => panic!("<k> starts with {head}"),
    };
    (count, head.to_owned())
}

fn run(semantics: &mut Semantics, state: &State, stop: &StopRules) -> RunReport {
    semantics
        .run(
            state,
            RunOptions {
                stop: stop.clone().into(),
                ..RunOptions::default()
            },
        )
        .unwrap()
}

/// The criterion that ends a run at the `count`th arrival at a stop of `rules`.
fn counted(rules: &StopRules, count: u64) -> StopCriterion {
    StopCriterion::Rules {
        rules: rules.clone(),
        count: NonZeroU64::new(count).unwrap(),
    }
}

fn after(name: &str) -> StopRules {
    StopRules {
        after: vec![name.to_owned()],
        ..StopRules::default()
    }
}

fn before(name: &str) -> StopRules {
    StopRules {
        before: vec![name.to_owned()],
        ..StopRules::default()
    }
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
                    stop: before.clone().into(),
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
                    stop: before.clone().into(),
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
                        stop: stop.into(),
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
    let traced = |stop: &StopRules| RunOptions {
        trace: true,
        coverage: Some(CoverageOptions::default()),
        stop: stop.clone().into(),
        ..RunOptions::default()
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
        cover(&mut whole_coverage, &whole);

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
                cover(&mut covered, &report);
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

/// Coverage summed over runs: by identity, whether each predicate held in some run, and the
/// applications added up.
type Covered = BTreeMap<String, (bool, bool, bool, u64)>;

fn cover(covered: &mut Covered, report: &RunReport) {
    for rule in &report.coverage.as_ref().unwrap().rules {
        let entry = covered.entry(rule.rule_id.clone()).or_default();
        entry.0 |= rule.matched;
        entry.1 |= rule.applied;
        entry.2 |= rule.committed;
        entry.3 += rule.applications;
    }
}

fn rule_ids(report: &RunReport) -> Vec<String> {
    report
        .trace
        .iter()
        .map(|step| step.rule_id.clone())
        .collect()
}

fn stopping(stop: StopCriterion) -> RunOptions {
    RunOptions {
        stop,
        ..RunOptions::default()
    }
}

/// A run under a count ends at the Nth arrival at a stop, which is where the uncut run is after
/// as many steps: the count adds an end and changes no step (CF-21).
#[test]
fn a_counted_stop_ends_at_the_nth_arrival() {
    on(free_running(), |semantics| {
        let start = initial(semantics);
        // After `boundary`: the arrivals are steps 1, 6 and 11, the third frame's work queued.
        let third = semantics
            .run(&start, stopping(counted(&after("boundary"), 3)))
            .unwrap();
        assert_eq!(
            (third.halt, third.steps, third.stops),
            (Halt::Stopped, 11, 3)
        );
        let stop = third.stop.as_ref().unwrap();
        assert_eq!((stop.at, stop.nth), (StopAt::After, 3));
        assert_eq!(
            stop.rule.as_ref().unwrap().item.as_deref(),
            Some("boundary")
        );
        assert_eq!(observe(semantics, &third), (2, "#work".to_owned()));
        let bounded = semantics
            .run(
                &start,
                RunOptions {
                    depth: Some(11),
                    ..RunOptions::default()
                },
            )
            .unwrap();
        assert_eq!(
            (bounded.halt, bounded.steps, bounded.stops),
            (Halt::DepthBound, 11, 0)
        );
        assert_eq!(bounded.state.kore(), third.state.kore());

        // Before `work`: the second arrival is the state the second frame's work step
        // rewrites, after 9 steps.
        let second = semantics
            .run(&start, stopping(counted(&before("work"), 2)))
            .unwrap();
        assert_eq!(
            (second.halt, second.steps, second.stops),
            (Halt::Stopped, 9, 2)
        );
        let stop = second.stop.as_ref().unwrap();
        assert_eq!((stop.at, stop.nth), (StopAt::Before, 2));
        assert_eq!(observe(semantics, &second), (1, "#work".to_owned()));
        // Resumed, a counted run takes the step it stopped before first, then counts afresh:
        // the next frame's work step, then two frames more to the fourth work step.
        let next = semantics
            .run(&second.resume(), stopping(counted(&before("work"), 2)))
            .unwrap();
        assert_eq!((next.halt, next.steps, next.stops), (Halt::Stopped, 10, 2));
        assert_eq!(observe(semantics, &next), (3, "#work".to_owned()));

        // A count of 1 is the stop rules' own criterion.
        let first = semantics
            .run(&start, stopping(counted(&after("boundary"), 1)))
            .unwrap();
        let plain = run(semantics, &start, &after("boundary"));
        assert_eq!(
            (first.steps, first.stops, &first.stop),
            (plain.steps, plain.stops, &plain.stop)
        );
        assert_eq!((first.stops, first.stop.unwrap().nth), (1, 1));

        // A step budget bounds the run, and is never an end: a bound short of the third
        // arrival ends the run depth-bound, after two.
        let short = semantics
            .run(
                &start,
                RunOptions {
                    depth: Some(8),
                    stop: counted(&after("boundary"), 3),
                    ..RunOptions::default()
                },
            )
            .unwrap();
        assert_eq!(
            (short.halt, short.steps, short.stops, short.stop.is_none()),
            (Halt::DepthBound, 8, 2, true)
        );
    });
}

/// A run that ends on its own before the Nth arrival reports that end, and how many arrivals
/// it counted.
#[test]
fn a_run_that_ends_before_the_nth_stop_reports_its_own_end_and_stops_passed() {
    with_semantics(|semantics| {
        let start = initial(semantics);
        for (stop, count) in [
            (after("boundary"), 5),
            (before("boundary"), 4),
            (before("work"), 9),
        ] {
            let report = semantics
                .run(&start, stopping(counted(&stop, count)))
                .unwrap();
            assert_eq!(
                (report.halt, report.steps, report.stops),
                (Halt::Stuck, 6, 3),
                "{stop:?}"
            );
            assert!(report.stop.is_none(), "{report:?}");
            assert_eq!(observe(semantics, &report), (3, "#boundary".to_owned()));
            let json = serde_json::to_value(&report).unwrap();
            assert_eq!(json["stops"], 3, "{json}");
            assert!(json.get("stop").is_none(), "{json}");
        }
        // With exactly as many arrivals as the run has, it ends at the last.
        let third = semantics
            .run(&start, stopping(counted(&before("boundary"), 3)))
            .unwrap();
        assert_eq!(
            (third.halt, third.steps, third.stops),
            (Halt::Stopped, 4, 3)
        );
        assert_eq!(observe(semantics, &third), (2, "#boundary".to_owned()));
        let json = serde_json::to_value(&third).unwrap();
        assert_eq!(
            (&json["stops"], &json["stop"]["nth"]),
            (&3.into(), &3.into())
        );
        // A run with no stop, or at its first, says nothing more than before.
        let whole = serde_json::to_value(run(semantics, &start, &StopRules::default())).unwrap();
        assert!(whole.get("stops").is_none(), "{whole}");
        let once = serde_json::to_value(run(semantics, &start, &after("boundary"))).unwrap();
        assert!(once["stop"].get("nth").is_none(), "{once}");
        assert_eq!(once["stops"], 1, "{once}");
    });
}

/// Over a run cut at counted stops and resumed, each step is in exactly one piece, so the
/// pieces' steps, traces in order and coverage are the uncut run's; and a counted run is its
/// pieces at a count of 1, joined, its trace that of the uncut run bounded at as many steps.
///
/// The fixtures' equations are builtin operations, which no memo serves, so coverage's counts
/// are compared too.
#[test]
fn counted_pieces_sum_to_the_uncut_run() {
    let options = |stop: StopCriterion| RunOptions {
        trace: true,
        coverage: Some(CoverageOptions::default()),
        stop,
        ..RunOptions::default()
    };
    with_semantics(|semantics| {
        let start = initial(semantics);
        let whole = semantics.run(&start, options(StopCriterion::None)).unwrap();
        let whole_trace = rule_ids(&whole);
        let mut whole_coverage = Covered::new();
        cover(&mut whole_coverage, &whole);
        for stop in [
            before("boundary"),
            after("boundary"),
            StopRules {
                before: vec!["work".to_owned()],
                after: vec!["boundary".to_owned()],
            },
        ] {
            for count in [2, 3] {
                let mut state = initial(semantics);
                let mut trace = Vec::new();
                let mut steps = 0;
                let mut covered = Covered::new();
                for _ in 0..10 {
                    let report = semantics
                        .run(&state, options(counted(&stop, count)))
                        .unwrap();
                    assert_eq!(
                        report
                            .trace
                            .iter()
                            .map(|step| step.index)
                            .collect::<Vec<_>>(),
                        (1..=report.steps).collect::<Vec<_>>(),
                        "{stop:?} {count}: {report:?}"
                    );
                    trace.extend(rule_ids(&report));
                    steps += report.steps;
                    cover(&mut covered, &report);
                    if report.halt != Halt::Stopped {
                        assert_eq!(report.halt, Halt::Stuck);
                        assert!(report.stops < count, "{report:?}");
                        break;
                    }
                    assert_eq!(report.stops, count, "{report:?}");
                    state = report.resume();
                }
                assert_eq!(steps, 6, "{stop:?} {count}");
                assert_eq!(trace, whole_trace, "{stop:?} {count}");
                assert_eq!(covered, whole_coverage, "{stop:?} {count}");
            }
        }
    });
    on(free_running(), |semantics| {
        let start = initial(semantics);
        for (stop, count) in [
            (after("boundary"), 3),
            (before("work"), 2),
            (after("crate::work_amount"), 3),
            (before("crate::work_amount"), 4),
        ] {
            let joined = semantics
                .run(&start, options(counted(&stop, count)))
                .unwrap();
            assert_eq!(joined.stops, count, "{stop:?}");
            let mut state = start.clone();
            let mut trace = Vec::new();
            let mut steps = 0;
            let mut covered = Covered::new();
            let mut last = None;
            for _ in 0..count {
                let piece = semantics.run(&state, options(stop.clone().into())).unwrap();
                assert_eq!(piece.halt, Halt::Stopped, "{stop:?}");
                trace.extend(rule_ids(&piece));
                steps += piece.steps;
                cover(&mut covered, &piece);
                state = piece.resume();
                last = Some(piece);
            }
            let last = last.unwrap();
            assert_eq!(joined.steps, steps, "{stop:?}");
            assert_eq!(rule_ids(&joined), trace, "{stop:?}");
            let mut joined_coverage = Covered::new();
            cover(&mut joined_coverage, &joined);
            assert_eq!(joined_coverage, covered, "{stop:?}");
            assert_eq!(joined.state.kore(), last.state.kore(), "{stop:?}");
            assert_eq!(joined.resume().kore(), last.resume().kore(), "{stop:?}");
            assert_uncut_to(semantics, &start, &joined);
        }
    });
}

/// The uncut run from `start` to where `joined` ended, bounded at as many steps, since the
/// free-running machine has no own end, takes `joined`'s steps to its state; `joined` numbers
/// them along the whole path, as the uncut run does.
fn assert_uncut_to(semantics: &mut Semantics, start: &State, joined: &RunReport) {
    assert_eq!(
        joined
            .trace
            .iter()
            .map(|step| step.index)
            .collect::<Vec<_>>(),
        (1..=joined.steps).collect::<Vec<_>>(),
        "{joined:?}"
    );
    let uncut = semantics
        .run(
            start,
            RunOptions {
                depth: Some(joined.steps),
                trace: true,
                ..RunOptions::default()
            },
        )
        .unwrap();
    assert_eq!(uncut.halt, Halt::DepthBound, "{joined:?}");
    assert_eq!(rule_ids(&uncut), rule_ids(joined), "{joined:?}");
    assert_eq!(uncut.state.kore(), joined.state.kore(), "{joined:?}");
}

/// A stop named by a KRS item is a step by any rewrite rule the item lowers to: the context
/// `work_amount` lowers to a heat rule and a cool rule, whose labels differ from each other and
/// from the item.
#[test]
fn a_stop_named_by_krs_item_selects_every_sentence_of_the_item() {
    on(free_running(), |semantics| {
        let start = initial(semantics);
        let traced = |stop: StopCriterion| RunOptions {
            trace: true,
            stop,
            ..RunOptions::default()
        };
        // After the item: its arrivals are the heat step (2) and the cool step (4).
        let item = semantics
            .run(&start, traced(counted(&after("crate::work_amount"), 2)))
            .unwrap();
        assert_eq!((item.halt, item.steps), (Halt::Stopped, 4), "{item:?}");
        let rule = item.stop.as_ref().unwrap().rule.as_ref().unwrap();
        assert_eq!(rule.item.as_deref(), Some("work_amount"), "{rule:?}");
        // The name a report gives the stop selects it again.
        assert_eq!(
            semantics.stop_name(&rule.rule_id).as_deref(),
            Some("crate::work_amount")
        );
        assert_eq!(observe(semantics, &item), (0, "#work".to_owned()));
        let heat = item.trace[1].label.clone().unwrap();
        let cool = item.trace[3].label.clone().unwrap();
        assert_ne!(heat, cool);
        assert_eq!(rule.label.as_ref(), Some(&cool), "{rule:?}");
        // The heat rule's label selects it alone: its second arrival is the second frame's
        // heat step.
        let label = semantics
            .run(&start, traced(counted(&after(&heat), 2)))
            .unwrap();
        assert_eq!((label.halt, label.steps), (Halt::Stopped, 7), "{label:?}");
        // Before the item: the first arrival is the state the first heat step rewrites.
        let first = run(semantics, &start, &before("crate::work_amount"));
        assert_eq!((first.halt, first.steps), (Halt::Stopped, 1));
        assert_eq!(
            first.stop.unwrap().rule.unwrap().item.as_deref(),
            Some("work_amount")
        );
        // A rule at the crate root is its own item, as it is its own label's suffix.
        let root = run(semantics, &start, &after("crate::boundary"));
        assert_eq!((root.halt, root.steps), (Halt::Stopped, 1));
        // An item with no sentence is refused.
        let refused = semantics
            .run(&start, stopping(after("crate::missing").into()))
            .unwrap_err();
        assert!(
            matches!(&refused, ExecError::UnknownItem { kinds, .. } if kinds.is_empty()),
            "{refused:?}"
        );
        // The item's name, written as a label, is no label, and the refusal names the item.
        let label = semantics
            .run(&start, stopping(after("work_amount").into()))
            .unwrap_err();
        assert_eq!(
            label.to_string(),
            "no rewrite rule has label `work_amount`; did you mean `crate::work_amount`?"
        );
    });
}

/// A stop named by a strict variant is a step by any of the heat and cool rules K generates
/// for it, which carry the variant as their item (not the grammar registration the expansion
/// generated for it), named through its enum as Rust names it.
#[test]
fn a_stop_named_by_a_strict_variant_selects_its_heat_and_cool_rules() {
    on(strict(), |semantics| {
        let start = initial(semantics);
        let traced = |stop: StopCriterion| RunOptions {
            trace: true,
            stop,
            ..RunOptions::default()
        };
        let whole = semantics.run(&start, traced(StopCriterion::None)).unwrap();
        assert_eq!((whole.halt, whole.steps), (Halt::Stuck, 4), "{whole:?}");
        let variant = after("crate::Arith::Add");
        // The heat step is the first arrival, the cool step the second, and the run ends on its
        // own before a third.
        let heat = semantics.run(&start, traced(counted(&variant, 1))).unwrap();
        assert_eq!((heat.halt, heat.steps), (Halt::Stopped, 1), "{heat:?}");
        let cool = semantics.run(&start, traced(counted(&variant, 2))).unwrap();
        assert_eq!((cool.halt, cool.steps), (Halt::Stopped, 3), "{cool:?}");
        assert_ne!(cool.trace[0].rule_id, cool.trace[2].rule_id);
        assert_eq!(rule_ids(&cool), rule_ids(&whole)[..3]);
        let rule = cool.stop.as_ref().unwrap().rule.as_ref().unwrap();
        assert_eq!(rule.rule_id, cool.trace[2].rule_id);
        assert_eq!(rule.item.as_deref(), Some("Arith::Add"), "{rule:?}");
        assert_eq!(
            semantics.stop_name(&rule.rule_id).as_deref(),
            Some("crate::Arith::Add")
        );
        let third = semantics.run(&start, traced(counted(&variant, 3))).unwrap();
        assert_eq!(
            (third.halt, third.steps, third.stops),
            (Halt::Stuck, 4, 2),
            "{third:?}"
        );
        // Before the variant: the initial state's one successor is its heat step.
        let before_heat = run(semantics, &start, &before("crate::Arith::Add"));
        assert_eq!(
            (before_heat.halt, before_heat.steps),
            (Halt::Stopped, 0),
            "{before_heat:?}"
        );
        // A variant's Rust path goes through its enum.
        assert!(matches!(
            semantics
                .run(&start, stopping(after("crate::Add").into()))
                .unwrap_err(),
            ExecError::UnknownItem { .. }
        ));
    });
}

/// `krs run --stop-after NAME --stop-count N` ends at the Nth arrival and says so on its status
/// line and in its report; one that ends on its own first says how many it counted.
#[test]
fn krs_run_counts_stops_and_reports_them() {
    let target = shared_fixture_target();
    let temporary = project(FREE_RUNNING, FREE_RUNNING_PACKAGE, "ORG-KRS-EXEC-FREE");
    let project = temporary.path().join("language");
    let run = |extra: &[&str]| {
        let mut process = krs_command!();
        fixture_build_env(&mut process, target.path());
        let output = process
            .current_dir(&project)
            .args(["run", "--manifest-path"])
            .arg(project.join("Cargo.toml"))
            .args(["--package", FREE_RUNNING_PACKAGE, "--definition", "main"])
            .args(["-c", "start=0"])
            .args(extra)
            .output()
            .unwrap();
        (
            output.status.code(),
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap(),
        )
    };
    let (status, _, stderr) = run(&[
        "--stop-after",
        "crate::work_amount",
        "--stop-count",
        "3",
        "--output",
        "none",
    ]);
    assert_eq!(status, Some(0), "{stderr}");
    // The two rules the item selects leave the stop's rule unnamed without a trace, so the line
    // names the stop by the item as written.
    assert!(
        stderr.contains("krs run: stopped after 7 steps, after `crate::work_amount` (stop 3 of 3)"),
        "{stderr}"
    );
    // A stop whose rule the report names is named by its item's spelling, which the flag
    // takes back.
    for name in ["boundary", "crate::boundary"] {
        let (status, _, stderr) = run(&[
            "--stop-after",
            name,
            "--stop-count",
            "3",
            "--output",
            "none",
        ]);
        assert_eq!(status, Some(0), "{stderr}");
        assert!(
            stderr
                .contains("krs run: stopped after 11 steps, after `crate::boundary` (stop 3 of 3)"),
            "{stderr}"
        );
    }
    let (status, stdout, stderr) = run(&[
        "--stop-before",
        "work",
        "--stop-count",
        "2",
        "--depth",
        "6",
        "--output",
        "json",
    ]);
    assert_eq!(status, Some(0), "{stderr}");
    assert!(
        stderr.contains("krs run: depth-bound after 6 steps, 1 of 2 stops reached"),
        "{stderr}"
    );
    let report: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(report["run"]["stops"], 1, "{report}");
    assert_eq!(report["run"]["halt"], "depth-bound", "{report}");
    let (status, _, stderr) = run(&["--stop-count", "2"]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains("--stop-count needs --stop-before or --stop-after"),
        "{stderr}"
    );
}
