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
//!
//! The fourth ([`BRANCHING`]) takes `boundary`, the start's one successor, to `toss(0)`, which
//! has two, `done(1)` and `done(0)`, by the rules of the `nondet` group `toss`.
//!
//! The fifth ([`CHOICE_AT_STOP`]) has a choice at a stop rule: `advance` and `leap`, one
//! `nondet` group, are both enabled at the start.

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

/// A step with one successor, then a state with two.
const BRANCHING: &str = r##"
use k::builtin::{Int, KSequence};
use k::{KItem, KResult, Term};

k::sorts! {
    Op: KItem;
}

#[k::constructors(sort = Op, result = KResult)]
#[rustfmt::skip]
pub enum Step {
    #[k::syntax("#boundary")] Boundary,
    #[k::syntax("toss({value})")] Toss { value: Int },
    #[k::syntax("done({value})")] Done { value: Int },
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

    boundary: {
        k: [Step::Boundary, ..],
        count,
    } => {
        k: [Step::Toss { value: count }, ..],
    };
}

#[k::rule(nondet = toss)]
fn toss_heads(k::term![Step::Toss { value }]: Term<Op>) -> Term<Op> {
    Step::Done(1)
}

#[k::rule(nondet = toss)]
fn toss_tails(k::term![Step::Toss { value }]: Term<Op>) -> Term<Op> {
    Step::Done(0)
}
"##;
const BRANCHING_PACKAGE: &str = "krs-exec-branching-fixture";

/// `advance` and `leap` are one `nondet` group, both enabled at phase 0, so the start has two
/// successors. A run takes `advance` there to phase 1, `leap`, the only rule at phase 1, to
/// phase 3, and `advance`, the only rule at phase 3, to phase 4, where it is stuck. `Start`
/// holds at phase 0 only, `Reached` at every phase of the run.
const CHOICE_AT_STOP: &str = r##"
use k::builtin::{Bool, Int, KSequence};
use k::{KItem, KResult, Term};

k::sorts! {
    Op: KItem;
}

#[k::constructors(sort = Op, result = KResult)]
pub enum Step {
    #[k::syntax("#go")]
    Go,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub phase: Int,
    #[k::cell]
    pub ticks: Int,
}

impl Machine {
    #[k::init]
    pub fn init(start: Int) -> Self {
        Self {
            k: k::k![Step::Go],
            phase: start,
            ticks: 0,
        }
    }
}

k::rules! {
    for Machine;

    #[k::rule(nondet = toss)]
    #[k::requires(phase == 0 || phase == 3)]
    advance: {
        k: [Step::Go, ..],
        phase,
        ticks,
    } => {
        phase: phase + 1,
        ticks: ticks + 1,
    };

    #[k::rule(nondet = toss)]
    #[k::requires(phase < 3)]
    leap: {
        k: [Step::Go, ..],
        phase,
    } => {
        phase: phase + 2,
    };
}

#[k::function(total, internal)]
pub fn Start(phase: Term<Int>) -> Term<Bool> {
    phase == 0
}

#[k::function(total, internal)]
pub fn Reached(phase: Term<Int>) -> Term<Bool> {
    phase >= 0
}
"##;
const CHOICE_AT_STOP_PACKAGE: &str = "krs-exec-stop-choice-fixture";

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

/// [`BRANCHING`]'s Definition IR and compiled stage, built once per test process.
fn branching() -> &'static (DefinitionIr, CompiledStage) {
    static COMPILED: OnceLock<(DefinitionIr, CompiledStage)> = OnceLock::new();
    COMPILED.get_or_init(|| compile(BRANCHING, BRANCHING_PACKAGE, "ORG-KRS-EXEC-BRANCH"))
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
        when: None,
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
        assert_eq!(rule.item.as_deref(), Some("crate::boundary"), "{rule:?}");
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
            Some("crate::boundary")
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
        for item in ["crate::boundary", "crate::work"] {
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
            Some("crate::boundary")
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

/// A counted run's other ends are looked for along all its pieces, each from the stop the one
/// before it passed: in [`BRANCHING`], the run to the first stop after or before `boundary` chose
/// nothing, but a run counting two stops passes the first and takes one successor of `toss(0)`,
/// as the uncut run does, at the same step.
#[test]
fn other_ends_of_a_counted_run_are_looked_for_past_its_earlier_stops() {
    on(branching(), |semantics| {
        let start = initial(semantics);
        let uncut = RunOptions::default();
        let report = semantics.run(&start, uncut.clone()).unwrap();
        let choice = semantics.other_ends(&start, &uncut, &report).unwrap();
        assert!(
            choice.as_deref().is_some_and(
                |reason| reason.contains("the state after 1 step, which has 2 successors")
            ),
            "{choice:?}"
        );
        for stop in [after("boundary"), before("boundary")] {
            let first = stopping(counted(&stop, 1));
            let report = semantics.run(&start, first.clone()).unwrap();
            assert_eq!(report.halt, Halt::Stopped, "{stop:?}");
            assert_eq!(
                semantics.other_ends(&start, &first, &report).unwrap(),
                None,
                "{stop:?}"
            );
            let second = stopping(counted(&stop, 2));
            let report = semantics.run(&start, second.clone()).unwrap();
            assert_eq!((report.halt, report.stops), (Halt::Stuck, 1), "{stop:?}");
            assert_eq!(
                semantics.other_ends(&start, &second, &report).unwrap(),
                choice,
                "{stop:?}"
            );
        }
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

/// A run as its pieces would join it, compared field by field ([`staged`]).
#[derive(Debug, Eq, PartialEq)]
struct Joined {
    halt: Halt,
    steps: u64,
    state: String,
    resume: String,
    trace: Vec<String>,
    covered: Covered,
    stops: u64,
    stop: Option<(StopAt, Option<String>, u64)>,
}

impl Joined {
    fn of(report: &RunReport) -> Self {
        assert_eq!(
            report
                .trace
                .iter()
                .map(|step| step.index)
                .collect::<Vec<_>>(),
            (1..=report.steps).collect::<Vec<_>>(),
            "{report:?}"
        );
        let mut covered = Covered::new();
        cover(&mut covered, report);
        Self {
            halt: report.halt,
            steps: report.steps,
            state: report.state.kore().to_string(),
            resume: report.resume().kore().to_string(),
            trace: rule_ids(report),
            covered,
            stops: report.stops,
            stop: report.stop.as_ref().map(|stop| {
                (
                    stop.at,
                    stop.rule.as_ref().map(|rule| rule.rule_id.clone()),
                    stop.nth,
                )
            }),
        }
    }
}

/// The staged form of a run under `count` arrivals at a stop of `rules` within `depth` steps:
/// the run to the first arrival, resumed from each arrival before the `count`th
/// ([`RunReport::resume`]) with the bound the pieces before it left, its pieces joined: the end
/// the last piece's, the steps, traces and coverage summed, the arrivals the pieces that stopped.
fn staged(
    semantics: &mut Semantics,
    start: &State,
    rules: &StopRules,
    count: u64,
    depth: Option<u64>,
) -> Joined {
    let mut state = start.clone();
    let mut steps = 0;
    let mut trace = Vec::new();
    let mut covered = Covered::new();
    let mut arrivals = 0;
    loop {
        let piece = semantics
            .run(
                &state,
                RunOptions {
                    depth: depth.map(|depth| depth.saturating_sub(steps)),
                    trace: true,
                    coverage: Some(CoverageOptions::default()),
                    stop: rules.clone().into(),
                    ..RunOptions::default()
                },
            )
            .unwrap();
        steps += piece.steps;
        trace.extend(rule_ids(&piece));
        cover(&mut covered, &piece);
        let stopped = piece.halt == Halt::Stopped;
        arrivals += u64::from(stopped);
        if !stopped || arrivals == count {
            return Joined {
                halt: piece.halt,
                steps,
                state: piece.state.kore().to_string(),
                resume: piece.resume().kore().to_string(),
                trace,
                covered,
                stops: arrivals,
                stop: piece.stop.as_ref().map(|stop| {
                    (
                        stop.at,
                        stop.rule.as_ref().map(|rule| rule.rule_id.clone()),
                        arrivals,
                    )
                }),
            };
        }
        state = piece.resume();
    }
}

/// A fixture, the stops to run it under and the depth bounds to run each under.
type Row = (
    &'static (DefinitionIr, CompiledStage),
    Vec<StopRules>,
    Vec<Option<u64>>,
);

/// A counted run is one backend request, and is its staged form: over every fixture, stops
/// before and after rules named by label and by KRS item, every count up to past the arrivals a
/// run has, and depth bounds that cut before, at and after arrivals, the run's end, steps,
/// trace, coverage (with its counts: the fixtures' equations are builtin operations, which no
/// memo serves), arrivals and stop are those of its pieces resumed and joined. Looking for its
/// other ends is one request too.
#[test]
fn a_counted_run_is_one_request_and_its_staged_pieces_joined() {
    let both = StopRules {
        before: vec!["work".to_owned()],
        after: vec!["boundary".to_owned()],
    };
    let table: [Row; 4] = [
        (
            compiled(),
            vec![
                after("boundary"),
                before("boundary"),
                after("work"),
                before("work"),
                both.clone(),
            ],
            vec![None, Some(2), Some(3), Some(5)],
        ),
        (
            free_running(),
            vec![
                after("boundary"),
                before("work"),
                after("crate::work_amount"),
                before("crate::work_amount"),
                both,
            ],
            vec![Some(40), Some(7), Some(11)],
        ),
        (
            strict(),
            vec![after("crate::Arith::Add"), before("crate::Arith::Add")],
            vec![None, Some(2)],
        ),
        (
            branching(),
            vec![after("boundary"), before("boundary")],
            vec![None, Some(1)],
        ),
    ];
    for (fixture, stops, depths) in table {
        on(fixture, |semantics| {
            let start = initial(semantics);
            for stop in &stops {
                for count in 1..=4 {
                    for &depth in &depths {
                        let context = format!("{stop:?} count {count} depth {depth:?}");
                        let options = RunOptions {
                            depth,
                            trace: true,
                            coverage: Some(CoverageOptions::default()),
                            stop: counted(stop, count),
                            ..RunOptions::default()
                        };
                        let before = semantics.execute_requests();
                        let report = semantics.run(&start, options.clone()).unwrap();
                        assert_eq!(semantics.execute_requests() - before, 1, "{context}");
                        assert!(report.stops <= count, "{context}: {report:?}");
                        let joined = Joined::of(&report);
                        assert_eq!(
                            joined,
                            staged(semantics, &start, stop, count, depth),
                            "{context}"
                        );
                        let before = semantics.execute_requests();
                        semantics.other_ends(&start, &options, &report).unwrap();
                        assert_eq!(semantics.execute_requests() - before, 1, "{context}");
                    }
                }
            }
        });
    }
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
        assert_eq!(rule.item.as_deref(), Some("crate::work_amount"), "{rule:?}");
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
            Some("crate::work_amount")
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
        assert_eq!(rule.item.as_deref(), Some("crate::Arith::Add"), "{rule:?}");
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

    // A case counts its stops in `run`, beside its rules, and names its stop rule as the flags
    // do: the run ends at the third frame's work queued, with nothing chosen on the way.
    fs::write(
        project.join("counted.json"),
        serde_json::json!({
            "run": {"stop_after": ["crate::boundary"], "stop_count": 3},
            "expect": {"halt": "stopped", "rule": "crate::boundary", "compare": ["count"], "cells": {"count": 2}},
        })
        .to_string(),
    )
    .unwrap();
    let (status, _, stderr) = run(&["--case", "counted.json", "--output", "none"]);
    assert_eq!(status, Some(0), "{stderr}");
    assert!(
        stderr.contains("krs run: stopped after 11 steps, after `crate::boundary` (stop 3 of 3)")
            && stderr.ends_with("\nkrs run: expectation met\n"),
        "{stderr}"
    );
    // The case's stops and the stop flags would both say where the run ends.
    let (status, _, stderr) = run(&["--case", "counted.json", "--stop-after", "boundary"]);
    assert_eq!(status, Some(2), "{stderr}");
    assert!(
        stderr.contains(
            "and the `run` stops of the case `counted.json`, both say where the run ends; give one"
        ),
        "{stderr}"
    );
}

/// [`CHOICE_AT_STOP`], or a variant of it, as a project, and the fixture target `krs` builds it
/// in.
struct ChoiceAtStop {
    temporary: krs_test_support::TempDir,
    target: krs_test_support::SharedFixtureTarget,
    package: &'static str,
}

impl ChoiceAtStop {
    fn new() -> Self {
        Self::of(CHOICE_AT_STOP, CHOICE_AT_STOP_PACKAGE)
    }

    /// The definition `source` as package `package`.
    fn of(source: &str, package: &'static str) -> Self {
        Self {
            temporary: project(source, package, "ORG-KRS-EXEC-CHOICE"),
            target: shared_fixture_target(),
            package,
        }
    }

    fn project(&self) -> std::path::PathBuf {
        self.temporary.path().join("language")
    }

    /// `krs VERB --package PACKAGE --definition main EXTRA`: the exit status, stdout and stderr.
    fn krs(&self, verb: &str, extra: &[&str]) -> (Option<i32>, String, String) {
        let project = self.project();
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        let output = process
            .current_dir(&project)
            .args([verb, "--manifest-path"])
            .arg(project.join("Cargo.toml"))
            .args(["--package", self.package, "--definition", "main"])
            .args(extra)
            .output()
            .unwrap();
        (
            output.status.code(),
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap(),
        )
    }

    /// `krs run` from phase 0 with `extra`: the JSON report's `run` and the status line.
    fn run(&self, extra: &[&str]) -> (serde_json::Value, String) {
        let mut arguments = vec!["-c", "start=0", "--output", "json"];
        arguments.extend(extra);
        let (status, stdout, stderr) = self.krs("run", &arguments);
        assert_eq!(status, Some(0), "{stderr}");
        let report: serde_json::Value = serde_json::from_str(&stdout).unwrap();
        let line = stderr
            .lines()
            .find(|line| line.starts_with("krs run: "))
            .unwrap_or_else(|| panic!("{stderr}"))
            .to_owned();
        (report["run"].clone(), line)
    }
}

/// The `<phase>` and `<ticks>` of a JSON report's `run` state.
fn phase_and_ticks(run: &serde_json::Value) -> (i64, i64) {
    let top = &run["state"]["term"]["args"];
    let cell = |name: &str| {
        top.as_array()
            .unwrap()
            .iter()
            .find(|cell| cell["label"]["name"] == name)
            .and_then(|cell| cell["args"][0]["token"].as_str())
            .unwrap_or_else(|| panic!("{run}"))
            .parse::<i64>()
            .unwrap()
    };
    (cell("<phase>"), cell("<ticks>"))
}

/// A step by a stop rule from a state with another successor is no arrival: in
/// [`CHOICE_AT_STOP`] the run takes `advance` from the start, which also has `leap`'s successor,
/// and goes on through it without stopping, counting it or asking the stop condition there. Its
/// one arrival is `advance`'s at phase 3, so a stop before it ends at phase 3, one after it at
/// phase 4, and a count of 2 is never reached. A condition that holds only at the start is never
/// asked there, so the run ends on its own; one that holds everywhere stops at phase 3.
#[test]
fn krs_run_passes_a_stop_rule_step_from_a_state_with_two_successors() {
    let fixture = ChoiceAtStop::new();

    // The fixture's premise: the run takes `advance` from the start, where `leap` applies too.
    // Which of a `nondet` group's rules a run takes is not part of the semantics; it rests on
    // the order the compiled definition lists them in, which the package's name moves.
    let (whole, _) = fixture.run(&["--trace"]);
    let labels = whole["trace"]
        .as_array()
        .unwrap()
        .iter()
        .map(|step| step["label"].as_str().unwrap().to_owned())
        .collect::<Vec<_>>();
    assert_eq!(
        labels,
        ["advance", "leap", "advance"].map(|rule| format!("ORG-KRS-EXEC-CHOICE.{rule}")),
        "{whole}"
    );
    let (status, stdout, stderr) = fixture.krs("search", &["-c", "start=0", "--mode", "one-step"]);
    assert_eq!(status, Some(0), "{stderr}");
    assert!(
        stderr.contains("krs search: 2 solutions"),
        "{stdout}{stderr}"
    );

    for (extra, line, phase_ticks, stops, arrivals) in [
        (
            &["--stop-before", "advance"][..],
            "krs run: stopped after 2 steps, before `crate::advance` (stop 1 of 1)",
            (3, 1),
            1,
            None,
        ),
        (
            &["--stop-after", "crate::advance"][..],
            "krs run: stopped after 3 steps, after `crate::advance` (stop 1 of 1)",
            (4, 2),
            1,
            None,
        ),
        (
            &["--stop-before", "advance", "--stop-count", "2"][..],
            "krs run: stuck after 3 steps, 1 of 2 stops reached",
            (4, 2),
            1,
            None,
        ),
        (
            &["--stop-after", "advance", "--stop-count", "2"][..],
            "krs run: stuck after 3 steps, 1 of 2 stops reached",
            (4, 2),
            1,
            None,
        ),
        (
            &["--stop-before", "advance", "--stop-when", "phase=Start"][..],
            "krs run: stuck after 3 steps, 0 of 1 stops reached, where `Start` holds; 1 arrival",
            (4, 2),
            0,
            Some(1),
        ),
        (
            &["--stop-before", "advance", "--stop-when", "phase=Reached"][..],
            "krs run: stopped after 2 steps, before `crate::advance` (stop 1 of 1, where `Reached` holds; 1 arrival)",
            (3, 1),
            1,
            Some(1),
        ),
        (
            &["--stop-after", "advance", "--stop-when", "phase=Reached"][..],
            "krs run: stopped after 3 steps, after `crate::advance` (stop 1 of 1, where `Reached` holds; 1 arrival)",
            (4, 2),
            1,
            Some(1),
        ),
    ] {
        let (report, status) = fixture.run(extra);
        assert!(status.starts_with(line), "{extra:?}: {status}");
        assert_eq!(phase_and_ticks(&report), phase_ticks, "{extra:?}: {report}");
        assert_eq!(report["stops"].as_u64().unwrap_or(0), stops, "{extra:?}");
        assert_eq!(report["arrivals"].as_u64(), arrivals, "{extra:?}");
    }
}

/// A case of [`CHOICE_AT_STOP`] stops where `krs run`'s flags do, at `advance`'s one arrival;
/// its run took one successor of the start, so its expectation is inconclusive under `krs run
/// --case` and `krs cases` alike, naming the start's two successors.
#[test]
fn a_case_passes_a_stop_rule_step_from_a_state_with_two_successors() {
    let fixture = ChoiceAtStop::new();
    let project = fixture.project();
    fs::write(
        project.join("stop.json"),
        serde_json::json!({
            "inputs": {"start": 0},
            "run": {"stop_before": ["crate::advance"]},
            "expect": {"halt": "stopped", "rule": "crate::advance", "compare": ["phase", "ticks"], "cells": {"phase": 3, "ticks": 1}},
        })
        .to_string(),
    )
    .unwrap();
    let branch = "the run took one successor of the state after 0 steps, which has 2 successors, by `crate::advance`, `crate::leap`, so another path may end otherwise";
    let (status, _, stderr) = fixture.krs("run", &["--case", "stop.json", "--output", "none"]);
    assert_eq!(status, Some(3), "{stderr}");
    assert!(
        stderr.contains("krs run: stopped after 2 steps, before `crate::advance` (stop 1 of 1)")
            && stderr.contains(branch),
        "{stderr}"
    );
    let (status, stdout, stderr) = fixture.krs("cases", &["stop.json"]);
    assert_eq!(status, Some(3), "{stdout}{stderr}");
    assert!(
        stdout.contains(branch) && stdout.contains("1 inconclusive"),
        "{stdout}"
    );
}

/// [`CHOICE_AT_STOP`] with `leap` guarded by `Gate(phase) == 1` too, over a partial `Gate` with
/// no equation. A run reads `Gate(0)` as having no value, so `leap`'s guard does not hold at the
/// start, whose one successor is `advance`'s: that step is an arrival, as the run reads its
/// path, even though `krs search` prints `leap`'s successor under the condition `gate(0)
/// #Equals 1`. The run stops at it, before or after the step and with or without a condition
/// that holds there, and a case stopped there is met, since no state of its path has two
/// successors.
#[test]
fn a_sibling_whose_guard_reads_a_term_with_no_value_leaves_the_stop_rule_an_arrival() {
    let source = CHOICE_AT_STOP
        .replace(
            "#[k::requires(phase < 3)]\n    leap",
            "#[k::requires(phase < 3 && Gate(phase) == 1)]\n    leap",
        )
        .replace(
            "#[k::function(total, internal)]\npub fn Start",
            "#[k::function(partial, internal)]\npub fn Gate(phase: Term<Int>) -> Term<Int>;\n\n#[k::function(total, internal)]\npub fn Start",
        );
    assert!(source.contains("Gate(phase) == 1") && source.contains("pub fn Gate"));
    let fixture = ChoiceAtStop::of(&source, "krs-exec-stop-gate-fixture");

    // The fixture's premise: `leap` does not apply, here or later, so the run takes `advance`
    // and is stuck at phase 1.
    let (whole, line) = fixture.run(&["--trace"]);
    let labels = whole["trace"]
        .as_array()
        .unwrap()
        .iter()
        .map(|step| step["label"].as_str().unwrap().to_owned())
        .collect::<Vec<_>>();
    assert_eq!(labels, ["ORG-KRS-EXEC-CHOICE.advance"], "{whole}");
    assert!(line.starts_with("krs run: stuck after 1 step"), "{line}");

    for (extra, line, phase_ticks) in [
        (
            &["--stop-before", "advance"][..],
            "krs run: stopped after 0 steps, before `crate::advance` (stop 1 of 1)",
            (0, 0),
        ),
        (
            &["--stop-after", "advance"][..],
            "krs run: stopped after 1 step, after `crate::advance` (stop 1 of 1)",
            (1, 1),
        ),
        (
            &["--stop-before", "advance", "--stop-when", "phase=Reached"][..],
            "krs run: stopped after 0 steps, before `crate::advance` (stop 1 of 1, where `Reached` holds; 1 arrival)",
            (0, 0),
        ),
    ] {
        let (report, status) = fixture.run(extra);
        assert!(status.starts_with(line), "{extra:?}: {status}");
        assert_eq!(phase_and_ticks(&report), phase_ticks, "{extra:?}: {report}");
        assert_eq!(report["stops"].as_u64(), Some(1), "{extra:?}: {report}");
    }

    let project = fixture.project();
    fs::write(
        project.join("stop.json"),
        serde_json::json!({
            "inputs": {"start": 0},
            "run": {"stop_before": ["crate::advance"]},
            "expect": {"halt": "stopped", "rule": "crate::advance", "compare": ["phase", "ticks"], "cells": {"phase": 0, "ticks": 0}},
        })
        .to_string(),
    )
    .unwrap();
    let (status, _, stderr) = fixture.krs("run", &["--case", "stop.json", "--output", "none"]);
    assert_eq!(status, Some(0), "{stderr}");
    assert!(stderr.ends_with("\nkrs run: expectation met\n"), "{stderr}");
    let (status, stdout, stderr) = fixture.krs("cases", &["stop.json", "--output", "json"]);
    assert_eq!(status, Some(0), "{stdout}{stderr}");
    assert!(stdout.contains(r#""verdict":"met""#), "{stdout}");
}
